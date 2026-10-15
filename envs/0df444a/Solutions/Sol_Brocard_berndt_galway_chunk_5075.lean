-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5075
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:39:29.470141+00:00
-- url     : https://prove2.me/submissions/b029052e-be6e-4cc4-a097-b2a2a77aab41

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 912589928 ≤ n < 912769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 912591178 1250 912589928 912589933
    0xa180906060b0403060f05071202070503070b0a2c100c051e0c0d0c0f0b220c06080612070b0d0902040e0f070f08030a0e0409020303121605121305070305 67
    0x4602c000380500103005890043c3ca06110400c0c0380d44019040350000c41d40000091003c28410740f110384c0c103800518080b40500112414114292110500698143d55101100d80e958102c541320042032840e07503044a800780c0c100c2035045000e80c90140c42d4482c180b04001c000d80d441b003550380312a00510556841a4400c001060300c0d600b0201c052070140e00c1001020078512644c1d82cbc030b8040345d00c103c041d00340059000900c3c4255007581e036540132030030801811b0094000340a02d1000000d000d4101800310039400340d0342541e1282e1811a0240280754003620040c020140502032080440c4005904811107041d10740032551840c501007603c1c018519503030000e45c42400c10a141c00210304c0000e0308000001d044041d038840e0f9585011a20f89440036105030b00356a0030a114095500b801084100c1060002820204050344ca66001a007076034401b07440362030005002428450789003081e200340112a83c490802d5494588445d100c016080c100610140d94101c25486001c1080003e104050095a11108 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 912592428 1250 912591178 912591191
    0x2070614040b06090a060501020a060c02150403171305062715010906050109080a1e290a020c071413020406111b0603150a0b0d02040302040f0b0a180906 67
    0x2c0007000e40c2c0042d41c07168400d821090205058400703920603481102c005800401039412150b84510151201c00050000d42c060080c400c0380351700d500045035225038442c0d500c01c8030000d004000c01c0e051000c0600b10b0401681c6241750384000a4000450980203203001c0d0062042c07152161071703144140a1021010b129020300c000c100490311844c10154165003004d42c3c14400c007a1103400445014849208080f9194007820703070140407900712424403005070010b5440072042d620f0368460080000c00d050070104038243c1181c00c81030110344121010782103c17418038150701d0035042d4440d5544d170341d06600404120031411041240c2640e90303424455501c82d1000d1066444070740d02d00c00a41200305003aa240303028001c0c07910003960b800340142d18904084c00104160b0942c0c5801648400e603810701c3c2c81050704154503510100da09080800941004070f01828050b03950f41c21841400182c801b00d91403441c02504004802103d80c4c2c8a141c070700207480e07100b072032507800030071002c484d80241030f9070803000d0309a514245 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 912593678 1250 912592428 912592433
    0x105090a15051f021b0d02091b0316030c02010c09181407030504021c051b01050714061b0f030c03091014010303140712141c0207020f03030408070302040207061404 72
    0xa0200d0034443c0b068094500041140d407990b08075007482c0090030780c4a0b08a206450052a1000500343c100301068601c3d61034540c900000011940180c0d00070b2003000c440b080258409a15004140028130b007031000f4000c9040c0000094401005401801c02410454116140f0032580b980101800320b03d580c2030023118186a0b10260080c9010741d400c5c0e0050407900b0b5421290744011445415040c0c2c007100502e1488251030b04208105140083c86040040420a07000402c080342c001c02e1140403514060314842c10066008881c4210152244003a00800c2c41016128000759042c1c90307200c05165007480c1d6a5690b001101d080081c0aa071842c1c0345403511504d84480f41010031000c3c1620b03c01e446e80d000502c64540065040d0246240081010b0b0810307150745010752042c02c0c009000522840c041e07013031035413031007031030a0801e609481d04018a0340815031805600c0c100d0070b02c40e285401a00a903191a09001500c0e0700c48906000190003603400049120400550364407031110005001034451950901e032 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 912594928 1250 912593678 912593719
    0xb030105030c01020d020309040504030903050a20041e0e010204050a0e0103120c051e0c0a1e060908070e040f150b040e010e07060c08040803030712060e0105090a1505 73
    0x38012140a4881d503400c1c01d596500000721149244d800b60019070408082904220203040010f00803001c000d040000000026010400c10b00028402c4421000001460110039070f807441401c405481a8200302c2c036207041060041d0440401d4200340408504102c40344059406841140e02c955000071002c400060303806548080c2c24140c9108414004080d401218120340c40a0180805030880c3c1000000217101e0071007070b200004a58406041d28010310701440043d644081d203038011134004401181014074800c501c05804c001d8949410070002090400034403598820b01d40c00752034800100c40022400f4000325440030361071075030711100d1904007114101c0c0b110050030307290070002c0c020380c01d00d2082075800034180030f100c0c48807a1002c0140b8400f8904003045503000140d103010b4401080410000c0f4043d8014001940f1031480c82d01d40c446020550105201101c00c0c8ae401034641c4a4088010300c01903544c0c01e0350036007100340030710301090b10441b01c038401120b84100e40c031495010f9a0142d03881c4d0b00f00341c103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 912596178 1250 912594928 912594931
    0xb2a0f0a1202030304080306060c120a03020909060a060c120306080703200f130c0e031b1807020c04090219030506071205090a02010f091703091315050402160b010b03 73
    0x9081040400850310405a983c1c0c0010b4800815260b002d100041d02400c106c00030b001102c00482c00c80b402c0c06082c90076030969074000010000000d030001034080c42403c0c44440590020b100361a420700032480c1c510001d260030040c010080c9081026006c0e200041c0c0301e80c00c06402340011105441c015603403490500c40015460040c00403442ca9032008800c90300d02080e01501c5400041c1c0f0701c45242190024041c02044d1039140b001c2406290545640c00d61010000c0c0380d029510784080e031014005c100c0400141074001d842d00e50b10840300c9010840056800f0a03000074179141a500450070402c0c9100080080d07125000381c01480c25000c40000500000082440c0034203169111810403011041d070350425200c080f20780c8980303503005d13a61000c0154841c09400c00030300482d141c5041001c0d01c44640d403404130080344030080741382e02c0031801030f419181c0204055070a480000c0700f00040104030540348240c2d10039208451145034041100128000a0300704808100d6000041c0031956840da5802d0303035203400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 912597428 1250 912596178 912596183
    0x15010212040b070b0603030c07030305090622080c0d08090f150304030825090b09060c03030c0705010c080702061503010e070602100f150902091c060f0b09010b2a0f0a 73
    0x225800f11709141000302c1147e4195100c2c0020307020443c295107040d50203034002c00402e41c00a004004522655117401c90b000c6c9000281e040e01d51100f841c01a100e881d115502d40468402c010402c08140091907942c11607001480075107040e8011000c0a00081c036441981b51000c01c6401c0002c1008200341e80111124070584015030143c52010740c030b81ca942101500c01c409140820200b940c18003800a80f00080c04005400800580c50440100015415508195441c1400860116044c82000021300440f040c003016860b05041d1494004070007955414040c1c05400785a0000b2351100850324290042c01c4443c2034901211000d5030f407042c000703554001b41040c0d4a40140380c01c1000d90b076002103000e009000c84990001141980c1070618502c002d5110b210560380c05094039000013012004065200344540c003403440058009600050503054070202c0c28400d10900c490001072203039508400c1030358500e2038400800c04512449036003c0401c6440c02d8088081031081c541501e079100000030304580b8052 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 912598678 1250 912597428 912597443
    0x1509030a18050114031008030a020303010609061701260616020601090c0e090901020705060a0f05090610120303061e03051e03040302010e01051c05010f060c050615010212040b07 78
    0x2440d00d080807500000074010540003c0500c080140452000c10184d82c00030f400e0b05251030070726680d9a203245107600c49c071003203009600048010070100e500b0804540007031120b400c141140082a100340881c0c2c510500920121030350700001600c0800c03050840b8801240071401329140303410011151050b1001031560800103104000001c55550a0360043c0001508192182000380391403404110741c1550040c00781080b99824008200840e804200c030901504414200044100402800200380d60004043c0b5003030798000024441168030201c1803030215444041e00081210140c6000c90103030120758072000c201881d0040c1c80300c1e105034070122001140d119508590101c000b02c440c03c840501040d84690712a08141701c2000994041c010030766965405160007894544000351091040c0007211100c070b40660f0703d800501c4a80c00b45030f080005060941030480f8284001d9031043d0382d40301c00400c03403645001003590260f2745034000c2101e0b41c8800800d262564407035442d16034800e40c0340c0195005179000d0303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 912599928 1250 912598678 912598697
    0x23130515032406010c050106061e020a0f030305060604050d12030b1c110103020409050f070908010e070b0706150803070210090332071823181509030a 66
    0x501d000100080c15854030400200d14191080322900d00c04002000d03181440002c40000c00000d0080c4210400f510540d1601892000041050700c54010610030300c4007550f128244140100b24100030301c400c080d0341841c02007410356070000811b4403409241d000075007044442e8581410000c4001c1020070f00925940e041155502110030001404404500c0c00b1030b40034900e41550104403901c445a50010042c100507141c680e40350280b074226082152005603a482490038000071503403003c04d001c01440004000d1184000b20410b040d00d401c0c0f280710308441c580000440500300504c41d0004d040c1d49039426440410699144c0800c4d85a510240c4100c0c80b0351494218010314501030309026058035000440101c5940a200391088180d034072001c05204624840311500792000c04010716030181c0016000d004041507120301d0003041d0760f00254801121015017508208048116100c1c0d40d10001c001000400c1d01090380005080c00d141c8030b20f18240b03104820800011140020080800750f40380d50782d010f8503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 912601178 1250 912599928 912599971
    0x21c120f05010e0c07020d150b0a1401110f031b0133080a030801050603040311071712090d080a17070c02030c090105030d03020a02012a12020301030c231305 69
    0x3034414205d00950200150200b00082222a401c00d120321001d25800900d5204800014291401540c000708546904611155040d40d00c00955545001d00d0001403080a00242c03d081e102d0046400240180d00505c0c1d49807132055094202030010881c4040d040500c107540441c00c003a100c00b943c1c04000c2006034050000d040c080010303a0404068140e82c43c0206642060708000c102d03400540190304000c494550344c6100300043c458000101614018159008250021603044c880d810181c5139010744203105000007910398110010241c2ea01c01c20181d90382c0000401595540e11021f40e813200300c6c80b00000c2051058100ca022140d1600072800c07a0003140f260030030804005000d0240c1a0150044401c204541d402900500506c1c84280004560024000110b85407034521607060704030781d00c0d0b41c109050955040300c8940001c0c0d0b00301d00306610390760641e00c54001014030340c8100d4510500890700440c6414080c103500c0c8110000034070382226144640e00744800740409035800105c021001113850795 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 912602428 1250 912601178 912601201
    0x9052d1204030803010608060d020a150e0f0904020d0f0b010807030309080c030c0118170a0b0108240a020906030a0603030305010f060e060f0405061b0111030106021c120f05010e 78
    0x120ba910681152850b0b00708501210054000f4203aa0340040843c2c103010010b9540902c00c81c042c01c4440f80c0380c40e81c0185500020701c4442d41420715800f0303024500c000c0c200c90302c84051840d44a901990940d041c03c0803860880c0184907030003009806483d6440021071110808540c83c82101e00968529141c15210102291500066600c00747d06078417901403850294050300795020244907016440c5480e07075444614440d02e400358400800f4a400452000c403c122010344028054100000140135000034605030340148003d4103407210b4801206c50018a03400e5841d0122900f07004013504407612403c02a070914054100d600003140803070700302400410038580c6620004221349013562246141c402000a118003036014515001c010842000089582c0c3c07680c20040c4a10f0442d5070900c02035500008480e821500400701140d0030800400041080560000c0d541480340d001240b00b460541c900d000662356503203034880900880342041c8042c00d8150041d400301d4126507010384000100c1d42c90310803041 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 912603678 1250 912602428 912602437
    0xf0209010f06050a030b03030405120102090913030516051c050a0f030e07050103020d060306050414101a0609011709010204170d090b03040c0e180c0d031209052d12 72
    0x41c0003500c14010342490390b05c00c2e0419a282180601500c3c9415245c502065800601d48440d050683d00001e6000c994100107a0300c6e41c1c82100b0404814640809a40042152007507900021a50011603400c00c1071003814001d41c0b1290b640381007880300201c146040039289030001d80003440850181d40030015401d00a0090340a00500c020140000310305150041d0020f4000c1d40510b03450070b680e00800b00004085205250255004201c111240105128514a4409181305a0704124104024980c2140f8a1099043c0c2c40400b03d90061b03c46800d40c1c0100d4084014240c40341c504103000050000d10790040d4000c1c001e480c04015006003885100d081941d031f92200c04842000162512810049910040d02441e0410703c60031080d05e85550380c900f042c1001d281a0b070070352941040040400b841580c10006941e41d0308042e201c07460102d0343d80c4c8019012401c462030350040306031540048010841d0510000c0301c616807110781424100b40c0e03540d20800c85c000d600c0d081101c80c8602d0b100d81101361031b40d8080d20f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 912604928 1250 912603678 912603689
    0xb1c2a09030b0712060306050a0e070f0503071202030102121513060e0a0c141315030504031e0215100303090e0c0711010908030a08060301150515070f0f0f0209010f 72
    0x2c20180c8500710115503403030b1140b040c0c0204c0b40d603501c0c0100000c0d00b180281c03802144403e8020800c6a21f881c0c0340340c280f02090740410019a510841080b031610040740b2102162404200c0f400095103900109000e03104c0c1141c0d012401160104104800c80103101c00c83e02254140c800003c0500f20480810850f04076001d94840c141e032140007e481d940c41604038803481504e40c5802052281e4540c5061300d542c00004c41882d8100c0c4192040c407403070701c100c5003014040100c0c1c9400d10047c100f42e1805005100e2400030f01000c1703000044d034000920f00030050558584203980c0b0030350980c0f030000100c041301035441c00210001801d40e0340c0001e4003003000603500c2c0500701d0754410074031700245ca035034200001524006a6041c03000208001440e400103101804503040d10707407915030003450201d04140c219003402d020f01c0d241100300f110a00c0903845100036099440c0501100b03617555070b1030313040c800b041d0141140c00903c4080c0d45c42301388040046140105030310a200740d443ca09141d8846411500c074074158002d1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 912606178 1250 912604928 912604943
    0xf11040b030a050c0909040b0601120203251112130e041a040320010e0709110904020c121c0b18070c0f0204020c031804060b040b1c2a0903 61
    0x118507280a55403029400415121320b9a203000c14110200c2d44000303048a065444c2c1250008000140d46c0003031844d000080342c0321085107140341605020814000c01c201510304000514041103445000d07520351014045100e00301e4007100d0704801034100648c00411100818503825000281030001901380c14062548650b040f601038400001c81085002c2c0144150100181c841e8001101c3c5003103441d5104203c51200082423041124403c00d1418a407a4010202c0a1408040d4140001c0007401e854000c1c400729000750b582c50140540b240343c0314140e0a4880d403440d00040c4001070b150404181c0f00003469040c000c0c0120111001080b651592014100903080c080000180090340300380b180500c070510840301007491103060380209089811050a012940d4000140e2a103d9640c1c04581044454111002e12100c6e0030014a40300b280154429180088001300c3c4076201240b0b004d0fa070203c001d507191820000094002010740c10040f401c001c0c01c00250170003481e044660310a01c4d103c41500d802551 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 912607428 1250 912606178 912606181
    0x5090609070c0618030806040e060f0604200c0309030f15010506161407050f03030708180303210a0c181403100e0f0607021c0309020d020d03030f11040b03 68
    0x101a50300402e040307802c5425543c1c41c240544034080701d20014051034003954480441e49001c4050000300e031a141d04c0e81d49554420000c004488080c405403031b51195042c2c90100f8565030960102d5050302007000030066601d004120016914030010140030409400c0301100c0d20703d91171031022903c620b440740c224109004018018022410302400910441c41e41c3c1410907440e00040e140c0c0443d280201c803944440c0d4100841c00c011500e400c8000b00020f0208034040d40ca80703040740d940c54a45204400341d0740c000003400c51039580305a40034401d4a407401c62030961616404403a54048031184012951440c08030714007109403034698802d2a1500404500355441c07403415041410000300003803180b41540d4580f00d48010311000074081e0144558400c1c00c0f10080c45c9840e04220340c0c600b0904000d1806003150720400805840f40113107a40c44580300d036107060000f41e00c501070011034040c10307600384065003210080c034914003010f44c1940b1507000c1c503001d8003042000c4480d4103010446d0703225511403010355a03401e10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 912608678 1250 912607428 912607441
    0x1030303021605010f0603050c0303090303071e021203070303050c040312030b031009152004030f0f021e01020d05130b160501060b0d140105301f0605090609 69
    0x50050140401c41d41044440c0460b960710b80b401e4441007280340502c41d48855040040203010003900c90301c3c00049000e942842d10300c00c0800c1d0b49006140000d0910144902031140340c224101e0b004c0a01a0050001070040c108074449956039880280120002454040010198003840080e102a29801540c030405000c0b070f40c1c400c5003d0818514510340c0350003003840d000c0003014940f15103540540324640340c81401d007200c1798040031694002c02000c902c00c102031a1038951800d020031038080e650701641100e0011080d0801000c0c11185820003508082242654140301d80510f00305881390b8400d07402c071043d0301e500b000110743c01e000b440038000d001d0740000010712815084a01a010444078103110400756203541c0c0f20a400e4451941c4082003004000880d000e100b0481d006d4103004050510300d917002c2c0c1d450400864500442c0c80181581c140d8400c660020f9420728142e40107804801c981260301504800304da1b00f0720003044001003407000c2c1c0340840020355410000602c034403445005050161544d140d9 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 912609928 1250 912608678 912608681
    0x3010507050a1d130902030c040515090a02090303030c190905013006120b070305010317030601120e0708100e10021b0d020a060f0b0d02012a05030a0305071701030303 73
    0x201249581030000c00030f0b840003922410b40013085140c4140c00440d002c0260700505080c801d8005086024900380f030200000c0071500d100310b0b01c3e0010240c40c0301a803a6601c6107040c0c002e00509400d660325020000500c000f180390a000703131003490004000400c00c0c555226050300d400c0318a12442d80070a070710b40c0500649455000c814000d01c445100014110030140c00c1c00000c0310010b4102194003001600020244940341495982c003425a0408010395411515003082c0b40079400d100508070040000003400e01e034481c0400d0452104150001c0c000c02070482206510381c0c4440c040c400f140e10401c203400b0032112042c026a450f0b18101c0d80642062442d80042d04003950069842070001101034a01c142454010054040f000c101a03028084030742d41803038108250b500207030340401401e0414107026040d03524910b401242d42d60909100b031810319007000c02e40300d01a00720703802d00e40c114107030f0b4501061100102c010030002c0740d03d030340070461b5a070351034010344448000c0d055110528100c06c00500c000f034047e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 912611178 1250 912609928 912609947
    0x60712050d060e04050601031713050402030a090f05100509030a050409051003050f060702060604020403110904021314041407081f0906020a020d091a0d110c010e030a0e03010507050a 80
    0x91403000b0405644550030f1001c0c00105844c11075140c1c0c0300d00700400a008003090903030701c0914a00c850078600440d00e5014841c444040c02444d100350350020109100382072a80c04161410781c4a00041221000307410415190344d042e01d0f80e6038002e820071000522001c4040100d40082c88291907031404c107400e10803100000d11000745090f4000003c80d002002140c420030600c00c030321241000030314061a044034000c0c14a40d014003210302481c01031006100080000c218000201c0094036141800d40d2507000058146511060f600b50440c6000030040d641e21040e00501c2c07140380650300d400e0624044100050b5a206140f090f000c45400c80800b500240ca100084400e01c1070048a020a024034162201d1007240d110000c02000b6900c502d85001d043d5400c9840750300201005250012003600e2104840400e00c24112030940c0c550366083e004850310b18590070b454031012220000c22088400c0c411050740c07580945500004030750401da401c005494140200c910030f05440c4d6031542040480c40054074586007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 912612428 1250 912611178 912611197
    0x50402030c04050415060f2301120e03040609050d050a150f020d0e16030b13050109080327060c04060c030e030a0b2a0306010507080f130306060506071205 68
    0x1c420340500c01d580c03140681809140038052180000d0304000c0f0306004c950040d48503c1c1d0090303842800704860f00e00c0820341c601238a52401d501a043e95854012180d00684c039050000c12450072a03207c0790040008064419039095481d0a503c65880f282000310b030404660000342598016100c10000031941c100d4045490090a0080340c104d51601000050342c209250000c105540c80b0f018004640040001100e001e01c1250399030046400d5407a0b40c1d0041c00001c00190007030312140b20450401c6000d51201c1007007a0031030076158030782c00d0500d400001c542500c070304003194860010510392320140206116008900d00c0e0210f40ca054a030520a5902411030b01381075040c809490f031442020f403010310464042905c1503401c0c1d0b607185040070050101c503c260301e04030620070448031881466484813007200d4000000b400c109458410916002c181c1d840740c00003009101038049829410041c102c160b071020b03648105020b1241075118814003510f4020b850f40a404000000d500790450750250004046021 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 912613678 1250 912612428 912612433
    0x10020901053a0e0d08150a0e011e0602031602040b10020c030d020a0201090e06272505180402040b0a08150f031f0b040501031b050109051305040203 65
    0x315940071001c1d014a41c2404410300200744155060a40c500c040c0c0154500000d980c200328003d001601590341e840ca504503802403210480104800b0b40340b5205800c80a0401010368500ca91101d030004103500d070038460a0712541c41c254020901c0403002c400d5a05640807a0300850600c0a034121480c192034606e02d050380c005a0318403422019494554203181020180d070002c003000110380091502c0c0c0700294560000b1500301c0240f900060303038011f041c001240c1042201e00d6441d242c3c44005001c2c00c08008181e408190001c90958400c0c0f60700b100d861103070215072105060310805c0c0a41d00c40d4101e030705c21800f0000e47c042044102d0701d0500417400000401c041c0c001401c00d5203990105c030f05540301c18070000c046500e4408124580140c0203150740504002d0781e42e40706400da5070000c83c1d522000c56107031500c44400d8055080e136400c000d40c40304001003001401440300d9692801c143c00c989480c6400d08003070010300d150100c4d60b0750007000d1850440d0340250411700400c54500d1480000c0a000c4d2003241d160 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 912614928 1250 912613678 912613687
    0x31b030d030b06041d060a0603020418020f121806010501090e07031d06100f0902120f0a0225052505010e0f0409060203160806100c1b1e171002090105 66
    0x34002c403100c14055150158412030b0406c0d90400c1580c1e2040d44c440c0b01014010841880040d04651300386100444000707000d40c5500d40c00e000f080c024003e8810214400ca01103041017000a00c543c0d00c00580e81500007540d5840e622400111f0f001d071514010303215141880030100d5001e511a0b031040420800311b070b0141040d0069108100e09000060701c0b401c0e060007143c0c00c20701c0348081401c4813000402040307804518050074680d04082e5644020442c0c81d40c0941040007a42e41c95007a0115004110341d002c40340c1e8a10300d0b500300f900000f10054410f443d144030b000341c0d020b01d01806138020508940f20b40003110300b040c5000e00441d000c0148003102ea8000c440c45010611585560180c0b0030703003c1c071414002d40c40c2d1505003800030301003100144400821008005000301d545a8080134801c021035480c0c4085025100d041449581a00302070907850b091480a0018140c4401c2201c1e040d02004003030344040783da03583e40344244400609040941c0316048182c041011a03035503401082034180606089007071 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 912616178 1250 912614928 912614939
    0x1b03070f0305030603190f0206090d060e07060e0d02010e060a17010f1d0c03040b180d03090519021309060b030f0102090301050601141606020405120705031b030d030b0604 75
    0x1114080c841107010803030110a00c0441d15092054202c1d220706840003a980344025245c1e0007049007c00c1010f801144009003d1000b600c40e046007040311078000100b4005400100035180e503139207452107094002014035036012810f00c1c0000c0702c64021a01603540b86002c401c40c5003080902e0b88416211b200388a030700e200403000200c50007110781c02000d01c1918031402904d400c51450008404c450303041100401441040605a0f4000503240c000e82c02c800d8a12081e50382c102d000c0c0d20f1031103800c0c0c0056944512140581c2c403039072641003144141d2041050b42e50041407141c102020038000e8000960001c0e40ba042e208105280740c3c00004c0f098040e000c0030600c29582c0700400d040c0301a050b403088050350005034140850500740165600214203107080d50b100c11080e00340320001d000381080007090380b5440c1040000c6c00040d030123550190100420710728170541c0c83d10a455880d1494030406000e401a805070516000207812100c40408000d400791408903c60402200145214401560f000350140408500c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 912617428 1250 912616178 912616193
    0xa050607030806030c3a121103120f100906050d1e0b0103152304080703030902090117070803030f070f110307061d0105090721080d020901120b0102031b0307 69
    0x12800c09800c03405040c01606c42906a0210310410340b8854960b000380d2802c0055035014001ca200b141314075040d0703c202e1100f00480e045200c0d080203441654145030510542404950000e400b550020134040c0c42195144140003c0d901c403441001c3e4800c4205d000b11001c50051426400c9a40300c1039510b01200240342c0e07a90000d42001e8105844038090001c100d103911010388218111008a03c640b41e080f0b050600e61f407600304000420040c83c040010482c0020540260009412558000c140038020760310344600c05141e210a0202c5000c07849030b0000001e60040c0802202d015506031503004126039200314003034601043d140c0305070040012041100c40c00003400d002a200d681c0c0700e094080355055448030061040c206851802e0076a0349004c041c0300c3c495100090013400c661030700c5c0d040700301603000c912a4031749055040c0b80907001c803400145000c00d1000f070354000d0550030400d072184203080405c0100c280444500c2002a40540c2c8100210a1461001c00120318602208000c0300d00d090059541d804 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 912618678 1250 912617428 912617449
    0x1030b0a08010b130510030305090409050129120706050f04150201020921070306050703020c030c0c0a1a1e04120b0103050706230306010c0c0807080105060a050607030806030c 77
    0x7805075941d490601c22841d141c40d20014024034890140301e1030614a480865841d5240b0005061080004070f240807a01e640e0081400e036500803000f088840c4002038220b900749074001c51401c1c0705d10502100205442c00301da0494000b10078000501c482402e00384240c078140d1000d45046a4440207000000f00034040002c5081c60035401c0d030016890740c0c00c8900b801803031412006054424000541240c900403400900641101d07000007008c00c06440d070304130584c002c3c811700c10002414000003c001201d00b80009844082c0307003054540080d190313038482c600b0300380c40c440300127400130100e0401004c0990200f483e658004803200d00c807440c5c901503440a5501006869400880d000b042c200010401d02c041031090100420032420b001e003580c07000c5005010020b841c2c4551002090011000c0754079648605040070000d43c0c487c0c0c08001c0c2c9606c1c2c0c0c0140e80d6821861203203c1e907070343c01d000004000f414000030f80c60032500c0103000e4a0a10905a07000e1710030758802418a81c05100308030b19000503960740f01608 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 912619928 1250 912618678 912618689
    0x509061801031107021810091503050709060605030a0b01051c0b040509060903091228061a01211e090b010b16031407020a0f0608060a0f060e01030b0a 66
    0x10399510608005419501e011803031405100041c000720700540c80d100710800080d07440c621441c2c03007940c6403000000c2801c1c00d500f016191034608001d2001d8071760448075080074ac0340100106c454069450b413a400650b801070080600194042c408a00781c0600347c2c01c038100c02d00c0141481c0382002280740c040320009003c0d015401e45142c440c1d4040303c2904052050175040f100900c050481d40c54582c415a58a214074568540a503409920b001d00400c000d004c07000140c81c41074408400c060340c1e102d5002040f00564000c1e22600e240010728051310a10310a118980907042e150104056602840b4075500c2484e560b60030289600c60215210129846020f052507003859440024113082c2d0b8142402604c2d0144c02192248004200704110104a0410728000075454500007440c440c1c80072500c00c0c24041d41c003000350002c03c00303000400d04401c10740d20b0700c055071007640d545065990b58608000c0c03040c01c11312886440a055442c144000d52007204003541001040c10f000c41c1c81080c0c100458040e29031a40710 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 912621178 1250 912619928 912619957
    0x120f04030516090e07030c06050f0d0903020c091315050c1c020417060f040209060102031e1806030f04030e0a051f0305010b0c070e1305010518060c040e06060901050906 74
    0xf03200c100ca042c03003106400181d490042006a00b0741e0b541001041d0103008441c1880780c04191801c0954104c001c59820028040702808403540750314000e940e401d501030302c043c80754010000003040c1e80d40c19800302054580140302201d840406600e04001090045c020030307841c110801004c21007541c54442c0b11840700c0d10380c0c401070740c85140c40d0441601e4008c1f844000300035001242417003c205010b9080c141c10940440d0300014549450b801071b45107128500040040580d0301c1d40740840201c200c0e001c6d0502c1d0380318048200110002c0300410182e48401c0f5002400a031009021401081c13084192100350319001e8480b1000c1525080041c013444600c501040b81c10368051007003031510380e03d80207082c01130494002703d50034464809401c41e00c801107030103204880c03058a0300007a45140c01c40400601c55821400802c100d0a100280900c420100002a4101e12804007c240800303e00b108440444089845000032910b44d44200051030b800445107a041000c14043d00c0000d94602c0010640c00360b20450 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 912622428 1250 912621178 912621223
    0x6020409052703092101020403050d0e13020f0d0902030c0a0b041401020a05030a0503101205010203100b130302010c0f061e0b031212040f1e03080604050405120f040305 74
    0x4019160b6802c030b4421803640d0024428420a610380103803114103c003408107200300c40100304181320700a006541c4090001c3c840c55200c4040305400ca503100d0110781c002e5800b0700c030001500c50384506078441d1000c4060100c02c01c2010715441450381e88040c0c52188000c085c0e90380c602207440010199200b036003198154880011301080303000c01c4003d01c0c041e121006e0001d0b000d45003158a8664490082c05406414050004000b078611440c1102000c0034085550101e024003080c4e040a50007500121039003050040a640d020961042800540b50941140c20300c40e080d440c110745c011a4160340220045400344d16005a801c000fa825004800900451031080030803014040c0580e800d41d4002070201d40a40c0003540f05004103210202281e5034140004004121901c9524001e00707008004800034004120303205070005590004c00c40c0d0301e00309000c0e99500310075480d00340411088880590303000341070380d204544030499540c40c000a4480100c40304903440c1090b43e0b98645a0400d05881015000310f00c8041 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 912623678 1250 912622428 912622471
    0x4050a051b040e06010b0403080a05120c090f0405040206030a0f060902030903070b0c090105070b0612120a03062106090f141f020c06070311090315070801081908070602040905 77
    0x440c103d40c502146004241c254580418860140304030b01015245040001d400b00120f8014012205030540c28210f10186260000d0040310a400043c0918401e450564805e0b200f460540030f030600444e00144643d107580c44c0c128650008001c1010040851600d6000001b0200a10701c090361042c500c00002c3e60350f803c040c0c034040c915420300074a00c0030300c04003d100d102540d0744c1c004180d414096103c1510010391715540c00040004058044185041c81261484031580d10340001a10117400079031818803050307031180c00d180d903170481c95040155585c6800c02000c01040700c5030000300c5054000c03840d450801c5103d80b5802c522826940307000c0415442a403412107a180c80440089a80a0710307a030860070031a0b8000c0194550340c6c09800b150415031039600c1e4511310348081e8111444040c00500326810000d84042813072050381c0850300301c0d0200d01d1a000010301e4400101d030031480401e0034a030380712141b01207503103140c1a0b40120704103640842d030030300c000b00302070070184240b90190041c22100c8a841c003016 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 912624928 1250 912623678 912623681
    0x515131716121704030b06010c3f02030a0c06022104060902010207090c0507061d160e10060203032a07050319180302060c0a08191b02010c0b04050a051b04 68
    0x21031401a15500401c010804102c258400c60f404c10024a422150505a400c115102e11030100d0035103000070b000210344009180301c1d12b81c0045400f040301c11540e500c044c41d0b070a0342c990207a011008007145403580174000140903503000303001c1c401c89a502d080c031543c6100007203c814841110115103c5588070716200940da01009981c001740403030703c070038030541100d42001403203802010303001000c068547ea00c0c500846007125454550b03840c007004450029010029144070036803d84107101c007811400000c02e80c4030707010302c041030145c4096400940ca1070321440c80607000b404050071a501c0900c0c01115401c400580d1307000800030030b0300400045480300424081000309101e01071000740bd0203801c80d8500c1121907035403074000071260103c44054a43d00d00ca0162800c05040000c010411032000030a441800d110b092002038030142655183c00c104800fa0242980d1601400301901042c401d4a84500040301c1007600c039400f5116500340c9030401c43c1d50361054078149036445000750b08045159480d145003042e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 912626178 1250 912624928 912624953
    0x150513080102030112060b0f04150501030e120a080c040f030f03031d0c060a03020706021605060a500105151305091f080601051513171612 61
    0x200002c43c5075501d42080840305007441940205004c3e12524645034555400b01641e0410402400a020101300e62501210100e454090305010910f00344011900070070000f203448001044100b0f02d460420406802d0319110b0340107101d224011000c03c4041343c08080034080340d00942c0301c0e10240700c01030f00a2802a05440c0604401c400e0950403040801b918100094a25040c1c28292401a40c840d81e90340124081d101d00603004c0c01c014000110620504100700300c106141d8080d00a8811035225000c50310250381c1c8039580d41c403000c00c6800044051341e40501c20942d200c6400e6041d441490070414020100070752402d9070a02081803080100810f090450107072030000600718040381381c1001000083e00141480c090280a107517080001000103000440b40e91150b43c01d07a1090242c81e035070b0300c40f095030342c2424018640541048a850040001300d08199290b0f84034040e05601c0982c1070610074000380d900b0005803a01e9105001065214047c98003110f0085c03c00d00b000321070100704c1410b061740132883c1c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 912627428 1250 912626178 912626189
    0x231e01020c0706050901020c06070f0302010b06070b010e06010e031506030106271517030301061b0209070f18090504020a05030303070c0602070c030204020d020c0c0f01020d110106150513 82
    0x10412100069030108001080e2110f03403e0050f00c0340314290040345820407800c0d520f03070807100000700d240601c594540d1440904e0302c01d500a121a900031414030010380240403004100d01306a00040c07044a03c1c07040501e5001c80c0624007004091042c0340000e1a0051049184141d0f22901d402e21500e403c003030040901070440c12101c00140b14005006180b03c200003403d441d011a0b584268100740b030480f031803440080c41c003450b0400d01c48030810f8010b92071350702c284510400b0070044c1c4040600c2a40785001804108d400038a00c00072907035070340e00540b1906682d04d000010410318444603880300b000c007458103004d001001d0002490746064030522028803a07640000d4800c0d8414001c00c6040c5512031541c0c104180d00c003001689850b018541002c4038882170b00001d502a00201c0c40c00b140e09a1640a0b180d030240c0c6600f21540070007000300b03002594103400c0c440390040c1c001c0600508110b004154046000e02440d0000071581d580b0403106150502c00401800024000148020b240400c40d400002508 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 912628678 1250 912627428 912627431
    0x31e13140c011d04091a01181a09040311060709380c01090c0b180a06051b070f1509080105010609051314010e090706030b1c231e01 58
    0xa0900203403084a85940000b88643c0708440000180c85a40014008a500080410401d42d5519419612a40174090120402010010103032404100d010b101d600290151345006820054024002c0c2c08000410030340500820840440c4410020032020f07100d40c0c0d071595a800494100203a0700701c13014800c031000d40c0c110303007162051010b0040e800e8000c0440010350f00c440e50b10070781c506241e8090002414090302c840c01c149400185041c0800090800740c00c00c0080c800d40801450422501c420f41c1d001e2480020303003d0206103403020b1800040c0428006030400c4486050751602503205816403170f000104c9080c0400900c00005ea08450504081e00e00b160090005604001c00102498203c1c840c451140d17545040180102c40698000e1850300304480034500700b5a110103001180c0c0794103940490740341c0315180c2c000803c07610a110f16045210010503a8401006500e1211904a01c2100554144400c0d426841000c070100064441001c0e049001d040303041c0903c04c0800381401101c40405d4180d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 912629928 1250 912628678 912628693
    0x30b03150c180f0a05190e1006081f05100306090509030705012f30150612010302130e03070f05010c1b150b030706030603061a0114031e1314 62
    0x40d80c44c42129000d6403000e0b1640300680140c00254003031141654031034034500070400144110998050a88001d48a8a443e812020b890300d00488000d02c2000d04690481c14124109101078540113401c0040b6992601d008290300b5100c00008003151001e0302d00c11179a61000a142c01040000e004440003181020360144170a60b01221007a1185040102402d4401c07002134440624408090f000d040058814a1028424158401341c101c00c9401c0c0c8408005407071010b00c0318082c1c82d0120480d500d8401c61803203132016918550034800c00f0103411222a0b4a41d444180d4003000355000c002600d4958061023070020740d2003442c100700b421200035090110400040c800303ca1080e42500d50141c40c210780c03202d030640490805040d40002000001c0303020b5454040e0020009410358141c10070020713203000340c004004041480c541c000016000201b0b41c0d0205100840800408117600099603212042011030407101c1021880624180012284d02801c0c03581e424107101417122511079111280e00c40300c0101080d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 912631178 1250 912629928 912629959
    0xb010302031003030c1b08010c110105070203041215022b02090915010315120302070e06091605131205150403080a02090307030b010b121302010f030b03150c18 70
    0x6200f40400b900b480a40390502082040d1075a01410040752000b0f24220300e91208074071800307080e20201640c0081c14800400c90000030600c01c0340e004900075002140b502c1c1c6051038840a13001c0c606815205602540d052a13106c03620742c00103282c41d4241409666505040d0101c480f0a140800b03a5058094030500141d009601c034224001d0304040d440526400703031401040124080d18071590040868006440001000d42d0000508030b0558403c3d000da400060b02d4030000041e201c0b00300d40d819031000800020494060300902804040b141619095140c40c0d11442d08040b070402030342c0030102510307402001405000c024404415101007280c01080c540c00c294800500000000d00b00845803680060101c446540130010600211b41c01f2908800750343e580d901941041c0c01c05240c0301c02044034000040c24000004441c584da465050312240807002c0c1c80a401c034024003c811045030984038420740e01c2a40ca868403202441400241105503482c04c44070f4409281e00c481108aa01400400c13200800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 912632428 1250 912631178 912631201
    0x80d17190e010906020a02100b150309030c011505280b1c09050105061c031205100b07060e07060e01140306010c08122421100c02030306040b01030203 66
    0x1044200d48940c06003046812180a000745a4850071451641c42c08606404005258000d40409140354085c0c809181c0d40c40034207425140044140d5030f01880c08101510310f860a000a160030405610807a818a0741400d107071404c4603140c501c01200c0d150030040c00c00852030060403509551440301c20340ba0000c02030a9520b20056400e00039009030302000706669070480740004240290f16040d0800340306405c0c00c0e0420f82e000344030940c3c02601078011808201c0d0440005402802c20b1649552a059040d10484105000780b8002e40040ca00310645240011082e034500c0c05408401e004400010300c61402403041c03890101d00da40004180716902c807610300944e0700140c0700d541c0d1700c2224000c2641c0341c2d0340c100122041001107000404410b00070458184130301401d044244207a0210700e400e0500f10407201d0401c10119469544e0741d200303a1400390010f40708007030f0b100320504041b280102c0d503184203a2070300542501c00da40c2d032800050740040304000031490140600e240306802804c04600d1401c0c2041082da = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 912633678 1250 912632428 912632431
    0x120507150b120312040b0f0c030a090203100e0331060c02040207060204060c06050105010302160303150e1819080a081306020409060e0601080601050d0e1603050601080d17 75
    0x320a2607465602850a845a512101d40c0140d4842a0fa540301010401c0e08404141500d050303031307014040c41c00980c11007240c0b9069070140c04514100e600316070341e44078580044d144401049826000e110f200582440c07250003405040958500a540c0381c03588103484180c2d0141654044403003943c41a140044010b50f1640041590b1603031a00030025141c81c000f14000c2c0c0701d00c2c440180180e00c0041c00003442603025010001542c804c44043c810340c0d980e040110164007031000d0642022088951003400a07000358001c0c511001551b520b0910641d440901b048190022912a61102e5190140b8170782c8170307428003030f41418031003094010107a10a140c54040050094101d68401d200c80c0c20b010400c5000c0000300750318001c1e4030440540d42e030358644c1850000390065102c0c200c80040c1c0c00000c40c0307a941c0100180d51103440d042e940c540c1032041148031107000e48402c00d0303129002d001e12904000d102c4401c507407003005140a0f500815076545815070303080ca000d200c0a120b00800161f403541c210340140c03410266 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 912634928 1250 912633678 912633713
    0x11704120c0321020c1c02060105331c15030308040519050114130f0204150909080a020f0703030f030f020c0a0c050f060f0d020d1107050a120507 64
    0x101c441800030316056a51422800d044205035070f000504001464807500103002c0a5292000e640030241c0318218818959070801c030740c41c003580100005004a0501d0b244480c0054008000c1070502914288110101d810301c015030000ca0400203580b200e281284a43d00004031004101005036a00cad1088a54a0b01031500006040001010109041c407600300100075140303210030703461007806a107483c040d07000348030700e4054035071440d1440c001544003945280549201604403000b50b6003840581d08010050807580022881e04005c1036005c0382049652180f0641d151150b50910350b9103c0902019240c0003000580c06c035564000e0400f80002a8040480b4106a81c0350034046800d1480c0e006020190003904060704203445122802c0c0e0600c031289001004440c0c2c10b07944640c9543c40041448903030311400d0100b41901c442009020b0b0400155402804c1d4081691400514111354407400300351540211000e4403070740c0c0001110000d2200038400114684400c1c02c00f2403403e2800c2e5500490100e900988 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 912636178 1250 912634928 912634937
    0x180406121e0602120f09160501120b031906050603010e0a02013908030a060e090312040f020a0b0a0e06030609070e0f060c0f0606040c09030b070306080a0308040201170412 75
    0x80c80400200d60182c2d94070881c00e50000400b4540b0084401c40d1010403a00e9610f24803c0038820308480d1f0000480e076003520b206a41d56018403104050b604081d144e4040c0d15601841145906070052220300560030040303109000110349800c21904150a44050406885c819041072104c0f4006030780003500244080e101c20311031342e5804054481c40c02402c205212007100410030303800100c1003186440083d032082000320020000325445901d26840c0c403100711000d403200e500c20030170048040011390750310758031620601a00c40500e185a000c581549081d44c0407581030800400c8090000d9001252a103d0b518103403519821032402c00d0000d00070001c0a41030070240580c0b5440e80d5920341760091400480c000190103a45d90340d148546c001e0b51a40e49481408003401040c1c0030481e6807a00f40643c00902d902c1c3e99405002c40e05545915400c0c40e005000c44080c582d56402c0002d4000042c0120070149000c0c0e1102c20461602d0700026003900e83d51800d81000484480c2080b000920100b0607801a411a103803 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 912637428 1250 912636178 912636233
    0x50a0602030a08040f060614041407020c06130b0417070801020708180102030c010e0f28060e03040f030303023a0c1704050c150f0a050702041118040612 67
    0x605d025981180e120290001d0300f05031004c28010360070080b2070040d000646080184d22038041484100030400e4516030010b8010440c2c0c46514034050700503100fa0440d20800309003e583e02c00c0c8902140d4011342c488180032902004c02d8280b603c0601414005044800080d40750485990350302e8418880e200141c00905241210b402a50b4800c00965003210f600c18000c10012190074a02582c0e25008180c03522075108a010f401012580b00c0441e1043b20410120006516003030b60f90180502490003a605052005101c0018407000100c0034800541c080d03180103030380700c42c0c08e00103c060444400c4d2070342cac1c590700e0400d15006041e590b8110207800c0f06000c500180c903101180e0102d900d03070313855422180000c0400303060000f4080f02055460403101e00705c41a8840048192032581140038554a483c2a000e060040301d6042d0702480007004c500f0b2004100082100c603209100d000780c3c001614103415a080c4e2403034080d241c24644a020058603540d081107000580a0740c4003008001c1e002c0318100141865031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 912638678 1250 912637428 912637433
    0x309030d141b1918210203100612060b0d3503060607030804020f04091103070e06010f081e0103150c030b150706060b0f1809010f121419050106050a0602030a0804 71
    0x40103400640503a60741050400701d070000345c1508441c071031003c1c1d12a00880710700010700c540510a602c00c032003900030000708618154443c9402048070086c141e42005000c1804030005003400c0c503044011030107810710181c1c2207040003041d0750702c0303000c1c1e2030809031440c1002032002a69458050300c001c3c95040c600359101e581c45101290400c0e920350502c40e002400c02d80c5120801040307010a5100302d505900b140e00e815540c0c241054098410344816011401c4000c0ca13a0025209240941d408080d070f84040301a18070b801c600d02da601509034025500c60740c140d00421070b890800d0003000d4002ca481e20b0244180070001c40019154280784100d85000d0706c00107841410070940342c015000800c0602c41898440c910002c000203203078800301014448441c0c8064001d00d40c5420000503050b90014290302404a09001c45106007001841381511852241d654980c000d41041064102000e0700c03941e903d800a6039840d069007941c490390041807142000031004d00003158000140c1d9000b98661900c40407640303403130 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 912639928 1250 912638678 912638717
    0x509040507050a090f050f1023030607110d0e030d030e0c1c0b0109020310120501020c07060e1311090607020105040801050906010e0a05100603020309030d141b19 71
    0xa0b406650016030460000032007072043ea003c2850884900c0041c0281c1da120380741d089440c01d00301c070114001003416900380600500880c202c0740201d07003a4019000900781800007840e0020071100c10380000d64182c281c0c804400d0901c1114a40407031414070600320940c0400103600c0f05c0c0000409400c042d668050141512410807a600344407070003400004000c00420340140190001c0002942c15402890000503050318510031a40304000400c01800f8090500f090504049840502913072299024445810081c00a128800003002d10380c4840302410001010b0245c2c0c60365000c0c11144107454041e80503c0c05020908842c1c004404490965450040340b0043c4c071a402543c110484075031801007006420f0000280150503114842512112542e071090303660140c1d10100c40d10030201008080030081d082c040e4010307503003000420081d45d04001300c080c024000c4400b0a1100411741c440b05052004003200d00344c00302051703c5035201141c501547c010300058050401c0d40004208511a125140440d030390 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 912641178 1250 912639928 912639943
    0x80c03090106120c03060b1c0615180b090a180f031808010656070f020411031605070c09050702010c0207061b0b1003050613061b05030105090405 64
    0x10b04609140e0180c950a02d100c0810603800f04403011ba2424903030341501d250802c1041001103e800d07082107000007a42e01c10006e011410542e20300058030740c1c03010449013000010002c400c00c07108000524000d060007040700d151409070800c184941741c840310308041c2c1d4004051344039403074008045c0d42d00400546002c0b181c292011006021405580300c0c0410b5214040d040700085030018603041c450349481814418000301100710050844000c0d801186490141c1c66071030415081411454000303440c0d8200441c001e40c4808030464110181108260444c41c0c50311407104540d00352040700f400c51034a0000b4025074085d40300c000d000d000d00031484000300611091440c001c3c044010307080c030103820200c1002c0d010300821326840300980201d14020510a01c503c0420440010940e20b4402240450b01e17076241300134000c2c02c40f11a4612544011000c14410418280901d094415022403407105090500446104285549503040012209034000340d0040c2a80c1c1910001c90300c1c032060362260b1030402d180960 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 912642428 1250 912641178 912641189
    0x7051815030903040806150a1e0b4026030d050f0a0c09050d05190309050108010e090a02090a0b1002100c03060506180a03080706050a0b0d03080c03090106 68
    0x280001080000b10012001c0e0013261902401c0f0b0700c0545035060540c0c0340300c09601c8642d40040e540d000400113850b030380390321106035070502c0d5a01a815807910007924613540549a5202c8000c1c0c4940608121202e28070b07404028003000601e400a295a03c48440540402c2d1140200343d00750403154001c0420403030407250035403a00d441101d5903404400ca403503029001c11030f441c02c1c03904004400207171580d0241c082c112503c081580c580380403904020410100f48000300303064501d480b41c001e65240c6091031a091000580c000d480740b0f501d403460701d00010403100058005104542a8800b40286a20001030a07426150b0407984421a40d50314101c0d10000c0c030320000f0340c46c0e12001d4101d220030065000b041000c080c0884080074000800b07800420b0741501c11070b20a01d5081041004003942d56006108071040008000301052411a580c0d03d8468640e0410340060b41c107a541e40080c402c1e00d0320140b1480c010360034103950319902e01c1e0050701d01514000e0014440302c070103200003000904152081d48420013421 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 912643678 1250 912642428 912642469
    0xf0a0b1e0d15060e0102060a0509071806091b020d031d1006060f0c170306190f0914041109040c080f030d0605030106030c1a160303020a03050f070518 66
    0x31100c15035400070b0000c018403032103604840107000c00c0a40c4501081140d03800103800410312070716440d490000401008288131420b000c3c140c9e0114a01031462554804000300d1407000c2206820f02986070121092012040c0d0120004603c40c2401500481c0440c1c1130307502c500300041d0308000007054490907a0626548a620b0048118915541c0c038258404000c0e2819556102040095280192100031090101400515107440000e1b0607010b01070055074850400340551542e04540f401e44000b0107083d8218410b0381401d0300c0c060002e0480c91055282e80055040040d141e070038162180a030685000308818000c891400000f418041b415440c9001410160215443c0c9113807104500c2d16504614100c207501401c02c00001a603180501486064a07080064006031625002043c40e0800307089400b0140d0762000e00c2415540b1000c1c450706500c450103078601507504c060128004040b50001801d8110520600d0140906aa440400d9400c0c11056044011b11407044c04001003a2010310710994104c030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 912644928 1250 912643678 912643687
    0x170409090b151210020304080702060c070311031216060e030c01020715060608010b0a0e150301061806020d0e010306091104030c0801021e180a0602030c07050f0a0b1e 73
    0x7001d10900e07684100c40c103190b918006074240040014546240c0840d0a01c0d03440a40c0c918400c0c1441c0e8021a000791242d40301c0391404803c2e90200c3c1ea0b07600819a1440740ea04040707010003d0048118901102d08000c80c0078206010400e4003800b0107020b4801040e5440350300641c0e25040100d84c0d0721480407080e100f000c40707488294282c4100e000c1d40c08028205c03130b9000c9805140d008107020340102c3c5c05643c41611980c0c56682024826002d5801c0a4540000c001d2003401070b5541d601d601d03d403103102442100c0003a50303070740c10140d000c0c1c020503c1240c41c140711420942c080010603070100b440410310000b4a031400801c401e1310012030240c031050b000303400c91510701044018590020001001180e00c6805803055240da205c810070b00b00e0091078840001403180c0450002c00189000080151840b0249411f480b620698003145c4081015040701c80960320003d83c0c0c1508600070007a010050108a80d40040c80c0a040b0200709050700500c160ac44600010a21003907110002160b0381c601d00c114452551034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 912646178 1250 912644928 912644933
    0x201081b040911131410020c09010e1b04080d26011e0b0408010509071a09010c021f0e0406051c0212011803090603270209040507050607030507050705010504080a17040909 75
    0x10845d0040900c90704079526402c00d01c2e8000300d8090f6148c03500a02d801c40e540e1802450303454040d0b00524a810b215040e00280042030f08681c01f0740040c154150040c26082030400c00a001e103009103114001d84610b92400c50050358001001c0c42c19140c1c011280044c030404840800c5c1c00440b903030850411450f000c107012402c0f0350305500c0349100c3c030706a0f0101c238203007507480e00e0980507184601041100224204100d031000c2d40692001c0c14400c1c030141030309658010241014541030b80f60f810303031000243c0c0084c011115203801c1c000c9001401007200c0c52480318004d2003000c000000b92200c02030013030a48000c0b50f40c480b04298481c0400110040701d101e00305095140050041c0391030b0003040d0109150a20003541c8915a51285d060b81c03c08241c40307030754001c0d29000c01c0f90201009100321014801c4600105041d06c55001402165200c0c2d19101d4039100b69141c858180003c030b80006041100501c010055148001803484440340c100080d440202c1d50040408000c1c030982d080301d4000b5040c080320404 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 912647428 1250 912646178 912646199
    0xb0616060911060c10020703090b030a0920010e011d04090b100602030901050412020406091d0705180c0d09020a03031214040809040c03150b03040201081b04091113 72
    0x780c5442440d1500000c00c0c20002c011403809040100006940043c07a124038085440d4000d01c0614001d0800c0d00180742d807081c2c1180d803a03208540413012682c550f81e000341003244001018150f05011000c2d140011900070000b030031424140c6100c2d041040c070314600030750395040c103850b41250380c0040c10a00c00c120307a9081c10130f288007041d640394242c0065610001070f03d601c080180c07141400d059480c5840c081ca040309007c02060203450990744565140c2e030004800701c1c90300c43c40d1080310510a15200388101514854109000360303024034000d40b41c0c0d407084071400b10504851507225501d54051922030b0144420303c80180443c03030009401407641d21000c000d058000800c00281c825103003080c4107403030625041c8908c1c2c2d141524010084502400882254601b5401400903107160f40741c0000c1d0795510607000041c014181d4403039a443e460010501055580c0081301a45c07001401181d41d5050a08040740c003918482da01c150918070381e54500c0e010001034590200c800303002101c26043e040c0c5403502d54070340 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 912648678 1250 912647428 912647441
    0x5010312021b01090308030c13060206150102061b0304050a14101d10020a0210060f0927020613030206281701150201110f040303022e0b061606 63
    0x3400340c401c42800380c400038050349004205a0060b03688000d040d1039a6240c52041d04082c1c02c445040d001888418042c92105089500420195000380079a0910464507030720f07035810f8101c0034115001402003110502d8120303102c010079800940320aa4036030762400c056041001c4081d004007801c1400c040145000c02c0043c2203042810340107000c00103100d511180078a00d40301c001c02c140564000c1c0545a49202e1541d01a04241c0ac843c010354503418000b0703440b4012103444d0b03004220f4006041a0510100034a8840c1d00d4409003505541c080e1001c546210344003524403840c00a12411000481d00008117403408004021580038048549501c0007034440d00000c0d1a0445a110044080c040006140e1142c03600390901411074041c00c510381d080040e0350f42003160100a0005564840842d00100c501c0000201048400c0003010358a660642c0b900134184900c10b01425161003d1104144032540b903110707200565031010100207181800c80d800f0071041c2c003508200314810400000f46206100b9560440b5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 912649928 1250 912648678 912648713
    0x30b090c0315010315150210051503060103060f060b0a030525120b04090c08030a080604060b1b0a1e020906060c15070509090115030e0a0203060c0a030f050103 70
    0x200125038aa8088040c0c50000311412103401d0040610012954025400002003901180e0340002c3e40f0707118940804c445444051085c016400b80c00d160407001741078031410386c0040d136111b05050250a0100000d84e14001800050480b50752141c49001c0f070380c119400100240400b02d051fa41382d580d540005402010220391501a010080840e41d040030740d011011440c5444030384034641241450031250006082288209421565480204010034020741400005296040095070307503410803c0002c04462001e00054000c5041c04000e009010031a010f84080780803c0314101000c0490204e0740f8500101200e019003801c0e80044071500d200b860030038a450682c002e0781c401283e81c80b48024400c00c1d00c03806030000829040307958030000350110302c800760340c000c039003840c0c464245481032000a81c3c1040c01ea00070302c44d0146003280281459058004c640e08005110060400d2140c582c0100b1348070f0030000c0a000c61004000381c103254250007a0f20108888108030b404000310342e1640341001404985100e00c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 912651178 1250 912649928 912649939
    0xc0429220303200607030b040f05041121120a020c0d05010b0301240905060a15030c0f210b0a08160303090e0103050c010c2f0109080106030305040e0406090203030a030b 74
    0x82205800390003400208988040f0062520742d0725000304400412500076000d0b406910303030070f0a140e0441c5500580740264040c0420356400d844640030440390307822840c80c600018a8040d5601b403100e00c08900c0c16248140340360340e2075480d040e580d0101d0820705600022580220000310300002d103d0154400d40d0141429030003003002c80210121080303620314440c0e05215244e100202448003000035000281c0182014000009080e11f4031805031500c480e100d08030001035658012a48181c1d8464000090f000b40c41c24010099488071120300164229840344450340394a8038041555038440b4000c2d48000d2000d5401c1d07a100e40780250810041a100748000d800103034045da4013042c0f022248014604880c1d0210082402031400c01c010349002c0c07070fa50810780d0760505040c0c4068500424252080b104072858286480c501c081030300240084c0d0168000c0c2040740e14280d024000a03070428110b17001c1c0e41740e400142d1519961450018060444600000e4143c040490380250702c581541124424607411501d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 912652428 1250 912651178 912651197
    0xd020d020c0904080a0e131e0204060c0b060a08120309070f060512130204111b0c03210c0a0b0f2818020909030a080c0429220303 57
    0x2000ca03035403803000c0c44859214204202040000d050301d4010308141001e4101450419213610000d54200744140c0c40b100081d8840390b201e145806501c00400781041440011802c050801500400c0c3c1c007650b0000910207503182d03000c24030356510012464000d01c0701d402190b240c440d2840b2001c3c03894000b5100c44400784101c0c500441d0544c0a03208810030341d10166112410059412110032486201a20400d40054a00d511801580b524003801c40c01d8180c0255480d5120604845104620b454298a10443d04289910707602030b40c0200e030840c03a107100641079020030b0b26071004074825803160b40c14000003481b0700d2141c00d08020940344400e11443c09c0c041e103c031842d660749117040300254104804007505101d104044020070580e9220481303103850001c08600300c0c842c1fa804906464820745800e80564408905200c00641c8802150340c0902030400040c1000d1503d0f0300c420914400c0c40c9400c5803405600144c201011a09007540c0b07400c608440d24000104040e82c0c80c1c10301c80c080703010903000584440c9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 912653678 1250 912652428 912652453
    0x6030106030206190905130b0f041a0402090612070224040f080f09041d190c3006050103021206090d05030603030f07061a09040c09021b0f0d02 63
    0x4a21001c5035009480c0914184c2c040c1801601808001c4202003030259207040131840c0e4840032100310b00c600107000e0001c0d0f101080402c103d0190011002e40b4460350410724003d440300c581d4007450038560310540b030250700e51102100041660040e0103c006400005030300b0000640e81c005500c041172a130420680681030701e225003440e0991802c80d000307003030465407403616000500e090000300781c1544624480c506181c503800c00503054500140e07000b04142c5555040c2d45020f48284145100200080700c1c1500300540c0d680d40501c070307590030710441c00a400c103454070140503448078a54108600201407a010b080c4d146144c041c4c000d20081c0420b0340100c1d5038140780d4006202c00034500d4042c6400c0c00060554804005c011541075200030901a0107000510103907804140c41c201501005205180104142d0b10a6003508a080070b1480720900c901702c0c800030704c40425198652482580d505030b9007d0707581c9c007408420052440c1c42104004881c0304881c070483d0a61000f148400d0b040005500740c4400714040b4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 912654928 1250 912653678 912653681
    0xb2a0703081303030b09100f05121e0109020d14010c0512241917030702010503010918020a2408160c022107031a040f03051e04080307020405060301 65
    0x1690028046440c003408518503031080d850594285200e403401284620010000c2996420161130907001036910740002d1060b015100d0b00c0030040d00c2c05544007440d0301440b0303180f50380c0d461003084220b80390400c848403a03038444c0080d0001a0901d401503d0390a0100003494020100c2001c095404815441c0018030b00030300e442401103810100c01107401c3c4a02e40c407906031900404502028015030b44118400540254840940c01400d45400c4900c070001c4500d40158240342802c2031650340c005401c00c010388001030fa00007090764151030ba040d6002030713048109024603c240d050303084c0c007070743c06040c61000150000d0605004501408000c0c0c3c90404d88049a0b4103031090741003070392441f41010f000103140584c1171144005904040c001410307111003a1024640d0031180808800300c1d0040d070080e09080c818059000004001000b21046070101e80c40d0035103505005c0780e00703a07070018200b000000308100d200469603c0c486952902032056a543c965403007025a40780d01083c0c04a00540c1440002115480c06 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 912656178 1250 912654928 912654937
    0x60b0616121b02211b12060c070803070306050409120f0801030c090b040b090a0b030d09060f050a050903010e06010f0905060f21010509030a030e30070b2a 68
    0x5076403504071105250703802c005601e2941504134080500000001110510802950241c180d102d130b9010300012850050041e580e00145038001903a21030740c14032040c42901d00c1240c0900e500407000a8491702ea401007140a4141540401e034414100f5850b402488a941440c950800f155290719030010001041524070800c01d102c0900311072400081000740541a4100501c007450043c400a05008000006108503105071034248400f6941c2c000c0d03511074281000400c45450709401c048090616040d001030140074142c1d041410801e0105214080328068000d41d05802d10083c0203100203802090b030300390348a00922801c95808408800003807214214403845006200c0a4040f03090080380405014408044d804403e8410500300803040c0140d04c00e128050080402130007450b510800e60750020191a1071020807071440e000011481140c012400c080940b110384001181030003030214014805034052a04003074400e403900d1042041040d40d010f180c620500407444040a806262100c0340f50038001d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 912657428 1250 912656178 912656207
    0x7030b010f1d0f0904080408063d120b09010c05210c0c070e06010212180d150c03020c0d020703120e04060902040801090c090e030a0804060b061612 65
    0x800c020800c49045100444400384140900f80300d55625191000c507503140c10886058425080104003804000ca00740000398000102d180700810180314045d41e5600a14940700307040b000d2680c81024002c414840440e000104004845d02c0d000e62450309100022100c110b4480742c4c50f510f88580c50b80d0340e5016100340c0d204060603820001038146000cad03056842d82c50140c241c17480028103220305540510708100d5100508610306020f0042d05019001900e000e010b27100307104038030341c0912254000d200170f21480c14040c5021148000c14118034140902c01c00303039003480b00c890075007800c802c1445107405400409881e20f1281c100e41000b42d0104040703031075140d0340c00020040e080304440c4440c00c6c1d20400d0b002c11800c40080002520030303035508104089a20541c403a90990351030301c80b590240081c41414000600c42c0c1c1d0ba042c083c085500f0030f4aa1240316409a00d018454890045800d100966002c0f03403003000050201e035994014214000c500302d411503c216140c401d42031420301d4040c4074020040303101c2d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 912658678 1250 912657428 912657437
    0xf0a0e03191107090e0a05011401030b0a200307020a11041413150c0c03080603010e0709110c07030b06090a02090904021c0209010902130503190210090b0309030307030b010f 76
    0x910560210b03060010800c011070948589140415001000c0c41540d040021020003401da0455510b0441e00b52010002200c207143d6442e0010000301d18042c10041c0d0000d0452000a40940310003505011007540403000c4100a1010007041807150700040d070944028040e00200c240340744000c080100791540740c00040410349002c004200300c030515890740402c051040481c040224a900c2c02c82d03044503c2c01c100c0000061481e0307110fa05141e00081181d4200d4001d8000f84101d4140b80400f03580ca400380d100d0200100d42d0f5114800c04500780c4015030b010b41c500070b02035542c9140e076410400d11501c810b030b0700315100704000004200003407094400c0701c00b9103001030611500e903a9541c003002310ba190200d103c000241040303808000140e4845402c140030f0105940010f8407005030429500e13191885821036402a0300691440700300301030300101035045a5040312400c00c02842c0420444080100d40e0200144040100512404035000306c0958800d100c640d03400c2000b0711000004464030340000031940d0119 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 912659928 1250 912658678 912658717
    0x50909070e07120f1506050c15060103060302091503010c0c0b010b070c0305010518011811150c100902010f0c0b2a04060c0209100e180c06030f0a0e03 66
    0x501c51500c881e40070032182491a904056070340341009075980e20185440c915680c44480320415555840d05001d42058a08141020f0f0001656a602c40c4c265142c203110842d4280080d446d0781c0300350010b00c047c56002d0803030480341c00d05450b440040003111146912a500b884100c20301e07540301e402036416480c1c21041c5540300340d103007004183c120340c0b0408056510301203107400440490024014180582c8800002480c2038681b90100341c01c6440002c0c40300045100c002000011400307040280e210340c0b000b100c272180400f070394118030b0700c1c075102d25410941107018400c06120440029404804ca9500030388880130f10b80301101d41100c0304684108001c144c178000d003010454200703040540c03c14200307652100320034400780d0030f42400300c5801a40c4a20000f490303d120342d40c00c5052014049812480e07011504420034104501c40140710001046100c9845101e800280c0040f02080000e25003400075080c540d0701d040c1402c00410907a0112010040320b4100480703003011031000021691405034603251a5041e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 912661178 1250 912659928 912659939
    0x3030608060f1b0d180302061605030108100b0609190608090304060c08030a0f1b02210301054e060933091606030b0d0b07020322060905090907 63
    0x3e54200b41ca80c2080b041c2d6800d000e0001444e01c1c03490f561268041d40041105140c0711400030140308c1e000c0b0850b810804180010000d045000424030364448140c03030040303a04104400400e54600400b498568072580c01d41024440058201c00795003074074200e03502c2a503070740e6030080810b64034412803049000181c0010300c120082603040c4082d642114044201150042c4c3d24a00171080c2d4610855440c1d02e042d04000040003180c04104c014001a03010301180d480c1d0944585000b550b0005104a5014808054001880780f200301d0106d4481c080310740003480a4000094202c007032002002e03030712030020207030203000720b850200091083c4205280030007800484640c2c100c00c1400c0b6040504400f4601d00c1580d1481d024540c2c0d00c4040c0b10f8904000207149815080c1c8422090a142c1e03032150091500e4482d030100540c803064901c0c1c0c503158000740740d0342d4640c4030b5601c12842c40c4280703020720341c070800103e210078142d103c4850340074100c42081d0340328030740e49484200f00004030205507100b0030b16034400c8008124 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 912662428 1250 912661178 912661231
    0x903020f010c060e0604081b01050f07110a080f0409060b03060d1103011413061508060105090709080a05100e01061805040c2102041a03030a120f060303030608060f 72
    0x8184149030104400380d0004d41c2c6454150203035811518014080754605480002c00001c021140d0640000d002178140000c0380195080040c2880c81080031104c00c108500c107040000da1901e40e4450380c15a0355141000700a0110340003401001121820000300040c003c0080e0241d070f004120040082102000381d030340c3da010042c0003900e02c40e05552115107540c00000c03400c4a0b5441840c0d13025a0884822462034150201c810a44007090300b1542d00d001803100c01030001c6c01c541903071000c2c3ea088606448040054500c044e03107030b007c00d0181c03040040d10020080042201e4582442c511001c0c464080c00004003030070380306240524001820703291202c4444405a81003550054000e05141d49200d450f1018281d507002c4006044100c544804000011414103100f05480700c650450102860f845a000281d03d078443c0316007220400040c0d03469a00b402c043d40e03101c1c0504a040c204104440c1d552440d028010301010310680d02d1074020b5900190b4141f40c0f003030001c1e00c82d5020703c00c855480c0f00c07001e46102 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 912663678 1250 912662428 912662447
    0x23040c0207090204030c050f0a06080420091315020301060f050d0b100504080f0a030f050a11071205010509011a191d04141501060c050312010e090d0903020f01 70
    0x404612075032100042c102c841d403005001075401029880c02081c28130043c091454291f5855602910002e01c00708499580101c005402c694042484c10710004220f440e200e0040000140507808142d00b014030007224025005051501d1290142d1009004880c0343e91089000c00d100f080089811652030082d2207218000400900c420400b0001e41242074502041154110715406c0020800009050203088800c011070701400c0030510090942c03d07410b65005015100c890f08c41c400b40100411000102409800940300034510134080701c112559402600c0340d0401c401301e040d112540b80ca404180c018104dc000e0410803e0b0081d011034007030103a4000c0c01200250240104d036203601074080800ea00c0780456103003611082441032207400f0309003410211948445500c481803268021440e031071402c0350a14070241128260308111550800600300142107101318a0009100120342d000070a0303014401c844180120000c0c8119920f1090706501035a103201c42e0301029600550907900f45945600c2200382c82c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 912664928 1250 912663678 912663701
    0xc010e10050d0527211b0109061505030c15030403050c0d0203041814040204050a1d010c0221040e130501090c05130908030103020409110607110a2304 66
    0x76494a600400b200048403000d40740d102e010816111002c140c0c00502c0010303a4401d10781d50240440310001c034940c0d034860700c50103803101040c40c02059460032048081c45480b20100030340c001b4030500c51546005002031076524800710003a004c00703801003014180003594a03407003403010302014490070f5040c0080e1001e402c010021800c22104016086503a03000380060907a0300402c2d001551103030f041114a4003100a6070303401d0840240340c10390001103200c00382e29280e000b42d01943c000516849901c00c18001c0c004450100070307410042a07001506910543c08510828034503400d40300c4800391050160200b80b60381074030400c20030303041c1b10070312041c4200d01005811005d041040b0b00d12000550b07486007500e0b80060b0076110451079283c200001e05000c1c602c60000d0502c10001c10800c10996980782080c04107000c068042c41d5505800400c201d8000054007144100030a5103880300420714100a24504851000e0b01408541600265072120700e119416601d900800c007200410301c1405001c01454508040c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 912666178 1250 912664928 912664937
    0xb070c030210090f0b0c060a0e010b030a24060303020303040312090c0b0309010b03010204050a1205031b0703050d020c1e130617070f0b03040b13050304060c11030c010e10 75
    0x1039a4404290071070b070280d502d52100c3c143c5414026503030030040360b0280340603482c20801c104480c480032811aa10a10403076001172a07082c0c2d144502c2c014068840001c0d0184102c45040381444000448108441070600b5070001141c40c1c0562041510050311000b80943d01c1400490300290140c0d19104900004c20f2000982000c00d845030079549549901c0882c03c40c00002c10712000c03640c02c0c0a010100c00045c0e0007135140c1441c01d030120703a070200503210b580580c800701030f100c50411509100300c542d85040c4001007401014004a601d4a4902c01d2008903079502c1602a0107600a001041c1340ba9070b5100103141c02c2c64808107248602e2000d03007110509a114008440c02e041e9511180b14101c00b40203403425024060402c0303103080b840c04150781c00504101104100030001b000710740d070440307500650101c800d010540b504250f07030304011141c1000800901001c41c01103800c69201840011b924040c0e81d40d003080100d9101455180e03203440b0410307400070384403400362646802d11502c0c078480f00103603140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 912667428 1250 912666178 912666203
    0x9210c06091e060219110d03050904150b09190909110306011d0a050601110604080d110408061803070c030812010617060609030a051c140301061d010e0904051f060b040b07 75
    0x87c1070b081604108401041020501100030b060922a00b8588031000c606154583d00f44880074400c2d00401a100b841195500d0a050160b40c03d44418002080e1041051190107094940001c05030b28034901c65009104400000855011107a01070f040e003c83d45801031426152440380380041c103001080c04d1305220310403e100219800403c2518800c0740103d04440c0c0b564140d10745401030b030346040611001910700780b100b44610032001c10481d810003080c00881c00d10100c0010028158081d058000d88400e40b240c50000c14854000d004091450550035050b80c81e0307032034030802e4030301407006403070f25040041c0c900010719641002070003010101c60080031a80302080e02d0392014940101c21800b0403000c83c2c00400330380b0744c0da008050800f042841360401c0c0e0a40d81008030007407180d01d070702d03240729004040c01c02000301c680d024101d0600f40c040043e05901c0c032454142001c03a42e451420070000c0725401310b0400030b110000a84035090a5a41c1449200d2500b8036018203124550070190058400c03980540 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 912668678 1250 912667428 912667463
    0x2030a05190c0b190c050c0c0f041b09060915020a0210030f02180405010605120a0b0d08041401140f1c0f1d0c060a09210c06091e060219 60
    0x10403c43c4580d107121802e40c1203030101e005031000c0e00c80881070002400020710540d215a00042400e040000c41611065203041404c000540600028001403500015803800d4080256104208006959440d211001c2c140c0e6aa103000750030514485060b001030b0450394904005152883c070b010700d40c4010380703804503a840d41c41241004a900c0440e1760522a603c0a403a81110309080c041c240c010f10441c24814245214429403030408500105100d5505035203000410303503550740c0c240c041002c41d00014580d4589442ea8240c00d6141003444982d4007140200704c18841110704001200c090000310520507007484403504007106400307458216010a15140c4078045940e00e000e1064810901100560f0071400c0110f01780c55040c5191080f0440c003500041040c0711000d500030503c07008641d900c465900000b5031400c03504100903420b05000b000e40c00700020010b00381341c1c4000310805580d040361980c00b20752515079440c0d803401414490f03070f405a00040e40d1b46907401282640151260b0141d9280640c002c80b51 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 912669928 1250 912668678 912668693
    0x80403200603070504030215040e010e041a070905041d030a0f140c070f0e060303190e2809050f150303041205010f1404111005070c17060702030a05190c 67
    0x103c40d540005240410700b0000d600e0300d0075205920303001c0c0c03107150b916150a040401e50941d01c1401213020015950010508000d0710010340e44102d8580480701a481c01d1180b00207140341c141d4400c0c984180d081c6504c0001c80d0229004a946004030400250f03d4096607000a2310058002e4014009101f00341e0701d01200300c400030b80184540061880a00301c0103050410448080e12581c00800d1b010b1042d42c10492161400000c03690304580a0680c03200b2b404d10040120b6007101c0304030925400ca92024943e461402c0e04c013402c503810101031000348c0c18031b54464003400100e5408803844000c03218900c0220310f4400e0842040000c2c1d21014054925280d140d04148031895440c01040b41e0700e03076507800300c501d0ba841144101c110070b41d0100c20341e0005007081e480c4c0d0b8071051481c0ca0503d00c50241101d0310040d00d17024804803107400381e2002004003040d03031b03a00c240c0100c8002c0d49102c0a45011700000280e585101108548100c40141c4940d0b00302100d2548291007181c0e00c1e42080280080c094002c00485c455 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 912671178 1250 912669928 912669931
    0x4150f0902030915090a030c0602071a040b16120c05041211030c01110c010305060a21060f0b0a0303230c06071205090c06070521070b01080a080403200603 68
    0xca030805a62070400012075840c1003031015488103821038860a0040caa1740204800b07a1403a09440c11111100050505500901c5900700081c2605010811281c1000074564810310132805117446003d00d030703503001e50391250b40d40c0c01d40d003080003070512100400304024a60182c543c00c0080d103440c60506171282550708d0450b0242c0303030035180f1841519407421146020000d50884003000c0c41c0c0401c401b03400499050756000407222031414140c0311000905661651035160009202c0c25020000000d1124841ca00c0da5000ca50705440450600c0300d0034105c10b0700c500406042040c0581860314041c59514120740d01d070540000c00d041800c07051190342c442ca03000006052903017040005408907081c0440080c14602514042d5884241800d04002c211100881c00803101d8006403030741a564a01c52a101d400d00c04112503400b0401580290341403040c4800010b0420188911441d51940e600d420a5640e1404804001810b0303203c104800e10002d03400008610304a42c11460300c0094600d400001241e5810 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 912672428 1250 912671178 912671189
    0x207050705210705030706050406110a08160b0604230405010e07150f0801260f031207080108030415032406080a060f051c0c0308040e011d070c0204150f 67
    0xa0000c0304010342445240e00a140440046c281c8900d00a406400e601991103190140204070341c2e034101071141070246807178195000c42c0e0990381d4140944008850982d90000307139212031400f0001040703810a84241400d43c1c1800c51038091840700c0d46441100e28100600c121655500c52401c1c1041d15800c0108102501c040908940c0340021070400819201c151942c030750420040b40010456414265275443c840f111180c1c8248442d8500201d043c903110f44200342c001644000036155a220480084c0c5a01850181d41c641c2c46e40d90340c801d500382d40c2c1e01840c0540c12240c0175500034608000d0003984020403039900cbe04486202000c1074001d400d62035403e41c2c40100850905010040d112206128203c05085441e4960003d20700300004260300c001c0800005172800c0c9010a02414060700070001001554490401c40da142c4e101c100d4003040000a12800d14591020440c820094003c405110712070017081d079400c8070502e40c0c4d80800019208c08115003d03000c01123807011600c2036001010401600c1c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 912673678 1250 912672428 912672469
    0x314030c1206010e09060f2404080f0a050d03020a201b01091208130b3001062705121510150f1209060e011a060d0207050705 55
    0x1003000c01e40d62824000400d050304100e250801102d4aa98199515400101c282c4090441011000c00308481494620321000c84940340e0685043d5909803000400c243ca900d001515010803141e203815646403c8801c0040031900f090058030f01d12031107075001d070180350207034035210004114540c8c04c450044c1e03a4243d071394010b420440154801101c2c11030382810406080c170300091540d16090341c0c8440c030720310100020311600000070b111243c040200c2c6d03904043c08001c20841c1d1340b00035040d1901440e180f4070100444145210600110809040040b40c0c100d40c07250f21040c100d03640c801003070b01c2e110307512141900c044401e40304003080d1902c03881307600c6100c01c0034440100055100401803c001c448014800319008180d40c90038018070000c00500041024682002411044e03006015210100700c21210030441c2e00c1d000c030305400e200294004043c12440c400081250000e00d5540701013807441045001d800000c10010703425411a250700411000e8082d0302610405c1d900c4800290401071000041c04001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 912674928 1250 912673678 912673687
    0x9060d0504020102070b040b0406030b1809060906070c0b06041e05070309030801290a11150402100e0918100c03200c0a0201030b0414010803041a04030f0b040314030c 73
    0x55804111200207032451080c241d0a184c0340150230702c0c1c148503074001c020425455140f0f100b40d03621102544071111400109084151800040342c0d43c3e14002101c410980c2d22030391002c609a1802541060540b40d000140b141c0c030b541d2010700707002c06004602c06d142000b49098083c548400c4091007898000c00e51954041200000f500f0300810300b000c1a00586510306002d20004400345052007030580c100c80b102d030919162800e40c4419100b50b00d0005611000d40601140c007001d4a40d0b000e001803145101b1100780d2a10000701a08640d00c2800720f051360b41200220700403c00f0f8646840084084064910469800f20003900c46101502c48c114000400320740c440349010404a00305024950f2681000106c5007094840d04504d6950840c54038043d0605680e0304031420035840b17642018889421560f90407070300e569180d15060781c4c3d0b84503100e442032560394104040ca4508511040307a08032500025a09003900045d20b500c10301d404040c00440912244000044007801c660015612621820701c1c0c03a03464 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 912676178 1250 912674928 912674933
    0x1e0304090c050f0301090c230702010f0302030603060c0309010e1b0a0b1611040204030605040b220302150c09030609030c010b0a061b0320060a1109010c1709060d0504 73
    0x141c50540c40e802080c02000e100c40381a541040d010f0304c0c1181c201c2900410080310341030094a5120034022482803490301c40c02d42c030414440c50b600030803e040c801e07070f9240e00b4205070071030880407404152420781d49500503001141002940e01c0203542c00032100400010f04100c0c107001d02d8501a2407500b00322a503a1209a02e00203032a01e071606030010190a04503030701d8034480140103a02c0503520800207000d01051002c0b0001501c95505031805941d100904108a05085c00c110020354001c41d11601c2c08010403c00604100360300450041981c1c1c960004c00d10b8612030080401c0c1d40000411a40340d559091200c4291a50100500c0340150401d00185507100300c400116030075a411400c1c0700e40690039980c010030510703501200031100c01c1015000303c03040340f48604d011501e0201c07081c0704090442800030500380d01c5001243c4513005d800c0c600d00410031002c101102c1309480c0158000540481c03101c2032094041441591100340610610b240720f4500700c8844005000344e0000108881410b5442040108 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 912677428 1250 912676178 912676181
    0x1e0204090b0a080607140703030f020304051b0406080316110405040f050d05040f052101020307090504140609072304090204140d1212020d18050d080609010e06031e030409 75
    0x42c145443c0076040070303c0c0545000d00003441c6e40c030080c000941d00144010525200358021601d2101d4084c0a55581c1080d0404542c2c0b2404412800a044007516200396180740130b10945080b240050081c1d410701d40c000306117840000d03081c0410f079100e1a4502c080905644d0b94411070348030768812401840e01a04604101c1d18040c100e103640c5081c000d00304401d000503001d40314540c0880381d08546604104100c18940050a580441c1502107503002005004000d0303001400c1c481903907020f0360300f0040345e03c1c1d40c42d0b009074014007030741e51a4000040002046032288070392211a17141c00807a11400d4241180e000c2032000d644164451100107601040074417840013122044880204119442c126200c240e071150310343c030b040c10380c2d990007400703009041100e0400d141d0f0180c8028114100c0c08000c04031482c00d03440c1d000080c0510846240c0070303421801d50703094060071440d0700542d00a040501560300f090742d90201c0402c0a880c543d4503108441c07141d2503941506000c5002c9081c0ba6000c1d40d22240707031130140c50 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 912678678 1250 912677428 912677449
    0x807060e011d0a0c17010e0d081501030524030a0c060203030414011e1e020c0705040b100c120c06180c060c0203030708030c07020a0303020a151803031e0204090b 71
    0xb00d904a1107860020880312070750b0388240c85207050038481100d600f40d0001e00600d030307124282034540030f40c4412110040c5c20075440d0b48640740302c40781e0440032038ae81d20044048940c112001c40249807010945001e01d42c0c000b46413191070b60080c04072000c9648a84501c4c0303041c030303580d44280010b034030010400082041050149200b520000024803017200402e0700c1c0b23a00f01c1380242404c1000382d07580758100c2c1d540341c005074031041c0b546a214003155907200f40035034182c90b200a402214041d50904441074528181445090706984041da40c2c09610b200c00c1d5180d0020900c41c20041040000242500e804034000703100f05510311144542000182d901e80c034140700e945185d588800c003445221048440035031030120444440c6a0300001e00c40e1b69030399032142c00100d80650031029410141c40e00c4003204240e000500c00d10b4460154284004880c000341860090310f2101e016028007010040034800000e00a4100011030b00210b400b69004001a003407d0049070031540c0160348643e120b50205229040061001c5c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 912679928 1250 912678678 912678731
    0x3250606090c02060f091e0c0306010b0418020d150b07060b09160503100e0403020619090f020607020a0b1309060806090a120512010b0306190e130807060e01 69
    0x2c0c0811024004040e4031a01c2c01480f94076039100100c0002c8141a0601000011066110300781a0107011401c41650f500c20005103a400703841110000302d44907140301c05542c1250092412400c02a4203003040c9006500301120b0189856100e03c511254882c0160026020f0030600155130344070320090030800c0a55480d0071182c1c1c020394080090244818404203a40c0c003111075410074559a8403001c0c3712040401c900d43c814600c0b0072948040c007040640c0405c0c118045d260b110517044029844107401d01c11100310f00001401c0803c070000300c5006040c50b00103000d0841c0010030088205689040d8003402c0e600ca185c0303040c00000d543e20144102c028512a04c0041c03e5420001c2400345440c0c42007603905e9a20040c05050a0030329850191080c0c403c400704c0b0881400c030a00c1d40000d5035101d0040e034aa401c01d64006105081e2070032528044018000801e0841d000c1c0c144500301070302c0c0d1071000301c040b800352a07090320024070400480300800c41e50702400c0e44060700c039400000c05036035a812804442c851100c42 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 912681178 1250 912679928 912679931
    0xc0703060f23010602062406070305121518071209060b01020d030504170906041508011a071a0702010b0a0311010e061204030503131e02010801050d0b010b07050325060609 75
    0x5010703a650000348640d0103d0a070b00350307a00c0c022400002c141c58940d0141101e50202000941804056100c005040c00c081032005d0041651242c01995070765000c0c040c80dc9400010001000e80007800c00201c4541100c60750500d0000d400205800c10255a1a440151a0641c84404200c50382d40d04005040005945203400c10990415549103071039500c3c240c8241410f040301091045160707a035002100d0041031304540c140c81e0404c40e104050300005e02413080c010105030039030034032041400c0e9408440f00c070744c1d1006e0b0f01000e6800e00c1194100b0350b00c01800c01021076585036070310b0395543c0f500c0740174a0203140614040e4924142500005002c0c075225a80c1d0750050900740b00402d00d0301030f600384d501c0d00154942010f81d1265940141031084000300f44014000300420154041c4e010407444034450000d000b82d9903e403032a80c881040c818444246600146910142c0c00104070b210611400b43c0340b104e2013282034a180000e46110607142034a020450302d1403074204d1528404101c110310452000b0100217a0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 912682428 1250 912681178 912681181
    0x60f050f0c0f0f12090919110430030e121c092105100902010e04060308070b0f101707051f08060d020a0509070c17041e05030d050c0703060f23 63
    0x7241110386c0141101000b40440d10490001c14442c2d0030507003c4c40d660f480f4003901c03185d8031018014071040800a44401d90348000c503280e414102201011041c0340c16442d50740e085948201440f05085042d02524518000c0d061500c2900800b003022020510003550394000e13407030800ca1105e80261407500622a820a01010703000003440104109001d907114140000b0210b01900040c0c50340b248841002c0c1c0e02c940740003004003c000192015107800350040740040e4441c0d0721204540d20b805030660b10480034100d01901008401d84c508803415003000000240c5032601d17620004148099a03a409241c0e0303c0580000400c0d01550000d81280d110034102d548842031a056000724032a2042405103502078040580000e4507240a074906142045d8003095141c03c450407540203a20035009400b491036448902042d80c0200c2883c10707078034019580000c000e0441c100890000750b5007540b00080580d2580601003002000c1042032003040c000c0c9030b14460128606805042000d15002c0041603c4a800e00010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 912683678 1250 912682428 912682447
    0x1704020d020d031107240207030b0a0e100f0e21030c09060c0a060b180c0f071a040b0402100c030915030618090219060f050f0c0f0f12 59
    0x1104003690707015680d01411401a003801c40d442d04459038030714418450040f000440300c06000c401900e42c10030302034070b503481500390b9422030301c0c1c00740743c0300241007003400300d0109000984c2503000c810005942800c0b00c0000e140c0130300301c1c016101c0501e0364241713481d60340d4031900324039074144100071480902403050707010130354400307d03500c8a8040540f2650110f500801c0c01803031030320344000b01c50b002400c81c0222540e085c400c0c980302020301170300ca04660280c45c5c20003203201020940310049005940d016812810a00c0603001d10880c0d41101c039040c0c9101039060203d81903000080401030040e401030205000528040c01030084200410741003c0410081c0346c07030000840c0e44020980c0031b171002c0b00e50300d1262014440c4114040c003016008521050680e1400401d41000d86e40004180f0788290784070034040c40d140c0d00d10380c0366803940c2c45007802203146240c00005c3d0302c0c4101c0050001105062025040c0000e001d141c0d80f138801d04c1142c54135a60b001c0c40054645a40800c009942529140e40c01c42c640034048 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 912684928 1250 912683678 912683689
    0x306010b0a081314280213020306060417150123010e03100c0203030a1505090c03041e0602030a0f020921012706110a08040809030106032001170402 65
    0x205100710402002d180461003007110359a40141c003a403c60503c0ba000c0400c000000e403110385120399252407034950480c1065075802c04040300462500284000002000c00c4009000380d0f100600d05039220404102c049502c05503008480e200f0410203005040003000c046170340b41c01c8601038022450222a4100d0048030f5407400803c951490020f103045614180c644c000310780780c03051102072140c030300c2d0400000d20000c1d58000f000c0c61146403559018080f601e1402004180401280240e5401c20b11860016404100410055401c14818400c024008000281d00c811480d814042265016000030901440410030300501c0c1d45120303500700451800b540c0c0b000049280e0050044540d81c00100b424982c051030082d40f0001103c5100900504649140e102e514914125100e04440c0d45182074602810703211214151039286d40142c0743c106c00d5880f580c0b00e1b5500f581014000e5903041d900d50742c0200c00182040b18400d440030b9000803014500303801e034002405c1d1403010001803a4180440c1c0400c00075a461 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 912686178 1250 912684928 912684937
    0x10b130f0624110325050f01020309010e0c0a031a070c0206120403030b09010f06030903020309131d07031a1807090c0e04051e19050c0a090b0a020601140102010207061d0c0306010b 79
    0x18603011724030381c0321070b468841c0c00c0a9000340f144072554408000c110300ca120640090442d0340300b16042d03503400e407505410000301080360f010140501400d2111401020080301815401011038204603403181900d0380001c8203948070a80e5503060f005540141701c101a003501030560054002c5071081d090350b06220f0200090421445a0f104140e01c94a018081c14003d1003110300d20318015140480c42d54945480501078000c0642c000a1945442c151000904021540100f66031380400700c641880301b860300c10f2250700000303003041003d40301910710319921b03083c00c005501c0104440b480101340b0006140010b0704454030b8100984c040c2d400c200400410040c00b4900460502081e5101421503d401403143c00c000c2d110b441c43e000c102d1030002406010604030000d00343c01c600310b90f0f03040d11443e110f031040702d600e000d00384020026a001034014003150440d0b0008071040c10307040c400103091401a494480595403400c43c058800303200b02c460b0781c920a00c00c0c0b2080750085020740003030200d54501041e50700588034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 912687428 1250 912686178 912686227
    0x30309031101030b1008150d0b060a05030a08070f150c03050f0a020901120f0902060c0304051003020408060f041401021606060f080d03090206070c0303030b03010608010b130f06241103 81
    0x8100000d08031107c00d151012a40b1f002802c001c09418107450070102652096400300c5c032410002500081c2880c0014120300141d0344a4440f44c18001507039100241803541c51821a0000508028400b8200c0c082c40b8000c030041503540c0c00b007540d00745403010305110030010f40341804003030040107100c0140e40c015000540d145000c500009030800c481001710004c0c0027540b4029841840001c0d12081107400202400c144c42c400c850b41c424003a141c0d00264101c0c81a8440d0130f2041d048500003464110920700d250b6417040c0a04e07225036001040e0380301c490032a030100c241c103550742568a5814051101034801c5601802300e113081005030a05007004650385442c190403d00c00c01d9221644c14085496510603100503581c411512000c068503864083e0160480e802018007961910b180007031311010501030319114101c00b07002e2045240c040c0005e000a821001160140c0d2070720741d01c000881212030b881000d110410200c115080c01c507080390003846070858080429240c0d00c10b0040b082c4682600310144070000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 912688678 1250 912687428 912687437
    0x201030c0203191b0c030503030906150f041a060309210f0319090210080a0513120c050a0c03030f120c0206190902030a03112e0507110601030309031101030b10 70
    0x310105445403010148820007003881750072140010801c1000000785018490880640b5265945c0f143c402c1c4003030744414070080e848140b410503528141003035440300700394100d4a000c05107414506404180c56610607240020a0b9000760401d03024803030501e0710441c101d06180c001038940000324854104500029080941c0c030034402600274040101a8003c16009901524003e14140c0d20314025115110071625032011904100002d01c3d500120078009048952202c507030000e80e80138080482d4441c1d41400c088400340b280032900301c045500104e0303003402580303e5034584104034142ca030020030144075154400d60041c1091002c0d60250707004120950301884519000d44407601c0c150715040035201008004c2d4150091000017400d16034000c0c3c42500d00e507030280440f04054000c0541c03414954490f9000d0300715203118008070b0340340360f050b070060758000d142d91820440d40b6000d402102e080200c02e0303104402082c00b03100c08004020149030740ca20b181009003000c01c01e040c90040882c640c146c00444080801c07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 912689928 1250 912688678 912688697
    0xc08071112060703020406110c0a0b1e030c0405042306131b08060109150c0209041110080f0f01030f030c0510060b070b06030a170315090906040201030c020319 70
    0x5441d54038800000d50312031811201c5904002c07602400950145c05030500181e40f88040071882c80300000d0705100d40d94090241c03d4100e240101010540c0c00007091610600c0b4003001d14014064418095802502c103203070100d50b118646010007088819010340c509282e050b551410000341c0d005032882c1d038011030954100140c000141c00310f40c003c1c4184044501704101003880034001d55808044244601000c0c1c903a021030a03142c03004e1a44541c14854440001690300600900504010228a401511030811038103000348000020b5011052421804000740090080181c0d02c203035a121329030818034102d134001055045840d040b94841600001805010103911200700b0814204950710b60001400f07010000e0702d807601e800d019140e100c050203441c00c40402021690ba0b283c04180240340c02d0b8001c100c101c500b0100380354410203400050225420480602407031080c0d89403d034447c1e11811642018260320f181610015040301c02845107071007103610502102d00e140d080b40c8103480c1308100300c1c200306150 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 912691178 1250 912689928 912689963
    0x209010b1c020a111e12180418030306230d050a020a170105150303041707030f0305091804150911150a110d0c0308040615080c0406060c0807 62
    0x500807419a0801014400110b080c04690301400312007120039010280e603120310f40756202141800da04d61780d030b07103035904640107142c1c4070030680d00141003072000c0c1084401c030082040c000404954110070060040d814820381081090391500c201c4024040e2a000410101b402420f20200d12150140641c016481c40f4104400c0c4901003141551a0340e0003018291a651200c050400d01200c02030360078032075802e043c0824101296080c180603040c0c2c1c007078020341c109031816070494004030740d03480c400d441d0340201500800803c80d283d1420030365074003035128a07558600c1070041c01051440312000c1c0c140004a50140000181920604602082001c5011802c0140ca05008601401e10f0802c00d03485044031010035040c0b1541c1028007900c25103501c1e400f9064101a241c80e80301c1020034141c1c80019204000c03000007070f0141b035406800c9802800d0024502840101800c0a54866007050800f036201240005072440c06009010141001e840c059012a250381e4891201d4000d02030000c00c81c00245446040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 912692428 1250 912691178 912691207
    0x207140904150c051b1b090726011412070b030c1308150612070504020a03020c0d0201200403020a0b16021005090301060b1c11090a0b0408190209010b 66
    0xc0c00c21252000c1260500780f02001d02a50f00210012071001005040042003070f201040710745160712500d00c412861803801e4100700c00403200400407000c1c00130141e41d84060408070212481721110b1412400d481c2d5040076400301e07802d008540441d01c0b4050803900c45114500c040b40d4802119200140d4503141d455044400c41c25001e8804417450381810714100148038400019070200c00444c400107500381c0d440f084244200080700780c952035100d5104030300422081c2025401003011880b6071a0050600302c500c011754bc28004441d807040d0040c0e46942c000e03134a92601f240ec0201d52003840c0c1c1d40b18541807965021500781103d61003070040742400440e003000ba80405000b5881003682c001c00f0043d4880c01c46001500541141c030301103001c7d40c6401000724030003121404035009496510f019050302189014000050020b200c1d204011403000d02c00400b264a8119105001d0920f034655542c4a50900e000c00d4a0410b521001143e0051050400c00c0540c585270130040c151001503c42540d12981c0241800 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 912693678 1250 912692428 912692453
    0x902180709330f050f0c011e05040210080a090605011e08070602101a1809060106050a0e1e06040807092910090f23010c05030405010f09050409120f0207140904 70
    0x80134200000740b01c07403050406511800101416a4004488004850323001c0115081118000d421001052800160600819902e40d100442003000b08091950355112020b60b80280e00840c7d01d04945c0340c02c011400501d40c08440a464607500401540d40b40c42c200a644619200c0c00500c005c0e42d0315200ea456400703000d03088010190240050804d91005244040598021101101c8a02070100082140c9105100312211480310f80d841c46030700b0486100b04904441e80328074022400f1004001840c1c90307118003028000610428010b03101144c40c00380c18074152440780001e045042e1940d080701d07070b00368406800c2142c1218107035141c2d070031b103030300c068041e02c0072801a042048480c4100500294041da1b0569888d110301c60107100d440300f801030800640c0d0212007454010003e82040c8001d1060754031070700c1e0b100c4491000f4603124061aa5420101e801c86000020980304c0860013100030014640002c11021420f03210310003030030000d1404cc00c030300640c941e4068441c030440248000c50140010b10300c840 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 912694928 1250 912693678 912693697
    0xa05070b0903210106230d0e0c0a080a051903121a0a0b13030210030b1203040e0f040f0605130501022b020f040302040902180709330f05 60
    0x52114102802801c0c0d036078100301020442d00e0b12030b543c40540000c440464504917912521011021141c0410003d90450403441400c440c08041c03016050620441c05041a03043e580300c049d1964074605001c2c020010401d800c440c11031f91140c2003030800607400190102260031120364040000940d498120f50140e40b20004440c0c05040440402d4501c0842c062006a00800c542217444159a1502841a800740c11152150790009000030009400d0150304050705000074640000c060b041003000554a00141410885507440440c003840900c560007000c035005107441d58281c5251626554058240c800080c0040c107050b02d0307202080d900ca00c0201c0712100180e0000013503460310a04444c280d40300040349880040c038032040707110600c0c80604c0e1013181d512003043d01ca41c500d424210340900c000360070200005c0b6041214508003400c8440841d14a0303018040e20750b14988114942074460480d01c0080003a0000319180100c135003416014641c1a40507600c290a210800c0c4c9610f450a9500c1d0080c0d5810 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 912696178 1250 912694928 912694943
    0x1030f0201021c0e2707111009080702090703090203030f0a021207062319020913110d14070804030305060a08030c15250c140d0503090624060a0507 65
    0x2c51070359541081002001100035102c0e90041e85c1070342ea0540d200b0516008500c6000c9004010814542c803920203050329020b2070040314120b03241c00e0001d40868480c42c40949095501003125011460a0000d40e9000200d500c0d041c000c1386155000a5100c6c80303030411001c03002c2c2001410480c018001d01140ba0610524031407642c48520740c7c10008003800006600b142c15914140724500140340c070100c40c6006800ca50a0481503441404240700254404041c950340b1640054503d01560350394011102d10040c000340d1103890b02c400807462025608881c1e001072240c081c603820007031040e601415165120f50546000704080d110b55000c94041031554100c0d200a00000901c00404000010840804012300500240941e104480c00b02d0034072514207108100c1c401685e00200b02c61003100c1115a190050b51045019010100703003501e000d01c402c20f0034001c02c00100410500c09420b10806520603550460075800b40b10444580c00c00e560015240742c072440002c101c41d044035201d02d00765220300b90300428 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 912697428 1250 912696178 912696223
    0x509041110030b03010f0c360603060e160e060304060b102003030103082d180907050c0703080307030f0203011d06030a0803160c0f0b0a0b1801030f020102 68
    0x5004003e402c21192181c06982860094400803245c0c1c400c0c0307a824819542ca07440050a5400001c800301030101665070f01061110b8030b41c0e0101500d244030002060707039803400210189000d03d13241c403055000f041c110054100104030b03001300f9002084401c00007001c0760f00ba0b60300e54440c50010000d0004107a0644c01030004c001103d0340c40c3d00440d40c0851310300c1c402c004002c050481055195680300c00d010090098030280304c1000480110000401c900c031100c0e5841e4012075200c0c511464940000e84031114941e680c482006903820f1024015411020518000c1d1230070008503e110b070359000c58030000340351003800400202e61600c01d07800303180c4400030542c05544d02e51351818101a94005050050002d90026011610501c0c001a0102525510508941c2107540340b030040303041c9814018000091109016503800054041c60700034810078804c4c41d02160038213005210b981103031803103120140516091280c121144071304040b80c50449500086200031206d0a100407400d1160020102455601614 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 912698678 1250 912697428 912697459
    0x10e04081e180f030d1b031b08180d020609010c05070504090b04050d05070b2d01090f050c09010c06110c1c03050702010203040c170f1609060e040b0105090411 70
    0x281c1242520401c840d0444406001d00070075417180883c01030300002c911545100c0300806201e000109145020741401d007044003420101d4510000000300880341514005a11940b8962480141e0311110043c2e403100c2038204582e010038054401c4201c520f040c0301603e008101002000c01a96000e8500608184041d40c0d0b0703450410080d0750161000c640030701541ea0341c1600c06200e1010b89c0c0174142c11030444225a15150200d0804840c4035600c6440300070751003840e002c003401c070042c401d00811650300005604030040007000110b94024080c3c1230341d20000c024062081e0390100c0b12501c40c5400ca000011781e00c0b450200702c003540c42900d54940c0b190280841654004040802508450015441c107104590300c03100d04030308034442100c00800e02c414140003404518180e0541010040c808c8040b200d85a02d1aa9058580b900308004003c000760f0303d000c2404000795a00aa00003030102e041c00d000e5034100740c0d4803040c694205010f0107000d142d0140c00501400344041e01030540c0322000d4004c01c155a01d20 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 912699928 1250 912698678 912698707
    0x5070c08011d06010e10031b03050111090102060702150a15031703060307170a140a150605030f1b040b0307090908130e1501032c030c15010e04081e 65
    0x181c0d40c0b0540c0780600d2000007440585140c480d0f1198500e0b01004031480e04550301da40140c400d0302c1c5c443c100d14801c15004030005400340f080c50003030030301b1012140d2159001c42c002403a05400400d0281190000400c20004030611109150045002c0c00c0200c0d010009200c014924540303540f01500d40f44505511103c229094001540140c00039004d0305c80c0982c807243c00303001004007584105a29440841240085030580c0c005444450468013510415003168649540003c2c1147d0110f4150741d682000308101d14003004400854020f00e0040c00e4682080e0038005003070380032801d83d54041c0341c41e140009840e0713400340242c0001d840040303801c000c3c0171124203113012650030666080c200d00d25003900c04601602d4030392209203e6003e4088800f200003a513001100174241540010b1745d6180c1001110700304105441c4d0030352110545a00864854811003501480d14660311000c0524404180052000309002c0d21442e034010f4201008030360380c0c580c040c2c5807030103080400d00e640396801c0d01240d0b00c659800e01 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 912701178 1250 912699928 912699971
    0x305130f0b10061812060b06070501061503180b1f0801060513091e021201090b1519030807080f0a0c200a03020f1201091a0a14040305070c0801 63
    0x10034000c2e181e51500d4003401e6402e40b040344180c0882c805035150800c0060350811a401c1440d10a003000b0907814907841c0070624540011100700c406944443d000c0c0903c0321030040340b020140c1c4e60b20702030091030035494403001d48813070074000645400f16a10014402245100c0d18800d010ba030b103d501842540d49807115030081c0228003625100348101c08069103c0d2896004400300c00da00224800213282c1c522500d2004d411800c60100e030411031401c0085030001085c03040300711300d41c02002c00a006140060311721141201426a25204004400b4810440070140c2018015203034009640d43d0740b9445824140903e000740810840d40070000240440004c2c4c0c0020650040c82c858442c0d010210020800b1031103c0900358840d5801515640c0104050b1501071080e9591070009040c4018400340b0b45502400e491154009507601c01c0900921000c5400c92a101940305e41e90348000c100080c42c0700380089940c03c010304003500704007011440c2c106110303002c1d1300321004002200080010000401900748030044 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 912702428 1250 912701178 912701191
    0x50904080d11040b03012706090b031911060d0b06040909020f100806040c05090d0305030403120e0a08030408120f010510020606061e0c011401170c01020d0305130f0b 73
    0x10000c400300b0700c0300b0302e10a603416103400002a40c00c42c1e00707101000300d20003410020503100126200750381c0203401c4c1c04e10807030000c1e004207200400c6040c51a424145801c500c410042c5c0c48025047d140000304000e180358041003003085845590356890411103801508403240019440b04000500007007400c0b81d07a20001d00c1601c00d03200c070300c1a800d0501c20007c18800540034100400d0b030440010b00c0c117113401c2d405407003100e0741420300d2818008100041010380e03400da1011400300b24004140028541c204010402c140d0b2201c100303001004201200e640c4402440c02c0c010407900f0040046804c022440c0c01350307001d00103c5c4900f4100c5207010b000040000d0000c1c410b440c00b940c0412901840144080792952085101408042c50580500398481860000709502c0340c0c699800e002d40c01d01c0e09820300071801420a0035100891a504140c104c000d8040c0c0355802142d00d5000200c85a00740e60046403a04048400c1c0c1000600d55403104c801000030880c1140007400c50603034240007402c118050444600601 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 912703678 1250 912702428 912702431
    0x90d11032109040e031c05060a26160308040e0c040e09151302090c130b12040611120a0b06190c050d090b030f07020309062d1c02070c050904080d 64
    0x30384041da00c6403a4402c1000b46d1184000c202403d200c1c1000d0b9400150f00b011029151800080d075415403c00202e00c2d0016030300c1c079800710100c085111102000b012100d80c900e03e80315040545150b07510840f6226610030301e80c80c11113a000040720f0f500341c003060f14000d14042c50b150b009c80c030709113041b03945414020341d55150010000c800300303c5401c07264a00f013941c103070b000d000c100141d1248580401e46400100f202085144000d0010a8104030003014088a44818804215a09061504400b40e40810042c01c00c401018850500340402000003035801c110100300c009400001d51011032818854040f00c250780a144411500c02c1c0340e4040e241881560150040d0350b80e16564031411103810501e0701c2000011281440403440f9042100710058110241e1f0041f40e1400441101180198200d0318035101942e050317a0302020040011a1001c16403110407444529007036840384401d1031480c100859100040d40416904100113003031000901410000341048818501482c3c03102071680304511002a85 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 912704928 1250 912703678 912703691
    0x31506030f050a06080a0201030b0402160b1b120621030c210406170907030b040b011811030c0901020a0236010501020a12200304060f05090d1103210904 67
    0x503056441044c05445001002d080403000fa50011400b4100d4071020f258455400c0103040101e0134001c440b9614548110710310300c007614100b087c400440e001072950f40c4076210200008164010880d11503584480c007240d001340800b0300388100100ec03d901d40d408414a100005880c010300310000b80e10051004100d500c5407950201602250f01070003140f26101c04110000d8003025100304070181240d10001d03120031242c0656580e25100710320002542c0580780c1c100e10600620010680340007034201400e4200c03091000103011401d40c81c0c284001041030103040c60205541d2150b078803d00002a5090b001003030303004114140d4a0031100360000406c1101c01698003820400301804a10700c042c101c0308140c01400402e45103845070140c96044692800801500d500c0888419020140c000d0008110800454036182454006411519896402401e000701032086030015a55803009c40c481d103600040c2d03410900540e40210f803034070341c40340c1030640070705888030300321400c609040c4c0604803442d800c0b0f8007030100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 912706178 1250 912704928 912704941
    0x506011401090e0103020f0607051c0807050c070e0622020306100c0503030a1109090a0e0705120303011503270c0e040f12050f131703130312031506030f05 68
    0x20140e01c9400e8088109070010405403601c40714482030031398060481c03490001540d071501d00b86203a40d0203280bc010300443d0301300740f10b943c8505410b600c058942008e0b0b00d4000078519440e0b40701180d20036800d800f0341100000e00d03242c4400140d40c0d445100c0a031402c001c03442000c50b00000e90012203206004804884c3c03100510742c803501212540d9a04600914915140d4a510340060300301d40401c0d404500081160100a440d40b5900c540700314803141000812440d030710b501038117150304c0703501c804e10881d5414205060a100442140d04440d00701ca861488843c2c0c2240c1a0082d00c94659249511030103017001c414101016499203500e64481c21140d0341c800c1d02c5031906060042e007900d0152940114440d1840002e10f03070071110f08142140c0c1001030410841040c0044558480c0c080c0700c4140b41e45a8040050034603802890083c0300303d590145060200b0241c0c00903075900179210160003030f101003500d404824001d90203460441c603140d0540e0030b41c581f9a032002d005060070002e02c1038580d1074000001c0a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 912707428 1250 912706178 912706187
    0x302030c0d030909020901141911070f050409020a05030d090e010801020a0806041503050601090f290112110d020a0f0e060901030f1404060e190201170411030a0506011401 75
    0x111260b254480000460030715009000075001136000d40e040c4040200014400d464a601620705041c1d072050301c5000006a010060080800e2020306040380e000190501c05c820192001e02709840b41a038000442c00c6582c00080c0d1174040c0b0343d101a0701401150650100030364414241c00c1641c0010b0904802a40d03603a900390300701e00c5480201030000328180d021903054030b02508040120002a0755030700809490b5191300b81011401c0e400448100da1303c000e4440411101d02401e030010103500041e00d08140642030020340c07810082841c0c1d04004070140240e4004070540e000d040c151100210654841c0061248400254009071031000802e01c155000703c03490344600614000030202400044c1414026001900540228241d1210301d035106c806044c1e00c83c0007403100702e1040340a05004a44a1000e00d1001e080c4042030382005100034610f076582000d40d0300302451540a82c60178042c007826076a0342c01e0800120b2000d06980ba818041c3d10380311030500c4000903000d81600c0c1310307040031004070280c00015903 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 912708678 1250 912707428 912707449
    0x80907080a0f05100608030c0106080a0b07200f0604061d300c011a01090e04110d050d0909050105010c0b0415061505190318111201090b010302030c 65
    0x400d80d01188003100080d242d041d540b0300a80c403030f20840310200c4201d610581590040e070882d1a4507440440c401e9200d803801d00a490081c02aa005041140302d25201c00c118200000c00c44004d0004000c502401c40c512045503000742c40c000350641d0019244440c0e15500c03079800f91001e0710301c2c50070503030380380d00191602c2d000c54410300180c0e00a110007154a050a4100100000080e6241d80c04d0580002145281c038000c248901c0c1e690000644640c6104845080442c201502410007091103801d019000200c3c0300c054010340c0286d00341d40c0300d8840c0e80000d4107603044d600e4018158000c0e4139804c11895000b0143d841983c42c0030074144180e0fa203d4004440b500294031001e0503035003503600400c01051340388180c4401205000740104009071110380915640310155002000103800040400040b00c41c084510340340c2c01d031482c0c140b020130031500248001850fa900090300b040c441050141065441c001100ca403400040024401192203040c40c0e198070409110a9029009101c10750940340b41082465 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 912709928 1250 912708678 912708689
    0x308150f0103050c0d09030507150513081303020607140601090506030a08091f0206090120271504030302120304080a08040c0f030b01051306150509010507150b01080907 74
    0xc00c52003456401140902400f40030035500f03040802c0488040c51486c011010014020340700c00c0c0d507840081c5411401c0d61f0920707602e8003905203000c0c1805183d602e00001243c4c4c85800118980c1c03911044409114100803950000754400000078100342040b49414010301590401415954141e98400d200b5059075021a01140e02d500140c804000040c1c000000d400c2c804030213008880da40c41000644400201e1040540025a000c8810060803500900079080781010300112900005201440450940115180744803d4000300c0e103c000603140104188061110041c51001249030560441c202030b03100b0700080e0014091280306442140d4280122405207a11804203032030514072030400c5440c414040d03c1140d051703075511000958052500c1c6402e0165014041207807455241004100024420414003072140b4108801040707074401b1420b6086d00c0c0709050030241c0d542d1004800481315481600e00003440403600c411004c40342401d603406804480c00c00e0300e98003138948a49120665410051051 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 912711178 1250 912709928 912709939
    0x81b12010902310e03070b090f06010603020d0b040609060602211b07080a0b150102160b0c0c0315041a010b071e0602121603061d180304060507030815 66
    0x440e081100c1003892404099030f4140703c941d807500c07045140402d1310070040b4090b10b160b0011480900780f01601801680002840c001415507005058041c1d865000510494042c5980031542030700a144541002d05d0b0854001e0041011a48a2501c00c008002e42d019000051003004410b071034003d0309401061140d06c0002d0311900300592003071840003d00e24682040c0070345c001e4000c0007540310740030001510080e1090f1001d08641c50964002c69580d43c00c58105411980080362402c0044201d10010042d01d40c40380100740d80b120805c20b038628001900c21429010b102d005120049090352210303c034003a5208143c0000c041e410f00d451070f50014428015072000d1001044000000745007000c145100301214110060004c26580300c80040b40c1100c40107140c005824020801e03580b06000314003905802070f0508202160a203055182010202c4411440310001d18000c200500c641c40105503000c2c440404480d95030b9140c8400504030b0308550780860102d000c00c40860210444011043e0614002800c3c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 912712428 1250 912711178 912711199
    0x1206010f0815041202070f0308030a0b0103020405060a11010e033006130b03070e090f0c011b14030405030a121404061d0f0913030e030a030c0807030207081b12010902 73
    0xa0b104844c58652801d07000750f01c82c03410001901c04110803804002c42c014020303180c0300c5c030b0f0840c0004181c0d840c5900f01d504041c41007006114542c2c1b40001c0c2d40100a180c41c0408003007211100d5140102103060150082d0711001c50042400342d241c031900d41280c1c0c1000003200080402c0500c03188100401e42d82a5445140302130520303400c0c0c1980c1d0200000ca007000b02140c0c89581d5030112556011801c1e20002100c0d04420101c1c01544400c000b804500342080c42c24580040c00c184130030350075021103a001448900d40c20000107041d80c040007a580900002420b8036941c00d060f2a10751303080a07081e000f201c0400c0340c0d03c02005054102a05680460f041500c40400c0010072880510311409107a01995101c002c960341000d01d52210282c56210310003011034000c401c0c1c2c841c10040c00d00410b50040d03e1107603004442c440700095003d503035200c1c0d09030b10039103150b11280307146401c0e400d1000070b0700708071103610a070b560100d070304800c0c01d48404400b0701c107991101143c90a46a000e0a0b140c00201c081d42000c0d900c030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 912713678 1250 912712428 912712433
    0x301110c0d09092c01151d1005060d0e0102041503091a070f080604150324020304051b1206090610060503100b0d0209062d12070c0309051206010f081504 67
    0x4040580c0000800d00006d4407010091072000785960340d4016840c090300a03604c0e4059021110ba0b4140c00c40104c00d500f2100300d1070f00c40040c495100314a45001050348800f0301e01000c3d2000d40548020b020408240c4200c112400f03001001845940d0098440706a890742e06522050042901d5004031660350728440f290030450320a440030a0b01908440d0003595907048103121622a40d00c181c0903511409440364010305030344008410100680040c000103104009200000b003001480300d11b28000da1107840409102003001400c0740c00002ca00103c1401002c0411544260110380070344a904924628034455481c1c081c00c5910703020486901d45581e084030000d200c800c4408000d00341060241074090315003200d000204095421050a0710301144401d01460300541600025984003100d01d046142002104803440f0f03080c00c0003420a10600c00f000c5036080601d44103004181c00f4105c094120b102140341018000c1d91108244124004100f28080114900f0f5000c40d200d004056581026031994039641c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 912714928 1250 912713678 912713741
    0x31206010e0d030c060c1b021513120c060509030c090411030f061012020d0303090602070c060503040506070206010617130c15021504021e0301110c0d0909 68
    0x150009050120720380304694580d46011054025901c00e0396001c6102c04146025000e9642c2040c41400380888000c201c02181c0b0040ca18131026501116000c12001220300120003a10480c2e50459840c051220081900885c0c5e03456405501d104100c0d10708a181d480004903920701603020b425901d5000901c4a03272891910101e8640c005005810f00340e040c1c0314445c0002c0c58500c15040b2444160016020469800da1442040c001003951400b40f03140c1c4410b42d0300103120110341510060905a43d26085001d21a8550503268406d5001c032448800d680c03198006082c80d00100c808540310f01c9910000340c04503101140c440d040b6601902e80140c00201c0541c00300000f403004058a01e000c034003c800c1400300f0a40ca101d00010090803500c10f0700708601e424000e042001d0014050240704101d4140700058440c031190216440100e05400c024282c140002405130008401902402e14080b90700d450201001c0f514410301071058451401555441100000340e0382d00304514031144210b170b01c4214103040311 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 912716178 1250 912714928 912714931
    0x90f09090c0603090f010b0904050616030e1b040f090c2d270207050601090905030d05240a051c080d18060f0203060a091505060414040b10020312 64
    0x403202030311000c0c0e500300301260003a00100e40019195000300703200c0030380361800c3c803074954006010f8981640c649032544605903500fa02400c1003000f21010265824014840e610400307002984005030340910403002c0f141c01e403600000b128241b00d6450120304d08000c0d034003481845482e0341e1000c119442c0038034202e07810f4410348685420910b4072440d544114102403018140102801018a80500003080000194440158180d410701c40a20410040c40450000140700e41181c1081e00c001c10031010918006082d8002c40c0d84a01035681080b0500c01220342445101c010b000d95040c00c584801c204108010f4118428410a80c00c5120250f00204410f00d1858051115018042c0c20380b81240790074058084405500314408448621524001006054003440c02d1844000c881135003507060031000901000c1c06449100c141640c0c552000d11083c521030401002080010003050700c95540d2019568100181c41069114030314042c16000540380100104002010b03035070045060040441c55074419100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 912717428 1250 912716178 912716191
    0xe0a09021305060a170a030828270506010501021014060d0206130311040b01110d0e040e01020418110301080316020307090606110c0306010b09090415180c060203090f09 74
    0x20401c030003017603191042503018111182c920017408076203241d0030020000a0b01800700d0202000c080781896445464015a107025000d8180c0002d20a000711780403100704130502c05100ca40e0180700e1521042c40300124070300c0e04840d001e800342c80d89105040380d00c8045590640ca00000344409002203035450070240740e0200c850f071010b00030602e0701d10310310000103140b02c0c190300480f00c00701c0c0802c16030800e051600420a590100307090801551001c2480c854a0300c1d04c00004408118040b40740c013080b595640c10110100407054000c540d61525440480820328605100f000d01d241404200c821055400080340d04888040380070b1414032100310001039600c42d500300241e0341441050000f0650b04c45d0b070b10079a03001b0103464031039188415a22890b40d003000c0d03a2941651280e00480c00420850032003104031070100c1000c943e01c106540d00d40c648411a09880620005100e2510f00155400300400b810101454040d184046106582d20b10072a42c0b442204001e6030440c0e01c04024900b10308144509942120 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 912718678 1250 912717428 912717439
    0x70f0806040209150a090e0f011a0a14210d0f0e090f0a1515090e0c040e04060f020307050a0e0d030806150d0c0504051201110712020a020d030315060503011d072003040e0a0902130506 80
    0x30481030030140720601542c374031071041d0080000a42001d4004010180554090511484402e00e0b403000641c1032100030000c500c0c070703103902d00007420800c855480170a44420180050480d1615000c03030154000e00103404001003030815401007020200500340034030406800d00902e20b0103090112a652414001d40100e400c603880d400c2c0c011840034140091071155540e5607540e81c403100ca001c070052403800703002e132002c0c082c00412a0503c0801d130b000030704079400803050785c100348900440b0741000003a11505040c0040d01d40741482c1203514a40c000003c0c0121201110030800540c08041d842d07003216204600200c80700001c06c0104000fa0004902040c440500c4c0156000880d00c0d802148001d900c4141c01c4002903540c148000380c0300c8000c1030a07005440c1c24600300b1b055606200c0b8030800511001c01c0b0400c00c5201c40e0001e506148100488144d081c1000c0440d1080346969401036a83c1d00a40100c6008941d14000212014020f00c6080c540ca50014201c4410440c80241c40c001030030003600064000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 912719928 1250 912718678 912718699
    0x120906110a1b08010c0e010323010b18030102040311150307170a09050102130501270306020c0a020a0909030305060d05030d150b0c070f0806040209150a090e0f011a0a14 74
    0x43e0288201403000001c0d4030748041150202d0001805c456451070303d000034000b1610003482407082955514190303002c000d001c547e01c40250b81a0000503024003038295142d0b000250100402aa8410780200307034400b40c0b140403a43c142c0e1102000940011181c010020742300c040383c07050800362100c0454029030041d0000a0140070390302c50500303a034401000304055144100701000302e540d000d6005003d88800d9100100f285520100d00c07015107001d0300c40580542e0b004243e045145030113001c1011900c1d070041a80c503500d95180002409403400d0003003500031a10b0140040c8140c2002d00b91208007692020186161034908003404004000d0180c48090350b401070000425503540c100d0080c00c00700c0c00c05004009062504840c0b4580243c56045050203801007428840140c442d0f4641c0c83d0400d8410040da8044c039011004640c07070b41d415034028201103046c0050030750b200c40c01250001d01c900d2440024403a00040c40d00030400d10070075804094010340c1680003000741e0b484041e400e42c40c6407801000c1d45131a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 912721178 1250 912719928 912719939
    0xe031813050106110f0d0203092704050a0b101412070906120510060501020d110f0d17060d0201050306060a090e091606030c0207120f02040504120906110a1b 69
    0x1c49800742c101c0740102d048014028401030003088041d242d41100700080c448840d00410094aa0058251083c014244008140078460540c0341da040070160001e24000d462500741001d95a030444014144c889002c2d03031012488041150354603805490100030850030070411740d81800f500000c103020215250240e102d003c200107003680140c0e4010500030759602c4090549007081c07420046500982c08429180040070085070340c02142c0080c15000c541003580c1410060942c1605240b079604007001940a41d20240080d1500448190b00c6000b119840866a41e51241400042030b80610068081340041c4001000c0c0e2400d04000c088028461034035400d0503a889103500304010041e5044600da4110b00c0b001c498404c201d600701e4008003010310f01404a03405050010f5201c499501039074100c4040d1880c1c0e0f40500030700c02c0f400ca90385940070307000301701510b00fa00b0080d00741c06205400c0f1f40051040707540040c0e9140706d030b604121003004840141083c00182c0e80d0b00c0307000c154100b1700a01ca190170500001134 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 912722428 1250 912721178 912721181
    0xc04180e3a0201020c0f0304120f1a01060c030905010201021218010b04050c07050115060912110607050106050103060503071d15030a0606140607080307030b03011b09080706030e031813 81
    0x100c020749030000b50315104407034000742c01e040252220344070b6903000b440300b000381c081007506024450350041030076550580a414103c8041d00129041150040b01400016000c0d90000100885900030395030304120036180c0c0012401e0344141c003401241c490310080810443d40d480400035501c04640c40c0001165600c400100303095407402c480c0e00d072862202165110520600b8011a2600419051441c00b51401c043d00a0000b2015001c0c8007075035001103100b0307001c002400802c42d4031440002c00140e00c503025450240d002c0c003064001c05000906200b000a0305040c001102d4044c0c5030120321010880c5445c00b00d400c40704200500a00702c01c84580a056041d45082c04141203a40c02088003185407800e00381900120310680c2c250718000c5004200060104482d5010780350400c2c51407501082921210002a0140040c8080540200300030a00c6020b02c90f0041061300403240d5800a488040c0c3c0d80ea40c00f503041381c4c43c100780d05229800070405048098a10780446d0320007007000f0716060304039035060780340760 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 912723678 1250 912722428 912722533
    0x150301060e10050922080d050c09100201020a02030d0e070b030117210304020409060b120a06060e0601020d0c0303060315090302210412050f03030c04180e 68
    0x1c0d0516001c018080c0203900c035901c01c0e02512081e00c1050300350500a0400e180b00e0040c2c420465508440c07141d003010414030380201d401c400b1240a003440713035050001e01c16800703034003090403580310310441340c804180710f8018000d450501e42280c0140d0300b070071044078140b13010b441001600c010398051031601081404a40c2c025501130044642903a109200d0482010710340f0f00380c000509001030b440500c440c0000705407022264041c0d0f060300c0124050600d850704002820a80d2481588886002420901c5440008003440b400e40900d00c1841007654071128101000001e071344150050f00309181e01c0307003690b01075140c08142c0c521030710b40094566542d4441e100700228010070103800948504011060580c100084074030fa032014070513001c40f0f00c85000c0d01d540f64451391080d114052800d0100e001400010300003000c14000c6001078035564600380c890990168040d00a0101015110004040c00403082c440c540c4034000c00801040d880c02101d103481c004c0301d44241d24000200c3c1843c5c0c004040b000041152 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 912724928 1250 912723678 912723689
    0x50123040605130918030e030319030c35100f0f091b0c0b090a06020d021315050703081003060e0105040204110f070803060402130e0f0f011d15030106 66
    0x1ca440e02100503504660940e1a132240880909024240f44a01480c43c00038005a82c54100880440e248074046804c5001720105005951030844280240e0f68254001040098966982c2c0d00f1060081002c02200018a9217400c60300742d00e4504a100c00000303c81d0207800100c068038518a8940d104130701c0310884000d4100841122410304200541d003058000c480c40204030102d40c003150403d2440060450b540101c02801400c82900402c8410805000850966400c12415582d465050754942c019611814042c09100944000050f00580d110055903a942190707840a00c1c152040d1021a14040040c180c411213816000d8000005851031040d403442854000001c240c40c80c00d401000101d403841d9442c84400082000590313100491901121318442e802022070361283c9500307001c1002400b5680715940b02c0038820101140b410b003164030302131207200469181885507407195159180b210081c8100241000591402d1841110342d01205a04c100c4440c44501146250300c0020300751441580f20 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 912726178 1250 912724928 912724937
    0xa0506012a15050112060b19140907110d0f030b060d050a1103060607020d060204030b0103080705010c1d0f011e0509090603070302030c060d11070c050301180b010501230406 76
    0x94030810a445404802e21481e00d5400c010070740c5404810340c0c0041185000802c1d1550300c0300b07580306603515021079162000c0c0400c3c0302c003007050715400d40c0f000c54080d03916110303c11070b15100000c0546101d440c007200c68015807009441c13100d0300417006503405407a107141c142c18151940310f114515110800036100c206900c00e40450507091104012084501e04107140800c00000c108120543e190389080390901503050340d90310348485076400c2c404002c0c052038200a01c1c0800e04030001080c001854050188240114003c07c8005d60784a02038411204000307070410711074000714000c0392524200d061081480418100102c20150003083c02e42615030080c080d502164001c40c505495090100c0c1c01ca9019a00750020040c003810754000030799074482168880e10640c0009444c007021100c9800041c2d580661500b510348500031840c0c01103107500c56004481c0a50f01c8c080f680240f00307501c1c070300d083c0c1e0407900052034030bc0c140d08080045070403070045030207215100d5601620405009142d8010002400309584 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 912727428 1250 912726178 912726257
    0x10815060a05190306030b01120507050604030302010b120607210b0d0506070215060901270e0a0b0a02280203070b01030b06011103070503091e101716080a050601 71
    0x183c503010403844821502014a000418400211016407850654119103120398500e150791820503e407480365081590821000305000082640541084c240c18808445074030036080706a2555a8400d02290b0320400501c08c40c942c44130360408031507004141031040c40701003140144d01000c0348480942d400308440c1c0d540280100a14558148010310821200d03500d149083e081c500700042400406014031a40082d8030005c950341203054860300d52189500b400300b0700042c5040c101194681d0030488040ea0b42003004400a00070201074801c0302c0c1d1390ba024205090710141c0d0300705201c51903420780c54290254401023050001080c400810140210b10078450258035207026000100421400309840850798001e02c904000074002000341d512000064687c1c1f081d40c40600c0b02001c041d11801c018980100c011030240d1003455000c0f002c0e000c0801281406065a11900100b86070705510901441c0003401c0349011440c0500c43d5000315411200c14948418806e10711418480d001500541944000040d800d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 912728678 1250 912727428 912727447
    0xf0f03160806060a14041505030f070e0708130b090c0a0306020c010c05091804050a0f12080c0a050a050904060b030f180c150d061a1309020a0e010815060a05 69
    0x100b02d6a00540079141628a58601150802000034545a80e0300c15602c541344100c042c51040340302001080c0040c00c0702c0480b0350885260b602ca0b5120300480c0e001034ae1080001e084607000346455809212015540041d10000703440e01d00d0001c0c4050306008542c000d007114205d4659a181c0c02d4006140503160040e99402c102c2000c80c2160242c4413600144601489113000c0c0d40c0e070300e802c0720150929416a42c0c126644518115050041402000300302d4150030300e8003028040850034901d2040c2c0c8544030700c81d04e43c5640401c3e903e07502130250410700043c4100328070301403240b00307202074141c00001610210314145c0f690360910054204071024005a1400001c21030b0915850031816400503440e00601601003003400404c0f441e4101d040e039120301c0140011704040003586944010010180c074038006070007050304008450298030076140001c0c03090280401064454140c03007140c911500544030103d010b104403006540d0040014202d500c1804684c0500040751210703802001800c25907030780c007070f9a200c010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 912729928 1250 912728678 912728683
    0x13020c150a0c0908070e040b07050708070c0311090609071202070f080a12060812180a060f020d110d0c02010c0c180609022713180501110a020c0f0f031608 68
    0x35441213899500c0b500b020080700d5181d240c0c40e038000350042c4640c58280e9070309800b6607140c4210b44000301046000a00305040c041203980000c1603911a035251300c0302000140410003508025140300d07070b020903620301140300c95000d20100c44c480d030444400982071580c181c5585403034080610041d211140b00144140e002948442c0e00700608144050401c0500d041000c060341c0c031810382c1d820480c40980010308540c1101800b1884840c1c180040140580d941c84100051010700c810403c3c02c01740c4204040012514003410004650700945c400400e54164804000c484a0200180aa0500c88000041401f094100c01400054682c0e40e031211210100310001e0030403107440b680a18440741c410300850214140d038a003a07400d8000c0f00c0c00108020a2402d002901030044070241c950041e20340005400e083e815014046030032401b1308000c001302034100301192007601c210f41020703005030086240c4c032041d450614921141a10050205c0015520400100b40ba00420864580500c00510707010000c00104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 912731178 1250 912729928 912729947
    0x100917040305100b0109180f06080f0318193002010c0b06040b0307230105210a0207061113060e010c020906030313030f1401050613020c150a0c 63
    0x444045103014076545541e80c44050070100b8098280d11110341140e140c1c4150f1841c00600340002504055030b80c91465000100010240711171420300b02000020074460100d105508022254061440c009070944460f04010f4034a55480d0f001102421b01c041800c14000000d014000000c006400c0388264064000c910a41100414007100121840d0300103136441007180e28041c3d400115105191101e03800500030b0101001c81c541c040c41055000074000252140b0846010410311400980d0f8581c81c0046402e845070740403200404000b024004401c0145a136100d510864490380181801d580f44d030307070a0640d1014400c0b60180742000c500000200d1085202400500710b170309107903a000e0540c0e4006000b0305080840640f10702c141200107400390300d0620031110442505425906141d482c0c3c50000c082c2410410701f175500280c420802014440144079803400341d840140000c0e414a41160504013035400503454400c3d40c0070b504020a00c0003a4584081e001e03104482020402c1800060000c188060 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 912732428 1250 912731178 912731213
    0x1d06040e0f03041406130e072a02040b04060509010312140d090506060108010806071103120903250c09020c03130f18140a2003040605150108042a05031009 68
    0x4000c5a119060b90181c88000c4032541f0780c091490f9038980c40c0654280410381d404600c6001404043e640381315080c0c030305551941c0700b03c90400544208809100441d00c45020307041c0c01002440042c0302088402222030100e101e14a45909061118000090746030804c004071000c4603202d18002c01000014000780c1e900c58000e281026956141201d101e541c2d10015003044180841d8800d021080301041c8202c030141c1045412007202070400c0c0d502e070795603640181c03054100e0300041d100156000500034195030410360094402c50b4502c1c2403011107002580070351560100d0384001c0140c8101c126000803141c004000c104010f8004910380208020b00e00032186000b02030500c0d0034000110740501c8400580c010070506400182d42e1801c00712080306c041e241e4518008004044100701c200906c0d80c22032445459010080c450040f802c80040d600740c50140c43c0100300c040f4181948440ca0202002c00808081c200e02c00300c070443c0d8600109040582100c09148041e8070f91111500340f10000e403101081c0319 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 912733678 1250 912732428 912732439
    0x512030306030a1e021f0e2e0519030b01020f0109051209030a0c08010204060906081e1f0305010b0301060e06061b100606031a0a1d06040e0f030414 65
    0x80c10344002511080b480074002d181d080c034071a003110310000e40b00303c44c850360f03074040d102681d0010460944444a00b940c5e030000001101d034400700310380341444d204021001101520342c1001c407900f920341000390341c18a00520104a0180410001c1042090100b0480715482d01c0003c1d11920502c002030a0035600003003c2c5c000e81c10716000c0000a040010301400c49c00c1c9104540fa01c6802810000b410100006000341030802000c0f00416030041c1075008004861858642080c5035a0b103840c00d40b0b415508a42d1030311101d441100c41c441c540c2407a040554404c140c500b008128a11100840408540c00c2c1c0081d180b5a5407055100c40c00d00b82489600060080040740460f1842d1141c00100c1600ca00040300501d510400d5401c03d071110200b000144281280c03106020032602c401e4002c004110306281c8980a203120040000c4030300b4480308440560b0520401840300030b14409828400c400003508644d001075950760716084440080c030007500521000001b07151b842d0710b4400d46203040f0514030040c1c1d2180 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 912734928 1250 912733678 912733681
    0x150507082808100e09070e1b03010608091005041a0703090204021809090313060507050109050a031707140910050706180c1406090418050a03050c0f01062117070501050105120303 78
    0x5c1000140d01030031104114144040d82e0b90303d20807001d14450f90244030310070050101c004940315400c84bd5841c03081c00078800f159034402c18164018240e82d42610701400310700603241c4424000c8180302c0c0469000d403041c200495050351710340c04101264400c06aa11002e0444000d880301490800c503841e4001000d40011400c2c08546546003800d88294820742d000e003d130008202003000800e4102c018025044070036500d00070283e0401030115091462a024510902000211954092514080d1040c2c007042207a0410300b01c04140500030310511810300c1804400d0017070300300040c03d40c007523418060200c5803240b8020805203030001d207080c2c0681101000000000074500300b500c641d8140e80036402c00f103501140c0c4c2a803180300c01d50010f1080742c018045000708113404041c581c00038010804204510115024052000c01407802c0380c0b0305000d2115030741513400b0000d03c200c02e0740c81515092401585208050f004400e608012607210703010494250f5198401004a0719004000c54048203248001c1c41c80c6 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 912736178 1250 912734928 912734941
    0x40f0e030901230a05040306142712160201020c09010608060d0c030f06240e0103060218030d170705070213052703090a150507082808100e 61
    0x140d0041c0503941e4100108205600c00f60340300403021050014004481558132000070400410541c070031b0106440307682c00d150887c8880f140c001091403040700b0320052100c0c1d80c004002d41400b0b0006400760040144900c00e03043c1c51020300100103105030f8114000041003610310b48000fa0612004d411407034891841d075401045100d0b041030f02ca80d8050700464408186021a1800c2503045c0515040500302c1281b1980748403c000c502e51007007013003030000c0508442e80392420903907400c10f80703507070103000525080003004000103242900a0040070740c4804070258804001008a45040c004001c004002500d041e00b000c44035102c0d05180d5001101d91820304c0c5070002680115190f00c82e264800038851303603200d0000c1c590040b6451003040760705001101c01c0d0019140300da04c5030380c1d810030400f0b00d2192540342000a400040400034803a10440340d1285420b0054945072840c3c11340140207500f03024481030544112041507590942c0d2681c80580b036a014500788440c0d20703140000d49800810029101400f03100b01c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 912737428 1250 912736178 912736183
    0x17010605041805060402070602040b0a17071b0606171606080c2710031d0703025e11041a0909270309010f0f05120103030e040f0e 57
    0x105042c00850110b1140c031644007042c000d1103640030113010a48045408500c407507400004020a1400d07607102491200030b441c0e00100e22805641d02008a210814512005101441c032010b10074001c8000040c0b45a03102286192a44004c241060a802141c07011006d00c00200c1c066011703281b03902d00840c142c84d10804541c4603204070307070312217280714902000907000110340e80c440e066501300a0841c21058555030700260142000e00c8000199580c04c460725000224001044002c17650010658000130502aa0759031030fa88801d006040c081011200d907040c544c000d881c00c8047c0024010740d80b124003c07409011684c0c00e5201d0000d1aa0b5810002c00c0404040660143c40a440c03401170520144104603965030102c0c82514402c9070002803400400590000210780305030111a862454481c200440d80003540f40d2185000490100d460428070420107807146030880c019105a062052a01c000c240315241280002d85c011400204110515001c42c03d0902501c15045d03403000b418403000003003406207034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 912738678 1250 912737428 912737459
    0x5030601140d15050907050117130c150e2b120306260d050a08150d061e110c0a06050718230108010321030e07061701060504 55
    0x11202912280010015035641e5031402e0700076800a05116000c80907a05140034140c2250300201d180031b21140056994013601e410b8201c10b446001005656aa4421000e00c5407841e050954015a0ba2403010515001510908a4031000c50301c41d00c1140c0450420004400c691030411148880750309031408000c07120000060301300c2e0b0300c5004659400305d0b640048004100c1f55102e40a0aa440c00c55001e43c00b4105211a42d00440c501c169000c8a07150301043d90705210303210a6200060f01100010f40311881e0f4403140c0407400000380040326100d25a100c041c10758500203040d5107a444c04c05000c606059903442890f581d910041000c17402c2c0703941e00103080c1c0c99010300d25000c0c042584850000309124030940f142c16400b0010100340c0811a11020300c2e4030541441a4419505000e503002d00510750301035a2000d0499030f02036010109400c096401d1100380400c540b401d81495150068581c8070a824070049020700300035918071203080e10b000c0070b23011045410391040041c4441000281b043c0600e214804 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 912739928 1250 912738678 912738689
    0xf061e0607030f02010219050310090c0c12050f0a0302091207050f040221041214090d12090f14010201140903071202101d0f1209190b07080309060c0405030601 70
    0x4610052503160140e02900c5074046801e940307d4000c9080007007a070014040d500070005900a003c04c0d0343c03107003151804c85072035229240100b1584c4e040740000a140e0038081c00c00780d400340380c8142800b0000142074040e400044001c000309402040404103401c3c1400310840c5600118000d200c076920b40004510449110450345014a0b0005284805204a104810140c403840103c04040d4a41803d10303401d404400c500910024014104400880b040c0b00203640c0c0500000303045138540c070021703aa1100710a24094405080c081d250324006940c94610540c44010402007098402c400d1205000a0840d904d8404500b4541e40210607c8126040003041d11440c0340c1c08003001d401192003800580c500020714000c410035604200104803000c80710079032094076140c08d8003150801c1a03840ca0887c1c0f10700444021035454803050160541e43c4c9481ca10444c80d00e2800c00302020425290100c2c0c8030a076000e01c0051326403070000424080d1101041010592002c500d016541c105807e000000b901e480061060 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 912741178 1250 912739928 912739937
    0x303021009021c05120703050702010f0206071407060b1315050d0c0b090d12121d0d08070c0611120c0403110108190f200c07150311030f061e060703 65
    0x80c0d1007045130800818004904800441e81c452500d494020155403000c10101c3c0001e00e07501d615801c890000070458010311294a4000c40700310f000f800310400e6000000252555900e40e440070305151a0301181d001101c035144000b00c0c1e02c1545c02d01070b40b00c00d402540b00314090800c50441300c005c03404a402e103900b42c9088101450390b80f1084000580f0b4140d4227540a00031003692585c1c10403541e00412560b6040c2480d0702c00748090205011151000e044009010700140c1180020b6001c152042072030319801407080c00e025406441035121002100d2140203904420703c000101d10000b220040d040b540e106000d907103000d242c64107680d252001d036201211154180702c5150b0128152140501150f955841002010087c160b03103050083c0c0944040603943c07580c040c0e6801151464121603040303468070074641c1d0081407041e02d000141c41c54840440c400c0e80070943d942d84a40e20b01e4440c04002d5000300500080452a0300b0500100491224550304c50a41400141d000c4829522140103450740305804d03082 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 912742428 1250 912741178 912741229
    0x1f020f0309010207141f0e03060112030f03050615070302031201080106050604030f080702130b10030c050901081509042d03090e040c0e070203071a09060402090403030213060306030302100902 84
    0x3041c8021180701000351103000c803085c1b102000d90721020a40e45c11030114110799140c0da95096548010b1b113000000340c0060b080050b0000c285010340c00c09500104054815000b800d211911106503402503101100182c000017864038174400c80000150241080e0740080003000e1070000010341c988210303c4000c0030741d840c2031007403018003100e10b058034100754004d4a90070088420350704d0700e8010070501d100a031250b4202c00303181503043d11034401c031050300b00251156480c2c00c6000005588941d4014007001907484524895850f40d20780c0000e05002d1485046500e1500d244040c42c4100d0086106941c01d6041c006c06140d00441c1d400f00c1c0c4c04048980c81c0b454058a515070713090110802c05241c00c002581030441d07040c408071035400002004518007840c500001d00e400d44803145204003090f0740b42d00300340d4040400701d4094505292042e4015101c0d0078014900f5804d81d2415508a00c0f0340e001c2b0010070768600e8108107258050107800c48040047c0010070000c0d030030360300151f10346804500701100d03e0315852 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 912743678 1250 912742428 912742469
    0x905010b121005060a120c021f0207050a0203011104061407080d1d0a0b0603010612020a090c110d020105011a12070f0c05070e01030c0b0408030901031503021f020f0309010207 77
    0x403a040c0a828040c20803651032035407130f8000e006d1302c0000400c0d805841c80c1420403054240b020807406043c43c00c0b5003040c3c491100300d50342d603000b81d08082d00c165218010100c8400040c1d80034484c402c2110a010b00e015100d0b45840d101034503d60300090b00380c100071420400000001d010001703d90ba040411000010400000d203016210368244121803a40380c0700d051103e20500415100395031081c1070480080c407256444043c1c0401c04060070038001e412640a400a00072090140c00c8410385010310326110f181d20720154262031070055007a02d0540580d40d0741c1d0060200c0a4003035040540d80be54540c2079440d2207a0303e05460640c9000401a80400459040394081d0a10980701d6050f010341010885200c079490380403204030010300b84800c480501d40d41d40d0000307010321407609580803a1800e401460400038010010f501401002031130307000c54825104080010f940c0c050050911490f40241c0440980380500007034580b060034028200c2e00e50061116031156030707001900c4d10942d020380703000e2003111a540 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 912744928 1250 912743678 912743701
    0xf10080f1216050a051609020c0304170c18090c040c050a110f03040902030f070c2a0e0c03090d021b3d0225030609141e06010905010b12 60
    0x42d40081141c0a04206882801000110780e100303040c00c035a0500b0303030b503640d082d6a40032440b90190908198009000030007101d4000e01d40d8080000e8203005072400d0360000800a2418040100482d00010b8802c0500c5440ca404100030000500f0680b030410542038403e5000d00a0701400203807000b0451300c45003601c030aa00900214004125540c02c80b031b156603d8290383c101035002100d1648010881000048100e0320800700c2621681c0c02c031801d1181c100a0140c0d010f010541003808102c000c07404003001070002d4169a4080c4116440695039807a07041841025042c0304a00d0342c0c0c1400c550014440039103e41889046d6001d80703800722845803a0401151287c072a000342c82110341c0034081c00180702d0203546203100c092180c484540c0c0c00e4a1802c04000c20840c007041204d034903042034840c86482800022002d03803200010364003074070358181c000441e95011813a1103050780b2034180320380d4980c050b450816401c2008a0142040c0c0200744425030410341e51491601540544c1042020a00007050701d01040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 912746178 1250 912744928 912744967
    0x1b02010e030607020703020108060a27060f0314012a2a0c031401051006030c0c02030601090f1103040506160504030c0f18050f0c0c010b090f10080f12 66
    0x18065508500e403c1c00d01a4440c802c5110a901040581c00010f03a5454148915400c1d580c95044003860b019050f800701094030b80101d401c031001941d50501250800c9031b040090021032082102060002c160540e85003540d9411000408240340e422120300044074441c0c50b50283c0305a4500003003808a0610280d958046603414140700c0c4500100000510034443c01e542c0503a0300803d8410100083d20952501702d9808075a89480c807049003c0a124003031003900200fa41014504c1c1030b402c00300e01070300044c0c10f2250a90000901ca555441e450484034424006c801001c28811138860a610301a201c0580300d03000248020b0700456045004002c15000e50b081e50065030300b1402c0346c5030741c0e0f49a5000008140003406484051790190f20546d800804501901c0d02c40c0c0030901c84018591a0803000303400d10340214981042ca9500c030000302c1c410b62200c03100d85120320426228884a41440e14600800c40b04036049110715810002e0401c901100c0024091914850009501d964809150094011105 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 912747428 1250 912746178 912746207
    0xe06270a0506040f06090b0a05040e0630010501050612040f020103020f1c050604020304030c02150d0c090302040c020d0c030e0d06050405030a0927020c0c040606180e01061b0201 78
    0x100300810390340343d24010807090711000e80706e6111160b100c0070780070418080d00c80584009001008140142805070b03040e55009000074290b1b052a00c0c0114030814148459481004035022084468520700000d00400c1c1c01082e00f034490500c2c0c404040c000c0145942e001f8000791940c1e20007190a8116440b980c100d4194820001d030a54588089000680c002c840310284241510300382404914689407078800c1724040d0754035449204542d08075500380300002240c0460030150840074420011145194045c003a2400c080d44d403091070702801d40c41004211102c0e04410000c41d480500c8507034103290448003c0c0e0b00c04d6094244a440465618001000562480002802142424140020440300001602e81c0f04443d407036011a0710f440743d5540c001440d02d40c01c0c2040c60b08031000c0207a0031984d01c1c4d0050204030b500d10141d8101c100308101090a0301c01680c44a40041e182107107010f25068550851030140a603211000341c29403402c800106810030364a60030034001d440c52803c00840e8024442001c0051 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 912748678 1250 912747428 912747439
    0x30803100f0e0703050f0c040315090516080f070305250902180f0301270204090218040c06080601050708090324091002040819050f030d0c0e06270a05 66
    0x68031402d03010381d014070a95045021908000c0801c1c0d00c1c41840c001507201c1c4070340074030f46810141385845d88030310409005c0e1031a0f19543d88059035008034070107000d548014140d0f080c1170707ca01860b18a030546002c0ea01d03441c00d401da0300554000d00005502017110b1010858001541102c2c240510411100030381941c80040e0340b81c400a001180300304000110207201904072a0101c01c0d0f443c041c145400d80b443c00b0031101e28166046142c1403041c1d10f011b14040e13410300145c0000340503101c941c0440e0328254013800c0001b41407140401c200c20040541c0f022000b8000c240307031281490801ea400a806800f4299004050000205d1130754000d45041011705040240c40c80c1074025111003d80c03c070781589040c2e80c0016075000c1d8001c41b489540041c0215011540050020082050400741441d851041c203a4115000d0040c84a410780b0900100f01130046110042c0d4006805400b030030000c0c01100c82d0350702180c040c102c18010b4418103120580f2402c070035552290358428141080c000035040103041e0300705c01d5001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 912749928 1250 912748678 912748709
    0x1020c09160c0c0b1c0c0f0c02011b0b040b010306050709060c02010c06290a1a1206180703051006030b060901110102041505071b2105010209181e070903080310 70
    0x30a072001006102410b44001004100080e400c11104a0700c10031041c1c0c00302e000f00c1d03c2c02004ad4030808508a0301407450f1000f00700c071840b81d62900501030080c0e6040c0c2c2d01c00040b40040c003d220b000d1144a0b0807603a5410190342080c581080584959101400603040c1b200c540010004e00103290408910344040100c049603055140c1140d2452801403e88075000345058280410602c4220b42c16004606100c00707910f0811081c240c8182c2900c03030081586400c01900c02c100201c04809141050107401d0301c0c1c801051915006880e03c041c400c40e5800f110426013031404411003600c0d03e20442c1e519510070310340308882050b00e0604501a214503408240f0004150540051440d4001c02410a10b48250b000310030103244903807869100c48850043c1d103e0300d02d203001c2101d01141c200c04d22409080c482c80c0054108001480002e28a5580900541200001e1401c110050680303410104c64500114001c1f010f9044c024002404265640402000c031480000070840c00c26200b0040b6005100303c400142d0030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 912751178 1250 912749928 912749947
    0xc04020c0d0831060b0a080a17120a0b120610090e0d020601050d05070e040807020f1509040e0106120503120903031306020d0207060e0c01020c09160c0c0b 68
    0x2035420300960180000c81c1480451034902e00c0d142400805041c82001d07401001d041c500543c482540040d0840d0741d5540d410b098409501c4121018004200003000341880c8442c9041502e0000c0d030a00e0450451901002215041804001e400e070704150041c100244503140b031008500c51440002d40c0c0101880307003000700f080004100751384000361489440300b0301080b004240210b98030b0135030703030b01a6015070007100040c459406c0c03c1036000541801541202e684543e502d603000e1503600103807005da80b900c100082c502d01b58200384480d1060340006a82080c415a2030100001841c040c0c2040540300c0c54448042a00303840c403d400800203803502c1601103540c640c0d5031912694130741c81a100d509504d081c401c00a07a0410700442135034030801010760b211320086042c3c0c1e03844000f54410090310b0031003075080c092140031132464480e45c28000071041c0101951349414001900d403c214107501d82c0f140e04600101f0420710b04e0750b10848445c000b80e0601c080c01d40c4140c90310383d2070340341d054100301261800490384012 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 912752428 1250 912751178 912751183
    0x19031505040212101d0a02030601120c18050a0b09100902030a0b06122e0504022a0a0606090603020f090406060506210112120e0102071d10170604060903020c04020c 72
    0x2400c1030b00c00f400245d0303a4464210141c5032200300e030300039516400a04c01040b58204480b000d00b8258400c107401d0b450281c0b1102840c080c14103c20700250215641d40820242d82c0d480e1003008008141110041141d1030040000100110381d406007160741d50700400032998041030b0b5001500001e8004040030b071a127002001c40101e40c40300700d5582104e004040120340b01c044520084807818191244c032505881d08200522020354040c1c1d40d6400e03140c281e180308510f5118108290b40b01e650041001e042c880b101c40c107204042e108690040d0301140e240001c1000141d1f900074a151080c0c00a5641c1c40040da1a81003400c010809680b000b0341010001030b29600180802d1303240d01050382c00c010455207690f00c80801d142d040d420858020031107000390050f40c03000d42c042c43c2000c0c0421130510488400549495041e05108107015003039400c81821000c5c80750014104e41c58001070140842d0300b85049000c0303110982e40e540058000303405280e43d400c1c40014184240b203014160003015009540d42c0700008119036 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 912753678 1250 912752428 912752441
    0x60d1e060f050a0507080f0c1318050906090d1b05120301080f06070e0402031b0a11060a0e03190201020d0204121a0c1e0d0603060b1903150504021210 66
    0x4441c5000002011514644900c50243e88551b03219450356881c00084160f009016007801d40c100c0080c06100403070f102e05c10002000e040782c903059410401d4010540da044e500041c0c85c01805400031000c20111003400285c605000055150240c01c06044c56400301d02c103d03c2c5100038215015400407645a468240000d50481d0405811241c0388540944c1207a210441174a12a00081c001601c0c03942a14141c1c02035500b0000781c00074600304d0034405508400c544d108001800100d04400d0340d000540d0700501c142580051154010301800710b102070010f480344240c1c13113902c0c0a0000300c003002c460b0358802d5064070701c1b6401a1004544d9503440b001c2c09038000c2c24144017100c002c03c0381a94055001d100c0c0d00703000c1c0a1100d0a00c1682030101e22840f5680c11499400202c3c0780302414400d4101c9404103000c0c101c0103600440d000188030528406101c0303113a12048001260384c207003075420000114400300382c8803800038080c8002050344071032000441042001c1d001c003440d03202d0951140003060b0a6808003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 912754928 1250 912753678 912753701
    0x50a0e3a0c05150603030403030c020609030a0b100e04050c21030408030909060609011d0d0b04060b09070f0f0f110a03030606020d0c1e020f06040f1a03010806060d1e06 74
    0xa51003244003c8010044100840303a85403d0380040c441000040d0040d2026126680300400050030b000350a000320380380090500c01a5604515001848501050540d81c035015000030210004d8514223510b403a5940e00460800c1c5006411891082c10203004450b028050084013406481d42d5079134031014661703030f1b070401c01c2494481c442c0c40e03000c00c04a180c0035003110807541068541c40c1d003004c1d4100309074a4070b0708600360054104040c14542c40c00500f0560900d07119910540c00054040f03250814040e0701c580082c00c100074071a8031450201489d0300225903403008503882c98035110109a405080390f86006081002103d07100d03c007942402c146c0c058002405898483c2d003210120b82c1e0021080b42c03511420a03015105a400300f0226140d201400c0034506480d0000d0014500c100c401170200b200782c0c2c0705511503980d1003c0f0002c24404c0150350440125000740d000340030f03800c55060040c2282c8070400900750a10880c8211400d408011512080107008503403210100b0045886081c40e078054004007891 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 912756178 1250 912754928 912754933
    0x1e0306090606130b0f04091e080418060e0f0402360705040f0b03060604050d08031009020a200c151e07050a030f09091b03050a0e3a0c05 60
    0x416000c0f50354418104d1080f4002d00d001d2520b140142480024150500305442d4022400c5201d158480304c4400303002c1c40ca12903030030541c2c0c031032510106412004040304981819414180200704a9020780d5105801c800404103403509519184006113030700c8903c030a072060300c00c980a44c600070030320840c01407089581c00708201100c9540d4404200c600348254000d4040c401b00d0620140004840f44000e598000d034007500352441c1540ba900001c008032418041103c07100d40010411600c16031044000c1c005000c0c0320320070b506004180718042c2000c481998050311514015420920901e800c03c12420300c1c0307101070020918886280e420500681c40000c18071101044044109420340350182203643c0301c0e03008400351250300010f90b4100e5210700903115540400000010100d0340451500c1240c000003040c2400012112206001a06071070005221003100e0b071030320100f2802441c012407401814015011000342c03010842e100d032764030980390544540204800515081c00ca0340c020b81d5807803003103019070704 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 912757428 1250 912756178 912756199
    0x40f05010506300c06030a020705150c160302011b08060f0102070e0f06010203040f0608041e11240d050103050f03040303090e0c0c010504050610150e1e0306090606 72
    0x2e1080840781400000880083c210010a40700c06615804039a10140e00941e404203855078001622030301305407111030b074540d80050748004210302004070002151424078000100c3c0390841d285040ea0080b085000c0c00d1a52805980b41014400e5000030503015518102044012400301c0081003010304a0b1558001d01c01090100f90075030000440c0c1c0301320740c4100030581c41940d6481101c81e8080000c0c2c00c80e81540b00038003000c14000b080404050182c84242c0d01c0d0342d601d282c40e00f4812007101ca010110920302000d002500082500e030680f60b1003001084e6158100c1c0b444043e010000000d2a2105809078180465032148482c1c0ca50840c904880c000c400300c0c1c0c8410224580c0d0b540728402d6100003804203120701d80400c1100078402c5000e43c02000c2e004036509140c84900d666081d03e104403030494190f00306004010002c45060260300180031200d03280301a005440e20301a283c06101e103c500d21031341034003011050a00c8900e203005540e09019065405905114800305d80c0d603041522201d2141752100c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 912758678 1250 912757428 912757441
    0x130306050a1a0f0a0503060f09060c0f090118210b0f06061207020c0604171c0207030b0c0906070f11030c0a0e0a09060203070c060609111c020909040f050105 69
    0x4507004011512240c0c81c00ca00c849040181814002600f0f5030407500312000000d46507000d000030361055900302510743c5c02d49488400e603414150010024a103009090164441040f40c3e82c00b0344981c40d400b800c0500c14000d0401180c80c040b07902d6401070071300c10b4100e4404041d9906420040d250548034003100d641c01d4030342400311902c18400316009a0060310502000d1b10700d150300000940c002d03d4038016528400c0e40b000c0414403ea100c0d4025050560002010f0400030b07000b040140001d14984401072050110f07080003d4585105220240800400c100821041a1444100d9000703800081c601c0b980c80c140d6250450040c005d0b18400c0d40e4440d05a400303003055003008100320003e94801000e01c0400e80c200115007454480150100074629942c200d02c4000075039510096020b800c1c40d89907d001d040c400d20340b22082c0d50342034200c10b400782d0a12700031346550221142514030038074020038070510b0350003098140030080c040e4007045640700f03a04000348010b10907607407484120107004d11f0080c420303651071a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 912759928 1250 912758678 912758681
    0x313050a0f12020d06020d0c08040209070c0c180b0301020c16060507020a0303080901140106081008120d02092209140105100501050a030b0415080706080c0d02160503130306050a 78
    0x148901c0700d00302e070103042980040ca440c005a074a031034841c900040c109120090000112a00c15103040d0200d802e42c400c0c0000e5150120300c05a0004e680e19014289601d0f607079450500e86003605c04e83c1c0001c00003684c221079508094015450200002e802192142c40ca03001076540c5d800c1084902c000d01c4040300b80401c0c568440c0d000c0322500c03a00030b403002800a1943c1d0741110300360303802058032081d5540c409400303010b03117142c1008a000708001d59600d80311b0700308510800044010b50b80301c0265a8024540c039059841210191848004080ca0040e116042c10001c01c0046114444140e0300b0880d00300509202c5450b83c0c003048095000e02c0b1820801120804028200d941c240d50392020f503c04000100141d44c410002426100c1c00c0e0314000c245081258003080680708622805030070021030a07010b0200707060412040b00105414a00303007405040c0745130f01a80e10300c1500c100040f05a000250507118141701011101e0066202c02120342e5981440c00d04802c00d8214082115070508000c08100c0505c100e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 912761178 1250 912759928 912759959
    0xc0703110703170306060904091208070f080609070e0603090609070f061e09090207030e040c0503040308040b06030a1406150a080d0e0307030b131202070f0b0d0e0313050a 75
    0x455030f10300b00404407411400d0f0541008102c29070094081200da0250303200ca00031140b83c148102c01d4001040d107218400b41a510f0010000010410701080022106030700200706600140180d6201541d6101c96008175040200c403026680c21410001c1844642c8000052061003405014243c510301510b800708181c54003c82d10800000a203c207070452030031015800c03812000c0710705c0d040040409648420f101d040e230304040410307030100ba09482581a40c0c00c0c60301614174204090f140c55480c528096502626004010b4400340041d10f101c000202c4c0c40d201081181d00c200e8110140f241315940c81881c0c15a50030044840f01290380c01d5401c2c01404d0f08105426000f50346180000c1c01c42035092113012030700c40394013860440e454400c001002022601c4412441d003c0c00c4130010196101155040c105800e102110342c1d44210351103100c041041040140d203030400e03200c0345a03895a60700103240b071060207001c1140c2140c0b813601001880315201c2e150750040e02c0483c0e00503078108450030307600e40c034608502a1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 912762428 1250 912761178 912761183
    0x106060203190e22091515030f05241e011809050109020907020c19120303180c0b040911040509010620060a091502031303030e0c06030c0703110703 65
    0x50381490041e50203503901c164101001342840c400e8101186400310a140142e03d03400c507031a55160700030140b0020340f11a0f900140380e8803040c04094422541050503120610000d80f20300710740c7c610603041000c140840965041c00610090303c150350b005c111008210195048895480b45580d241c5407402d910f01518121400d00800b950130240703c01032140038110110040340c055503a903986100580c1c802030340070f00074032181e4001c04d215070407241408107114601d500307580040b0130701d48200030f030004001042c50810b0b4517240100381c082900418400220300203400400c859501c040209000e20108058000c803460f404090024084000e2583c2d400d00c214012180c100e92000d0040c81b10b40e0090a0340450030b11100301c0003501d482c824800c1400c0c6203050b1800d00f131007070300d91408005012906440907503003244090b04600d1070510303400ca0082c4140c60f41006007456240c2030824009003040c00311800031140a403c2c60f5803894850740300d4000d43c0c04110114081121000303000394042001503000c1c240d0740d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 912763678 1250 912762428 912762457
    0x90b0d0308150112090b10050a081218040518010b040c02063403202a0f031b0714151321020a140a0e0408071a04050106060203 56
    0x4840b8440c1c08812049000c500e03040c0304603419100d5514166109540c041405000d01c01018102240c075200411016400103208151101d800d029030000418000d642846904801e03980e041d042e84c5406100c0c030f0003500e242d480340c0f8013010042d8220740b0010461501003407070001c000043e44503080000311028560300e200141c0c4190001a002c44207801020340001d0900c551450303200e0100c4a0028102000a108000070b480b610144c4000790240292260321a0102409083c20a25035451000c0c5404a000e81a0011400107407031002c02d080c8401340c00741d044201500d03900c1c08050f11403c0302034040d554103001446018030015035028151070001e010760006098002c0c0300c2ca00c1030007a4070398000e00d5103180c025071450000642d9002030710090080591014202030904041d00410420904641c4107040364514000040704656039440030030180c40340790f01401090381f60760406425038003405a00800306009185c07080b606030741d4140220321032407148000b84a015150b2604980b01d00403003050101c0d00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 912764928 1250 912763678 912763681
    0x415030b19050136030b010503060403140d0b121e030301060801032910170c01050a0c0807020607030306050a15080705030711060403120b010903020303070b060d0f0c090b0d0308 78
    0x2c0d8801c50503c0000360303034007010621800168404c040c045500401c4a52903888010081003000307010202c15004000c210043c140e14a41910041c01814201c1c0a01c10001000980c030070601049500c80708200ac0080c11401003003000480b403030303624003142d100078000b01c0380c004400c031050038000216416a490f556030b1004a0b461961051148409044c031407840e050010030101d901401d083e00988036407842c80242d0360792441c00f00200842c1d0a645240080f40d00020040d2605981241c11101c44140e03616040798030322103e040044080c080c40d01c1c002e60181000880000389079064000c3c40c140d4200701ca1203845036a03140d01460b4002185808040071034210340003d107665015401442d4010036a0424070844884040c0090800508990440100d900e40742c0d01c801400b01d621030703940541401e0808500880c11a00001e0317890059150040c03103d0348100001700139031240788401d000240d002418200700b60a071f15254600c400c2600801c18621b10700500030003503107051142d200b901a01900d450195 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 912766178 1250 912764928 912764939
    0xc1803150203040f140307120203030402010e12030d06090603061103010f180e030a0309060f0603030e09070e0603090706140f03060907051c0902090730060b0415030b19 74
    0x42d4100600640d400d180181000c1c001c20702c08440910321140800c040c1d5980d10b914984090000f21601d000d404650081c070400c00142d821078848083d40404442400b00b584c0320101d00c80c5188510321004000608160780002d140b60150010000e8900c20402401030505c00c00c0303e01c03814002407054144462300385600700180d0640641421001d40c0124003c23403030320001c105061566111150100000750f07034180030401d0101e948510052020141c006001c0d05180d520000e2284c1450520307a0721945281003c91010383c0610962180f00300007415203a260f16000f03a840307440f5001441414089041a042c0c4e080d0030482d0b00480e80c01c1c1c182140c4160858980c401400054100204a1004e200c0c0030010b9000305189c1c44080003e19107080d10214180d403140c410710200f040007601c40d002744602d0420a00707000700c00210029042040c0c0256108641c400190a0040c00c1c0c0713540203074000c01000801007425200e0040d100b0040c07915480c00d001d025580024882c1540d00d0f0032914080306a49c0d0000d011 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 912767428 1250 912766178 912766181
    0x9110f10020d121104031a0603010213090b0a030c0803070c1a032d0c210702060606130e04060615020d050910030f02120403090b070812040f05010e010c180315 70
    0x500058040c40000c0d40c91024400c829154050f4201340c400900b40d8061fa54004500340c05264012000e82c020b40c00d1a584030b04801a0280c0b60040e500002d440b40e84c4160107803105002c100c002c6401022100e100d0760394480882e204d0380504015111110304c16070200d80d4644404003164208001135200e491981c4200441c025031310315021800d210701403800c00520000111581d0b50144a01800d241c3d510405002e900d003400c11850001c40b1100d03591002c11003950b03000704a081d40321109807015541c41c143c540a042d2890415040f49558803090b4003440f0078010190f211006403100b00e100440b42480c030200503a5200990700305d940000b0b40401c240c8070141000002e856046085040103d4500000c00310742050360000e01001b585440054108001e155005084800911100c0401850b0000381d40b0750003aa80300d05040d0001e0b02ca000070215007001455603c15031443d40000080000000b6500b51502801003098030800007600c05e00103100480c0044002d1048991000001000805046a240 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 912768678 1250 912767428 912767447
    0x6091b050c07152601181406010e03030f0d0227030a0311070e0a02190810050f010e100e09220b090f15010603061a0313051009110f10020d 61
    0x203040022801c101006135001d0140406801461401e4035000d604006a0003450b405190315031144a04000c45a085805003042c4c1c5174002c00e00307107826281c050140e004a495845088a4282c28038000074004000c0040c603030282200311030b00340703001c802c2c143c158000b0f42c1481c3d95840b046500d40c2002c4540000640258101b41d00c2c2d601d9441036541070f035980d601203e206101200c0758050b440e0001810740700c480d01148007a40300003990a1501640c01c16090b004100c1c80302d4003641c0e00496200300e03001a1a8010009882c003d600281111040941c01c5c000600101003c80e159010384036520101e080540d048007509401900d048604801003426101c2290009000d08040705500442c0c11680000c03400307004060b0720178818850360011b5490000010203c0d601e607444000a01452400d984024071071a046981040901c0c014030544081420407034204655841440c204628210380001000489542c4113052034048440040a106503000d104c1160300d401c1d6030500681000c0c1d0408915030041105c0c6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 912769784 1106 912768678 912768719
    0x90a0f150314150c0415020a02100e040606020c060a0c11062a0a020a06180905130308060409020d0b0c040b0d0b040b010c0b060d030c0606091b050c07 66
    0x260001e0185c1d00030350704807010f41d154103444070303108004640703a40d80c004140080502c101c200140c852503821041c1c034011424a440050098008502c840030340700040c140c9440c261126034104c51900c003041302190a02010701445140d629210080c00e00241c11802e0003524480c904200e0252080440021040b40e0144190b030005071150b601101c222055400e1081544116131014051001d440d0880e0960914020030003031070a04040c08030b01c16a00a84424810b03488407000c4c0400d454002d50065040030022400d00000344100014a0740580480f03003043c181902d030800c140c5254400102510301075103404d0746811510f400d01c18841c440c0700908240700d181505070784040c21071000400151045201450440c2032500a00708465441c0d8072070001c204c0b0300d403294000c40042040c0c8014920401c42030b58000340c440e000308225840300c45840000c010151504081219100d4201c80310b = true := by decide +kernel

theorem cover : BRFrame.Cov 912589928 912769784 := by
  have h0 := BRFrame.cov_init 912589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 912589928 ≤ n) (h2 : n < 912769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
