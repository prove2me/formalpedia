-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4128
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:39:10.319021+00:00
-- url     : https://prove2.me/submissions/bb66ec82-10c1-4d2e-b012-c57e11bb6e35

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 742266187 ≤ n < 742446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 742267437 1250 742266187 742266193
    0xc0315060e060d0b0a03120503011a0304110103050c070b0c030a0c0c051c0903050d030f1505010206010504090f02090109091b061e020f070605091801051309050c1503040209010503 79
    0x1c81c120109150b8030542114400300c036240c69121646840d160784e04002142c0185828003c180c1641004080e64002e1040b040a18800300c000544101d0a1088900540e40410030001c4070158030015005004020801c144e13048003800301d200401c81026a141c4500c1d1084106c55807032078007003a85c1d4205c45a4000b030200b01b10b805150800060340c000740d510502c040b0742c0682c0600e003c446108a81454003500010304d1805068003a1401c0c680640203184480c1c0120700078480c120510007802d8050303006208480c0141d0000340104410305041d44400035103030240c40741c40030b80c80542d00494407100d806c0c2c0c02480c04030b40d83e2168400788039605000c0f00c0d003a400c001d01005500e1503c01c0040002c483c0b801361b181620b02c00d484140c24240200540c0b45100709103019164000e40d604006041c1d50003a1480a0155520381848230720a600984203a05032030006080101c0021060955070007004040d8048900d8412808480a1030340d40a6214120f040106a2142d41e41790610503c040301c141030f40072a000b54 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 742268687 1250 742267437 742267457
    0x90901060302060d0b04060b18030601080f0d0305090a020409051b06030f071b0c060e03060a0c021507051303060c0e040603050c063708150108060f130c031506 70
    0x41d03a0b02003213411a595000f8003058040201c40080c00174411a48807804107a0005410400003010480c000d1507030fa412010343d1040c0eaa00c101e8152a400315000c0c0d400140c0000e003030710b80543c0c00b0b94811504005074000721110844298040f404680c40305400740c4a543c000d40c04a1842444010123501111098815500390306001091000d401e1000d4205824000102102c1c0da010200f207025100d002c3d08201411550b0b40d0710080544604000d04402d8000c1c029180020b0f880c3c00640542e4114404540c001c0c51030710920120203600035405003d0390300704401041415162881c0ca29200060342c061103000442e0101450064041d00000c0203150007581021400c0010850100b42803565000030b84840d80c0d41c0c0655541c0c001207520010819004c11001081248072104418801c0014100c0e610340c1c50032510340581c032045584401159030f00069100002640c90306040b0030038050901c0207085000344040e20450801030310b03541c0d101c0d8400a40d81e00340040400d0031040d44100100f800d420035140c50 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 742269937 1250 742268687 742268689
    0x200f0601060309030f0c3306170601060e0a09060e1503010c091a09031006061710140409050303070210060b0406120515090109050709061412040606150e090901060302 73
    0x3503c01d50344c0c2c0c5040c0711006c2c0c04001130050141c10304403441360381c0c1c1340d1680801c0c113001840303e0f44604201c182d00742441c080002c218405210100e00c40f90440382d00900641c0c1c0f812a003220004001c9204903080a6695000248482980211781c0508400784400c0300502c2d021082d055401c2d031000c4d08a00c26810107500661144e00400100255000ba50046060f8420b0700c410200611500c52806d8151250b500c1420b4410141d50010003560082daa508528118400164811080907100b4040e8400c640c0ca0070002844000084595030901510211384941e864842c14256042120311002507000312510800011841c804c08014007520f0b001d060a240c2000c0c0700030101c4030118000144599241c0110f00f003050518281c15840c000140f0366880356031281f1300350340900b800707651000114051040c08695107006601c61503108031030106581c140381d100c150445400d0b40140040e6a21603545030041509100c000100c10722200548980c080e44444000340411084010144803040e45012030503c01 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 742271187 1250 742269937 742269947
    0x20705010c09030209070e1f0503090d11030d0b01022409060105011e030b040608010903170112080a050a20031b0601050109050d0309050d0609050c101e200f060106030903 75
    0x71056203440600c11403041c010425907008c000d9078600c0354203000f07400111035920130f004501c40c240240649501809000090f910700c0040c41d0004107a8000b408555491003c661250010340c4051044500441152603071400c60941c0c10212001c1a80c5181004940d29003000310500415080c6014600600035101c40f034082d0151560741e40825132584041071499a4580161001c0d250b41d900802a2404030720b406400c01509203440300801031440c1c00003840d1001c99041500480d04200d01c10318007404840b0440d42541b14607281c00034072000040c04462000c0740c0d103e16001d01c0510b070007180e0ba100c2407018030802c2e910180041300c40d684140014861130b68808202e0080b0340084d070b07440304520028541600c10700903682044da04a00d000c0321035024071540380c01c044803043c098803d6654906c40c507428070250015852045d000300341e200b42d0740d03242d4001c07220222001441d94540a810381e4400081c01024071502d00c0004029808509041c000758800e019085c018802030804104840c00307036038007400c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 742272437 1250 742271187 742271191
    0x2071e1d160e060403020a14010912080412020616030839090d141e03310306020c010e0105090708070302090c090405041412040f0e1b0d020705010c09030209 69
    0x308110a0881c0c20307000c2e07100d00040d13402840e4000c00118900d9100c030a410051480d041c2c403140001c0900c2c1e80007400c00b440d50910103100d82c1081c2035625060800d0a003030001d000e0444202d8021000700030704e8201c889172040200711030b407184c1e5810303089040c0990341e0100146088000910a041e1251014028a203520f4204510004c682038940300c1c5041800540040049131020341600c5040301c000420a2001c5110000c040092800341c01010001070010f949010741c0300100400030021280b54889500210380e0b14003c0c4c00b0080c040112600c0b60358400036a0024183d01100c3e070345a0501e070100c40c4c001e00689601a001e8401001e040d4641a0026a1074000d444080d018020030000b26030040b00300c0003102ca0780c007800341c000d0186040c03a10b400c410008480260000c14040c641c480c0d090000d846044404803840700e80c80c071403d28100004241050341c003804040d103011904500b0302c558401130014045100106d070300140c881400b03052007400d654008591008002429400717000503900c6040b000d0b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 742273687 1250 742272437 742272481
    0x501090c1d06040903020f070e0912041503091506120b01080309060301031e02091e090d0504141305070c0c08010219050d11030a0917040b04060c0302071e1d 69
    0x413501d0305a50800381d04145c091907595580e4003544a000c52180042d02e8020300805004040f500002c041c2040031506001302c1c0203544020b81d03544c503041a0180300b03401034512140144a528440494260358000311401544120701e200c4980314003600b0b011550748443c0c010040c0c00c1c040e62502d103000c000103e8a101c1408010071a81d6503422a00c941e0041c3c50180480d40c0d07028025220034140b4480800c01980c1c099081d110104101c800540d090202103882549190242c981604050034400038407840129801c0480e001801f014003940035480c2401a180600c0080e00e502c2068961400c10450503005a0040b819581c010499017642080c601d0011a400c0303607500d030480c0c854038031100c1200902001c2743c5100c1411030105c140b041022056101c054024807554403550b00c145407280c52490b60082d0720411110007401d11081000500030b001c04495907110744192000b841e2100c40003043c00301c492210a0161071491004e011420003200c8072091801001c004070b000f0302d000d085550394200910301907 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 742274937 1250 742273687 742273691
    0x601030b0408040306020a03050603010f060e01060f030f050c04080d030c021011070209091b09160f1e09091413020613091a01020610120b1005030a0501090c1d0604 72
    0x9014444982d09450141d83e020b8019941c82c201c1000050251a00b540c2d0f1030710a510381000301003804e015215090403a80500441c54841e882c041e800d07195070303409240c007005140d120b407188000002c240c403565200d012010b42040d203271410944010b24004522444200f0b061030000f0900030781e600010406080402140042035004050300c1c04803160198100c000e4200301d407401801034010000c514180018800020011036a42010400a070b955042e903081ca52036401100c50f4914510980486c01c44c1205414042401808001140c01c200392810a140020b64800384c240005110f80c0281513013000041180406800c107140c0c0c450711181c210b10300a224401c00150740310300c003800d5600c06000303118003002000300c480d00c034945c0005d2404080c100b40c01405103c00040c91981d41d00d8400707050310034940c20360b5440140703030350f454440c1e42000d010400c01c041503090008080e40c00f000700d416918071800c00800d1405c1c50345010b480b001e28940100550480440b008085403800b0360800303074005012580 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 742276187 1250 742274937 742274941
    0x1e0d050322020d0308060405090a02010e0f010c020a060c0b070f051602030f12030901140106080708090c1203130f21151b140307120b13050723040302030601030b 71
    0x10711000038800c000003500305010b621032100b895000704001c2e10454041d05c0c18441596034091460700c8540d145402400b2030291102c2c0c40d501d060098620305400c1c0d040c103040550800540000c0e02441950b80b0a00000d040305004500308000000703459001071070340c100020030307222401c40501139001c4e102c840d610b0035480581d00015540c0400c0b41894030742d4100d0640c0c0c2d00c0140712202c1c5070554402c0751600559820901000c1440f07141d50f51047c121000ca40d1286216100c5a604407001079004d06558090f1203040da03039044555900c89004400d0000100840e0f450481d1010401041a40d910013a468840d5100c204400269526118107041c900b00c00b406621500d460091614081415100c140514080300c1001c4507024640c00001300c101b41d01c2d00100040c0306a0055003034070007250894001910503020410608058200840c00da000408102c00c00800750885030444008a50000001e008040c00c902c8908000240001000165003200c0c500b0f411a0080390f80e0b80d4041c40014607091f01480 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 742277437 1250 742276187 742276231
    0x5090d0210030f060b18090c040501120e0102040b07020103180209070c24021308010c121a0306091c020616211e1a13020307030f06081e0d0503 63
    0x48440e40d843c01c2c1c1d16003085a20386a006007030f903a400c001003010300442c41b20614a424500340c22003a20440900790154501800c10004542c5081c0b400b450002c05034171901300002260b420300281c00540700200312140c5569a40c000181610740034610020383c14001008131002d47c99210b42c09510480504141c0700520303181c80e09003080c1d419000c0d85540d10840c188015281c088036001407100c02035018881e1642511003800c0c40c201c0309241d00d040040b560541d44044055141e401640704008440b880001400c0c0c8007000c20706005080794011a0340d0040344541c801007904283c00b0f0341d07405062000300100c3c5000d4000c540c000f23008203044e5003400040303440a42100c282c406001c030209891f400500201624002d140e0381410400c2c01807103001e0070034010180d0200580116143c4180007440c2e80b90091041100800a44c405080f01003015107542c0d07a9800b451990241d50300a01a80000b41090f50440e0300002c0e50000320b03800888c1359003000c019000b5282d4400c040e2608002c4001c6c2035401c501c0c0b050 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 742278687 1250 742277437 742277441
    0x31b0e040b060d090b0403020f070e040f020a1508040c080f120c12120f01091b030f1d0601030209070806100e03070f03050d030c020d1b0c031e110105090d021003 71
    0x2c2802c5a844e0609055a080281e030000135030246201e60200c0d10910f908020b403507111450341c06800d20001d002000200805c1403409500103c5002400c0084115200c048420245035460010030105602d8010b0204100030311140c540180348041c09000040740a00c007264441d031510a11024160004c103000000f10000d0000c043c030409e403442ca01b40c4e51601042203036820314048030300c0e0409901608c00000c600500e8011648224024000b10102c0d40515000b580100b00c615140903007a0380d644401030f058201c91003412004846400249641e40c514410800e84400051010003005041d0043c00001c0d1117074540c0410710a510b05015400c41003503001320b4900501a440b9181984190100106108010851814002c000e03a801e1114400345c001c00c0c1c3e5600040d4000303100141c80c80c2c60301030310710348600c980c010380d07074414030468442c1b41e525201c602d00c09500030840b030980035070703440d40000304440c65042c0004100e007820014201401140002d520401940b8068001c14003008442d8600d80b180e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 742279937 1250 742278687 742278697
    0x3180c0f03030d050c0f032d07090b030702070807080f19080403020d050a0b070c050f0d050a1d03010f0203070807111509030c0109030e0a091401050f012001020901031b0e040b06 78
    0x411b4025071640b810704540403034000b91034a00c04a47c0d0542400402003c507082090b841258107031100801c09241c104942c01c1c03079100418100443c05100800308046030b0500012000b4403881000300301010880ba4400c0c140340e0501c040d1007050b2480c50368140003800307610590b011170f034045031896045191400c01074180031580341d004015003804007c0100c1c0c1c0d50040101407804c1c1c06582100c1c2c10046030f994044d171b50340c5d540740100f02082d010302c00b45c42c05a1040101e105a003c2d01d2041d204040c94440100307003910310a0360f0031202e803034020080101080d0b0010310158020540d1034903408245190502940b9001010304440081050000240000c2810030485a0614405008004100c0306003002803d030710601d10103a1150380e4a840001b1400800d008007428009044a80d004503480d01c010407208070306c0301103418103024640f107940c4c0c00c50000d07880d02015500c1490000d692403207000001011241c4110440030120701664005525560000702c400100b13805540000c4d442c15400c000079014091 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 742281187 1250 742279937 742279957
    0xa0501050c19150506041a04051f151707140307030902061b0606041a0f0a08060c040f05120c0d030504090e100c020601061d0103020403060203180c0f03030d050c 71
    0x440804002400381c2c0c00c1e528141940b0200640d1702e401080000740c0c1e0300d0201c1000d058080038002002803510340d21490b0488803003020501480d80525444010300e01a902c00e0113041085c01605180c0f58000900002100411042844a00d0605005844001c3d000300d604113400000c40060b00b018002d903c00a10141c009100300c0d2110f083c011186410449820100c52070701604011070040e0400b805182d025060b002c0354014a2000c62080c40485441c4d0015640d001e080780380001041401442054010034031004202d560b02d00708441d420701c45038294001402000d4421048810356004103120b81d555a00301c60f486911606402c3c11621400b81c1c1c1c06c6605014035001019510b4070001403540f6208111250501c40010965016601e0b03220901c02c01020524101031003050000807002d03801c410405060050401ea03c0b074584100700d81040b504620f0170081500111550307402001f010054801c100c81c1d4032a00c0070000082500c3c2d0140019150403580c80703402060440d81c400d001c2d01d00c8000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 742282437 1250 742281187 742281223
    0x81c0519111e0c0c061323150301090b0102120f09041e0e120702031f0f060f05130c02071a04080f061e01030816060905010e0c011202090a0501050c 65
    0x1402008141d1a61009030f046485100311451580340e82001000d4a0010b95250786c100440c0345400c140802c5540e07225002e981210445010790415550009184900100c0c0e41c8200d4496041851400c02c41d090740700c2c0c0343c0c19036000b65003220b200c0c28900d003107501107a651450030380c907000e42c3c502160150060308402036141d4012010481000150f6209900c420480012521a602c4540b100701d214441e00c42c010350560071880ca00100080b0b191254020200d00d41c1000903034440c0d418811040f11895000340b449118401c20400c00fa2031300801700000d920701110204031402c07507400301954034910381c81482008100d02c0b0509605100740c506035802042c00788243d911200c60100d80b151501c00c04c46001c1c01060b10703071914014001c01042d049046e40c4e40300c0c40007803819411385402c0404003010030f07088540700d4840c2d1810f000036800703000e00369078070000400a10f4601140b00014100e000e02220070515148144280c01440e178450440348100d070800e0801030b82d0343d200d102c1481c0c00e0402d030340030514284c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 742283687 1250 742282437 742282477
    0x150e0301090f0510240608090304030f0501020417060601022808030a0c1b03050d1d150103020f0105130e04020a0b040602160e04030e0f0f0d081c051911 67
    0x4a000b080e0004c2c142080349040040600d590701c500c020166103013070341c00400415481440b00c14020040c4580003214641200d05080d90380e503990485a403040c2048078503035008601040101c00114103400800981c8018061a1901c140000c0d6600089000c16100c80e0000c0c2e000c044413001c034034020308815001290b0070f94030314080c4003c2d0003422840c000e90300058685104001441407100c0b00c1400aa85031755482c1ca082103a0034428080c080407151140c940c1e10f030040302e2092607010000100000070051803898258590700400042244400b4524180102000070340942e01400b901101900c4a00c2c820300d449407582d001040007080702d50040f403800d4000142c00b145a90700003681d8503900802d07142104070262a075400416030141500c00502288081004078011314000314000b0303540c64041d013101c041c811008001240c03c0009034040c0c50003900022840908004804040303186000f6004c1403265041c46148084400e03403080820400c0b43e96441c001000030f08810441d2115100840a224a1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 742284937 1250 742283687 742283693
    0x1c03120908030618060d0305030912040e060906041509090f140601030c080d05090108150405010605040302011103030c030613091a0a14090d0e270f0c04150e0301090f 73
    0x15a0064440074030410150009082503101e11484c180300340e201030300c020b190720703020b503015501500054200c042600948007000d00e2a800100980001d1000c100f400480303090000601c03c00c4030004d841b02d4000e50610340aa50400640e03c2c1650031103a0408000400e4030080c21325088080300342c0f100130400d2a8203501d06441000c0052654141e81c001d03e00c84131003d9030340a006a58080e220340c844046913061110880c5503024411499001c884240ca07030444582c8000054220b4100760015004688040350034015943d01c07211501041f4040d400544ca5400e049034581414000180030394403c5981070702600c1119a6504203240b81039000410b80d082c01034400c101e2071580c1c0125490484a8a03100c20500018502000c1a000d081c2c0040a460300e02d45411040751402503502c84c0541000800700f20280c5585d0008400d08a2107200326003400f24148226840440380300130707044104144044c1300c14403071381c00d841c41141d00d04842820002d072080b205102284c007601214001404c1c001c0d0710076402d824 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 742286187 1250 742284937 742284953
    0x50d0b0a0902070302070803070b061005090a060809070816031712010b07060c0e21071d0406060803040b030703180803160905030a030507080c0708030310180b1c031209 74
    0x3c0107100790241e40783c80c0d488181c1d09950f4003039a2800b400c44007030203021a08505141e241c0359134110043c0341c03040c0f4203c680c4000c1600000c4940c0000e0001d281c4030108a1a07040030301100002d420035001a0111070a400b58601da044043d00024000001d480c01451122100000700c2d6034000483c03980307607500d60755440c801020783c000d18410744485041642c0c506c0c915100702503460084100a018148901119603004d180a1040321031822501c6040700106d242c0b050a903411408000085101041e0f00d031501d441801c1c0d42c0d03181e0082c12941c0c410b00041c13006030200d00c1a01d920140e11b180010b00c0d010400d100152b03000da0100301600f0780ca400000d01c0b1485201c2c1c01c00481c242c52948808104941d101c00b4196170b001c515034040d0001d407084c40f180d0000780c00301004180044600d001c0351000d03074840d0f03d40703811640103907a2014030030b60a4408002208403028280000c0400c228104141c1010030041841c1c03c540302e4a006018665400000403d4060044c1405000240008000503c0b8920340316107 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 742287437 1250 742286187 742286197
    0x30703020a080c010b19230306241201091a09060a11040b0301140a0f06021506040603021f02010f0b0f0613150c05070509061c0515070c032706050d0b0a0902 69
    0x50306587d0503041c48080c0d144e2a02000b00008050f000300340580c2d8006441c9074095209030003d0001207441e00c581641d07642d081c0c5401224030240000103020003945015803106070b00800c211000101071b03081000302c250100c2d001d41d10861540000c903441c440742001c00464400ca0f00700011001e0080004102120115143d001e140d409558040107240c0b1060351609100561080388011703400300d200d076090740c81351030480b5400c03000280011803690745903030009803901945101e4642100360102c1005055509010b1a00c06c106910b07404c0041555600101e40700145400d90320740600c1c80003030f84614904607245060024072000034149690b10441000501d40058032000307607810b11408202040300d1410040003402084014080d54088020b186142503001c0e03040d4080d12640513840c01110b10380030a0030210300c84c3c907240c0d6a0210158032442c005e05211000340300c40001405000d62440030001100c55039043e90b4442c1070054445119001c020085d00d0b00518854200c08030b1880002c2541098000d82 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 742288687 1250 742287437 742287449
    0x20a03060b0913080405011d0301020a020622020102120903160803030604110f0304021903050105040605060a0806040c2304020408070504180807080708040915090e030703020a080c010b19 82
    0x209500c443d02035a005000c041009010880700f084200104e60081c0102c180c83d400b0100c5c13200b0171410b41c01c002400c9030410003204d0b0250f008081003104410308242489001c4442a0914004d2402900001d40c0d40f089045454142100040c040b0025941042002040b4001c2c0a40c901965194a01c5c2a00c03074205442d83c90050307040070b594413600700301542a200c40c400c90100d943d0441d0385035000c03c00c00405401102c07500002da0103010001c61400c0c0100352007280604408100c600b8a2028402400280e9000c6003d070f810400900002075403000b0b131790b030840d544044ca0502102402c085c0c4c1e6070030540c50020b594858030014000a040301c0220301002110422101000344100c44844040c258000660051411f14204111000900c07040c000e407000602424506003821b80b01c44030714080b5201030740c828010500e210000c10240b040381c0140d150640b0124069401c115496034081d648495041008002510101340344920000c04d510120104000621302d01002d40f040304c030406804200c0c0181 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 742289937 1250 742288687 742288699
    0x50901110d0905100c24020702031c080124030507030209040903110f03041a0a020312010303050304170a1d0d0b010b0a03050a0603030e0103050601020a0803090c0a080105070c030f0507020a03060b 86
    0x4e954020f001c407401c01500055030345e9a185010f21000c80030000750202c0c51103690300340894070142e101001042c00075000c080684560100c0c200000d4040d4805030b00c1880203007a00c0c0c21900402c5420700320901c40c260070f8140411642c60b060f4087d4080d0042c05ca4141c0c1192038103901e141810742c040c030380031035001140d4144d6040030308002c800d5032640b103a80a40408038140c9020492480000300050407404403078410f581c10200180c024240260007a482640041c0e0040103010500c02d4810021103240f9402070241e1401100183c080c20a02c1510b0608020365200540030078180c0780c03140c440c80020340c8036030900704a6840341d41141150300000710307070000a8a418002400b0001d284110070580781c1540740c0801c0f500e08040114050080241f0440c114020200b2000000d1503200145006250382c1010340000180c100030300c0443d8880b503020000030b0381040d042c4140300d5045a04420340e103426150050b02c040b0600000e6400e4800e5880007504017244880001c180401c41e842039005200445030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 742291187 1250 742289937 742289959
    0x20d2d0611040503061605070b0f071206060e041d030c032115060a0509090721051911120403020705092a0d0b041113050916050901110d0905 62
    0x501e451030042c0d00451390140c0c02100800c0030030120021826880f070301440d1240c5481055500d60b10b40d03910646448541c2c005400511490540090828201e850340c040200b2219140100082120049212590196a64501440b019010318074003110303198115045a40d586680c61005940e58042c07180c504a4070f05404c01c0e10000c1040101c0180076071051441410080d0350740007000441d0740580c01407402d1000c10842c1905a88a04000610508050b200d1801d901c012682d0643c4107105c07204001c0000e403500c001c0045401940030075407511180300c60001183c1d00c03100111b40c100d106007a241c0388052501d82c1003100f0198005441c009980c415180c07064541c4840c6030b1444a0780c0c4096a10021034584d15005020840b081c02510000070308100204950303442c800428120707490075004200240c00003443c569001c0d15140940000c04040d40c3c0c9100358613003221000050761110002c00104100010080141d030f10a00840d00c0c0d0100440540c2c12050980c14040c11850385840303494014031002d02 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 742292437 1250 742291187 742291211
    0x1106132c06090c0f0d231605042103020c0d060209030d050a050702011107050a06120b0a030203030f07020604180203150f030c01030504080c06160e030d0507020d2d06 73
    0x281c0b1405408980d91080c2040040040e440c280d80100311078800c03040da6040c905044125440402d0720140750305010707008034200801c28a40b0407500c294240103020b401c2108010f41034180c55191000b100782d0410340c07007a14048c50100d040204040500d40d10000000824092050a40c002c1480c600200c040300d80c0400a410140c0301c1c5c0c01890580030120318140140c030f0140d406143c0c00c0520f404680c3c146d503481612440003c205103140c2d004100050307410030705a0070400d031900c500b5100f80e10858040d400c82e4030b5580001d41e03e10031040d40540c03500000c55450215258042550081c20b00101030300001d100000e003000080d081182d501c080428180c002e00700b80d0900c06070784114448042c01a01d4050f40880040d030107000c0180080301c0302041000700ea140003109020103401403104c0e400c100212006e08000414a4009030521842a00020000b54a1a400c10304a401c9598103540c0e000c54000039003040681c14610301000e2624007031a03005402d01c03171041d1480701946442aa820452414024 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 742293687 1250 742292437 742292449
    0xb090f03030f01080f1f0b030f01050703020c0105090a0b070c051603060c120605010801051c021c0308010f18110c10050105180606090d24050106090b071106132c06 72
    0x101b0308680642095494000360f8041d9000100040c1001d03085403000f608450081c1e0840302c04445001c0041d0307000c590990b603040c0a002e0540c10954144c000c0410716190f848031035030070101030101c1062040900314141040003d01071036000703d50500608120586e03a00303210f001361040c00150800078000760724400c0f034840d080c418901900c20695a10b50240c3c01c20f401c1c0001c40540400038086407002140000040c0e80364525500b14150f807030b020340c5a0701d64914024051610680107207a00031010030342032004141800c0c6580c8181102a0040f5108071782c1c000b002002c2c801c41201d0302c0705000c1c0d00c00051040c00c00b5002039040741d00607100c400d440c440d2a000b41c1e8500000355440c1ba0310403402c21546e00541f03040b40440d45003601941558140d0403220600d1802195a2034041202c036498100410100383c0014100005010100a4516041041d41d44100c800c0c050051684903080204014001120b08140e000c043c01509200c9141c5040440000005d40c04085022800c45001e400081e40b5042c42 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 742294937 1250 742293687 742293703
    0x415110601081c03021e0f0405271602060604090c210b13021f0516050a03031103190903180306140702150403080c09061209010e0f07030b090f03030f01080f 69
    0x6040c502e009041c601da420003903003d2187c1e14030442c002d00000c2019921010040e005080b020094100280c15084c3c0b50440c0b0340c000c040041c1016480390700b003411b0341c000c516035901000c100e400080e045023525000012080c540c0006181550042080c40c0c444125004545080c0c011980c00f8890354401414154000b50346c1700082d0403400701300144032070701c009040000100b8040d04000e401c201c00300c10101000c0592050950b4507038840d112003018140c040c03003a503c0b400b040741d9a00340785242081030803210b82c0f0b0000ca09065550781d8170810040c14802c207141c684104028007904c0440e0b80d00c1c1044000340a03143e00d120104c8045501090b036040c000151088610001d00260100350348644051380c144200a080382920107003005a1955595424010484900c0322404c460b0942410900349085a60fa0510b41d078540e4416110040a035200060180c2100d5110690380c0c8070b40c1d00c001c03145040544e404000c800c1c0f44000300a114101c4181d0941a06842c0c3c51400c40f8816103801e41e40c99550011 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 742296187 1250 742294937 742294957
    0x30c030c120109090240060e090a11010c02010c1e061505041503020d0b07110106030305250b01050f1203070f021212090d060b1003020406090e0c0415110601081c0302 73
    0x120172402c1c0c42940d885150701b903030801550b100080c4140d684281c080e15030f004881c84a880c0d00242400700401802c5846060182000e207071440188100b43d0000e0003800316071401605210712a04c500302e421400d80180c052443e0700043c18460068007090302d84003e050b601425100d103080c20f001c2d034210b00740d0321903c00481c2e400904160141c10640c03680c1c484900003601c036004011104690300d030b1842d4240980002103120355907140d901c0401c103035011804e406ca034941800b5403110142c0307900480c444102c07150669804a4014030500010400102a00f040c0e1307149520500000c81c0d40c4051080c40304200c10801d0081e83c0c4480d1800b014420b20743c843c0254203c16407076000c14083c00503e418101d00450b0070500c9202c00140610f000800120784c1c18001d40304100181e000107045c08081d07441b00313000c0c00400703031504041a94184603004c030046000b607020792603868a141030001119446501e6424400c4c0342102582c810756154484c5a444a010520f445400340c81a24110305241c4207108650003101 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 742297437 1250 742296187 742296259
    0x3030516050702130209030f030a080415021c0f3b030c0d0e22060906120305030606160807030c12050c0a1b15030506040b010206010605030c030c1201090902 69
    0x3204000341402500002c41b4550180700c1d000da1111800010170041c850b040c410346859030185402e280c45440c0b400307184803480c0b6860040c00b1070568941000007610101c11103440100d442152440598001c14802135421038403050603100285c84140b010802c05010415030b4070154044c04040034560760312507039104022a903c08511148100d00c10150075030302d01c1c00103241d41c400b511405800c4a96071682152807807110768403d8200060250f5211300001000080218410000c00703440241143c00000d1010340100030010f0071010461100318a80001e0b940511110b03110812400c1c0100b504da000c500c100e82c4106603107001c01059000b602954808925000108070070140f42d512103030b110700d40480f00da03004e0b404801c1c00301e01c5210b6010b01000c544081e9900140603e40241040b042e01c40c849910340c15504007200500580d68007008482d800510209070940c0d81e04d80c844002c14074811030011034454046180045010061508503048060007242c83c0990000c021202441920300242c0801d1050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 742298687 1250 742297437 742297459
    0x914040c080f07020709090b0717071706060403021504090501091503032105070216090c27050d0605040311120301050d0201021504051608070b0d0e03130303030516050702 75
    0x8220242c0303199000b0440c0c4103031868103a44003105400d58581c0c96007101c2c1c50715450104240c04d584081c801e4050001c941c1c1032078150610800180c010085403040e2086c00b03814000080c4151110740c00c0b5001550b0240000d00b681502404001b4203400900a16580509003000051420300e240281c1c410040509105004149142d0b03040d20420350f588a19801201d134240d610b0402417a921520744100c40c00e4010301607a14951403440c3c00750060760412840d03145000b03070551413030b0f034004140100741007454400c0300f00502141e81d030941c0072004da02c01075000780007800d01820084d00d0380196010300c1c46512004c0c03500c03410010742a04c4000030508418150b8080c00104040e2400070542150a401801502e5040e8504140094001401c490588c0c0c503921141380381c3c09004a244094008140002c040e000703030b6003810034240d6280300e04400d1a40550b1901440000280107108943c00505d034020788407078190743c0f4600500a003200f03da00f603000c000700c00f0302c022255004034103c5c0e10f490f50041c600d540d05 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 742299937 1250 742298687 742298701
    0x30911060c0c121c050c030301060f3b0f1503180601030b0103020312031003020d150507020106090f0b061204050f06010b13050103091a0c0c010c0914040c08 69
    0x80e4200c14010341071445281031010090b102d0fa4903110301c0107640300240c0010461040740f0f080180461081c4003c01c40104800030360a10040180c9040da1a10301e40054035242031b0004560304074040982d40b030707412402007044190403124002a2855514103070954149282e08040001d500c0d034440602e078000d4000c0300c3d0b01d1443d0a200009603403240ca100321055044400c42121031800b03c0c260011601c00c800c0034018001d6280c01c00c212141c03003502c00d945610310306d440c0d42078044034003c1d440001e0040215074a40410040a0000d8440101c2019001c010910f00b5100080c00f03841c0900c07030b09009525001e08254a8451405a0300540d003000c1c3c070307552a0000201e9001141c5500500546540c0a00484010716980600c1141e008156042d1070300d881d05e840a03800d04e0682400e81c00715040c10300d84502600028440450303444664059803100165650b501004005440359000c040d240d540781c030b1181d03486947c202000c4030649110314207a04144101009101c00c4032030207060303500425401000502a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 742301187 1250 742299937 742299949
    0x1a040501080106210b043e0313110303160609031112041205070e100e060f0a06080702013b010c08061c02181e0411121501090219030911 60
    0x103c0c040c00000e0b42d00c03a40c842080904003800400400c4042550748034403140d5802c5915030020302c10810261441c01c0141c40c000b89142c0e800270050207040c2800a1048960741401600c90501c07040c600d48102c01071703a1422400401c40210102e000c02c0c0301a41c03036411610b0028441c0304010030340e20700f01d15060404541c041e4001154104940b588105074011501c0c0000c1c10899008040f030b542540c1da100d0500c0e1003e1000240201854001e2000c401514030541d100c0b02400e040382c1c41824100d002d922099012805499803441400c00c44241e42002c80680540c1c1c0180003401a9550590049610a1200c5800d9a5000d0503000c009404440030a54500c0d0400101d04010140d82004080103140c0d400305815524540c1c8070750050f04018200680111010000790a0885070071110020745047d0380c820001e03020391040240299a004410b6401d600e0030400302604820050030382070742d5030b95140380304041e44c8100c2c0744014442d0000d1845c020f19029014500c8803590210020007041440c5040c814 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 742302437 1250 742301187 742301201
    0x150f112509090602040812070201050426120901021009021e0d0615180902130f020705010e0313061805090a0605090a0903081e0f0405071a04050108010621 68
    0x1103400061003000a0010452050160140c403070000540c03034600c1c001d41d5504101c41c4d0110760459042c10401440144c2e4401d04482c01d40b14040e4400b0790034450055030403800c50340107804814070b1040ca40c200e03003103100b4a0007901814000b40c6c02c89000c000b0741e5a4a40c195401581d000790005401040c5011410440c048180305c02400780c180c1d0780b1007466441c0e01c0c3c2924822048143d03c21900301e024080c10300e5a40420241d0803e01c2d20611046103680d0100e070102c408410900e50031540e031030040c05202c0740d540483d501290080020300c41d0200d56114262694403440e0300400c0c51540e03c03400a550b9005641d81940e000d0a6014400f4003850b10091021242d40204a04d8405650f10404101a9500c0740344c1c50240d00e0078030b000030f82d1104c9071501910240c80075100100034040c07803980810510b55140c0c80e9a00c12514103014650b42c0384c0303141c833510341051500815219110b640d007204043e801c1d00050b100300d81007640c400d28280d030307290015a0848200700c418000c104156203225041c86194000301 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 742303687 1250 742302437 742302493
    0x30f08070f26040305030d0506040f020a02010b19061403090a06050c0a020d23090301060305030f13050a0b0708090f12030406090b09030d110705060301150f11 70
    0x20349080d9607581e030140301500c00e8104031550741508520850341c00071910b02d007001d44080340d0385a281c0350440d15802d0707482c02070507810019181c482000600c3da80706d5400029000d29083c0056480303a1007074070080c0c003134010107d440380240f000c40702d40c05a81050090074811129170743c468a041c0c10503800000344c190300042000401c1e01c44c106401c400500301c0c3c07140e18070900341040200e84841c080b1400030b0429403610005c2c002c010f10342000000a134440640f44d031240312102000d40c0e031a400f07100443c0c0902015071010788a40000700300b000c20700341d00030000d00070122560450801d894480c400c020a1044a00600c0e24404040c1700f2100001c24010080044120042c44a180c0e941900f00141c017081030b4098841c0e464002040401500b508407421101034140c0074803040c10011248e001c00d9440d0030f8401c5c9a81003120f1100ea8100700f034400d001b110081d04d0087c020f02d5496031074000d03640c150007602c07110707400041c2481d8002111030b00c19a03040300001000409008000191007400b20458851b40c468 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 742304937 1250 742303687 742303703
    0x19060f11060a09021008220c030b090604051005150108040602090901170c030f0a03050a09090c021b0603040c0e072f0606032b1412040506060415030f 66
    0x4520300d600c003000502c1c45540c0004000c50480843c0c4180454080a09445400e010140741400000c248040c003072581c01c50884035029070a4814100768000c4601544041c103041007800c144034034510080b901a01c200d001e1070440d065030586013072020840303104a07001c0ac90301d40e600e03079081502e40c46006503076009405010051b00700040c840002c2d403034150070b0344040682881200600e002001c2406804000c02d000c401400c6540b00ca0b50a1135207841040e80014100710000941d0b41ca014010140c44020785a8030000300a4171a091401a6035020b05040351042020740c28241c0c0410704e071030800c03640b10b140d001910485d10303440c0109031809558003401c5c1070184000700002420354032000c800448080310300e0005420144080b00c03c00d0170300b800540258020b030001c615514290346244081450120710900703100c41c610307007400c0446503505200403650820500007995001c40c09030b581010301030b50050013940c50a4865808120446801842403880b041190b1010030106030f0001414000358018102 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 742306187 1250 742304937 742304957
    0x1091707183b030c03040306020d0213140117092e090c0311010329031f0518030412080904090606080a050f030f12090f0d0e01080619060f 61
    0x10206400810441900c015611154003006952503045460b81d44074808061450050031025950f00d80c4101c1c000135010741c4c0c00160b4011106000d50488910240003080d2412158444c8a00001ca01c46080518009103414107101040d2040c03d90090240200900410424122200040d42c0310102c809034144102d51444484194415000300ea05852040b0711030000f031400d519285c98a40079050481d410949001586581c3c540480e220341700206000e07003001c5464811100180c900740d840c3c0103080300c00d06182d04290031110325800039401740b031001419500800d202080207540740954800c00c100300b108180c04d5004174a008004042089000c1c00c00315040039a5100c02090b00d019038172104082d4000320544052000610424124440724030255103490740c205030544d014001d101481c0c0c0c00400300e80214642c1c0c80104080c4041080c50810744000a80050000e0b22080c1034035400e90200380040e00082061070031303c400280c0c0e01156600503000701e08106007103403080c0360080407105005031100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 742307437 1250 742306187 742306211
    0xf08010b0315040f140d020c040f0c05040e10051509090a050610050d06091a01081027021b071707150e010903051510091b030b01020c120c0109170718 66
    0x3040c0c02506d0100d80040100c02c1e5135070b00f40001c0740e050228035140c5a1038040400d05099020089604403450111032450649600303544c841000a0343d07204d50b41c0001d810f0b0b40011045070724000b404544408491010305541c03100741c914260f0f002115055402810344601ca031403280950054030003444402c50000321561548103080440b1440014132a040d4150b000b2150030b580d003c840a0323030001541407400c0341c07149400c8001c80c1d5a1048000c4040e0240541c142c11827410803036054501d42074207000300700d1a000c01c00f40441d84403803641c0038035420041d01d503001d10515900007840d00d0440d41d4110b0051440c0018031400c480d00303454030802d18100500300b0000000f10b0700401440c0c81d00d648000c80c410700b40c00c1294903940304130015846818000d0030101e800e14000c41203965243c03400c1c03007410007148840036280100e0821405103c01c690010b06a030501c01140303000a081e207100142030701d0b0008820307210303c210300b9a10310010320384001754070942c41403081001580c04400a4801c1440220340c20300380381c07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 742308687 1250 742307437 742307443
    0x60306041b0317030406060f08030d0902060903060a09061a0102100c021c08090c120d08060102010b061b1209031c02070504090525080d03180c0f08010b0315040f14 72
    0x3004000f10401c1c04400e0109010292040794014106119089010703481e12202a440740124443d000505640b08920400c0d03484103c1244e00d00c01000b0140d94040c600800d0b42001080c00b0401a5085071516455403a0a8001201120301380e60580082c00c66112032002d02e03000e4a8400318400443c02105907061300c021150352101a010070548840c03405192201d40d1a1a112000c41c8403440f68448003100b01030102e0100313400c00804200d01d4125003550791140143d024001c420340490f004100055203d400210022400301038016081c00d80c1c0000c0c00806014410f40903054540360304d80c01502c4e8004102044004240e0054100c0c0140c400d500d540748002021264003007170507601a0092020741250423600028004600300030420010900d086c80e0690750744151400180d828142c0c0d1701c0c04001054080c000000c81103030700108002c1070075110011001910410f00c20380203d58280fa40b03429040c0341c0814442c40010b04501410700b07940e03ca45132800115804141136460004560b4404500d24080c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 742309937 1250 742308687 742308713
    0x170c0a02091f060f1b110915150c16060e09041e120f020601180e03091e150319020304060e0109050c0a06021f0c180f0f0509060306041b03 61
    0x10340c0712071352903140c0396030003a04402880c002d6900303035a111507501000490041005250490584100c0d03030329981d581c2c1151802001120003503004240110b09005010140018885581080180c405840142c0860911003440e8011200460000e410380c0c451824940b40c0903511034020b003691035200c00010110400c0742000f04042d118682d041c07010070651500b00c030712100155004c0c4010034441d8035000558071810300040300c4e029155201c401d91840030404000f5240d55410007020100a00d0381e06011200e07200c41c51b6045070050030722600708070b1086e00f01c0c1d06603071150310b907080600690500d000c1a02d0003544014000c403442e0745d84480003004014240f00b510b8030140718000600390340390550100105013030701c0e522100866000c1903450308071600d121080c0100c41d07081400803030100d510030b4007565101490000c0c080c80509010b80041c0b151001d48115088808030f030000a0380031380350018041482011603102c0c3d010b43c0701c40c0106001880107501100701c0201749100e40c92094881d40e4200ba00811 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 742311187 1250 742309937 742309949
    0x30a12093002090603070b161103030f04030f0f140106080105060f0a211505010e070504030b0f1b070812061002070b07080f16170c0a02091f 62
    0x25210303003404001c000c50305101c408480d034101c5031001e81590464203401948548000e0241e9000404a8007545040210b4409050070b003000d2501c032030801c0c3d24501d4400c103a05d0281c412112032001c010701401c001c03003162400d41002c0102840c147c02c41c1c8561802010f120021034040c2d0340307d83c138a00407038440246001050000000405d000b480c01802a095500c041c202520640b400542d4100c10381d10a24810308031004241e12000043c005401001c440200240c0604141c0d46525a440f55001651020341a01e03440b101c006c41640b5101002c85030360089000003003e080c181e07404134000380c03011510786d42d0040d8a500301c4c14111130318440071030498001104c03c80340420089400d180c64408008070343d83c004000d986603800600004c40c000d40d40c0c0d49d1881004070f40c000c0001c5000a1000900c100c03150f0402d0308031041e60341c0a0041d00f410807484040d2050701d001d105d8804001061680d0812590610300084c020720640701030b0b4081210f00722018103032808003005286e40c1113070032880401c160000c0803 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 742312437 1250 742311187 742311197
    0x15050d230c091602060f0c0714010609110d0c0c082b11070203101b050c0309032d010e070603020a090906090617120703031d01061e0f080d0e030a12 65
    0x340c01070282c900032010f000840f0301b016803c108401400000c0541e911590402e1207411043c003844890740c010201c035001740304180c1c141403aa030040b007411401081400b58821040002c2075a883c001c40d020054090b0085c060b0303104100607607420504940120440184c612800044801c014031103013281c01140b2500c2032034070049049000d40c0340500c4070a503880300d180300a1101c94040e10400000720300c4100301c1400d010001c62001005d582c1041175405c0610003400700c44c0900c00124480c00062009441030b440c0d89890f0b80e0780d418096041c0074144040361018020141c90b414a44240d020b90000c0702c1d21010001c15076800121040c090007160f009080528002a055081561301020b00b082072071a000302d82d01034051034445414001c21070b10700c180c042c03030300141c0b4520036500800d90190420a0040e15030801c5000308010000424440144925070420309409075540a444280c801621880034583c1050302104003450150b03600303e9051100405868a12000c3c0d0340c0c00b0f18041e030210758140015 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 742313687 1250 742312437 742312471
    0x180a090501080d09081e0312010306050604060b0702090f072c011404030b0112060f050a0b0102010f0606210e06090c1c0b130c0503030c0115050d230c09 67
    0x141d000d10074014000303c02d141c81c0c0b020504040c6070b6603688035a1001c00858040c003000315042d103030060041d07400c220710a400c1e14029507582d0500501421081d134100d44a1841c4c948006440841c3e0022105c2c8298003501c02000d90ba140045003100c80b02c000c105000f40181304001ca41c0540e10000c0309084110401000c4890341c2490000601000c40154030b0780b9040b400f00070070300115425441030750441d1801002d07016606c1c410300c1d14a001c0c2140c0c5181440a90611051048800d819085810080d1080e402000324240b1224600242c407840e104140210780700403044400760000b5843c40101304110b0b00c0204201110f07485552816400300c9021086400c0017500000e41e140080c0c81004110090f0012030f000305144d2903c000070080504a080039205c8492110100008902c6900007000e00800740e9032141c400d182c81034080c0803055031020500c0c210348070104071490f150048140d01d54000039108028942d1070b4050300c2410740004010014442d032204810079070b0b103101c0098810a11410034a80d02 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 742314937 1250 742313687 742313699
    0x60d140106081f0b09042003010207151a09100e090f1507020d0302120c0702010c06060f031406280204091b020d0e032508010207061d0a050309010302180a090501 71
    0x407002d400c11310b403007120030f4024080032580c84003010034910300307070401d030b0a480c0300200010f402445041c0004058038150400b41c1c64558555022104400c86265170f41c02a10351407003046840c0c08101c58400c01442200404d215248080b291154400c00304001c5881009140c050315160000c2c10f0500d2600c81d09c80301c10052510303814011120301008904041d030820762038103800e4012880080c00d44140d4007002c1881015a8460110305c0d5446c0d030010400c2107600d44441621801c400300f8007085e607580c420394134401560040069001c0c4241040c14000e00c0b00c030f202d08584800c41255000c00b2041c140c0902010860030308503c5591003010310700c500040240124040039041203950500c00b4107214144d039030010961001b2030540c1c0911620281c002c07040003640c68405200020390004520b561000c9482000c00c00b8642c018095850100300703030798104026080659590b403034000300806a42081c48045580d501a801420000182d503d007001022480c0000c90401c03283c0764040c0803241d8270b44004001c9 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 742316187 1250 742314937 742314941
    0xf02010c1e03022506050403091e12050c2e090b0a082e050f120c0906010309050102130303171b0304060920040b03011a06070309230103060e060d140106081f 69
    0x6010480ad810407954020145550b20b8203030348601d050700c080041d150b0040050510490040401c010f1010007000e00c048205007808009100d5040501d442844505049000710070f00e90403038881580b050719020242e00304035034481380681108113001c000c80c81c1c0c090907462559592210150000c0d101080da1501040103c80e00d01c2c503500c00d00540c45030180c0d0058000100b842c11a00b603094601c0e440c40c0d150000104c005000d03400c000340c100e51010518007140c1d854900301c01304503030080d5601d00b0780d801070703514000e0000c00c1500c1e4000d0214800d61040120810b003030107107520501071900098000410748800c1d03466120103a0b002c014442e00d20303813480181f809100d14490905c0c10780081140170078840e800507000b4641a14103101d55400700f038603803c061190078010050b0a100100310540000d40400c00c40b4200c200c88494007007400d10001081c20701d601080c5c103100f10030042c418000040f107501c0360040f10410380b4170f2182030754840304041000340d0b0400100c01c1b802107405107200902e08407010703801 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 742317437 1250 742316187 742316189
    0x31e041502161a03040b0411030307060608070e091005100e070f1413141207060c0b0901180807031710080c0301060806060105130806070f02010c1e0302250605040309 73
    0x4180342400f648180c02c0070004054981c410740c01100c20390191500e0800055500c1c1c0300e107045a0611001514104202d40c54216004441c0c1400488800a1319903481440311a0300300ea680ca9658800a0018951041600100c2e0098090ba070320b03001c2c0070384076215441174541c21110076012a0581403403d00c4030f944002990344c54001c1d5034065080260342c0007980005e002504c60301d0704c1d1801101400d05e43d075803200c042c403c01448dc00110380c0f1590f6207400180c90401c50790803d0342c2c0c8030311050000e00c21800c1805003504007410f40d403c0c000c280e10703203030b8a007050394100c00d07001d40800c20a02d402c084d081091185441c00f80381d0b803410380111203150820103807810203520f11240c0280d041100401501d5400a01540c0020742402c1c07568031400c620740007202540c541e50081419210740030601c03030501d0300000d910800041a900034070414035240001e071905400e07608059510404c070a0010341c280d100380d004d0025519442031040081140c10074050304a00d80310030070380f060366031a414481010740110820f0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 742318687 1250 742317437 742317449
    0x6050907020a122a140d020705030a030804141519020f04060e03100614040b010314161205010f170d0c110a050d050d0917031e04150216 60
    0x30030000b0080d503d954040303400c05044000d000246812a5850900f1038100341841011924241142c0507820140d40206000170041078170700a01c0420003a1034404211442903460150060094140310f0364101c0755624007c1090794000c10341100074050000c14000000c948880d9030390301401d8180306d00042202030707814010304d00d2a44100304200c030918004068404131003060500c07400c2c010240000c1381c1030440041e1014180d81c5803c0303010403469941040f55041810a440c2045001518001901211032450141204c9070645000581c441c190b00e505210031800703854210b12007200c500315503041c2e61080c0c200550003076014405000190800441d000e01c10309910003130000458020b4050020f92030118090708460141c0c0350303070a05844a048200c0200350190601003080300d2401c0843d11480c01c0400300000864a240000b01c2244000000c00d0441e100c8024504c0d01117042c000d2803c2800803110401031241c140300016a101400e11400d0301c50700d40ea0082c0069030101c180e82480214a07801c44 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 742319937 1250 742318687 742318693
    0x1806090703120c05100b04060b0c060a05100303080a0903021c08040615060507030f05040e070503060a05062b0b030a0503220b04090504023601080303060303031b0705010c030605090702 81
    0x4034022402c005811702d0903031010040052110700400c00304000d094950811041071000181d446900000000e21603c2500d14050400290f2170786020603078000e0b00c610000d00010b140744049511865694401205580319004442c0b84680320003600c06800500c16256000c2800b0304100014440513015400f01c031025111b10303c00c802e0420802610901900710058100000d8541d0051114085d00890b00a0586241000750520b8800c0c001400c40c0e00441d0000e0040181c0d60000555084c41e2041d42c4040300d030b0b4413840310354020034080413038200380c82561090980e480d00c00000c0c6948040c00306000590003000910b5803107501e01241c09620050168014600c40040d104000124210381070350b041d0360241d44041026259400012420340421f0310741100070341c401c04202d281c490803d0307104002140c1d000d030000c5980e9840d0b030481c1e1a40000c442031034140c0c20401c0007450030380f03002d640e00e010024050100d600301000f03511500e00711420b107810800401c1e81e8280a01c9140b030300701a083d5001940d8401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 742321187 1250 742319937 742319957
    0x108060a0302010c08130f09020403031e0909090503090405010303020105061009050102070612140114040c020a08031501020703050d02030304061802180703092f060c0304050108180609070312 84
    0x90004c0001c10014101e07070710101c0c00c0d0400449440202000701b17441100c0f1a003850f1940f220400a61103403000b20086504400700e0b6580c40509912495444440d4551048092903c0f0b42200500082141100c40b40010041e802003030b503640c072038180039602a6000203910b00e007217410b1200039503909040506001d1038403001c005982c0c0c00141032090700c4c0c03645030444a04c819100d00e5009000051013034400c501000c0300104004a401d4401312000408450601100340758481c1682c4888075098064400001040000c15200e8002601e0f100c02c1d00610440340300e10f03529111380d03040100106502d001608000188010702140d0300a043c0c8200d4210140e22034100613900084032550340c0d650b90344c88150403000041e01c2e98041d40c000316002d13811030302113075040b1400c40045842c070705035208242c0c01c400001500d00c1241003950540745603190803c01180b503e8140700044d0f0310740c0c0c0000c01c908101f0904000e001c2e031a1000b0300010340074035101c3c4c0003042c1607401c41c605000b290500c482e400c02000141c0103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 742322437 1250 742321187 742321189
    0xc030304030507080c190201201e0304050607030801030b060603130b0718030f051203060109031e0c0e07021015050411090409051b03070308040504051e090c0108060a0302 75
    0x411260400d9050802d2607440c103180c503100c2410b00441440c030300c0d5401590403100c002118410041c400710f100740d03900483d01000c101c01050803640035403c1e8034140c0c000c0c9070058007601c80000242e0005200350459041664400000301240d003c410110001502c0c0c800405c20010501c91280d0007a03421581942149044619840c0d82c4807200c0b0702411108641001c103001600911810003d035400c0078004c3e04168813824881a0740d003100504803114801d08070549144041d84043d80d000e100c0c140e44280c003003071858491a881004502c04000c034a152807180800040c984c04807000107150f104c00301460381c600050041e040007601c0000c104054108091080b81c030f0340741180c05040c1e540851740002c0000813502c0031800c0d4007520120980142c40c000458040c010300040384071441412081d0110030400d50814951140114800101504020321041c0310500e440d0b0800f642c0007082e00f9420303101c039103c0e0080040044c010303110f803443c0d9049280c07070076401e580c80040503a02c5081501c42c1500c0728034541c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 742323687 1250 742322437 742322443
    0x4050106080f040c0b1b0601050d0305030415110d1b02070501050306040e070b0a1e0f050406030b01020f011401060909020309030f07230106330f0504120606030204060b0c 75
    0x4040b210048050000502004001480304000c0c14600103071a4640001d44041da5404a050344086540d1007108000225450040044135032281d00d9980c4034207540712035581c3c83c214500060f070282490745400c4001401003905001d420322079a03000d400316043c0030440c0c071443d03c04010710b040b50440d00001414005039070000b0450303070842d01c140da0010304601c141c05101d040210b207070020b0340d69190004005040940c82103861a501c96031080e0051083c1000d40103a40e4070315685181130204038184400c0203801c0c060741c00030050b000d041c0180c440c142c8034900710314215440c0c07241d0303810006005001407190031340c0b00c501200504080142186103041c950030f11940c9000e0001000c1a0420010343c0508014519482800c0c0310711544025503040b0100d051240a041d0750f0288130210700c1003540d6001c079803011300340441c40000840340b110710381101200e04443e4188806070210030f1080401c00040d0f040045a546d480150060200145a03420361040100f5501e40340e0055050180600129140c0c52001c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 742324937 1250 742323687 742323691
    0x1a0711071703070615030219080607052503021606140d02030705120f010e130b04060506030c19080f0106030506280204180c050a020a0b100f1203030b0405010608 71
    0x4840761505040d140c1040c698858000b0040449050010004040400c408100d003924804c950004051007004144040204ca520a450726544044003003814035010b000140a0b410035803204240101c054942840031850002c4200c1c0164001c400400c8041000d14900002c3c100924103d101d8540b100c002c6141070041d081091141a8008042040c442c0114101c82141c1c0b00c42000c202c951922092812144c0001d22913412043d070b10100180e10006d4100070310b80c1e81a4411152001511551218001041300404441d050300c50781c1e4204e0034980d214005a88500180944510410708040c1c1080c204005910400c030940e040c11400d0001410202c0d942d0303031103401501050042102c80f203c1c0c0091881869040f49820301c001400305103406440340c1d004a82890039001d22260308602c1084a4910036840b15600607081108404d0004220720188d5400c007818110707034030f0055190401142000d50700e601c6500005140d18840d420950076001d0011103807001c4800b00265803411501030888200 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 742326187 1250 742324937 742324949
    0x301050f100315060824011a030103060c14031006111c050c01150902220e2403060703090209100e0f0711010603050c120f0309040e10091a071107 64
    0x600050f0a207600d45a0301c5040180181170072640c19118500010009000d456500c1c0140072a11002081c699540c1500d00941c52144180070715680ca5070f11008014209a014441041a00280840005010400380d401100052113034942e50380780420180200c2c04600c0000c8903074001461a800a1031490354050340e031146824820394901c12040c0305401420440b050315224170442c0400706442c201640030f4000320b200242000c004242804200340700304c845100b6226040d101c100000d4443c61550a03c1111150300d003880c41c000140759000a08042d403c4030144006544c607050a1306505d440041c05c1d0704100780000e10202e26081100340c00c95944014100030400c40071901040450380b240c084503d420064070020801c0c25201d00d44161204c40b03860441d8400c985ca010315200103000403070f0200108240340010b52401d01c8807010701c4042e14003c404085140030b44200c0b05080415806540080342c41800d164281070b40009000f00b000724090070603001c01080041c1060080300000f186415100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 742327437 1250 742326187 742326203
    0x203092806051003050d02100b01020c0f2b1b060f0c060504020604091a0f01090b0d1104033e01020a02010c08040801151406090907050306030c060c0a020301050f1003 73
    0xd118840c043c1e01d000960b00050003449440c054103101540810084054400d020092007900da444004927501d400c0240c00c50751181c80844a5086440d0044501e90000d0303041d052120440c41c072143c0304600480f00b00f02a5041101440c0424a00c1035006801d4050700c1182010039450f44520340081140c0c00304040140015900e5000c40c00707558808007628010300b0300340c5090080c2c4c003a0303c0303000110050890065000d6610740c5180c04030ba601821004050f10449210306e4104a0a581d84001401000c4281d1100c4581080044007081c1e2010150b20355215510381007855058030000040d42c00c102190103841d41c0c130b40388802e41d0302d681d012500540280e024a0190010001824400124070071544492400c1d842d15540149806105000c50112001c00340c015200154003410300065115010b04158810134a000081d081da02800103582c120302c01804581c0110b00041c04207007240e100f0702101c2d0a03a800701400d00110f19090099503404540c840c2e40d4821070a01009882c10a486404000d2900c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 742328687 1250 742327437 742327441
    0x30d062c04030c0f060c02011401120312020f0a0215010603061208091504121a07020c0909070f09090209060409171b01060e0603060901061a181003020309280605 71
    0xd80310342403c0c02000c0c2c101810482843c403600d0110005d102c040d201002550038440c2c42903c1c1444118110b048810300091180c16070100d40e0111078032010502d0303020b1104e90920040d80c046400f100500716458840c1c00500008001c8800905941d105901540815060a00902178a0214081d09120a92003040b03241c0350301c1305600084103090f0440d1045102c03480030500141e030800d0807030b01c10313407060041e03d0601d070403070603081e0200305460115502000b50740f1040c80c0300c1c85402c213030a000c0c0e805141801510b425035126000201d5014144e48072a500da921030781020705502d419400542c11140c04c40c1d0420010344140c4d038001c060300040008488604000c98080c0700d55006a1140030030841a100030400580c0395403603080445030a0720030074042d109080008541c0b440510410b000ea842440c0070103004401603003200328a5110f400d038005140d80d200c44181c0710381c951700d80160325028030b40c6016803a0300d80040300a00d00011140c1030042c448040c400c0c1115071040c508224000c0350415804956a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 742329937 1250 742328687 742328693
    0xa03030c03231c0e061303170a1d0a0c090f02090406090c0f0206041e140d030501060e0a050904150b090103030309060501050a050117091608030d062c04 67
    0x202100345100c154401d40d8222a004002c04010107491065005002004000c10700e40c00c100d800000030f400640c0d008030f000c01c45440c50b801510840f548a4544040101c4664110068841c0305881c0001103549130420400c0da102084c0d0141c41c002c06e4034006240010485e101c400c0f42c0107482c8245040c403666900302483c0380c00c0e650111043c20300c000d03005001d0356940d0640310000304003520b00c490001d5089240a08500d20101e0401d002c1c0f600103050358002d50304040c0c02885010122011240c80a016a600c18455418400380551046584000900b03600d04280505014a0502001d01c16001c2440070301c402d03074400c81340c5a0480c0d009512030180b0280070319524000e0407404890b560141010000104040e0725410603841a44181c03004d111607662241407004500540c0581c4d03001c1200c1d03880040c0703a10100c08555031722495420866004142c3c1200c21044403519070841c0744141c1000800380302c60b00244c02010000c201d5181d44600396020140c2c1c1583c035030709485010584514581c01301c1c0c14 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 742331187 1250 742329937 742329947
    0x5091008100503010903180911030c09130c0e1011100e010e0304031b080d0f050c01150f03061d03042304020a032f0901121103090307030912020a03030c03 68
    0x1402d0042c000700b00b802140d007405042d01d81420240d0003034940005004ca5180028003802c5c0c9685071514440d800d58513681502c0c1101d400010b503040e0040e030040c6203050b20004038040d5070030180701616801850680c850521404070442400941413001c038030010f488600380043d8082c140c501c0380100103035043c51484201d01400c11a882c0790558440410040148801c900e010107502c21072408004825035116103054446c402d4200354004100c070120214001402000140402802e40d4000034660401c51950344440038680c0144010704888102031041000905c04d0940c50200c40e070802c00d41c8202605103980d03034030403402031900710742c42020340c112030f4119000e0515480c00c0080042d9100c0040d01c0c8010b00a003200111040003500c003412500d01c24090008211100c525110800d00c5c105080d00155114007504040b12070066458015030034201150028502074030307203540615074074607141c14000c003003243c1a0004802e0040074000c5a005035140b01847c41180d91505164007010307010f04050354 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 742332437 1250 742331187 742331189
    0x6060e061e010c2901050112090803060f0f0a0312030b060304120e060409290f031b1206010314060f090703060c0e06070302011b051305040509010605130b100509100810 74
    0x2801441c0c0682e4480400051a84d5034140d4030280e8940b10070b00c07032002a4109603107601a015150003c1000850350701c1c1481d900c00c0011240160848500d1042c040c003044000040340d00541c0c084034104a01a0402d030315004a510b80501150800c4c02d43c102519200300e0345240c6801c1d003082c4468000d9182caa074590b502030340c004055054040004586686010070720b070200040301e40c1d0f80e5806582580c05454104e54601c2c2407030b0f0140c0104140d0305070084658801d0740f5440303060303400380b078541d601e14020404211031806140300315520030481070303804482840c0000113040d2400a90318101081241080000d503201100d41140340840c507079110103415110b001c2048411500a40005010401d164054004681d40440f208240b50706205086040392103000360084240c4150404a00308064030f0315420103600104200b0000403480d036074030000355080380d680c0d00c42498541c468014503007030300d4000482e605c0c06d04170f414981d2810107035200040207041c082d0045401c0c0840e070000301e02c001c40c90450b014 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 742333687 1250 742332437 742332473
    0x60b2803090f0f030e01090b09010e01030209030f010f0b1008160302090a140a2301050d180c030b0c04140111150c2a1c02030906040306060e061e010c 66
    0x80c1042d005030428060103c1d070f1010680115203060800b00f032551040000e80f040310215007500d130400a100340112094114580440d04040c0c0902084540381c1e414000100340000000002070324119601d400400ea50702c40500354400c408800743c1003040c0303410596880d802031080a40b09016051400250001d0003089169a0032011100000c83c0e10602d208441d81c10003030480e41091010303505c00c680000c4040d0100d07411100048030908180650043c4003034003e00359114004100c3c100b102d1003440500d1110380c002d40b07000d03190500c10028003c6145d1200d070000407400701d1924050134044200311031807030050618100603644200c03401461040c00f40d00580c0c84500c4440e0343c282002c0140300b4058000c0d0720301101d07800e1280d5101907405101c1c076180310000350540c00341603101e646030f5403002410b04080c0345038250702040000030240d6480c24018009948505000500320342400a0303e492964001c003200c1c000c00c00450b00240c881384c0c019800d03001031800d281c58495190070745803016550007100020 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 742334937 1250 742333687 742333703
    0x60d140403050408060a0522061d06060a0e040302070302150705060f0a060602070f060305220f0308010909020d0206090a050d08070303050c03040c03061812020709060b280309 77
    0x31000301035201c0d0082003201e4001003103400b0303920740e4070190003280d00942da10083c66440d491a80103000891080c09182402288000783c1e04c211003a030b01800c42c0e012441c2c0040351304801c00b0000c5615091040303001608040f80081c281e89042e0b40d02075070b01c141d82d01010703221380300580300419488000800c68614607880410b880450420704200703040b2107015215201064200180490150b200054602c01c50340d00f04585d07a030007403511034141c0042101030003e030380ca1000d11544d070344090342d045540d0180c54443c082c980346503030081c100140ba501060b0040440319050500c0100940d0324100308800c4550101c0750543e8400c603800c0010030450035035101c960003130717001003518061000140240060500903101403007182d9850500300d2300c603c022a0018034501001c1020b1001c0354096001030340780641c038114821034544035215a2000c4802d220300f400182d00060042c84a0040c50050100a100888516050031308800b20070340340344a150b861003041c0004030701d0850400d221382c2014040719002030315 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 742336187 1250 742334937 742334941
    0x1f0f0912020c010e0301020f040b22060908010501090c0f030b0a0533030103030503040b130209010b0d060501140d020d020d0908071101020c01050304060c0909020a021b041109060d14 80
    0x10b9110000c02c1c00d86404100d002c0c070b4504060030180202c480680b40c0b0520245010305005103030300c0607084181c0031581415990000b11b6503442044010002e8890364481804071743c81e0404660075144160403044800b414054021281034000da4006013800042c28086419681a80420800001030f44215444902200c890900f956000c408403210451950000c04001982c84000e58138803082c4001000904c0401c001804039000646150300a4107110004554160301d800240710701c039080e00608642d0300002082440c07001c0f2403060304001d100a0a01130340543c00001460385c14000c8944903c00746400080382d074402f04407a411140742c446010810020001541041e02864000e11001c49400c14980c0e01c82394a9800011000c4111405a4a1510310340e655a40c0601070203400090600740040b80001192a8510f4006090040e000c2c0d8014042d00e400e00500c05209074100c1c0d400b600a42c9810204110401c0380811a174407441c051380e000b076035103c41d81240801402e50004031f400001c0c1d0002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 742337437 1250 742336187 742336223
    0x1611070902130801060609030209040c08010f020901020d0e06090d05010b03012a1803061d06040b071403090a0b0c0f0f090901060503131211010203010f060807021f0f09 74
    0x1000d00003042c1d080d15400d040d951039020b1942202c541d4015940492820b460400052a04401c1141d00501c40d210004410340e0f20400703a400d5401c075280c1e00d4079035900400c0324021964108541c6416007560319011889182c0940490000e105003100035001e00d5902401005100702504410241c0030060b008010003440e45250141068009140308954010b9070340c0300914611035152410710010540d400c0a0385c0e880c507a910340003003402840c42440c284d2901488254441c042c88841c0c81030327025100d4407403103240a003c0100700c2004c100700e4104225017401030111840e8000b07030b0440c00a511940501c01038070b400740c86072107600038070840c1320100600051040440c21039001400c5030540c180c0d90010b20340d8030b841c401e031006e0008507442d03540b205112008101146415070f0210a04519083c03d24a050383e404160f403d981c801d8029500010b100c94003000750313541c0120b00c6948015548081d1800710180361043c1318007855239044081060315000f50242c2d203800c03944204007030b69002d04c02c03403035598400c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 742338687 1250 742337437 742337441
    0x40b0a0e1608061e011a0901030f090c0e0c04080604080a020c030a140c0a03150c0504050d061e0b062205040c0f08180d12060806010f1509030b16110709 67
    0x55014045a40d04c84992402d1034505a1150580f0784080c003180c02254140441c01907600301d00f088904144e15096101c100c844203103e41c03105180600c000c0503003d0b00f8200006044940039100b07100e0100c0030842040351240c003103015034005520600540c2c1e2050940c03412860403c006c981c5130741c14050307020300f1001c10206003c001c0481844505441c00d00540400708417164034140700192901160060042c01404540d101030440c040b941005410580c40740f010441300803c945003140c250b0b540380321031a008081090b8000000c03d08440900c031b00c40c0000c0c0829418001d44441c0044103070030018802451041e001000003401002c1e000700b0000e174404074020b2100e10040300150100380c08901088458040242c0e800c0e02507442c5005112179a12400304441441d80c4801c0748040075503032000401e6502040c04018000d0501c2000d02d01c41c24189007031040c04d084c1c6d402d144000e01110340c00400010303c000704c0c0d1980c06201d080342e07030b21102ca83d40c0042c1c5504040340301c140341c1030103484004603142c1c4481d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 742339937 1250 742338687 742338691
    0x304050111160b070f090b0d110c0c040e0303011a07030c020d0b040308100b0f0a021f051b16032a0308010f0611031801090308030702060103140105040b0a0e160806 72
    0x2402100281342c8030541c0955010120400f000e0004000c0e0000707022920410b17004000d1800c1d100c0c000070307a0020705e11465540342c114045103003858000640d104483d262500500b203038088110061403855240c0400d04403603080070b81c002060b950300803a901d41858082e200c9503010540240104a0403207441c545424800340844080703020078483c90100e010408020640c0042d030f06030707007403480c900104e005895000741c101281400440c030960b00345074150442e0307940301c0840c080c442c5404a843e05141250030307410b8120803500c0c05250414044502004082c0012106103034050600440c2500600c1550000600c808201c000b01c8500c014141300700340d400403040d81221341e100303011014280c480d8011240341090080e6076031190b00078022a05c0c1d05030013a0700c405160605051980070f840d540c1c0e17620202504200c132810056080b2000420910020009648101805400070045480c003680c5560f59040050b010518299036120010034800e000c01401050750150b0401c608401e40d52800c0070b5441c40c0c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 742341187 1250 742339937 742339943
    0x609010f1814090f16110a02120307231504030e04090507050907031802040e070305060405102711060f120402040b030c10081e0f0402010201060503030a0c08030405011116 75
    0x100100085115208400283c06505403000c829058068814129110042000da001040c0980036603540142d440d16a89e41d08000408040c544603402d074100900c10840c400080c01c0b07820300040300c81386203030303004a85885d0319402c1c41c080810540b2030b41400c8600000815a00743c100349003429101c1441000500307101101c0301143c0505265503400e030201c00740c5244500b102c00080014052800528141e0088617041a440b01155886a920f844043c6010300a440603242034000d40791060f107602041c002e0703644000b4030348040d0000200f024882c94410301c03185005886000c05d0604604150348140440780c144440107806600c452081d40b03400221002664100e00c15441d052007a1014240841c0e100e400313881c010030103980703000c0c4240151940007005200308086040c084480307004c440b080b007c550060702c0e11007051110303140c148006400c484898004030311961051000011503a404049080c881d0780c850162916a200d516003a0701501c00710a4042548102042414480c1c100450070100580 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 742342437 1250 742341187 742341199
    0x9050c0912011e020903100203040804090b06040e0115030608010f0608011a030c0108070c0206040303030c0206090a05060c0d06090204030b1f05100302070f051e01060905060609010f1814 82
    0x204040000742201c00810700700c40c0303c080006440e4031060460380a80400c42001d01540c0d8000e00240c0100100e034001c40301110052404501401281c0c0148a841d09664003035601602d000c0c1000c004000c0c01e0740510030700c2004821040b690000342c2c03003900071074000c1140800030b02c0030a803540c600101400740d601458039198a0403204003e600400301142e545c0c0c1c034024000e404200c1b0350000454041c0c070001c10020070701c240c0d88070a000586881004000942c001c0c3d40000d038a01281000070304256000e0600c4005a00000d01e290125030049000c58000b01c8500c0c8041d603600702519828003030130f800e6000700f04851010038008240100c1a560a20501e03c0207513600d20176002d285080c4000d050341c06030b150040d00402d20603201e1750195004004190041452084004140c1d0310390b8545803080856000c050b80c0c1c451000c20001c000d0190074050034691a0500c010300d4101e011500ca8003070320f41c00c18100a940602c1d2149603010b0150039181c070010850042231240ca1700800081c0d00c480d402c1c5140104 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 742343687 1250 742342437 742342459
    0x200a0320010203030c090d1b080a0303050108241b03010e07091a040603020a0909020705210a020a080901090f081c0804020d110a121406090706020607030f0609050c09 73
    0x58400700850740309117140801141081c024405000800c0d03042c40c0c1c125483d1056184524a81030120300381c60040590300018900b0407080d150040c01d50341c040c0d1103006680e2009440b29590002070b003034072408691400d401042d82d61500641c41d0342c4000014402c098200010011800c031680c0c4480503c00c20040d211110b5440c0c3c1c0b034114503844804d58854242d041400c0c0070078401a44290001d0041d0540361034002c00341922100404d00300c1e4054003080710264040d07840001010100c1310003005100000302540d0404019000294807103070f20f5200240445000901e424041e80110742450103010001004c0b0f1078143c545070190f985610300c019250318440c1006012840c1c40c40340a0300c2c0d00c03c1e13a01400c611020585980d68a0815000c080b2056100070740100120348200211f66020b1503038000d0300c1c0c440b0440355200002e41040c00191a844240d0088a0300703218a6800081954000031180b8000607079642e07803285030f00180110380100c118103060205102e03510720064094609080c0c2202d0302d02c004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 742344937 1250 742343687 742343689
    0x150e0111070c0e011403061602010f1107020109050406080c1302130e1504060311090601090b0a031e1407050c150c09010f020105011a0c0a02030303040308010e09060601020a200a0320 80
    0xc2c10085e01460307419480b040006610704c1102c50b5412002401e800049030001065100d1416195062503440c15248046440400d560b030204015000785010342d0204403490030101c440341c41d103100000c0a4015202010385d224000490f604803500e60500d200b000b66850344440394500800e4040d54030180c901d4008102508070b10b894440c4000322540501c1414143c1c0c03891040c03200090004001c0e50500003481c1c00002c010030304034020000c030040c50741c002481d880c0f0914504440381c8203d8100e51000e190030080091440c2101d000e68000800d4105030b5110030851407020300c3d00318001141c03e6007110340d4050164100301c03c4050450300400344c80720300a05804520480c00c8480074070a10a4406001c0d1510ba6103809440042c001200c0d14000e88070a48460b8000ca403550f442030360100c0000d242200100001e2503070500307a42d0030440034401b0b011035090000000750b0b074100a45c0c01500c0701944640c00700f81071101c000d07442c0044c1d902800080045035a414171200b80501c80001e503da16440880042607 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 742346187 1250 742344937 742344959
    0x206010b09011e021e0106170c030a0b13080c06010e0703051003031b14030c010e0d0807082212080901090b0c03040c08061807060507150e0111070c0e01 67
    0x100c0c10306954400310f03680340c008860480104a07003080306500442090754065100d000c0070000b686002e40c00801c40c1403030724100d023100b10b29010358601c0c260040f030806125540d01040e65121a03070808003000e0030741c45442d45103081c801c80800060503600c0000358a040c0d004007045681c100d41c1d41118041c420350f6280001da054407070845441544d40300460081c40024020b1202a021000d61074030740401458035564402800c5020350031f4541d660000c640ca0701c110702c00b4080d1014a40e907040141a980c00780240c0031380340d0000608840c080c41814000039413120342040c60f0a50000004d02100c41c1180141021100782e00c840c1220400100100c000840c116014040c00500740e9010152262540d01c650746180241c02c00f40049400581c3c2c2007000071500410480340380180040c41285e070100e010003c1003441c180d00d40d0b0000c014030105010034400715035810815444400200e501107495580c006042e401009140c1d82e013600c9004c0480c16605001072240c0d0792091302c0c560b000d800c1803a40c9640754001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 742347437 1250 742346187 742346197
    0x50a0309060503090a0204090503090307030605090c04110a080a0b130b011403130213141609140d0f02010207053a0b1f0315020c10051b1c060b0a0206010b 68
    0x82140d01031704002e001401c00798049490180039105403810242d94100207801c0404950043d01e446485005100740321100f440f904a602c03904440401c03021203d980301d0810381c003550384450180405007000551181c0701c1d41222409a80042401e40701048011019005140800c011800207403c41d804024000c0c001089078010003810001c1e80c5203907400d82c01c010840e45107024182e14642c490340441410782c1c00c8480e4a001e10b081c1503180602050355131000b050040ca0b42d100003000b19002c100c1d0101a1951035240381115001202891100220300041c2e103040300c0d9074402500002141042e003108081c1d00c0350916422190b0484030301d8801250814050100214000750100c41d8041c003184558070710584540312030001c42c030300e494100d40d43c9c0c481880e000d09a151007004160001900c0ca0101e8050105c07402100840b2000c00103400c020038840742040f014501d12444504c001046084541200e00c80b20b25005062403d010194541003112242d421441c2c1d1080503100c1d81001080480054059030303 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 742348687 1250 742347437 742347451
    0x151002060606130e070e1903020904020603040503130902040906050102060906060609030a1e0b01080a0f290c040e130f1104091b0e160504140301020412050a0309060503 74
    0x8186511001c040000300c0e840404060308011001d07100146450780090440c2c0700300801d440b861107900c4a501404161020158069103000001d6400c3c00144e84000403640c0240e010789116450b503559183ca240b80d4403030102400030441d0b42c1c60740007411078800d4004100361402d810044c00410f03030b10350040e41d640c001a90540c8058008500203500c2c1e041c10030240040b140c1c010704071054040310f5140d0a405503c0c030305007120740d1014144100144a4030030402070041a1050003060901c0c81515503c0c0b0038144400000c2c06c2ca03407407140b11480750341a196003c1022001ca00800c40c0c3e4200441505100d61003485810100f11507000000d50100117a9004113081d5000b2205460301046541c560700b007807220660071544a81d030b8070781a801045410795051850025000c1e00d0b4807460401c40d10220842004040b60078040b80e8a40c0d142219905c01e044d40c00f00e88040700c031040801103040000707019006980040c400c03101400141c0c010711500140c03012402e4040e45450b03280c3c5403101070403141d07031204807408 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 742349937 1250 742348687 742348693
    0x10b120d05091905100305220f1104060915230303040902090112050c070c090501060f11070b0a1e050304030f0c0c0f15030b0931020a0b03151002 64
    0x182118200140c00000c3e81040410181e405a12440010000d10f0015100030000740c2d9801003240c120705841c000d4001da80c0307201a902840100c1c0d6038000d10451741d040010030490780100c00d12140d4461703070843c0700a03050100d001c4c05050b503031030301101e0101080e103d5000c1111040c610325120500c481140501c40d88013402844c43e2034148420000070354400503006041001c03c2101001465462007154019015558035076500d892500b0080042f4410741c004001d001d26140042199541141c04841080880d0400500042004aa80d8107100302c5070f10281c2d900100040ca0b010180e407040302c1c646a002c42d0072400785214150392048a43d4002114014082610801644041406040a0008030b8458202082c40d10f03150300b5059540b40d503e61160301c00042e007554800301d094050150074040d10056803001920b180a0b0311480311030340b2580f89903090840d207480030480c0f40c0c14405488801600a000055802c1d650b040180d0319a1040f030380595a02d804070500500c0745801c0c140f00d291102e481d801 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 742351187 1250 742349937 742349947
    0x30b060a02070e091218130b0a060e130c080f07081e04060b0a0810060b07110d030203070503070305030711060609041106040f12020f091b0f0c0609010b120d05 70
    0x1907100f40f110140941489101d03103041450342e55445001070680340c0d14842803410480303040f41401600fa4a418464051703070f0628980300460f4845d094014200d8480d07180104184034001c0209481e004000100c0160310306255052a0701c581002440d4000c1030071301d01c000815520600120380400064820707510000c4501d0092547c2c40d110700300250054040d00c00040d0300111140061108030160f03000e403000750420007002c42908954072400004204144406141c103885075134000e405e042540300f1500c00d8513955110400d0500c00c1040e20b40840c1d1100c05c482e42d420503810b001d00341e60811981040040c009404a951140e40030482900a0304040c10319443c40d1604c0d42d8183c5c040c1c001e440803940140d014440043c0d0318109403058002071031010708541101d4080c2c01809084c0180782011805441020b050040e81c5c404040d84007012448081d611303444516244501c1101e00c901042c00718180700300340a000c220300c410b6001080119007242c0015250103034904007a1107805a4074020041001489 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 742352437 1250 742351187 742351199
    0x7171915081501060306141f0903080f0304051c1e030b03190b070f050406030e0307150509010509010e0304060c08070807210c0209150a030501060801020a030b060a0207 74
    0x115100c500e40c0500a40d1805480d4402140380025040e5180c0000c070410004200c5550140304110280c807241485d010400c02c1e44022611030b0351100c111034010000c0401030704005100e181c0c501d002c1c0d0707807140c0380c6592001c0403524104940c000342c1e020b035107502400e2180c0850811510145a94501e03d40300d100303190001102c080025007000c1415024117445540111082c1c1c1c0503c0b68210034510a42070364592041030912100080c80100000180445602c195511640000907181203403c10310b00454140c106000985c01c5024481c0f00511004130400d003442d609515030071080c420901c41d0f000700417540c4c695880700d00703841c0f01d04100204e41c5c2081000307100d603510543d051001640036900c0d01d8545031250340c845142d541b190000380c1d41c20b6a14295610602806070b481c8035282082e1900c01d412000c1a00011100c1a0141020302d1400890a140609481d00c0308038100842d00031000300300075a980c071480740c040e60100c0b0a1000103840d00700d40c001e0624010381914400b0440354004c06856040107 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 742353687 1250 742352437 742352441
    0x120108012f090d05011803021b0108130c05131a0414010b09270610080f0f180a08040518130b070210020a0201150b120c0a1115071719 59
    0x281000f508800c1500c190004918240540342c4190581002c4c010300c0401c9040007401c080107090303d450020013101c501c02c01aa400a03a85400014840004006689070300c1d003140591701d6640203541000a111032052540c0c803562105c182088441034000340b1641100c10002115a2460040c2c40404200018441402208042e10740e4070805803a581d0b00150040ca074000000201d00d0341d5025a242c203081020700d0602c4003102d260700c00a41807103201c40c00e0400010321884030040c0328258072a520000140170886002c0022188010b42e42951511612420846640da00900a060041c070803094440f4061002102c801d03c80c031580308e07011140304160307506c107601c40c50050441002c600c240000c109406086200038410514a81c00008a10680502c00c68040c0490350088003512410700103040704900075004a030b03000c4601c501d20382d921500144144c3c3c0070704001d142c564661050071941c1d0700f00c0069240303690042c0b1481e00d508a051304440ca002c1180101101d00f40741c5841100072a40c81d00d2025 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 742354937 1250 742353687 742353697
    0x312050903100f020d050c0c070512032502060c010f0b030d1205090a1e0c05010c08161b032a0609060f210207031202031003170c0102120108012f 64
    0x90015103024581c440c5c010507a001134034240d04400300082c1200900d1820019100101000d840c400410618507007019181c2c00b409030101400d4105414259030138480c8a81251550390083c882c5444104440300103009011506583d2483c5190101444061400182c0c28507880c10503685c2c607040700155440c1c0780290902508011141c481c8012460003d000405058405000082121900030090a02000e4069184e000e141400300350b10302136000c0748402044411203125644600100b140d80c1c40e20b110812030f45208103171000000c2c1804010425921002038064940e02c070041c81460040b024954500e0244c416800450100e550030021503020741094840703540b548c14440c90902000c1d009401d001c000c1c801c43c09542d0790009440040541103c1024203008041e00110f00754644584c6080c2040364030302010389102070542d020400526807000300d591402d4404025510b407a0315910522003030030207004401c195402e14065482c0311001d0302e051090040c042a4000c01013040741180c616603408 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 742356187 1250 742354937 742354961
    0x12050a0605060f071a091507080c041203120c0c020307050307062f03120106080a140c07080c030426060f0a1802040e1f02030603062815031205090310 66
    0x1d080038400b810345d00603881441003402401415084c5426000c0c151050402454241800006001c0c44041c1d1002c00c00d507800d4810203139100c02a0038441c241038611002c0440a8103480d800d241c2c01ca20655807003294a055a031003901160704241d150700c1096107401507801164001800400703264002554580b2075a0500d402c5a49a2480038003100c04a0460b44840c2688130b03080419001000f0207a400f029040c0e00c000d0400040000a550100200b000311014120955055001c9407d4090200c4401100c924990305000c49070b64550300d60703190001c0f161500404401140e02c2640000c1c640b40480da041c842d0001c0a0383c88020317590500540028100704100420303002801c400800141c6a9108500e52059036000802500349140019515600c2d907220000c1810b0042c01808156140014019000703c500385031420003200b4800a6451044c02c41e0400ca2000d003032141010003012032410300001d880c010300c515024045146000d8840b44030f03402c22a80c0560005030504e840184540c400088405 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 742357437 1250 742356187 742356203
    0x2090705091224280e250608070212041e0902030403030e010b0307030b150d05070b09010e01110d081b040b210f0c09030106030803010612050a0605060f07 68
    0x19841c940c2d80b5010f212a2029003064041c1c0d44240120000b19006520a0702200240c8604411255022001a1002200f000c03a900d030710030340724840c0c0e09021000064000401d11201c2c14241c0c0200d00c01c601c01d82c403507140481c0c004008200c9103480810340c50940300c0e51030449407501d49003078008090040d8082d5002a52100700c0000300c0c161000d40003c1d4065802540e0100305504803104e5182140c422050542c80703039100c80000c1001500180101d43e00000d464004c0c00000b954402040c22210340c840020001e000300403010603000d01300009061014002e07659142004620b10054840303401d10f810203140c9900c000e00503542c1601c9140c2c2558445140080c0344140e515418818110790000e0301b28001e5140d0105502d41c00241440c000401980f0f85103002000d0308008030341c09241d0300050802052400700080c61441d0361401d400c60801103074002d0b01d045e900e69440340000c0c81d17000180041e030700450800c1c2c00303c2d1040e01c890080c0070030b0703400007000c040c030b020007240802078941e2004800321a944 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 742358687 1250 742357437 742357459
    0x9150306032a0501110a080c07120804090c03060b19111c020f060f070c080412060605040b0d031d0109090504030206070906170606070203030715020915070209070509 73
    0x2c0d00c0d102c402c00140034403240440b0098105aa0454864054010a040100307041d82c0c0014110001007000500750031130826603950858101d45da0511038150400211901d401c0a09002c0201e48001070048405204c000c1003c519072000c00c6040c4c4015101d1141804000d0000c2c0d40070841203619680000c0d010b040580c0040c00f5018114101607130b01210640e0a4001c1d00d008030780c00d805115450312055540090101c91907d1903003001c4901010300480c0c108405001d200b410030103c5c0c0211800f400c2040c0c00045001e209184c03080150a00d8000c00d4022801e10104040e1410f22051122546506407928640440c80c0c01c0c429041018840159040108003080050307001c103684101c0e40258080d9000e09080d00e40110040c06284040c1d001c1010000041032803500001c02c100c2ea103400210071524241d80e0303107060000a117180640040942a451460783c8094100300b81c2d030007010024030a40b11502640070b1041c40101c2c0c0d009180010750030415000000350040e2050005050442000300340c40c51300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 742359937 1250 742358687 742358693
    0xc030809031509031c05100312140720030a020102101e0f20031b0d1103090d0e030705031504050a140303150907050d110c2401080307030915030603 65
    0xb03010580d4424965080000c4400042d007180442c81d01d603400303100090160b418640e406666842d014400606241a442600595144200700001c44030365180d15544c0c45009034100651400369207085002c1c0d400c503801031060359050224070200c8481d0140c000e409500f14528001001e0070700d0034bd01080d034582c03820b00d504003500a841600300800b801c1a00144c0744131600020382000c00c071841384a01c103132018800c2001c000922215413a064000c0c1d00c0301a00c0712452405031014121303034040c11101d410044100020035100141c18442d032001c0380d9a00c110386285500781070b250a0a4018150540c004400010320000c1e213840700c5030014810340840386401c10a07210b400549a02c0103008565030400070604c007100d81080895428007108440c0888a42012200900140300f03d04402e040262520040300720300340c01c80207840d00c003688030054070703401130cc0012480c0c2050081000034552112900002c00c0c1c601d8000306582843d0392540300c00f9080ca0134406050f1060080b120300c8000c05d80c0f00c82e408000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 742361187 1250 742359937 742359973
    0x305090f011118060f1c090609051506010503090c0d1b080a0314030606040905132003070b0f0f0f071b0e06040c080c0d060f0803030906010906030c03080903 69
    0x40c01801030714180c0c4907502184071403d060710380000d403407040300c0910070700745000002021284895401041c0c849490030fa1031030300024081000c03000d01028034005084041c404c01240e40f00d0300c2d040d14140144c4503a14040151810700086c0c440540c0c503032280c5003030b4170303c0d0405a441c1000320703005464841d01089008001d002c5140990060b029a03002903907003104164001040704c02980c0b400b0210390940c80c01c100411103a0189210700d5031059120004502080001c80704d6042c0c1d45c0c0c1000d144122410500c8008805080d42d0300c400e0f0003481400000190b1459001c1a10881e140c101e040504c1d01000b106040e045800040400c2207040d002c00140000482c5a00440c44480380c48004612051400785110400314004040c0b9010b603007031940c1c1401456001032007075808000181c1c0d05440715407407251078000341401e400c46010361403014008113921b103000024510134241e08049680c03580e201c504507400c0e107005e0310006041c13152125003800011016805000c03020805070444013006500c50417106 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 742362437 1250 742361187 742361201
    0x705012001151712070f0f20130504020a1a1c0b010f0315030308100302030f06060406120503030403080c0909040f17040b160201030615020d0e010e09070305090f01 72
    0x9040140350020410755892103440e8968441c0d88000d0880c1c8460700c1d041311001c0c807601c1002044160009005020811403000c00c001d80b503044040704124440c2001601e07803d00900c07841034070803c0c0d2040c451080e15030901550340f09550181034282150300d4030010b0700507520704cd402c4681025041c0207440809094220f015401c62008a0209100d480d520001d010381910000c5c40b4201070404c2400e200070302d44000b5202c00c0300e0f890310b009040c81d612451002c0180342c3d1500025414080e04644581c45000000d070140a00b81c11202007110710742c0e90a410220701d01c0c4180040041c0c2003440041c020a000740041c641c040355014029142c0304443d80007401d403000131038044405203400100c841c00e200c0210300040003518406c81c1d007460b060401011f0310f003d00888a102521040e000f10031011a403281d04003000a05056601a141711034018001e502e407002006108006558903003e45039541c8500b0a4180c0c5040241920100ea01e8125044001e81402080c01d0002d102d0015803160040003481510 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 742363687 1250 742362437 742362461
    0x30207050f0733082d010e010f03020307140a17030c0d030c020a110a0801151d01060e0d050a231504030e192c1303020705012001 57
    0x8411800d010310030300c03a00d410896807841003042100c140c02e243e0015003000200101030070190480c1e82d0361440b290711080d500030000e40c0300800c00044601034183d0141d46041c2e4008450458480c0e884034480f01102c01c0c68400a0b42c5544059410429211460300c1003010710f0000d13100c001015245c4009402c6803000107580c81e00e50780006400c102201d000c0c001d05090f070380c880c9003d012510342044001c0d5284032a100c0035007a040b0404502a503a1703600342600009105140081c081d41c010300d810f5a000302d01038400c010b0b01130784070001e10100e0f200014406042e078005460350080304071088107100c0c4100d9840c108444c2c5114244011001c5070b843c01c1901d00c041e8134140500d401e65034605415080011088800c140d00100105000010750030a0380c14a04400c02d41d25680783c000b0969030024201c0c42c41d80700308111b201810940380e03001c42c004210040c0c400034075103d007825112500405010f400d11280680141c10104043c001c0f580700d10341c070b9090a001c60080058011140f8500f82c01c4407500a281 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 742364937 1250 742363687 742363693
    0x14131e08130b0d180c05010e0103090b0108010618022104051908180d0807020d240603060c1d0609061b0c0f0d05210714070e100315050601030207050f 66
    0x1070003800c41070041006000810040740c0b144d511558840c03162604501695046c44160030482c00c1c0380c2d219520907410180c006005102c256900c040003402840d4074003503050b58080340e408400c0030f42140d00840c0d002c00556140201c1c40d01100100d401c21100c041d00c1120103001e080c00200c9001b07505401e0210080c020a5440ea0b0b916a40c50910340210340c1882481c05042000104c0f0041050503043d0b9074440c0c1c0603140c141140000303241194104600140b01074000e44030401b25000c001241d407081c1300f07803481241c5c2044206c06201080d68002c0d010584100680c100d04603a80300d0741021406481d074060007070241b6082000441840007030051000c240001c0c2d9001e00c0440400b0b1400c0241403148140a9681e141c18080035101d090b00c3e00d68001a20110100c11802200b03a84080001c0b00c03e00c64014050850340050803a540352200128820030305660a034402240801080f858030108a0740c0c42055032410b8401da80011024000c006c14170703414035900380f110b080410801c0c000c070110030f2202006 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 742366187 1250 742364937 742364947
    0x1101020706060e060f090103060902030f0d170a02030610200d08060a120503070f0f020d050115080d020706120b09040b180616081008070914131e08130b 67
    0x392114a490041c40d85201d082400303001540381e101c0906d001e05480d0060070105142d03082e07001183c41e101b0ba198a1442c58441c840c4041d4840e54884a8050800704018149806841e804100000d902080c1c0303c01d54010002c9440c62140e600801c00e285085030503107030342d00d10350041e8520b041c2803103001010b03007010450b0801005450301c0c022541601520400c110200c2440780d40c4c40305640d034003c01000410b00249013034042c043c02107143c508038115900502c031103201019031070075a001c3c05041d9800040030024050208518001240070000c8454039401003400310b280c50b004580460818600315020b0b0b0307503000040c1c50b03a11600b00061050b4099440640c171810312500740c80800c2d0401007001c40c039402c86403c0c00520880103095070044000c501e0091580d41303030b40481c541010342c0c9078426905840b40050000f1405541e03008000456610480305041ea42c030310200c0c2d0101c041344080102103030300c085e141080418003481c210040a004403021801c0181d0156949002c600c0b17038000c04026900860 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 742367437 1250 742366187 742366199
    0x100210060b040f2405030414120d140c0324040203070201060f0906060504050f1206070e0103150b190c06091b090e06010b030a14010e04020f06030403050a050307110102070606 77
    0x2007075005107650307030b81c54680c0350185280b4541c0b590300010410801200202140500c008d016500c0ba81142c5002500d456115025040d0a91340c40040456156420246104039821208000b08e100d0003010760502e145544001421090f864104a2520101c0c00e1802e00782090301c80748003441c81581e4940000401500b03101b00741041c0211580070b541141e081400c24885c46034401c06130b404568003543c00006a0104d0000545101d1400c205107071103115240800c002e807a400341030b01b403000340c007a2010011851791411403206040c0c135008034030a61008101c00000d124070170940654181c1d0515203000031070465130762242922140c40050f0b420501d1840d50014040304441c2c1e0600400f0190740400c410801c074403480c1e4650701c05200340c05c1d4403400800001c40b161900d070089024507005101c082c20702c0d82c4030007015189605c15a030036400f0310b80780c0041e040780b070421100300c81c001c5400d91a501d00308900c0303140454580c0d1000b440002040401070f03e10b88020341c02d00181225510480010603440c0c2005 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 742368687 1250 742367437 742367459
    0x2032502010905330106121508030d150f0e0f06121507091202011b03020309060c0a14190b1906170f010b01050720180403081f05100210060b04 63
    0x300c0c00c40100d01109004101c031542002c500741d00c0b2040c011000c08d4040300c00b01e01d0b001505c050b0b4482401e070300000400081c1212a80d1141110801d500040d805e82521003c065080c13445500802d020600c0d028041605009500da80c01d81c03041004049504c003081d10030080d130605036054080d8440d401504280420742c5d402a8040d4040e000010149800d00d0041c3c0009040d220040b84642056800e4102402414800c0c01207174120617020341000c3e50744a109034555510108000c1c1944c0c14443c44034400340c207410200d481c003081c10081c04c6030003a081464942da08003510242c5160f1221030340d03004941c011401d80c026a00101015440108662845810a8140600d021031000070b41d1410384200556038006050f582590b810001e11006c02405140c41030310608511102948205030101c030010703400301843d009120724861f5030b62080c292107800818140d00a10341c00405007403034a180070301c0345003000149115003107002e10464a130003030352413042c0c001c65101d600301e0503200034000740501080b1a80 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 742369937 1250 742368687 742368763
    0xf0712051b0906010807090f080a1401110915040305100903180501050a1107030609050d02241501020c0d051c11060f1e090d1202032502010905 63
    0x2045101085140c070001d0006030000705510305206140c4003064091b03105840c10009014080841c104180d240c0070000d91391010450201c50764801141c1724105042e0601031540307800c06600c006424464071004119400c07900303520218071607005000c00000b00b1410022140360038108880001c40b01010700703000b03100d652400d01e01c040080840740100032030391f441421a2001c03811841e0880c80d82111048841c01c0074410350003e0f04640c2014400c400703000010030320f20409a915000c40e01510003a114510902918a116011015400300041d032410110101e21450003c144180d0703401030503060004200000c1500d0540d141e5114590640d461122803031214522401f500317040210b013489a110666880c4020503004641c1104404902c144485c043c0040141c80091032400ca04d180900c00280e680c803100514070005a000940480d41a4452003140d008804011170340c0c1d0400001c10009400d031102143c69402c566a030603050010880500402d200b282e101d803c15181c65070090380b01000080e007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 742371187 1250 742369937 742369963
    0x315020903060a02031008031207080117070302011809152c060409020303040b040311150a1b170f0904050601020123070c0b070305060411190c050f071205 68
    0x20402000015590004040b0f90184100001503a0f075660078484400c01e5650758020009480041011a070005000004a100c0c0010f5581c0c007445aa9502d4440a0303c81e00d450043c102c3e8008000500c0994411010700682d4440a601980c0095641042c103084803031a00014030a4081040180800c4180e0300e00411240e14182e030940100d4007506861095103005810039104a6545030000115201401a03400a04020b1807041c0c031240d480c206280c00c04903044d0f1040c4a14500502d001030b81c0e04480640386003030669603074041c41c0448007003080d01c003441517001035521001d00c0d02450182150388004040f21007a5403852500d40c90b04006110554030041c1c80941564145800c0a4428150440c405182816542c0d603e00645905c01c041c0d82007148210050b0881c0141c000300029039405400240c054001900c04000c08010000c8900044c028840070b000741d80150020b4000c071030310a49951404034064019a4400f0400d030080a240c000107500141c2c0990300da01200c002c0c850127000821000c60 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 742372437 1250 742371187 742371191
    0xa32091b040207170a09240f050a0917010b0f06041203140c0d03090519120509061b07031e080a0503150d150c053c070305040315 57
    0x118040d04186006203038903019004a5011481c081032101d810701c8052620702c965849941c805101a00801c055802d00500600c503400b2500c14a10114038040106080081d82d00c0e060140d4030620126078136804001c0502c00c0080d44800400c9000380710980d41088601c00c1c000080340720000090000b1004001e40d414402c2d04107010401c40b201c00c0b1605541c000d40d251400442c4031003469040030392405420803a1038284601d00481d00d40700c0d019401604080d014004803a044c07103090302c0320100117004100090180c401c40e0a48000b49016402030043d80000074203407402c0581c0901d40343d51640505161406c42c0d40007601c20824049492041401014103c10300340d07140c219030300c030f501d1780780304610301c1c00d08108002000071207068549402c42c22102005088181c1e0946070f0410b091030850b0102c92085292811499110340c0f07003d602200c00f046d03060f50448840403c20380c0701064000803007004801080d40c92802030000800e400c01013030034501c0303500c6464440d0b04505000c82c607200c040784140c822034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 742373687 1250 742372437 742372453
    0x30720070f0e09030415090f0e0609150f010305150d060b0f0607080405010f09090507210e0606090a060305061906060c0b0f0901020c0d26070909050a3209 68
    0x103c0030049806498200080c0c102c51800c2900c12545808170758000c610000c65100045031900711100c1613400780c0b108681043c0d454458a064081c10344004000940c0a0421390300c01c0300550280e0841507100610303901104d021f80c640c10202e0040c6141d80e8040f9491640d031056400c6910f0010b0140101580650301e0906086082c0c3c4c500b1b4940c425802054107102110b1040c80c100c070b200b044040040c104800061089042503c005005804141d2000f03141c00d04081c2102c0c482a024881c503030855101100820740341d01c941092004070362000d407620070500e0701e400001c808554200910341c010081c0c86c1441080c4641c207c0503404880b0307690007000400c00b000341c108001c1295000c40e150003502e81102c1960a07115201b0441c020310640300030420310b001d43c281d003000300d540203040c0c128082070300c584540c8403400d100c083c50240e00040b1004404103070220400c2c44142c00a034002c0c1c1d8001d0413601e001441403044100b44004c41c2c0d1311144113001d03032303d500781c2d61195039104900607412104940050100c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 742374937 1250 742373687 742373701
    0x1908041509081e030f04060c0b01061d09060d120915021b04020901030902040510140d260d09230105060603060d03020115030f020a06080402090a02030720070f0e 71
    0x180400d6445006052003007003c28902c000140111003582da80084056500d0b60b44000150139250720f40c0080e508081007100010b0080d008a1500100025440d01a070b2822108000c000344180040c0082d030300121502d40d440c0001c1c920001c0011902059126108002d117031003959500460510b1080c400c54204034002d000f10391000303c0c094240c000865015844807078000040f4000d00404601071740c040e00384024032040804107041d0701c00741c0c1c40f8860603440d075425500034405800a4007100810140e040125000d10118000c121112806a0342a040c6040903440e05030381540c041900940c1d64032030147c20034880ea040788490304c0700c5c801181c00902007807034803400040c09400000c003401d00a42052000208152007907125084051200401e42ca1030b0f074407418a20104030055070100d001d00b20700360021801c1c9014a0302c05124540c000c1c1117002650b151081c00d4040c1d00003034110810b024408030400d800d0071080071910840c03002d500040403590f24101d120011043d9a500544500e1224000c0c0464 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 742376187 1250 742374937 742374943
    0x190503100e030d111c0c201b0a0803030406050604050a091205091302120601020c120d031d0f010522030e0d1103030c0a03021612060905190804150908 66
    0xe01800f0030700140d1104040ca41c1075040c403c51101d21460001c3d80764518000c0910b03131102191a40583d1544020281800302e0300807180d040c0c0064500c0d612000c0c201c04150135440c0c0c0c0c80401d100140c00320b44106d60f42c1c03907414a1500151800c440d03a64030f4400308000c6080902c910380c0d026891700c00a21a00c02032b612031800100b80e0b48624410000d00240104003a2600d074080c44130000300d102d00719520f40c1010b100744d920000c140c903480d006008204140c125454141810600200720784064011070700300d103c043c0c00030005d80115240708014685a0034400c0b40910140011030281c00000c12030303291402c4580311100d81c0650b1440012001f480c0900440d600841c042004a010b5440361822441800d20313418605c4051100350340b40c400003619081d0140041220340300079109400304d55584480c0c0c007a0a0441c0d40314011044848a0300440e400424107980040e1003081c01b890544022101840151040f82c501c9441500c0c18000003d08101d9070240c000c400fa91022a072910811240c24010b049032 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 742377437 1250 742376187 742376197
    0x12090607091d07031b08060315040312020309010f020c0a020a0801020a020c01030504080c071e090507052a06010605070c05030312041227060e010320070c05190503100e03 75
    0x182c50154000210000d001e5031020303510091902084050000042000b86884c00c12180c07140280900000108040000aa504c2c051949038030796422103030505038401c00a4000410f004003664a4083c110000c011510007001c12952072005071611036500e00601911341c41d48c0d80b290f58560310400854080c0d51303002c0349441514000b481c0c08511030f1224140750101d4010300d20b0b8000c0501512000107003510751105103000c201c1044201944071942c4000c1401181d500300c0358600860800c018600d4110b49261040c1c08682d0340710241c1c8051181c402c50180b400f41e003600101d0125a000480b04180021609888000c0c0b104800441ca0034020303840860448801070700041440c5400c40643c1c19490042c500308002114440c80c404c840740c2c0d84441c1d40007211241c403400b0003148881d0f502c900194828001c114a030451613204a13100e24181054852540c00301d00140c5081c1c0350003201013640d03603c0041c842104e04010401c8000740c1c0c2000d00b014244000110b52070181850810401004100441a51 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 742378687 1250 742377437 742377479
    0xa0f2303010b07141203010e10030b011815140f030102041503150306090803060901051917010e010908090f06070b060402030408040306020a080f0108030403021f02070b1209060709 79
    0xe4451000e4540040780320a09a816013950090b140064004a541e501450484a42803c580d1b00c07500c0b031030340380400036841d0f000c0a000320741000018004484070b145148880c40740100002042c898103080c040000400390802507051f90f254000000301d140c801a6450a00790407002180340c00c1c41e1001c0e07a002d02e480219880140f5450701c0e9448a03840d244103001d0001c540080c4184450043e524004c5c8140c0c0c811114584035544a4001066900304680000c0c620708880c00442100d0b818480320380c010810004421805640f04c102100c0503080c28080c90691900c1000c1440d02d1740719500070000c107038503d40032080c05908180059030210707130489032036038000605490060780d036110303070601a01034407681e04080c29a9000060182c54184d010000510072500c00c10280c0c0203076250300c000303074903440780c0e20001e0360010f483c1c92003038402c031107140c2000f21007000c3d801140d182ea03650b0018185250030650703072010216901010000f80c1001448010790106062804070046410302c032034926859000c01c080 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 742379937 1250 742378687 742378709
    0xb04120203030c06090102130b03010501020a060b0f120604120f0504090906180b0a06080d0f1808070303020604060b01021612051e0c010e09040f0201080702120a0f230301 75
    0x1160554509108641c038103008007082d40c00c1803400c180030714080d5111034905c001000d5070010008000c402c41e0145c9042c1c4505901804000f0f8150301c07008050315240010542c031070844c0d100e6541e642c2c0d0f842c03110740075017a00b01d029000030310b802c0c20720f846658034100c0170b513062090007001c445d0a47d40c00320440e020784022810014460a45e82800802041c414042019044103081c0d01d4003031080000310140704600000d4288556500e40030000e454519000142c00443c40d00c82d00c034044103010f1181000340003002151510307a03903540c942451501c00729920540240c0c10a02c1848180110742c01810b4202c41c2c20300041000c40d14614a00e4010549480344407601341c10041c1e41001c1001c18002181418103002c140004103102d0b000300740c1c4030001c1806e85408906402c8020046080501501b031003243c000e400c5402c48003c2d0b80066680310b00061540b000c500421100100e85145880a40400c01081e580e400980c4840c1102400c0f0914a07404804a506120b10710000f041c02081204d043d10020b80302 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 742381187 1250 742379937 742379969
    0x30b04150f020a0e1f080a022101064e14011401030b01020c0906062505150105030309090103030e010e0301060806040b06010801231c0f05060a060b04 66
    0x10034002401c030200440c00107800020042900d503403103c01d5aa550800b250101d11121600c0c15042e1040b0002c0240c030049011000020703c1021940d000d091045a100321030244203a540d188003a004a090b0003036404a020481c080003000c04c3ea5003009025480d800a118252084000c004100182c0c10701072207041c40800c1144418502d145c000089114a800c83c2c003006584400b80e81c0c0741c0a201000350b03400a803901d19100b200f90f100050131401d008010f01640f0080e100c140c00d110f1541d004d0703901c0032034083c50012b60840c400003030441810428050000390121a4100720705404022041e484a8440d03032090201085559890380400d046980c1805d040c104000941e005980800c0c0b400039659040d440c081c80002c00c4c40c80843ca90303104603c51013443c3c08035a5858019510020213019a5144c40d2103803a905a01c0c41074203060038540c010007048056005a40e200c41d28220054000440c1d544054400303e104100c01044020f400c401512800d0020505000251546019901c100b0410780c000840e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 742382437 1250 742381187 742381223
    0x30619090303091b030512282a11040903020c130b0d0b0a0c030c051c021204050a140123270f2a01050913050a0e1006030b04 55
    0x40700200c000d900c0880e0359281d00c3d0340708a00c804c4d140644400d8444d030044a0114944007110b4044401c1c1c9134030500c0701c40140c40240000c4110048002254040c40006030b020b404020407080c1c0c5520030001001801114681460003601245c40c003c40c0d40e0141d82407400b50030000e90046102044c802082e41c01440c50000704080c40c0c0500000000d0729048035a41840100f0700480c400271602c522280b46081c03205103280c4000314102d41d0407500c4100041c0c07060000d0406030300d0000601030b42184030705000d405c0c40000248000142000e803012203252380004d600604201843c0d82405403c22044002c101c50240240d011881e0510250070b40704103850b402c0028510b0000107502c903106400440380c0c50725080074108a0380e03940942e1010b1b4807503100d01c61142c000c02108841076440320170000b00b000104030000c00151a150000c104040d4070113250120020390074107602c40c15101d403045800104d08041011071540c00c0441d140345250441e070a00b0010f00200d403140a14540141c0d01c402e003a5903824401e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 742383687 1250 742382437 742382441
    0x2a25031713030b1e09010c020105060d020901050108090c10050a02060603060f0a0b2205070924030b01020a05011104150903051b062106100f080c0c2e0b030619090303 73
    0x103005131071201c1c1074082c82a502c00541c450300e074403a00d40d0000c02150320b80d41d013000503103482e0b01c2d070083d40115584014822948a446880c0d003050301c1b02c0807104409160000907002d010204151000074802040040d0059810014107130805c8094019080c5800c1110f0311910903140200441c41c02604c0d000c01010740c0d00c91080d402c00324052a400024180391410600c005440195002e10000e90120404145500c041c421b03110150079806d415071149200b20429006040c6e82030b090b0381507010381c68402010070420f0050344490707900345040540e00e40c1055100490b5002c0709507504204141d40038140b000440010760550111715521102c804031810000107900d87c03148104a4120084140c1302c02036100c21601070718000c1e80101c03840111000311240480d038000951280d20300050050f00800e02d00307000803004000721400081516803801d50808600c2c001080038030301da41c1c81007040c0c0d86899060a1480741d040840e1085000c0c0a0b075007001400c1951030700c6000e40030020940e607002d0b003604040c060303 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 742384937 1250 742383687 742383721
    0xd020609190308090405090601080a0209061804060c1101020a2106120503030402040617101a0a240306030210031104030b0f0a0e032a25031713030b 65
    0x10566060450351207250075546504041c0780f007406a0301b4000485c4c4c13446000302e0701d107050320003181c0280b096048540030040ca1003405089030b90081c81d00038050765041000080184030f540a03400c08030b0510700e00e513002440c050846106003826441031000c2110164081801d0a020f83c006000500f01d01045941800500441c2c0c012442a084040010204800400558030550003220200f00050b952035100307807403440044058949801c04515400d007100c581c0d101f45510605240441c450400030400b00b1402c00083c1c02c481400d8039007520080030b8001c05122418211403600e010700400d40303160302089451031190514000d040e103031618100101d0340c480944000f9a0002c11152882c2042c0803900c9141005072110442c103428460400f5902c1000400c42c3c030450504130516005006500a1a0b492003510310788519a014880c0801c1c040a54030340500c040d91b0400b03980040030791440c42c00300c06140c610051060011418005000745190302120314040329000b140c04115665500142d214040b05 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 742386187 1250 742384937 742384969
    0xa1a0f0403050f070b030408041215020a18051c120c02031b09070c0c05040902040908040305010c020f0a0308010b0a1709011d011a04090302240609150d020609 70
    0x2040000c144040021010b2142450600313030394419031517040e020410f02c021940608003020400c4208841c503000c01d01000aa800355483d0a1041800607000050703a1201d200300b800104c03c0400f4a0401c1680c000c074030010300080f562017068140e061040b8207800304400000d042c1003000d901a0503514050141d8025941e40103080c0c075024083c0d100326940241d5000072240c0202000d0001070660f40c0282148030240c2e800000c0400c0c02841d0000f004007401c44524100c4e00142c4610072100000c0380000584040d520a4001091620102c00000c1c64180603e5007114a80e20400c900c1d80400c2c0c001c6101815900f55032301180e82c4d01d20120f03080d0344100f50450700c0140d1440000803c071110106602c00510804600300e01320fa02c00b1101c40c01c81c01c0e2864441c51203100d5203414003480700f6140c50740c080001c0b9031103401540c0e0304120302595410808100044020786840c1e1508000080c503010b985141d0004040110100c003403040c5021035610035040f034000740240c01c0000c1101407035031014144146c05017 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 742387437 1250 742386187 742386217
    0x7020d0f02150d060f170c040e03040b07050304140114030403030b0a0803210a0b010915181211010f020c0f060c030a05090406060e010c0b0a110a03050402120c0a1a 72
    0xf4145907240b00400c2140315003000c450701d01802103a13002e00c5000040c24031030054003c04c0e9031002c25040000030580c850032040c0d00c0c8000c110010380c400c09000070700300081c00f82018507151450f010f92003207003c218035061810010070400920341d0f1804401a0381c4c1050301494006542404100441c0b184400c40c1c02000103440041040443d050b80c51030081e81440034452013030191380b0b94aa1010594404c0d90400c1c0c0401c2507110140305141910b17100103202c04491a113422040322003100710602e20a1038020f0365000c070b14070050b0000c0c40768800580880e03900c2880c1071013520b0a00a002511501d409601d90321aa20243c000303241a5904d0060300e40d609002c4065a550300461b00c0c000d00780d50b100d400300d02e000d90700f42a00003801502074a0851308034074040c1c507109155110b45e5260901804001c0000c801d941c0d1f40e000c84680e003421038001e012402841d480004490501d4010803100c4c80306014450025403040040d8980c58440c094050300729001c0304040c40e58580820340300701c1c10340510303604000051 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 742388687 1250 742387437 742387447
    0x409050604140c130b0a050708031302061b01150f061b050d030903020613030503130c15031d0f0d110c1206041b06021b060d0f0515040207020d0f0215 66
    0x15030b02d600130003224040150036803000382d403015403140304d015141c40c0c8404078000303100c14030105019000450b800200040615445107555000a47c1703501f02c855035480941d41440b11000301c02c0244078800c079250030611035034812440c1400d00100c092141c0500f0341000704091320f6006031640c0024107003035194000203603a1540d11411004004100381c0c0000d070014442c00303000c2062803203205808031150750169551455960b500100c2c10135803400950482c4d4041c500340d400a801c200b00001c801c13001c0707a640d50200c2c05086601c0440044129052000c0c201e400100b4025001c0d60000381003044001a420160082490349940f103040200411296800c90380d08003e03040441400b28541c1d1103240302d030381e5071104075003500c0d0040844485409036801507800b40b541c140004000034060608184010b240303514003a01910381c101561005500f88400daa164018400c40d44010014074a405005403011802c00c1015000250000700b41c00000e44121413082c5600300395244d05440c00309002e017000c9404d6442d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 742389937 1250 742388687 742388701
    0x3090201021005150a0501050309060f25080f0a1b0810031506030b070207030b0735070e0402090105070809041404050309100e060912071a250305040905060414 70
    0x35031303c8103c0040c0300302252070380880e1075070155080e40c3c0507014031401015182e594620b0400190350152030054030a4803842120f494028041050800380101d0303030382c0d84c1a03092041e800c002e00c4c40040d01e8000018103015a030b0308003030440508980d4541c0540380202e6643c6a411082010300c006030400f811045c4400c502281050190704400101ca00c98000401d05981d08401203032102818040140000c0c14080460884ca20403000c00c4940c03020040b46a58a00303215414112462030511207540301c00b81034040021a542207000d25824800a0b201540b83c000d00740c00003003403071040e014010078400011603991450788566104424040500c40076030450b0800e802d0455481e00111442442400d404803c6005075115460244001c2c901408081c02c006005040050550510360800050b2292036000120541c581d112502a4a821080703243e03248224003005070016015208626035552000b030810010764008100d408450001000082d00e8407080001009030200a0411140b0b02541c0144140 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 742391187 1250 742389937 742389961
    0x60e0412140c01060902071709030723100c030e19050d0f140604060e0c1e0d02030d1106011401080c0d0e16090b12030307300e100501031203090201021005 68
    0x3050b4080d0b0031008d911901e01c800003103144034040f00300741c258002c004208200003c00c0390380c1e07210fa40200c200d01d800303061010100d00038603112192080001c101010803400d0640102030070011420031b640c160b40e4403c0400100b412458640708035400f43d52584101c07014840c076046408511548402c02c07004030120a04003a039260340540317013510311503c0c01c0381b03014603028001261910b421001c0c04902c6020400c0c08420615242ea00c01560400c030303010705800c016501800036449101c0c04d502c0d0600d50341c100810491174080c05804c10784066100080c8944503030303004040e40794441186c03e00140d8844210350000c024019001803581e1920541c070050590107900019582a0303002c0385030800c1484020070070403400ca01d0000c108103203078004001184041c3c0c401d80306501070390704403174000320783e400c0e8a0303141004200034510f01105c1650300c1162110310328081c41046140b003c0c0c08800e004550440d1900d5291b045545030010906585032454411640280304900c2c41c4c8070450820000b0740380260050300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 742392437 1250 742391187 742391197
    0xb04110a081b0603190501170d08010503150402060d0c050901320c012d061509090c090b0c011d0a081215030313030501060e0412140c01060902 63
    0x1224558591020039460301c005003803402e10800b44129a42540c8580a03c421a80054207052a4003031300d64100100b0202030080034000c0c240d099110101c40d6025010340e06240d9646103000c01c1110b00801044299000a40f020951a005800c0c11903034981c0e1001403840c2c428a03d0451369203040014a02140b600403001c4c1500030000c1c0c940750801c1406000300b491502614841c011f040005100c40e1285c2c0181038041e12030101101b0000070040d60221507001d011244000ba680c0081740840482c6250070b850003450001d01c0084817444000c0e00c01900549585d809008070078245948181c01e01e1218030800403400104608403a66980d070f20720004180c040c18010320f081c40e1044840004a01c0500005a1054a144c0124041d800d01002c60702c00241c01c980070348030800200105041c4816550f0900c02081303107880181c2ca03040c80501d5403810300d003901c0c015401301d01d05070401c808020100e000b001c8140194611490680580c5000101c01922802441400f00c4e0301d40c609240403400340601d50081c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 742393687 1250 742392437 742392439
    0xb100801061704051c032915041503090303021207020c0a0f06090501141908160801060c060e0f100e0c0a030201020a0201081e0f0106030e0a081e070b0411 68
    0xb144152020144807208043e500141135a0040001d440c241c40000100300d0384001c1c1d4540824000403007541c1640840c026501811a00781a4100c83c6651a19589034610000e607040311a0900745851001c0d4200c10100455405054440c0c501c0c0040511941c115000e484080341600c0040c204040001e503181e0410050602032410090040743c2c040041e0008021144241c1c0d41c444810306250046030a810101882e202d2a4010701c46a60f213203039017440416410b030143c0e49a6980303186c4103920303055090000410106001000d0014000c45600180e803400c1d164000e4404514854603007006031400030328080c1d0006a00a051014120504a802c41c02c440b00070b000443d049020b1040c1004500c0b0941e22009000da4020600e100055000381079040c1d03c900460350030100e4080034014140704070341c111030503520f100340740e401440003c3d010b01c200700865100b0701c004e00324009255a001c680344191005c9040c22007800c0104511940e20390126904658051a604d21074207280c45e0a010501d0594406 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 742394937 1250 742393687 742393697
    0x605060103140c0c070306051f06030203062d030114090c04060f0302150c100902270414070b0c0c01140a02061f170703030210140c0d0b10080106 64
    0x41495980300e070042d0458505030941280c65a242d4400c0d00a0303a41c0003081140701d074042d4480020201e652403060038891a02e0941c8004a00340900305e500d41c103030054002106262061041c000c103a00c1d0b181d800a0401c0d580154040c85910701e203030003022002c0403103c695040d0f003050404061848001031143c0101e8042c4203d500c0d00108004200503141507004811010f606100104054030b00b0b689260300e2881d000e0301c0103107020b8049504509004000e9000c010107038842c00d80c4011800d055250884503421a0698061040c07410084802c02d00007400180c9103010000298900140a106c0b0780010031485405559421801c40c6498a518110449a01080349141100322500d4108101e40d10400281d01134101daa450b850344001c03081000020b20785403d25040e008c81d0b0000e04034404050308850720002c051251440c034009180240d000c40e944545070500401800c5c1c001c00782d42464016900048154031005400c8004000340000c070412940800d46409003035142d50801540c0f0b0685e1802e41d50 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 742396187 1250 742394937 742394941
    0x109050312030402060a091706010618060e010c05100c03051506040b0a050c010603080a080a05090d050a11010f0504120201050c0a120b010905060f0a02070906082e020f070605 77
    0x400d516203031001c81c00c801c120801c00025005213482002090a0700aa09041d5011500e8201c1c1f142e05000f0400030240f65440b10300188049500440c103000443c590790740980d074590070440d0061507689a02d55650510152040c910100700c4140010850940182d1080065400c1c84030000c0140c4005c0c1c650301c103042c1c071070744420000342000800c40302941c003400b101710b20b0b040c460401254264049103034001d0656803608003000007039a0100411f1441881d540d800310b103007803922500046500203051103410390700014051203a2034000c41907a061010b2410060380b0104620a0140500010560500c009181004000800c0020b43c520607802e10b01d94000c0000e82d1320001c181d400c610820280341d0201d00346104865000d14a900000140c0b41d061410148003a42c2c0e0010400035040031000000d2003401051500c0c0160341000b600c002040945014004146860300040d1a05100c000c1401185100c500744000300c1d41c503403495058444014811555010040251012500054401c8030032606180c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 742397437 1250 742396187 742396189
    0x90c0a05030111040b0711090c0c06090a1104091e080c06070903021c110d03030c0215060a090c14070b040b010b070c06030507020c1807080601020f03120406090204020c01060302010905 81
    0x3c210321240220210042c40e040c2058035060998108010860362440c0c003904024460f1500707540300c2d009100714080742d0707214075041082504103c00180411020f611041840e4082880d68010119070744080e00e000846984a0800001c202100302a00326000e000e1803801d410880d40c0780c010403103401c040090b00c2d19600e4a010403a401180783c031010390300030b00164002d10000c0c00742c5c000d600c02070b01c182d221904c11036400380400c0101c3c0f450740f01a000709a9680c0d02e00c450580501c20a0404204c0c1042120b0301c1c503110300052040060790050080941c3d4410710514003900a803584444084880c1405840d06101d140258414404440c1201d84070408d900010b15007003c94241d41e49a640304440070956418010110000d150040c00e0340114800e186640c03542d5100c030700c2201d40b03084100d07448400d14a49028040d000c0040a00800c0c1154810301070704015241c088166200d107100c0951850903625035051402c00740518080195101c0e20019210f100008158410001c0301c2c802e1b229100c006981d00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 742398687 1250 742397437 742397441
    0x1b0a12020303013218090c03011e0c09180c090b09030a060903090506040909050705030309091609051002010510051f08180307030c0b0c040f03030c02120303090c0a050301 75
    0x84201d013084200320b00112008000341c580e0100340684140c01c0841c241030070000580358072150b1200b08480e0010b400f44062001c083c085c2081c000c805900a0101b0030110f60024905a2840443e80311b180e42c40740b1040005106034131410003000080c404a11080500c980c4800078043d800e034040c0031a0300c0010010b510041281981d00d8110000c005d082d80115a0322041d010300f0280307504408010150001041c2030b174402e405807010b4052030302d000403101030700d18155252a078907800c2184a41e0042c00409950b0341d603101c3c0298010481d00303003d84032409203041950144001d0300001e5001100b80005150b040c1d056001500c07503020385509055907a41c807801d010146800301c1c02d5094901c4d0035840002c00718000c8406503004900115000c0c1e00301e540084490564000c0b2500b01e001600c0d140e80e4038284160724244a800c1074920400c0d900d801c0c0760881c40100c0c0c4400740f2009081c000c1a0f50008259551010224400342c0b0a0b07040d00e0307992820b1003039951211444440d542c4154008500414581014 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 742399937 1250 742398687 742398689
    0x3090c010921060f05150a050303280504081b100809120903030d0914070e060307270f0e240f090f030708180909150c1b0a1202030301 59
    0x15048188000060303500150000c18580c07400d0f544181c49801c0541c851605204141c40b031401d0b80ca40000401c41c000030458400349030382c03040d44a03074024001998003514030f81603580840f81070142d85007036202200c0c00360f5040c02180d01411041c0602e540c0e43c40c03078500710700742044900e104480c14643e1011102e0180d5035114103a40d14400e079402001c0700c8115210324002812203080c020100c074180407400d40ca20050b161000c0044980c43d0450752480f980b988204902c0001e00081014281c0a00d13000d00404e503a042d2910502031210782081400d1361103001c00107440044d94808106000e03074545078807000301900503c3c8001c0194456030f621008104440a0551001890810385884c281c0b60415034484e000300140000b0384a000d103024821025004100401c52244611070164444840c901c0d4900d109444000181c0503028034000c100c01c0d9200812011107001d5480360148850311803202058050061980301c4018540300e41c504034030400e000541c8108544a08112550f000b4542000c03070301ca0000f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 742401187 1250 742399937 742399949
    0x1806030f040605061503160e011d040207022b11120a02090c190e150a0c030f050c070303020c04240303080408070c06120f0606120e031b0303090c0109 66
    0x200303402060001d24940c100c99001000204010240341c681c0c10811443da01c04d4401040d05000e06010560040d0851090a4a0300e400d007040a00031180c51020741480815040c5a80b285500191030400c40d6106050800e0101e00f070b46880b2080e0300d82c16401e020580c2e03403d1003500c000c41c02403c22043c03072800414018001c050113001d0b1080e9022542403188240004d82401e505080a0000e81d004403020300750205656103e640b110481500b00090003c5c0e11800b071420710b40b1000c01c100c50b40c0d285030003804a10f4219414a801d0000c2800c0800840e81d82c01800009100d900034054000185039002803100500441141c0400c8051500e141e919441c0000085000b4416111a000c00119014681507940300b80a110101d1500100360348a5669070740b25008580030030505903c4400c06d129510030b03071102150700d81081252509191001d014140e09005c0301c1c0f45030303844445400c650300090050321036260503400c0807441c4c041d800107004d860340c004840c11a014031440c4400c058961140c2540300840306 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 742402437 1250 742401187 742401211
    0x305010e011a07081603090311090106080f1003020307060903030905121f02090418151505061602120303010303110703021008092407020d1e03020c1c0302180603 71
    0x1c05a000e01c00980c0001c403040d6130303403001131000010078110399890f40081c5200c1e83d152061141036280c400c8030307000d08841c01c60280540c0170042c44120380001e56203411103020b0581030416542c000c002c500110366500001e4060184200018403d5004011041034911907140c0400d515142d01c140148030410381c0000b250f41c4e01550901c0040008030406018001121002501d016003c2001c00d065600341c20101003041480d40c9404c0500100c1c17074003049130040d040b000303000b0301c181ca815a0440150364021184102d000061401c1210400c00c20034921320f0b0301034200b0322250782d901c1819403240c20902c000e5020445200965110b01c40100c0d11a050341c4d4020040c0c582042000c000710b41e030351401441243c2034801c040b11181c99810a0682e05140880e07211688894600228000e04001d2510864014004c50140282c6600c50440000043e0592881c00589601040c0c1416107403601e1400c80b040c2a000c040703030b05003d240c1d054005204103c402c10805813119a998140401c80c40221142780200fa = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 742403687 1250 742402437 742402469
    0x31611032b140105090f071d06070b1e0c12012907050a02030c040606020c060a0c1401020309010c09080d081b1804060e0f010312140f0a0305010e01 65
    0x80d140722940080402244514031201e050403114012103030540b10709000d41100000400c01c510f005901a5880840128003420a08000d10041c150708a004000c1102c45101c03041c84c62662220401d40d003410340c00205100c0181045802a2078011005503d001c0c1113051000290300c1d000c546081b01d02d00b0151851840283c1c0c6001210b4251048100030a07207580d6030341c0c02c001a10081c010217480b03207034062005401c10b94400d1041525201181d0007840c060b0f801e14408110168010501200c401e005554056440c0714042c000c0340c4c03481c00c031400104188540e07516007035100c50542c0514461000140200000a0315940c00d40380140700e071003071a071540e20084160a040d403261030003a80001a15a225800248400d010748003030308141164103060003151060700701840c00340282ea00615012804001030704104c0c444403c0050140800361540f4110130740e4400d030600c2001150381e0400090012070719225081c1303c40105031700001c8139100203410031002281116160280d40d040390425000d001c0c01d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 742404937 1250 742403687 742403707
    0x7060203090c01080618060d0c0311041508070608040f0506010e0106090902120a0c090f090c090e04020d0209150a0b0307020d0f0e010e0d08070f05060109141306150305010203161103 80
    0x460001850103400038138223000030b00001c07188840c80700594070a400c04c4006139681c0d003d0008949071152100c0502d801c0d9842005110f0001c110881035460b035180c060850390320f0341071071848280d0080005185205038000010388901c0d004ea080e040c1c032a10764845400300d81c0d802d10101607015050038540900d02c03c2011413046490342d0b021110b00c00303541c01d041c0c50465403403c100440d003103542d00c0180d20589071103000049960040e003460180944940100d0a0b05103900031440385055600d0090056100b5408140302c964616403e00100f00b008080c00f0415446101c40c29180e0000c2c0c46002c054401c2d011000300e824000c50b244004100d0036540c1084415400004440c046844151203030840c0003802c0020111301c1031001003040342c2c05240070400400843c50a10310b040c105074018040d03c4d20b080007914160401003c807640200400049500700391050a080c00180000f00014860240c1c010700042000f9041d0040d6126803e80480720018001000080e140e00070035182c8250950000c1250b8124 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 742406187 1250 742404937 742404979
    0x60f031510030c020d0c150606050309011d070b091804030207150c0506060112020d050c04051009030b04060207022e0917100f0e070816050109051e1507060203090c010806 75
    0x1907c0c0582c0fa04040e00d8050880039003200c0c1250071460000e40004200460340e5000d00891389064640c11480c082408a200c1203a20340741c0c6401841c14001e00000c20705110351f640d140c086010b0580ea030003003130b0b141018a8081e46d62129407082d100c194403d12646085280925141e40c02160850040c200b6562680011549581c0065209070303042d42c248050741490034280304240c402c0e00d01c7d00946565604000c02c20600348904c9107404100401400c0500004079480c6030190407980c048405070b214280da100040000004036800710b5480889006040e6540912054102e1800716031030780044642c5030540d01d2544200c14008114692000c0710400c0040d440e40e12229050b0900140010301c03140c5c984119003416920f61140e2841e5100d24603c1c220340f545a00b2440c010030003428070110413403800001c110783d4011111480380e040b08868079407240e038030382220f10740c0100340186d4a01e580b01624074250000750026248110544188000c42016500940516006940c0108401c00302c0c4490344100c48 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 742407437 1250 742406187 742406207
    0x601033b011104030f17030702031206010203120403080601110303060a12021c120306210204020a09090606260c071218060504150804031d060f031510030c020d 70
    0x4401c0d0360303440482c1c2e482d0b40380b00090f001441c851a03105c002c01029080c000104c11003052a00c0c115401002440b04194000040f2900c15000c82d0300030380c860381d420f00142c1c114003410381e1b6030707800788623070410003080540c8503200505c0385030240c940c25903181130b400d1080c2d076a000403a090342c0c01c01100c100070301400d0011a94403c01341d1009002c1c01c103408821002c480382e110780440460726440c001141080e025010300502c4042d2546140440100d02000b01c000071a00c0100d01c0a07024980c0081c0384840175110705040c0005c0c00c03510b0310911006907200002042c0d18805107019000072502007a40d1802c0c5241d400c0280507401c2e424203903092100d191510042022001c0b40749080c0f240b4890702c410181d034000c0f41c210041005846498840b80791103810010080300360068420000d41d00304200c0081d803c20080d641030000350303014201d0200c0550101d09544980040409989404030070440310b540c2c3c0010740700301d1980555071401203209240701901910403403400c45015822091500c2c40c0c10b44a005046 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 742408687 1250 742407437 742407551
    0x3060819050327060703020303240a0501050d1d0304060201140613020c0a0c060f0f08130305030a0f0f0e0d05130308130905100905011203021b030f15060103 69
    0xc80c3d41d010940c0041d0943e4000b010450240c3c0003c41006044943c4d41d010210100b51600c02421002113a4002030b41040740380106414460085030301c086507074899000180c425080d0701180302010070000d02568a40261081740015800c11004c40004e000810301d05000b02c0700646000380210080c850748010b5007000303008644078841c00141ca000705086111003001485d0b540c403002d2500c01e080100401300d9618800c12014440b4000503c081d458001c8054038401d9003600d02280c43e6150241400c003c0c020342d04882c1c03407241c2868115000eaa00381c0d40401550382d045400c0711081d000c0d210041c3d42c03501404684400e4003d0000040011420303580042045000003400000f815807102c6030542128410340d604d15421080070340c103001000d180d00c1414003420a00c0c0008030b04982e550b800070340d1140d21006603c818614102903030865142000400d0501558500395210300340345018099000d1011141580000e04045101c92840c200144d5504a1441d401d401c1485421407403074829800308500080c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 742409937 1250 742408687 742408747
    0x2701020c0901181a010c150b0d030503060301050703050708132405091618091e03050a030501060309030c0605060d210e040b0303030402240307030608190503 69
    0x40510707503451040d20b020309030780714540d000c1c82400203a803002c40301c88010445076148064600e40d210383e0403c0001061980c420321403405219032034aa072014155080d040e40c0c0003480c605a010405030002c0c040c1d48038a406400802c006e684003181102600ea0035a00b180c045106040403500301600c0800b085205801103d400d4944050701e0705c0031b0020002c080480102c55542d070f00b4440245803d03c4603a007002d010300036485545090210310358040c1c0c21450318003040c80d9160314074010804c2b400c0e910312100711000f00580f4141c40c83e0070301500711782c403248419000912f00b1001142543c046d00c2010400e0b609541d502c800c4401540c1e90000800d80600010ba20141001c9607400098030200ca0000d1848001d402030b444020b00e6002414240030030b40c49511940c281218a50561800030540c0d90260b01142d0490100400716000200400400b4030904098800030405c0042034154000c48121a001c204907402968240030300c040d031854424000342507400800411840301c0114164100d0b001c0b1810354 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 742411187 1250 742409937 742409953
    0x60b0a1d0906040c0b160506010e070224070509040e032808010e0105101107060e1903150b0a030f060606080711150a020c0109060e06010609030506010b1b01020a0305011a270102 78
    0xc0c03546441d03401d0741b02d0000340713030503000b04501c642d07050041e42031603ca4dc02040c0641c4846521803200c40c1c0700200f85e41e08000d004142a5400d80c0c850304502d00c0b255000c2e094030754405490414100e45090184001ca0180901c0b0031035418070b10034008181214424800b11000b030342403104100fa01c495042c1c0482c1044400b590700c05402000340524402000b40d034540b14070304001d4500380000e140765241e03982ca04018400d8204081540c0d800d0200001e200031030000342d117064039000903001c0d1459403c06890480f09006c80810482140d20020507501141c071500801c0c0d995090481e61150a68420b681e02d4010b0703580380518003540c2003010382005001501504216408402a0845d103006006855883d1101c85d50041600c0500c115070150106180004605096072261613070740c2010311545c40825800200c40141307104040303070f00982044010080d559404070080c000d0142c41c080c0941c02020480134080c0c42114801c20807105802d481060074040e1100340038070410341d01514012241940280d420b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 742412437 1250 742411187 742411193
    0x10b070206180909060a060609080606040f0204080d03020309010513020f0409032714190303050a05090607051011191103040801060e0708240409060b0a1d0906040c0b16 74
    0x11500c0d1284450000600c0c00b41ba1581c1a50251074a0742c0c0840300340100c0007400d0148240c041380c0304c0d512001c259401701d401c045d030f01b01000081c4915030140c481c0d0700480340726240300c1798160005d40c0186c22140081c000c6841c6d50501f030003490800f090007036100061000380c11041c02c00b908504540ca00030300740900102010012340301910b014800c0d959a500140301c080c054840b0905120440c44d43c151030400345000703ca1401c40c001e809034000901800303802304247d105035114504a13006420080d0115407624000e02e00140e0310740c900c1031041201e6080900c85601070f0fa501c0180c1e050740140c0a210310703003d0001002034907808030389031501926000070040815131400c240a85002080030036111840c45c034081030003c082250140c2954183e02080703281205112044c015103040c1c00c41100d002422484e07610701040280909041181c002407101c100084540c04490460310303c2c080203e20710304690341d4204181d1100c108840091100143d20000d02c15210f8901c05071548142d1020003103030f0000036407 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 742413687 1250 742412437 742412449
    0x60c0c2601050a0e0604241d06070c2a050d03050c070806040305071e150509070914070309170309071401050c1b0411070503040608010806010b07020618 67
    0x3003842800903aa1003541100c0091240c282c1c4458000790401c1144203500001c1e48600019202420200c0c0d240c550403146034152520090984801a00b08420a64104d20b0480e440e0310f14500e6105024500000d41100d000d840004c0c107180d03203c2000704001107400c64580317921713000300c002c5a400382c4030900c08600c68403161510340035180280c40d000c0d10b540c07200342018500318164100000d00c1c1c1019092100190304070341511207035503020b5282c95141007040022144e08490300c1000e000308c64011105202d440703942e4481c80c001e0008009483c80c583d15800c54400780c0f025100442c3c0c1a008a000203440113220390f22071900300c0d10416001303c000c9400e0090440540094801406980091808118070041030184000c482c1d02801e1240c1040c43ca0700348030792101460960200c050754104166201980c840d070084074292036404682d078803117145041440c0c0d06e0b040781c003030170340459030070400400d11500c0028246d04841c81c06462500d0501030f1303400d0203807541043c055041e2041244000b1080c5903105 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 742414937 1250 742413687 742413719
    0xc011418034c0203060d0807230a150f0b060f0901020c010c030e100509190503160f03110f13020a030b061e210106020a120e0901060c0c 60
    0x11201d0341d100c104964a64212000c0d4901910b482c08140036680c1000d841c00d00e0b0071800d601c1ca0300801601c03030355800003243c020340304030000030040640048d1900c1001508003c1141c002c1c0310810010780b4140085425640d03416a0700c018001101c1c00c1d18180301c0420681000c40c5106500d0740c0070039082c6c805008100e8580207007400520348100415495200d59041080300d1307508500346000c000100046d2130142c60f80e0540c0c00031502680c0b19a400d0542e090080d400c8401c4d03684040c061034007103003005811046003c01406011f00c07038094020075419100c02c074a4202700f9109450b00f00900705180d40d507281e075103c0703078240055008030700194000b02d1039594103145002c1e000c00e1880581e4442050344020221480541d900d880b45d0001d00182c00c040a000d40400e07a01c10456280c69070f51490101d00c00c1600480c48540100341160b00004a00d0545c0843c00c1c0303203601c0c0305a000c85448250210240e912990200440d07070025208030040000c01d1042800c0201e59001e108800d0185842b600c11412140f60 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 742416187 1250 742414937 742414963
    0x90301020f1803060601120b0406030803160e0904032c040906050411220e0327030d0206220201030b0901080115050d080f030c040806040309050406080c01141803 71
    0x1002c41d1960800080290194641c035080340540041c3c54500f001038401f0664804640d45a940d902e0a00907940f00c51740081c000d1904581d4a9442e0301d094450080303031604070000d61001070711120b400c03da181455010300d80690340c16216180360030b030060f00020081d03484410b04515810154055020b41d03c4600c94a00d0f9a40182c40c04100362400d800c019548103c0592214041c0f120b1054108441c035820302e10030a050b044a001065040c2075410181c9103015441c400400e80701d15141d00f8170701080c2403416800c0301e202034040d502454811a401e0f40c9840e41107031803444040c09e00f00700c2c00d4908100cd80c500111403050500003641e20781e410205e50301d29800d0700304c502540e64030b800020101600b041900d00801c4c1c03c07506c024004155a076520001e015210071070500e18808408142c00e40b8401090720060041581241c2452815080c01080c41c5150700c5020f01480c9801c3d0b0108800c24042102c113510803041e100d10000414014200d12a50301002c0c904455448030600d0b00c60583d41841542c0040360 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 742417437 1250 742416187 742416217
    0x30c0403030914100e0a030b090a05010605100c06150305060906061c05070509130206070305180904111003110f07140a05061f12030f0815031e0309030102 68
    0x2040d85406021140190440718019905485801803941c0380e0b60610b21903080c0340707018121640e22a020071401801500002c10340500c2c6010403206640008a040c141406600280241d940d81c10510911512400c0100c0c00601c0b000c0002021410a82000d03d0301a01d0346051070718156030b40c413642d08160f0255810000b2350030801c20b00100f440e101100e280d034410100066880600c00da500d1303d98901442c803c0c0c03806103040000003411a004460600002a0013502c41a40d0756000e10b0010f010354442c0c911740d070b10801074010582c001d0504203035440c0300c0c691121804902003440302c10840f01c5011070030f000d420542c07140184d000281613030340038005c079009441c0007035120741552500c040d00007185110800280e10441c1c00d0008a100001c00300d8100091203039039541301d0300304800c5031301c1084030384c0040000e00b880d501c44004050340315110940100c803580e41c180d0a51195545041c0e8264600341d0700e035042d03003d04045d0042d410000d007200208005030b82200c0c9060400d0020900b6038100e84030400302c0c6c0c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 742418687 1250 742417437 742417439
    0x31b07031101140105031509031306050a1b02090402090402031c030b0f030a0b010b0c0a08040e01060305061f0e011e090501020d0513180b0a0b04080d05071a0714030c04 74
    0x30200340180c940200715000070f82a298100408039035607150500080c801591402d011607000d007800d200302c40c0f4071020b00d50411503040d01d860018005a203e110034800252106072484030050f849034070f2054042d40140403490940316502000b00c0c118000d041a64180600075208142d00030301200403901d4184c945010aa4540200c200040004001802d41c082c0d000504003d00143c1e0300d002c154151045141d0064071685621501490032000d2100240b01d5480064080349030002e01824504880196809104c956500810300541c41207688580310030320a039090340e0b000c01d070240340001007402040c0341608881c8100510800741d5900c480c822400310311100340500444d40d0610400310700c01400e0a120345403c401c0300c0c03070700c0c00580280304440f50310400b02c1c0c12100180b401c0d003000da0801c3c402001607800945600c00b640c0b4a5015100b0300d0304034030621303000400040c0550182c0344031130303080590200600b00c0c501140c20148002007001040001c1b944c0000c05401c0540044c41c01201071103103454a40b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 742419937 1250 742418687 742418717
    0x20909190606050304080a180e04060f0501120c06050d1509091403120f0417120109061205060f0618070e0a0e0121032015060f01090b031b0703 63
    0x1d07907040d0050700c00c122040003041301080b4030500700c0b0b5284072585440c2e40fa4030111421281c04a4403a00715400c16000354080c0010701c100c54001c8130300580c0701001040607036a140820045100258001440340454000c1000014041c801a1242c4c9200b00c001040d03005400480c55600c0005402121710296203120704000d200724891520000c000030402180b8110126503910b900c0c0f00010603a144900e80d18000500300810001030a00d48a81007540039102d01c20703ca6040f422000074050783c80403d1910100050000c0031201d00303858541c01001130314954441c000303040076041000b004181c01034160398120105401c6002828480c00300b82c0d0320940410701c00810420070303480a41c031050f0007503032000040c400211007411500000c0d4400710f682050345502e140544003c24036410181d0445901e40707818841c10320202e203144908001d80f45100403590342000304000509084040340c0000e103076800c14040b1300c00480045401942c0d5600200381e10304400d01c1e06050350701c40306080380002c0c4014916905 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 742421187 1250 742419937 742419941
    0x1b04151e0e060d0b0415060f02060f100b0904020702062106040501030809010e0f03010c1206080601080d2601030f0b070809191a090102070309060c050d080a02090919 73
    0x120450600d031501c00600c802001070200c0c0a880091103505981303512461441d91164400b030030031000c2110038500581e4801c006400285c0c22034280000d8080c1800003802c44a04041c1544200100c00d0030100e0700307051100303c2c0c0864002800c0644c11a90070001340001d40e840002a00e1f4450503145001644410fa03408600c400380d000e04840d01960800e801880010825000d41e9214036080c079142041d03031301c0080000c00700c407014105141c0551038805c1404045a10802820030055070700014810950303030b409015911b407024070808203117400404556154512942d2403213502030b2038150380c560348960b60b9610710840c03c1c00e81c4115008008002d011041103004651150b0201e03403810028483d00e8034040c09621809801c44242c041c0781d1049100f020410b001200301c19031841a880c0d400145410401d0b54000d62100005801180b603078280060b48503c51580f011070b9903480009800040d45480080d90f00c130703401425488100350240302000040d210500101e104110003a000389403a5250340400302 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 742422437 1250 742421187 742421237
    0xc06040807051c051c0c020a14010e0a0f030320011806061203081816120507150e04050403090506160201030f180b040305070f06060504231b0415 64
    0x19001841e00400c0224501207100c01d00a40c030b0000406005c00d8488049030700485040c0003d42c001611000411400305d1840d00060105081c0c0720203410301c0c04801000f0b005d2600780f00d904022070a0700c02c1030000034410210b410303000c0d244140845c142031003400d40f98290784503502c50013075101c1a640c14109201060052400602c0c10340303651030941115440c02490000000c008507010000400d03044900d400810410351001e0b081050101c010b5114425443d64944202d01a59036110b516404070303602c40070240b20900014140c07a07401540010100380b20141500900660034410303400307800100c0c2e484130700003011030030200302008102080f14400502280d00703000709580340c6490014a65241820301000a01082d0410407540c83c0340e0795407600700c40354030600d40e000b0f080c610501040c03020002682c110000355142141d00344002d161322810789280c0f50078018500036090b05107000c206003a130403000305441c03100d41058039494152148203d41107202e80e10b800c5800210b12451142d00c054210b40c90103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 742423687 1250 742422437 742422469
    0xc0c06091409100902040305150a02030906160302090901080a0605010e13021207080d05181005030a090201031b09140904170a03060306180320030301170c0604080705 73
    0x11030150a00300d1000e0303804100e100050140d5482c601291281048035828801401c1a07001551348603124640581c84610000c5819110f8088102040c003090307480c000d980c89803048a0040070303555580c610940c6481180000882403503801c0002d00002d8603000c00b064043c2c0701c150014440c003e2903103005011208141d001c8120b0a04000034080f03034400004040e25500e4045801d00100c01000401509208103075002410034428401d40030403041d00000680041d613a207449010341e200042c0180b1015100c100b82d0000020010000113400540381d60000001c1c90061500044102021424400d9480c40d2155200800c000000070000c25040c034400d11040e50080d40c0c02452403c1c03d50340c07024602c2207080c0e00d0020580120760140c03080d00c02c2d4840e00003550004400d021045d1070300a101c1c40351840600540015222803590401b003e81181e4810400103c0703002945140e20300b10210710b1522140902a915010794054a00196102030140000d000e03001c0242c540e451501007040a41c82c0456840 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 742424937 1250 742423687 742423697
    0x50f060111010603230111030a0b0310140403030f1e2c06131b031a0106030b0a0b0c010f0516031d030307050d060302180703060f03240b0a03030c0c06 66
    0x84c800a00440c0907140040840c805407000c40c0074903d0010b025019000d0b0260703502c1004070070030011b02c046801c8100790100c20350903248062034810321042501c240f09210340b6481103d4000c940002c2c406d0f40919950754105500040d41c00d501034800c41d80f03450310021081c0c035a84511850320b003502181910300d00700340d04100214294400c403d0b46511124010b2000400d000d0a81014061108285001110700038a038000e086503612444d058603510143e0103400d20303440a1400200e4032134007903c9550340d0100028448c060452400d400c0d102d240d0300030310750078500c0d5482c0c4c0003011044400d4018280142d80d0040c0740380322103808000c01800c0310102c1d20005000c41f40781860380202a008411a60007034114507006554074401c0c90003c020300407a0344003d410070742c0f0000000305072000140c0103000d4282541d0501c5866990103d840e640003060001405042c02049208141640300d89048811140d4940100c0c14140003000142e4007006580b00380d0200301410080b008000a00c84031402801c120706017 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 742426187 1250 742424937 742424939
    0xd0c0608010f05091f03050609060f010b2b020c03040b09090601030b100e040b0d060203090d090518041106070f1401091104181403090108100605030c1c050f0601110106 74
    0x2545040c40601044007400400c0b24403000c40342c1c0b1729120340c09584c1250444030b1904212800c90341c0e81c82c00b110140a51100c0d003001080d240360410864000080e0a50642e0084144031500100540100764403e84a60308204419104200344007038002130125100030750b00d60540c803091040070103004180074101890410b00c00300a80c3d80b0303000c11800d84214a41740210b04255400f05000380004009a07910915900d00305040001c260011449131500f00c0c2a0f40514036620000da4070040140500382d480441c86555014117402120314540c0503000304100039001e00c0d4080410619800310b04c041d1600c00c2901c001d001481801070a400d001c0a02030300030050308604da101c880558808603521403140303859064040d107291060070a0180c0507044030700c08143d140001c4e0b00c590340ea48514141740c0070602d26000160300c0780d1003416490440381c50b902c40c2440e640d210040302c540c42d880404400c0d1841c21038500100f00b02034a11480d8840d0a516003441020b040c1380340054407103a42c0b1048000c95a040100c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 742427437 1250 742426187 742426189
    0xe0d05100f180b0c071a0c0d290607080f0f0705120307120e011d010204050a0e04080a0e0a091b2703020909030c1b2e080a09020d0c0608010f05 63
    0x9034804031244d04651200c1142c5000d03031035540b4190010a60420f88401d000c0c42c0305001e0b0040100c0a450350b01081507440c50b40d20411211000c0b44800850311034401882040d09100000301290b0b88600c0c034081c5020100045034000742c00c500c401040f0001c1c0412504d04201d4204200c1100c0c00c111101c440c02c40c9172020008201640a48003d00b003107440d501c412016144c250084401c503071130b55a4150f00d401030707000001e00030f42080c0b09981c4903010514000408101d419070940c0220b800039062450240076080c19104851018002a007002580c400000c964603035110b80301031103001c0d04620000101c9810002c0c100d18180445407600f507492803d036841e6508405510044a43c1034820287c0d541d64221050f00318060905000305c64003411080300030a000200b110000110300711403107050005154400c0902024120003040203884c003c000c2c860b020b0007450110341c8180320100204111500e94003081070003207825002c4815124001041c0030701c580041405026110540e00700c81071a01c4d101c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 742428687 1250 742427437 742427453
    0x10807081603091e030c02040b1203030408160f05030d0b060c0a02040510090f051617070e060702100302030f061002120d090b07200307120e0d05100f18 67
    0x79606006040c2d440c402c050411008040180740d60710001c0c0210303c1c81440e410090a154003002d412445030740750484da06040d1a244185500c01044c000055086030340e142d8a0700c1c5c0300d502002d100c00e03180e01541c0c013810004801800c2000380502c00d6019540b100c502d510031206460381341100521802080c400b4400c2c455000440188403501128045004d07115000425900042600008001030400584020661840d000207026a0030400c002d401111a007500b2541c1484901c2d4034480842500041078200b0311403110004907010040c43d00c1d03d8425150f00141c0002c51040d81880400d40100400c00c0e00c00e5a5400103600203029242c2b80d108106900f0000d464112071000075031101004030b50340d66840b070107921810229130700800200640c1000c0401800c48011500441000e100c008101464007070044283c902440c1c0c48100440783d010042020f661503031855610f1500030307442d041004080b4070100034a00e40c10340041d0000030004e0240d40702c28140d410005003c151032650524040014a5030f03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 742429937 1250 742428687 742428721
    0xe0309101706043e0c03131e03080d0b060d06080f120f0d061802040806010f080d0e01050d1b0207050102150a0506010c08030c03010e011203081801020405040e030901080708 76
    0x90034085211400c2c015810181403071300760000d04010541103000500000140a0b5915000c0c5c0f10901c0c0e55204980003400c0301b001d500e1b41c01c0e1041204100009030303a003802361103604d8010f800442c002d072217a40130034551780200304100310442d1600000c10000a017805003452051210001c2d2600200041341504c0a104174011342000c6240010506166001d035032045002e4000400c1580d040310894860b90040e40040c06030607124002d1000000760582602152030860300001d0292800610600c01030711a101041c4045050010401c1001c0702401d042c0f003041e00700c800d414003d103080070b81c00c0302c02440c1820f06e030807841c10341d440a9101360b00400540300d4941d025083d82c802103415030320f00004941410003414018140c0201105102006038040c01841c1aa10210b405180980e40d0b4132240c09942880740024001c01d10800c0814103028011034085403024028002503e410740e1480468101c0d0106186a14130340c201090030403056901509050b00701c0340728070b054029801c01a044403204201 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 742431187 1250 742429937 742429991
    0x606010f05180616050d0f120203061302072d0203030d11070506190b01050a08060f060c0a08040e0a05040506010b07061104060c03020106150906030e030910170604 72
    0x1c5102c101c0c40302c900340200c0c82d000c07014104603101c1103440400a42c2c0f00703024070215868092525100300c0144140d4803082e03a1007480e510502c00e81e07051013807800207601c0580b0054020f840d0040c0c0a10100d900e000400a80e442080000190f0310240c003078401520040301c003401226400d90350040580e0307002040d108001001000080c0000e504407400300544900c03840100a40034400400c80d2030003504044034000403403403c0501c241f1100c0001100d4078031075040c091002c41d2800f00801c10f24100311100c02d41108018010724500341e114501c0c14646103070400300706c901382c1c400202802918491720600e50080749584e403c1c4160b080c6a43ea407600c8003414001d50841d00b00124040c1c040c001c00380c000034032a0001400300d0b969180c45000080c040c24800100f600503600707046000511500031500080c0071280b0f40d45202c010f5007440401c07000380421800c3c0d604144001d1050640f0355035001076140105109480341980c010000302c1880700e1900c020300b0188518540304c0e4040750000c04488182c0b45880c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 742432437 1250 742431187 742431197
    0x90303062d0d080a02070f0b0712020a0203070f03020f040501030503071502070c0303030c021c1e23121008030f0307110604111302090f2101050a140106020606010f 72
    0x41541d81c462803010108420950001650709414180129900108005501c0c0e40c242c0c0c04103501c0d180c4290904800d4821086042c0c002c0140e000468403440c0c00c80b000f20605d01c1920300c90303403240d0002840c1800942020444c5901d1603010000c500d040c4452101203003095800340410f62464503121307100d00401d00040c1035403029241d0400040d40d5a41101d0a0f00d03030111606c1945602c81c00c1c000c0061450420f07180140c420301201c2c20a4a80240b41201003441e01e13a00c100100102da84140107860319912070b1802d03c1400810307007503072104201103940d80d07000d400021900c3c0c01440e80d41000d5547c000d004500003200341c00c414019050003004a4a80c0c0010f07801c100e6503038403a11300454a28180f40e259201c1c0380150400d10040003611302c95010102d00c00c80b00c80900400c65034207681240700340c41c0d90591003445000301001d1801d0072051822441e01c405060302c0344285040c041425210102d135146001c0355078001520750071403042c01707040c05040309100808540c034102c40082d1801d4040c0f00d6010030300c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 742433687 1250 742432437 742432489
    0x40f230121020d0605010f05070c03020111070e010902130b040806150a03020d1103010b0f09010e0a0905030307030227032a0d1b150f0c080d022109030306 68
    0x4544070390903800000c402800c558903102c1d40a20f2000302024001e641c0001d25986440d513134540f05800750340700182c0011181d42414910f50040d039002030510366107000343c080e2030000501c0030404e6030081c1c0245031040b40940c0e1501c01d0350f95022001107640094420000611051015a6000401c2c0c2d50100050f004000c041c0304060000f05480c1c0b0700e03407000b580800d50301141800c100350380d10a000b04000030380090101c00b41e00c0003000b0808900300031007508001e9500c010824178604401c500c0e00700c0c00136100012070747c4041d01c8031411a0310842e085800320740c0006e15101a0000030603008180b00f0001e541207072103030041000035224581c01881313010803030001c84003101c06008484904aa10001041c00110416a21b018074001051a5006840344c1002e10b000464500c1d1034294203139008581d9801483e610b15480581d00c849600005680180d0306005030903134004544010701c42d0b200310404010310a564240e810240e0400200031401603081401400a66143c44903c10820400013821254034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 742434937 1250 742433687 742433717
    0x101e080910020c010f200a2006091e0127030e1207230108011206060504050117213109020421030203070206071a0c040f2301 55
    0x1194445001c10380340c600c000f512160b03401055112604000d5051002e00000d00d01d00c0c3c100c14081d0208200c03074024201044140686446040d984110400d18518101c400b80854070305468000d00712500e21841d44108555a0644a00003240c54602114070081c060102400500704496851071f840d44e4501c40000c00e2141014042c850300f0052074800713812940740110f50300001d6503505d1284180007010903140e5082000720341e080c90311141d550060711100c281c1c0e4644100301c0c202c92040007080d40d101c5c0e5600b502013140c1e621405810300820100b01081020441c080606003080302c0602e0382e8401f90341c40c0340d048004141c403505071342c5105940703032030111005000201050703002e503004d0f0f135489007480038440410192020f5001e0010303140d100b00d10300c0b0102100c0041c030b42900c2c0060310250250b40140156401031500800614a042c400c001e52540704650307904900c0c1001040d1044905424042024888401920700b62401000040c0c42c01c0000d605448140c0c0c42550040150346c104901146500c0708 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 742436187 1250 742434937 742434943
    0xb0303070501050a0b12070509070807051306021506120d08060111070b180307060903020906040906020a030903030b011b060c0504080d0c03081605030a0c021207060b101e0809 77
    0x8200c0c1c11030028002890100c904c1001424600341462140603010541e001c100000240c0c202a10380141c00000c654503401403d07506808004c01311001c02500304640c41500071174602030801416250010a800c20210b40c00410f0000024081402100310308a600074507940016600c15800032401c045070305031120b00040300c10b04c581200085062141d20300005450b5000e00c010038041100001b41010383c5803030410503840d141c203481908005800d1941c10320140c50005480741d04004018800070b410703050740e81c2d642c080e81c01217008e0002107990340400800349501b42c010715111402c2440d024200d0f1104a4007101034150302d81001e03160303e41c1c601040820502034030840d8007500403c000c9842c40b03442c127940208074105402040700000c55510114800110400d4103041c40f013401e0315541e00355615040d0344d030010122440e00c0b00441c8030f12000000c01e0481c210040804500442000c01d0700c1d020642445940002c0d40710707030b80c01c01c640552031008411009240900c884580c0c90184010f48645800500d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 742437437 1250 742436187 742436197
    0x603061012061d090724051b030909090601051c0503090a0b04170105060d060e0703080a120b0d030203030601110c0604060f1211040902070c120b0414030304020f040b0303 75
    0x300d8503282c004045070002841a24030b4503885000c21080069650916460701d8000500c21040074200f05c0c4040411000d4401020150300700702d1805c503080c03038080781c640714800c1e644001c0000c2c1504001520403180c209204002e0b030000c0003000070500e6516180c08076076140c51403407080c424295440c0c40d59040010900460b1b60503c0e0003802400034503103440602080354001d10038905a00751240c00300c0240103040c080e01e446028000c221102c10100c40d00d0304c00140101301c500b01418000c0010100004440300b000e0414240c031030f515844150888448103017260300c08814544100c03050303404c0d0000254000116030703008d5400e190004c6d03022403813090140380481d0084d50036800b003400314000c80c0607903005003101d201b4501e40e42c86445c88a007880c0d5003402c82d1050554500780f144104001e100c40b00ca540c00902c64540724901800d490ba40e03490b181d254521010a045030640b8082c401c5c001440b50b075000c01c0251152440246103941000e45c00610198001c4501c0c1c2d00a940b501100b000a94060042d10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 742438687 1250 742437437 742437467
    0x403060c021f0b0f100201020d0e01020901030e0c090c16060c0e0a09090309290c0109030e030d05031b04090c020f190b0426040b030118050606030610 66
    0x80024081054007035110841c0d08610241020b0441d90740b25405000c0c02241e03040032000d0844c0f914040c200c024440100c204504c44015503408001d0320075144450f1049030059511340380016101d010110005050300e404071040222640b110560450700c1e0f85040a25800030920b01c0030558803071140408407501d940750b15003e0311040c40c2201129410750044101442254100c5a4498498584501504413002c000018000942603c41804001c080e0801421450448038419400000c0402e04015940c801d00103411141d441e0220700d010550401d000c0c0301a00403c50243c00c95020701c1000405502000f80001001c602c0300044594050744e0340112030142100031001e01c4908190000a5954018a03120302c005101d00010b05907020301302141d040d42680d2008255a5580301c9482c1e003a18030400582181a400321400c800c1d1100c42e00748024801018500319464503036150100c2c000f8881e00e100d1042e1006c80c28042080965902c500480b940710b001220303070302e404008d0014100d031004d20821201c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 742439937 1250 742438687 742438691
    0x29040b0a0b071a090a020108091c0c0605090102190f03020d230c0c0d0309020a0512070806060f01091e0e15030106080d05190c211814040c0302040306 66
    0x841c5072050100100100380c000c9034092202080c412103044000300031100846075400102e00383d0300541c41001029000b100c030404803850303118407000c11745c90b00302060180750104001d030598000300070301030103040d030321a1403031008600b0148442035041004400b10411020404c080803000d00b003a01990560b40f120390300003004c114040d1012140b0140b600d8a107200420b901181c0c0024405440c1081202c1d01c90b513854003e01003a15a1642c00d4025007a00c64040364061341c0c21102140b0b5850301d00300b078446250440b005160903868401d2260810720b0181c0207600882003048cc00d942d50341c100000d00d044514002c1c0201034903000154803110a107085c0c1080351845240d1051140d10340c4451640d19001100b200200072056941000302d940340403a00700390000c030310203005e5101c5c2c01801c2c2403074a2004200b8108041200c0c03013543c03004541d007080c2082111598042440900302c5604c0a43c8601443c0350640f41c1d990340382011400d440640c45000000c1c825522443c0e001c070141d20a806490040d9030282003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 742441187 1250 742439937 742439939
    0x703030e01080a1e0b12070501050a050c0721031d180c120907060f02010203040f0231022106030a1209050319290106030207060e031b0c030129040b0a 66
    0x1302c40035100200c5254411400c4020700c4a4601002c140f01048490503110315152001610381901d15820a80e041074040c001c0c20b4000903069840d0f094040c1c1c1402e030045126400381c4078036000c0c00e05526140c1d01890f817480908086215200d80c210304048041401d1500c00c19135030103c60242c0c1303200d607039240c0035254684028130000207400140308060f543c15484207400070300342c210120708034002250041c0404403001d1910026040401114889505000030320010384c0040c40f1080705102440308440040c0c3d4000b8001100c180701150000c005010a40c101040b0300344a40040c0d40c41d04840005800340c80c0d84104050028007440e080402894041c0554984c1c45074042e20070120449850291a545242d880c00c40c5a009200001083c07840b0b42c58150800e41d0070503a007140250020b0300d040b6103143d030312800746811102c10005031040e007020035281d0300083e004150640c200742543d00060301980c1440c004581410000507449200f4501d18540031340071001070001000340c464900759039042406480 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 742442437 1250 742441187 742441241
    0x61a03010e060d0f0318080c01120902010908060117190506151906020f010f0912050a03060504050108010504030f0e06070209060d06110a1e050a0f030b03120405120703030e01080a 79
    0x10a103d144c20440900d034000981d54050281c0390650500321714002140980d5441400000f540302004be03038018902054256201e000041c6098400e070081502081881c140403c519001c00c41d0840b158403142c070071003880143e5501c0d00d0703651002078007112840c600700341c01800c26100d18040c0343e840035a81ca10910840d90f141c501035200e540c0d0708403050055003007a800e003000b0420f80c0101504968080c6500382264040c000c204d0342034103c00303003170010140c5960780000c49646500419010f0041c01c40009074505045c90040c08003000307428800103018410409807101e1b5207076800d89502320780642e50318030182d80e00303c0040e800c8018488000c103c0b074501428032065009031070107010300e01050f44918100c030b81541818100700c0b50f40031510f80099410043e5114162080800035400758175403d002c20b440303140000080c280105540c1c40c0e00302c0c070300100d02004540b0389102034030b4a01d10f510015101d07003401c54070300130160020064050b051200000209011041c1503105201318685900c00020340500308c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 742443687 1250 742442437 742442447
    0x1b0501110d0e0a1106210103110f010807120914010c020a030834051c05060a321809011a060310090513170a03061a03010e060d0f03 58
    0x4079401c500c1e02d0050101c40c62040080c10014040d0003140c8082c3e00c000c50010001a6440400d205120480407400600b00329510060603000c0d52003010010754503d4a80c060000d00c1103031520780c904101480040c0000103401c81c201500c202030305032002c03441c00964103082c048101c0051032280550303c3d12a40341002c0f50301140d80310301144207a41c0c040007522a0442c80e0103113009046940c07600c000c1e12104694071190000b01d0303410031500e424014109516104101901502103099001ca10345a00c1000720901c1d02a480c0d40241822401e003107080700030307462040c241800481440410b01a082500b0110b80d03968261030000c980c034110a2290f074980441e0281c0a80048500e5080f0f50302960804419883c0a1080c0c0f032081c1c511702c8400015625000d2420041d00002d04042d43c0038030707480010400319840c1c030034000310021048101562072003084001802c45410b0761020741224200010000c6e040247c80c122411594039001a0500d600d0300d05c00111841c40510000b04100802c90b02e000c1010303004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 742444937 1250 742443687 742443697
    0xc02090c04150206040510050a0b030307050703061d0c1302070b09010c1706060904050c090d050c0f0301150e060103020d061401020c01111f02130e011802070c03031b050111 76
    0x4040803a100070800c034140d84e120342c15a401445504444a0800c440d030650340980c2e40b05018507000300300420604c000c00d003550310161094901ea0060a020f03c140480d5000d49a145c0348050820400b605490015640b105000c8039601d02c2a2000060f590689000740c055800c100c3d00710382d180340a800d003032548900900ea60030084020a2440d2032040c40c0e4055a80c00d82c1c031a41c006020649452948030402000304001024414801f1080c03080b00e19648072180c169202902c01c4009001c1c0c000420100800b0030f03400c14031903200303a040c01c4880e071004000b890f09070210303081c0d2114169552103040c0164064040d002440e261589054000034a00c0c08419841d04004400c0e020f45080d1144a001100c100707001c2e08500629500c01411040c0d442c0c00c8181024a0100c0700d600141418007140341c20001c00915400315140c954000010b0141c01011003807103107000034203441145001030603560b00301d11510031701c000707002c0c00781c841036224400e24000c41c0414580e520000800c030302d81d03034850503400716000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 742446043 1106 742444937 742444949
    0xc1c0903080c0a1403070506090604050d0f030e010903052104120e1906110708010515010c11040504080d060506040f15051201060234090c0c02090c04 66
    0x1e104c00300880418100c040d550306c0c4401d0401e6460300102800c0744159812100c244000150006104006460300b402c00e10020305a40c0310640082454100c0526694280204c540800d07502a0060a0900d0100701805420660f0900c440b801c00c4115401002c0003071084400c0340007405441c1407034040704001c01c80d040c20440d0702d5002040c1c582c070768482804501e45104a540c40c1c070040c4029030140c001c100080126140601c9148681c00170400030606000c1c0740000700c414412125061b404074400680f00b4011814146010030072039000e010703000322440c5410404207080c81e215040764121804007400420450604d8000114225241144001e1210070800341a0a581031240a4000d02c610b801030403030000352440700da51a14450586c071021400340103005440c500e04007203580a407102080c00007051a440c0e841030318080e1400002235802402001082084a205002441601d00d = true := by decide +kernel

theorem cover : BRFrame.Cov 742266187 742446043 := by
  have h0 := BRFrame.cov_init 742266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 742266187 ≤ n) (h2 : n < 742446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
