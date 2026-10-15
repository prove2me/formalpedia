-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5022
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:29:11.51521+00:00
-- url     : https://prove2.me/submissions/858b2699-65fc-4900-b201-a5b8ffffa7bc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 903057553 ≤ n < 903237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 903058803 1250 903057553 903057581
    0x100f0e190b0a0806010e1b120603031608030915041a070909020409022205010504030b1005060a17160e0d140634020a1b1a030a0b12120c010e10 63
    0x2980e00e421b0303c7d9004200001c0e0307104440c94104114108000c9046030150840341c01001d6914001e0447c540c003400c0008034000b03413107020001080c8004141c0400520207104041e9007505140d14241e00c8081c06040c2441000000e48036100001d00c52520a940e040060400f1803c04c540b01c0b41c440c0b030000025008451a9000340c01000f00561038000d0b0b1107841401c0b00c00507582e107441c042c1580e84110900320042d040381c04c489034a180111b610750350f01000d040031441c01e40e641181074000501d16205800050001c000c0c01c1d08441c0c03887c00d003560143c0b4402c2200000c0d500c240d0799074118030780394454080d0408078100c14000c09040c000002c280e1480c4035038445050220700308110f07018040c90700b003844960100002d079000d0741d006400180100c20710b011608040c030301410581e03a10042030b22250306031195101c10706400002c204c00c9508034031074004003210544896a50034440c0d02815030765920f951070000c8861003c02c1c48a410102508088a03409005068401c90020140818040d01e045d5211141c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 903060053 1250 903058803 903058829
    0x8060f0108092a0a030506060118080a0807032d02210315010c150203040c09140a0e07090603050a0c06020d080a0b060f070b100f0e190b0a080601 64
    0x19803103010900e000d440d0715030241c00400903007110141c0a0365920080c40c011020f0a6400900c1e41d50900404011405000544803900c1d00c070b0001841d0b000044134500a40b1a55013062028510000d40e0308207140c1d0240340541d9480c140d00307050b54105007040080c1d03d441501c21030710300e0b1040165200b24100f811078007101c200c3c0b41c0c001180c8202c2c2c00814400a6580d07000e20004010032207001c0c3e102c5045d01c06040c10302440311282c880380400b40388140c59202998001081c0001c004c40e03500030400804100c0e0301000300b128200044000c1200151451015507104c5402d04e083d500d0500034000104101041000b0b200c4e900c0c41e299072905030392070302074601c490000700008800e4008a4044c020b10309641c0c41e400c065445165010052542250303c0d030b0030803014880120424036482c000e060050190004804a241c81020003446049a0b00321032522a41781d841000400e0902d505c141d08104060203a8455000218407500203000b600e2403030b41d0280112074005100c2c01d02041180c169900015600 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 903061303 1250 903060053 903060079
    0x105040b13030210050a1706180103060b09100b07110a090905011a0a03120804080d050c07120e01020a02040f2307090f0605071b0b031806060a0e1f030b04030806 71
    0x1d45e06000d1801c90b07802103040c91541c0390f0200d008042c200c3d4003100c02442c0301081c200404104240810903041140e090341e031009008254507080e4000d59225010754407aa03041418001e03159224019500002c00c06071003512445081e5130350347d003550b024203038542080104894504009018060b106c2c4d41818804001c40080004c5c2400001c0300c043c0d9400114102198400c43c80c02c82d603019004000b41c9141c2c8080c40408510b081d070f0300a45014500b41458207031203101c02d041c5403481d2800d1804890521025608840c42c69801081c41c0c4161501110001801408214000040c158400e842401104407980034101e8100d035400307060103504036590307620700c0e15100e50544064540f14006d48010176014000c5400003014404509480e40711901c0f034070886e40e030724102c904694005981e1450f08080850202c1c2005204019181e13014104481070042d2602e8905194500f1201404200384c0d04540d8140703003043c41040880310011984840004105d19080c02c0041113404191800c07440b0700300d004596 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 903062553 1250 903061303 903061307
    0x80604061703090f06030c0307050a0c020907030606020c0111300c03130902040e04061e0603111003020301050a03230d030516020c0f0609010e0316080c03070b09040504020105040b13030210 83
    0x1b60f4814640e15540524549640d582952260409102081000003841c0180c005880b80074007140220359640f070100d00b25060000290601988043d0981000008021404100e00000c2d0342840c03c0500a00300300c1c0644c0d4130503404a43c00002407821342c4403400140c4010300038000801010000c101d0701113540c0d166140c0c00d080060f0b00c03c91007032486140c4083c01003400300f8520ba01204000d035200303004007a440085144c600513104039a1013507072402c142c03440c01005030a200ba0300c5601000d03146821072956051000058242c0c00b540006480b1b2102e000b02d038241424910860003002654074202c0e414040c8400008000d020100c1d46120020315001c0a8170b1000d00004105a400c207005041100401070b0100740041a0406107140b4100b1039081a5590151003c0c05007070700c400b401c003012903680c604110b04d051402c01140e801c540030f680206400c00122040313500303582045a00720360200e041d481e0f500040705c030b50007941c0040d00c62040002c0c103458800d02541c080402c6078070969580c407071040b646c441 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 903063803 1250 903062553 903062557
    0x8030f06121203060406030605070309021e150307050c07090c090f03030c0201110c10030504020f0102160308030a02090604060f0210111e04030501020c060109060f0312080604061703090f06 83
    0x2040c0542c0c001840c100e10740d0031581c069684000040d00000b112550b90b11003100396103043c0d5003000480c0c0e07110a184154101560b001d0362200f000030b4244a0a80f136000030810b0996100c40d520140c030700100101e4030032441401128400d03c02c1e441152440d94903440120300614003a4440804210b106000280400780700c440c082c02c90350191103c040327150142c1c005444412901d0744801190051500c06100e82d0f640f44152500703040c0340d82d800999031070148180034464201c10480d60540d070080200d244208000da4010050340e80c4100c0e0320b92692108450310001e401804042907021102003008a441d07a0b000610314211031007942100c070310000128039402100d00e008416500c5450802043c0101c82d904504503042c115914002440e103592500c4003801c9802400c060211500314030010045003000d4001d10025141054004c21181e141d6610845082482c04c040703028065070703000061032a6140e0340854002e1040e04050690a201001031503182d62103100181d100364960955a4414180942 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 903065053 1250 903063803 903063829
    0x60702010921032406110a0b0c0f07021507052406040e07090204030803040c090c0f08090a120201060815090d0327080d0506030a02030a0b0612070308030f06 69
    0xc8503000c1601e00903618180651881580240340c0c41e01c2e480000f114443e0701c041c004c154140307074010186007000002002c42d140052129003c0e131169070b445c40403801245050f40c000c0b800d10141c654030009a00024014022180d019500071005090790748800c080f04010309000d4420300558500c40d1020040700002ca5807a960b000034052050001800f46c141940855032800a0804444c04550f60341d502805aa00c03d4200b120140c8011052004100140b11241d02030440300b04140422a42048000e0545140b01160400c0002041c00b08010540912040b4040ca42010a111300c02040e00f8000e406003a243c0b00e0b800961080080100301c90700c600300036502411180e000340c402d03c100e51500300c1c05880041076003800c462060a607404400d00160180f82060321a2840c24cca42d1494400300b0300f1950018605d074001d421079030f4503800503503003c41c2c42c1084a03232140f0050090384414011038505070705009001854881d4010200511041001840c0701342004510f00c0c896564080510610b821142 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 903066303 1250 903065053 903065063
    0x20a0302150c120c09180c0a0e150a08040326060d0303060506030916090212040f030905030123010617070509011812060c051602060708070b0106110607020109 70
    0x1103890300100c0c420000316048884804101d003444851103c0c01001c0c07205032654412440005030510ba54145242500810001040054142e20300100c2c42070061240c1074a41d02041201e500900840e501c0b01c240070041d02041110070f0705c0b10480d0001034003070788044d603050703000c58180300000c0742101442c1988062a42215020551a1076050500102048002c4111305141d160b0b500071400d9116a40036501c9610f2040050a1007140e2841c81e81d003000858004448444c010040c0340c1e207205070488500e0b0415444072600061042c282002ca0303e581080c1c00080d0b255017400a0f90f2000f0314401c0c060614a840d1501031442a6070b1071300162194800312102420030410480010440c41c0030314094000d41d403040c180b2150041c69034589403554441c5422400804294226400920440340f049441d00012070408624040700103801c2b07901488400c000910465000414204104d0810183c2e19040d0344600001c1036561a07060160844811381100c180900c501000036554602c1400384410213034002c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 903067553 1250 903066303 903066313
    0x151502030f0903070e0708071805060f0d0e19020310181e08040b0301061b021e010c080c0622151107020d20010504050609091308030c070210020a0302 66
    0x1c1c0003940003a08410030541d81402a000c001032035400e5a00e03103603c80e840c0c83c0d0f141c0c0f125150030074000d060083d800388046ca0301c4071031486c2803000c0e44802e41110030ba048a00007483d01c1d986607134650b00140001048001c068000c1ea0a5100c4101580011142542c422000d07958485601141801203030000c54003200251789500010010400d0f07000c407000c1c0030002024450522000345c076810aaa802503002500031540003004210325640080442c200c1e540100003030785010406c2d000250b994907c202c4d6441803180c6a80042c280f44e00600d51460680d034042000340e00c51603850308103500c1c0d80c012665101102003900110900c00c51042404030466071104004030710054500e078440c010039251484502d00c940400910300560b8581d40000402c0b84100f0021000c410300e85102000403004410300c07810300605100a000a40e60001a01c0e00101c055401100e1540c0e01038ac1215140c08440d40500210700010500403891000001064014005d4a28181c5141c000004980d6454400c50143c016002 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 903068803 1250 903067553 903067567
    0x10b120615030a0f120e090709030b190501080c100f090b0a0e1c020301061d0412090b0a020a02010f050c030d0507021e061503030a02100906020f04060315150203 71
    0xa10709900810030405011640350020030740d90b94102801881c07003034401e801c1c60300140e1840d940c420880040040c00703039091802c6082003500a001d180907400300500b44100079000503244c42c2e10010201100d161039006020550359400344a07143d81c200046180075500983e01103500d103000344c2c2281c044000e43d54070440000d1a10000f0107887d0043d18191301088074403080c07800c2940e910040c880d00303036100b0030615100208501c10182161200d9001d24101070442c01c07030100c2c00000741101d50340070350800d0300190800380c2200b044800740d004d90045179201a0214443c1852980059652040791003a00e914070f4004009005907420300801c610207915510400c0800e52046040d04265042040b600485034004103a0f86440312030b51101103000d02503440001004041d16803490340320b401440580165141200c0c948000b1340b01c07405592081091611000c0781e0042240d00d504442c0c81040781d01125480350b485010050180400218001055103042d50200701e5100708a0b00e0f4070000e289070000c502d0460 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 903070053 1250 903068803 903068821
    0x7062f4305010f050429010b0706020d0e0609030703081003080a1b02060309010c02071505090d11040908030601020115080309102c120f0a140a140d02010b1206 70
    0x6492501114295200d490010104256024140c0942d06c1241d4000610140c4d009821002d0701d04010005101c181200401480e0b901b070003111313030312508800090380d00c400fa10f0031480a0071024014598511610041004c80130010014050032882030303070740342c0d050f41324442d812032920168000513208030000c10000981030b00992031084442080d05408180c0e4009400080e40c0e80c20407a05030080340d444140800405a041c4100c001401100341036188841c0d020b68001d0003405080110350048900564100c02d1107400002648001001032040c0001c442900c2c101d00181c2081e05c400c0d001d0341c242401002c1c100c01d000744800582c1d622000541c1401c044000300b0000706509400391062148402942c275031021000600d00c41455210070804240c040c071020302503840241c040721541900010020300c0c21390340216078112143e80110401040032036615006082900c160310080032440b51200d0008043c9012541200d500b106c0d0b0004c006c41d040705014418008841605494903401c00f40001d64044 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 903071303 1250 903070053 903070177
    0x1a120115391b060203090301060902070c0311010504030813050909210f04030203010f0605091342140702010204030c05120f0a0b1b07050307062f 64
    0xc2c0600c1102c030020068009104a0300360941001d801a04005901441e504003401040300405100608501e80a4181c40d064a141001e0000601c000400004c4242a83c13040040d54043c60700b0a9029a54001d5280c2ca8142c030b0402d4030940b8042c840000000703003a484042515003200340c40e400800010703010f0b04c10319400390340705040d41c101c0b41c0403e02022000d61800d200c0c41011003409031002070120b0516040111a03800100243c4141a024807414000743c0c0d207409405681e29404034907a641070004c48100f4804504001d4150296048140c090340300c00c83d608a01440b0142c8620781000e510b50450803400c1c3c3c032450102614140d0405410001420301789250100e01e02d240084d9900c01090202d0581001640007040d940c0d05d01c13443c14080205103000ea00e81010140c200f000d4604083d994915880703000c2c04101a20030782c1d9030f100309002904c5403802e8040e121075284103003513030001d0300c07030114000d8120001011044034440d8032403041841c45032031004841103c00c540d0844180c03180000980d1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 903072553 1250 903071303 903071417
    0x319050604110706060f0803030c0409020310050402070809040b0411041205030408010603030207060f170c030a09050741130e1006090b030601030c1a120115 69
    0xe030746110034280b0040d03090241c40a640b094801140c403925101c82c400c5007060a41041c60140c02c20030602c00710b030f40020121000c6442402002d81c0701da6882c07036008080302c01a0b00c1a03070800d0000400300c080080c0e040040c842c0e10300c211010480000041d00b4032040f9041d03001004402d84080005003c41400c81c0004041d40e88560100c91800e074442c2040c03400d40e6016071046025910908003404184d0f00468010a002183c3c6018101c1482002c0d00201038407000e040440c214000001198046415410003940d0303079006000c0b074803030340e0342d40022040758620326041031000c40c100d21021480c0c0e1500315410f00ca006c0c041da400318186030003000700035440070b400d001303664510354030042c111480310180010405828110400211180740c110f013081074600b034041803480703034002400600000d078901c82c0f517070700f6110030203210044505242a004120301c66060443c617800100000080d545a151080d80c0300c06c1090387d1194141d152802925071084500400c82501c4c1000003100400e0300401c1c0400502 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 903073803 1250 903072553 903072559
    0x5010509040f091401021b06040c090507231305091302060f121f080102030702061f0302060301080703060e0604050a02041e0504030e0405101a070203012013060503190506 75
    0x503c0015070340c0c281c0030b441440c0040d5003594011604114080c1d124005007440081080581464580b40da12021a14003601031501d42665074804a80b04a11440d08201d48109815000078024050031040449800c2803640301903d80c0005004a40c600b0180d42050090780003400c0c8050024140d070030055540c006c00c1110000c86410710140d034000a0003240513000740b075030311401d0322415026103611120041503000598a42e0040061210380360b80001c0c00740e8401140350600b03e0002280d0300c03508102c500b680c400b81d40464040004941c2641c04140d0200b00da108a804122648401c65103685552080340e01a00030b07001450b010002d07082541041045121003000301185802d9544520b0840b102950154001064103401c00042c0c10b0500c81c6603000030941c0c131a00c140514101000198244440000c032846c607000c2034502c01c5440035002010700b000c4905a411080308500111401d9820490711165440020040018140d006100301ca005a03048021040003800b000c0c4440050314001d0603003a0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 903075053 1250 903073803 903073811
    0xc0a080f120c030115030902030c09270304090b040606020d21090506151e060f0f04060809101808130b0a11010f0e060106210903030c030e0705010509040f 68
    0x10306001c007480400d2192198526240d1654106002c080d58030801c908918180f514012403c0c0c0940e500041c1c00349020022602d243c0300f40c2da451041c090824a8014100d1009402260000c0701c2c0808409041641d0300000d0411010404a0400042d91014030582000d40c120500c699400c620030504400d00c040640f0821000c01e44101200040354410142a1480c0e04294103221030386c00000d50801031203400b201c48804007c500030a0350300039050000c03010310407103001981c448050102019070720951500303813140d0784807032352002e01904c1070004407401c01c2c1c1c40c080d048810300d060080e8800c0000c030b0403003203280d00c600206a60780c0b52000c1e07016140d0504c074800303032813000134070390a00340002c0c20b1400e025600c400603058004074090955050140c514241ca081401c22081c800d40011828116405813500078551607682007070800700c0b0300a050000701c1e0b81c01c1c070344100c05164154001c00c0c2403000540c0c003049510581d180040d12400c0500550b80081d2081090300c99628054001108007121014002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 903076303 1250 903075053 903075067
    0x7110105030f01140103110c011a3708030a050403030f08010b0a0c050f06041112030f03010b03090a050706050904150503210c011a0a060f0f1115010e0105030114010e0420121e01020c0a080f 83
    0x4dc1c40d640091203c50700051000605004044d4411300c486a010b40c642032289140d4149100100c242c0100b0054a04020005240909200e0f040029000c0d80c02c5e10029a005414503040c60b98440c0103484510340180f02104074225109000411a00b0344403100301c0e01070459007001d00e2001e150340090802a524072441c006400821401c1c843c40c40209010f0302d409039130350498020f110943c1c2d07400400401c1503e20320000c100c0da1320040307400b480e034000c8886102c1294085180a070500d000c1c10314041e211398601021000b400c98698140191110215084040240d80d002c0882c2c264151013980c60000c0c10080c11010018000c000ea191700c009000300f500c803145caa404052009607404d9200300305415a100040207241030a02c103004c60315590544100d120740c10b1003901c0380d0180b40908000c011411441e0401c9030024403178021040104004d261038020107542c00410740e01c04100c00c0c2d51003002c81d14080304138001014030844211902c200050403400300c140d181c610720780d0005800080032041c100040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 903077553 1250 903076303 903076319
    0xe16031e08031503061003020105030c0313080a030c02010b0405151009170318032a04152c0105010903030c08120c07110105030f01140103110c011a37 66
    0x2d540308254844034000f14142c8501054907000f8050001c0d005a900da18040c00503036800404c03643c0c05903080c1e0b9425540d0700c03071440c01d81e8011100b071006009114045100c1c80c505034150410210180294001d00c080d041003810081100c0080e10403815103921508108031908101e100125000315605200d12400d6441110b0803842e06c0d50540c2c00c1c0309400c0012100c0030b445150246002040007a00100010b6501c4450b001d50150005598001d0b0070010f49244031710f56554004840015140b03070030405e06541c4591038a82d5030001444400401000b00498404181c0c40440c241201e905075969141c0d649140c0341901c05046c03444080d070314502c0c06c00140c000c1c0024034450074020701800fa0200d541d0486420103168054903104100d041000c00c005008000301001e02c65810354040c0140c4401d0145a81c0043c0d008081e14518065400c02c041101c100102c0d041d03024201c24146003040c0300c00c1c1d680c128108085089a42a104a60041d0304810032010700b0b00001011817082c0003c444800390b8446100c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 903078803 1250 903077553 903077557
    0x60301030204050901150f03031e05160c0807030605041511041e240f0201140c092805120c090703050711070b07170c0c04020f1b0304090e16031e08 65
    0xd006e0080c440c490400c09c00d540116400c10002154918018180d0380c4a801012407081d1510000c0c20911400e0b0310007800160340902c4018070091045410207556407070f00780040c0000303c40650b8151142100d140280e4540c1c001e890304900d25000315481d103418802c481680d1a0040d00701810b608000d500401c0940401d14040c850416065910090458001005100c0c2c40c50107001021a41084184205c80001c40d1005400049c1d0750511a00e07030880001003612001d0b100d03802200c1a5a6007807800e030700c54904c00c00b107041e55003c0d0380c4446071400c2d000d400c540d283d003207089007030b00118000c0002e60450300c01d0380855005822840c2c070034200c640071407441d880c000305600464081c1000003090403c1162100b0078120b081117407a205414041c0c205089500c030300c02108800c0c0590340002e5500d000d002072004540b8404031001680311100d041044c81c40c1d8030781040c011080c407203180010340421002c3c0028020b0010010269507540c941c1150380d0824100c4100c09281503000007000c0c2343c0001140d40740 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 903080053 1250 903078803 903078809
    0x160801091d03120a0b060705060c03070c060213080d030212040f08070804030b070f2105090f01060b0c0105010503010209061b10020c011406010806010f080c1603020d090e0606030103020405090115 86
    0x3c0e0f80149007000d420340703021a400c000043d40b08040410040c0c000400102d07045a100b020482d90540301d580d082c0051300c03500022500107108520002c4d400d0900d841c14810402520700c41801c039005490380071400e800724404c0c0c0312182d40c04da510728005000180c190706c2a101107486941e01a084c44500c0c0d0364851250042d4000300c8800c840c00041141460340540e0310a0941050700e80040c4260243c500c003104495080110501c0544a0740000d403010030811180200c0d2040d60020480a0f503500120344032904600c21070a880c0d400e0900005692a05000b41d40030920020030440c5002c1c00121240308200586030880030300e0054092001e0b04210314800791040c1250080082500c50001c40e00301c800304002015207050110b030106100190741e2010046501c1060b9051000f102d449640e556610f40c041c19004000c0c004980703030800101540070803444081012900d0b1f24a20540347c2441035074001046032841e4110505000400c00340ca05038100a0700022108000640c58050600c81c40540724250 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 903081303 1250 903080053 903080077
    0x7060f09080a030e07031e031e11011d07150e03030a11010b0a03030f030f150f060206150f010c06020d060e0106090b0f0d1e02130608160801091d03 65
    0x42004002d8982602070000030031030300da02a00050b4215925548141051020001c00c4005901d0440825024103103205400ca503e59155900c0b0fa622103004060481c0c8149940a650a10f026500c040d203a107010302e1451140000581801804d1000042000d041c40307510078100000d001e01040f05440c240010f00034407546607151550812501011070a507048500b90030b00500b111101080482e500c100c1e100c43d500380d207240105012120115550242241e142d103d8480303031404c00001643c11400040308202c80c1d4940a48155541c0c0e040104420054040c001e900019041c582000640c89103c5001c0068882e440c0181018414044c00d030480701240c0284024042840040c800c007078007da2244002c00708403058518100501048810780d0243c024030740f40c102e071a9405005004510b02100004880c218001c540321014071015034850b55003403060700049079205021680701584a0641c081d00d2404e81c60710b0b07445900e4071a4040050111034800401d25101c0d20071035442403401d000400040c0511 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 903082553 1250 903081303 903081307
    0x30d06181103130201030216060e01022101030f02041d0109060902040e12091e09100501080c09012f030c15060901031e03050702090f0405060a0c1407060f0908 70
    0x40c6856100320350003001c000d0030580041c0108403404044041c2c1007240c40c0d0a180240e15000009030700311072541d41c8080181564100728603544e180e0415405040f05445452000c40001c2418198601d44642800090000070340c4014100260900e50050b940c60240c810820600405d260a0715003141c141d010211901901c0e410030005604e000c1c01002c00103821440500340360b040c001420314180c850082200c0c010000d0181ca4045a215101c40c80c29414000e00312038002e00d0502d141e448003c466003d56408684c110300800c810207190810f036114420180c654812091500481c00d2410a18000c00c0042c001c141c620208001414406080642c1403c0024015030b0040141b01d00c810320b0041940d07002e201841c0040010030501c50200b4006840e44107031014440c2d89046c219083e00c2102c0020350480480c6090040f603480262045218600400c02c2d500c498070f50000303050035101d0b40e408410004410b0013551480c10511802030041510940c07001035180b000c003146206403000000207490364100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 903083803 1250 903082553 903082589
    0x303040611090a061e030234051207050105070e15090a0308041203080c034f110405101a0c06041a0a0b130902040b04050c1b07081b0102030d06 63
    0x7050381440c244a00608083d802d0829401114180b4080c01d8030824200c03220701c00342c00003103d088c25003152098200045d1091404482101c40b01944a10b17400c0f11291319000c00510001d10405003015240d800428226014040450364101c0e500401c0c14203a10151044002000030300c1e1500400c01070581d22201c0b8800001400e024228010040c80802041420405c000034100407050501c8240c0d000d030844a007611400707804600c520401d40801820398030322000c0ca41e915030311004507054a8461031411a1345100b65091000b0750b50140c405200c03185402505001102221070842c0d20210707404241d81c1026044258186001000c1d20160381104c45040749080b05050032035610350150844400784240d40c102d00204016004083c0c0000c80c03665100c1d40ca108655031a0461201460020024001410303e0a007202032035011410300020302c0612000c0e100d402d00c000c59910b00b03e640c1e07030000d4611058090100110b04400e0025107045010400c880c8042450902c01ca2002e0107880840c030207143c071 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 903085053 1250 903083803 903083837
    0x50c0301051816030515090f030c0c13020702010903081c2318070b2a0f1e070b0a030b100c020109091a0103090302030d0207050307020415080303040611090a06 70
    0x1450440180349803d4068042c004101c1c0010015581c2c141c0001c6209143d450700c006c3c50821903495200c400c01d0000241070b0702d03100c400190301c02c40000c3c202c17042d254292510701400304900c1040c0009002c5800c605082001c078414201070000c080314100d1040703912542c012050211880743c101201c401900d2030154000081d800c0102d640550036a602c1c4040da02030b0a040d42d0384c0c01151103145a050307000030f1191510742d541c08144030448401200c4c184403241c40080f441d01d5182005601000b80b1510180414a503800c140a00041000d400038003441410602c40388425445103030380c10305040d243c120110b1640c0300c10190b4064058696116012403880344001040c2c0d0540d13030301100c89a42090100c421464104100d46d420081c24200062014a5890240d04501980d0130401c051840414a142030102c00301c001c00f00799208072f808100181c400542c2240f007102c940101a490b03030040c000200020013a0b400364400c08a8000840c1c00c0102c0c5100042212650b0f8000400180d913050101c28008 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 903086303 1250 903085053 903085063
    0x908070c05090702060c160b01170609010204064118010203070c060f020a051f110c06191b03020405030609010627150e01051311070b04050c03010518 66
    0x102040710b200c182410103c100070b50715a03014009480c0301100041140038030030700c074440d00f00c19548150240d2240d80d40d03200385680880d12503884081ca000704400903c28400c103108442c15502e2503151040c03001904841c0c1c043c1d16504d100605104400140040c0c090750003511455000011141442c1c0d88201d0012072101c0c4861807945241590701c00e000102c00100c507105180e0694003285402d0f80ca1401c0c18104a10b0408100c2001e0814010b1074403018095a040c0d88003403405502000038080c01020080c11001841000d10411880e0014400b00f09803002402c9080b40c0c40e050035401080400c1c00000c5502e902030340e4459038020035400141000f01d0f040a0003c0da5000440c01d000700025842c02020115940b500c10710068504041030b46400302112030b0780100c685043d47c0b40c14202280c1c449505840404c0c1c01c1c002c0c00e00c12070a10200c46044410b50180d1174404440507459030404070310b540d9072178071a18080c1049420b8010301030207003d1510244505031051018000c100e10003242c51b00034504107 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 903087553 1250 903086303 903086309
    0xc040f0b0a0b031b0f1210170601030b0403180810050106080604150605090111031914030907060e0109030b040c060e100905061303020901031b0b041202010309060f0908070c 76
    0x8441801004044c42c2e1040b50446400d072a040d09aa803240c541a6200e1039200d0345041d40514520107041c4410003600c55013103c141c83c10711540d443c440b502d02105a42d1002d0034407000349096417410010300064460740c2c8425168544001070100c150701c0d054001d0400003516604180e90f603885d801040030644c00810303503401c010b042c2e8003084516000030320304140c14014080c442c184000040d00c032000380d101e0303001056031110341400d480d01c44400c1e804003042c4194018608000442e0101c082026040c001c00b240c0c0151208002000341c685008010394a074141f01900d1410702a000d84000301184003a511140303d58811781d03640700303098180440a0501d81c03000314050301802c0e40014004150307400480d6501038480c03c4034070540300c00300c41220032080300494100035000400d00307000008200e01450035040c620034410380b1171055615449014403a00480c0314040800c01d081240f000594029400340703101c2c5004103c0810700b1120003a203801514000d6504079882e610014800c001d11451a4119010f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 903088803 1250 903087553 903087569
    0x20160318050d030c051e030d061d0a0e120307081f060504060804020a1508090c0607030c02060d06091107051b03031209100903050a020c01030902030613050c040f0b0a 73
    0x150a0a0110b41c41e00c0c40c401c0024103024601c001002071100c10808090310101450f540e503803821303080442c55181e80040c1c0180d40e03940d04050b0003143c0c05c8040c4003203d0b600104123030b0382d001c1e55440b801c0c808050030800d607851119016480c02c40c81c050301e403040118402c1e40b1075241c4401a04242040700580c0d601c814104031295070310303541808542e40c4801120100d03a5585002802c2d501c503800014201030050380708407075408012240100103500700020304d10a01d070030802c0d10100c0e8500001d00040d441890002000500407400c40d030014070306071000d0001d03840f070900002405a20741190030116640d81803100800c0b2000316501c0f042180c2000328102950300658200904181000445c0d13590050703000e050102d4052000140307484404109190b5801d1f0781d82401e00070805242400342c0154000e16181c0014058070000c0c4100354080d000f202c10150f8050010603007a9200f094000400d04021022922340c0541840903009945602420b00d5002000400141030302c80c20b01046046400b551140702 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 903090053 1250 903088803 903088847
    0x2060708040c1502010b130c0906050405030c04020c0307020901030501060f050402071e080729130b04020f06042c09150c181801030605090a1104201603 67
    0x100068400206070b0460304049111480500c1e840f1040c0e01419202e080307640c02008a40001109403c950840c06151609444801c0d295441d0744045465200d28000c4d281c155000d1a400201410107038004d00510a00c030007aa4204030481d130001f507403100d003a40240e80c60381d11400140700711504070306820b00a02c400c13582140303401075a41c0c07444400e40401c003c240c0114458002c80d418070554004032042c403070f40f20000308030340c0c41003110312103254407048542e0b0140d0381d2600010b805003c031850025041500421401003070b41c0c0d5076003049454a0101c0d0855046103042c07000058100080808a44060a0b0a03200b1680c0301c50003552000828024403c0d001a80b10003401c0a031a500c50206540101105003c1c41c0d0b0340e18801d00400b40d983c0c0c90348802ea0010031010742028601d141c200e2260507203115140a024540700c0341da00b5641c1d003400c0c9001403c070003200d0341c80401924260f072000d0724407a00c014012140310030041c00d010f0385402450200c0380718a455a9000105540309404000074030320007140e07003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 903091303 1250 903090053 903090061
    0xe09031215041a1e130c050f0409060f0501030c05030402150c030d06090c03050f0f130b090c0102010f021305010e030709091b05030118060c03150f1703091c1a0408070302060708 78
    0x9800385c010341c00384101941d4421700e21681610481c11181480381c003031503048d40d4079505d511490050009100e20205e07140d2000c808501ca40c03003800303a41c4907800da0760b540d00e080d0340300c580801143e1b001a02040c00121020000149801402d1010b81a881914000042d80b00d00e17040c0c0420560b0344405e000020176141c00208041c07040b00c02c0d03015404c200440d0180350ba9a8800b144c4000d00e10350290040d2030341a1900030000c19950001d0441201102a8001d001e8007041c0c02c602404c1c1e01032040091000016403105000075441100c0e241181f58000301111002641c3c3c540520859081000030f88104040314072006802510306c034084010302080d8020804640c20403100c03d003401c0072142c002c050b59100c007001040c151080e0405070300d0000300506504040eaa03004140490302c4944100034a1071015210000100300100985c2c5100c0c0c0c02820740e0320a00000c0e90210041d5107000b4048a2100042585682102d0044401c921413803164850603503898550078081d00d0440002e02a4041064442c108 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 903092553 1250 903091303 903091309
    0xd0201110f2a0601030c03021908120702130f051f18050702100e0c031509030301050f1c230303060d1209030f0b07090e09031215041a1e 60
    0x190306180e000d5080c01c510501c59050b000c0340451080180405206810001c01408003444051007202d1084403000480180c6151150650106209201d010b03004421501c0c4100d10308002070500380d00c01481410101d00c083c6408044130107900c8000c600669900820802c0d06542444482c480a1030945241c90307490102120108444281e40d40300d0070b0b44038000729202500030401c034800340d482044240452060b502499507140007801e030262281c45104006006100055009805140c0c85c10255166a0a0034284a0303140c56410300c4a8101d1000000030361034100f462100d284a038403030600120b0700440700c611500320703010590185103290410000e0000560310000c2c400c00c080c4d408440308911340103200040d2203002403940064002c4010802060402c03001c2459144581030365181c04400301d0325a4805c2d1132440040300c0c1c4001e030764010490807000c16141030342c0e15404410603690642000100c0d022800742c441e81b03c0e03501411000c044d81506c0c5443c11891491024404020000803800d40ca000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 903093803 1250 903092553 903092557
    0xc0d0f18090f140f0a11040305120901050408070801230702100e031e09090121030c05010612050c040f1802210d26040b0103080d15080d0201110f 64
    0x200e01e0581e54a11020114003081e401000340c40394601400e80c21458903050407501010101c2c0c08211641c42c00f00c444004210310000d681c00e030303030b003000c0282405004003151a03c1d940c04429100e0500100340400100c0000400048010384400b00010078191803011110344117465540c0040c1c145103554040114403a400038075200d4100d000d07e0046601c000c041800c03401d40c814a150621060001d0b07080c80c28204011004050041c0d040c0c480030752a0380c1c0d483c95010788450301c0d00c07040d1071600c11441001c0401c1c0b00319211851240182e00020f101a940c3c920b0341e0618901070750031a2250801410038a4510f071030702c07a0f01480e4042a0090ac10b04a40503980b03141c05203030080c0207228064000b10b00c0402000342505403030a07810b010441d42e9010301104054420a41c68800000380c2408105058504100100c8603002ba54044000c1c0280e0742541e0383c00d01c2c19008142e405510a07656040141c1c20558007100384010032904025200600003194000c1c01d640c1030481109802d82c0410210744020540d4007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 903095053 1250 903093803 903093809
    0x515040507030b030106080c09090304060f140904180b15030304050118051c1b0302010c11030f0d05040f051c080705030d0f0f1b0801030308060f060c0d0f18 69
    0x180000d2140ea4001c02a0010300c58020000d8140d1700c0c00001090b44400000d40031030710784040342d80030303000c2c0d41d200ca000799248900c0c000c000016101e0400701c1d403050300941c0d048812040b40800305042c0076140e00070130100ea0810603000d070714188121511040c0104004500d42280d140c21241807240d46501c00700b030344e034407035886241e04102e06040c089051130100012140a40300042c89a50b0071707029002c075420f0202d0041015510f0940a00030345020305e003034100380e4040701c1e41a1203100c006402e980383c030422040c40c031240303a070940100ca4401d45d07803040501074400c400015072a803507200e90030094007422440c0745070865401440ba81000c1d81911905c0d02810030700303580c40b00c002c41d80e03450180b500702c1c218041c4ea01d00390105810034120702400551508160007044600d0820814000120140802c2d0449007001c5404205d0700d80050000c42e204049a0354086006060714aa0b03400180c0800c8891b88188038080b078940203000211265540099a03e40b80c0c41145014810f541ea4090401c5400c005c0388 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 903096303 1250 903095053 903095059
    0x60b01050a0801060e0a030605150a12030e010315080d0c050c030106180f0b03120d11091c050f10050609070c020603013003020d090e1506221511010515 67
    0x200f0417514503a170f18041c920165907c0f450621090030700e80520208454443d401511400000c1c1000c1200d03551030352000300058141e600c2c4403240c1a4400190001d10900e04404d4207048d02c0308003c5407000341009214000c1c0c034980e0341c0489050050518074100b180c04035400344264100300701080b020f41c1e620300d408410041c0500014205212500ca00c005043e5070181e0341d01800b40c070422a01c1d80702004003601080c1d40040c82400f4540c0100c05142083c13240c01c1159601060003003800801d15940b070320b2010418803900840c2c4411001400d072034600b41104030000b0380680ca520070400c40d4144210700c01e8002c170880c02c00e4800ca400681c0051a940014002d80c0e00d034500c0b00c44100342a845103501d810300d040c102c200c0d0303032810502424025114401d1900c0900841c8603030345d0000329210260b1015114054044090f2960841d4804001340c583c0710402060104a4019502c04022001d0040c80c00800550f0305042c80324682e4540034010045034003d000041e454001005000c01e030700807020f40860011 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 903097553 1250 903096303 903096317
    0x210801050f10260f041a0601050f1e0414040b030109110d061401090f0c0c0309090b03150f0702060c030601050a030504080d0903120b12030a0f0507061503060b01050a080106 76
    0x1e208034158004010019260403043c03051007203000e1000c51150040f0701481084071006422200c958007002c0075030350280000c0d0100005a50380203002d001d000c20455044030a40c1a46041d4030102180c1c215170040c16141d980d01117001040d103450f200c3c80c14035080c103800a00118a55803915095010b80354200d40c09851810481030800034264015884414286081d405558440341c0c174600400e00d100c83c042d407081c6081001c0305900c1c080c15119985a0341561080340481c10480031201912036102c0c2030ba0944200c0c481440d0108207140c203a40310382000d201d124040c0c40d110341c000703143c102c02030f140d4500088104240031280e41d21000700c0d480980d10342000300da152694940003a00d44600c1c5c42807070758a482e0000d058101540a083c020715403019802c10b000c5175540008101c02d103024208460b80d140d1042108201e81130045040c1400314400303060490400210b502c0310400e4a0054040c1c4d072446007203c1060040002e0740c8200a0315417420710f411401e05003600e90240190006006640c280442 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 903098803 1250 903097553 903097577
    0x501051c0f080d02090a140a1502010b1e0306010609120807080702130504021906120e01091202070303030507030605090411120d0c0b090a080301120807210801050f10 73
    0x1070900c1c0409603004a10359500c04949070340000035002850007601c030303c0a09000040400d45c020301e02000450080515510b540303030403062004502c1c01c411010640d52521440c80a55890b41100ca04408100c095042c08006050405041a40503080710091004800d002d025009400581502e00e03940320510f00c0c0d440c0210704140e260340c092000000d41c0000c4490354490221005e0b000300c0e0040b4400e40f44601d41c80d0074070145040721180c1c0d00407040000d03841e5080c82704410a0707030018443d283d0800000200942151252400c1515840b02140941d0180d1010420142c1c07501c62241d202c0b000b0320381048a1401d1200160880300054005072540003101c540c1541a03441c40360410580113220200c949030a140360300509052001c12041e139120491000041140d0b10203c2c00c8403403e03903c0b404941ca56801c000e40070703101d05940c2d8800c0d01c0000e410704c034110000d00c1c056400065004410040081c545014000418050050300214014898040103040c0c0d600d5024100700c0c1d0f48883e0a0550300c07204 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 903100053 1250 903098803 903098813
    0x708010e01030f080d09031d01020606180621030c0c040b0d02040b01090e1003020a08011803180902040608010504050a06050f130e0d05031e0f060f19090b010908010501051c 76
    0x81703609800744a460004d00008054008070500c6070718500031019054104d81070b005903203c01040315015041860107902c112a68001070700a80d004800034407101030344082100e1341402c0e4150303850010a41c0d000089196030380100b00008116280304913028060060311001082940741c205400a0040784c542c0000b4119070302030b0f850a8050210400080424684206030310021449071205a0251080c1b00c40855451010b01800e510302e868010f024441008a0b50100d0304000d4103603411120b1180c204004c1741403002c60004100401130b5942c1c000042d4100020802200c80140014100e0b618100081000d510703621032101500340f00311140407a601000c402140900800b284110070b03402654038620307030070f0340041c080c1d809034942c142011100400340c244041c0b0030030207a4000600041020000d004c501d01010411910a4042c0400500300041c050200200040d90031111545865402e0300c40d595034442600340c011b1444400a000c6c0d54504404199142c0c00c48511403e80c02c04520b6810600c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 903101303 1250 903100053 903100057
    0x6052202120c0a030f11121e04050105060a0501111b120109060f05180a02041e020a030e0c0a03150504031e0201020d061d0708060f1002070e0708010e01030f08 70
    0x21041e061100705500c1c209141015903400012500701180c90100b0468880316144144040088440c141501d4883c4d44c4d00c0f400c050340030090034120b1140010307000e0111202c544030007501a620803400401c05003400002c2207030703115468001d1030411a0301c940c0700a80070000900d41c040896526001904451803001180f00284030074044400c41d8207090760316041011903400380205810f1090108101d4440b19600380e540e80c202e00501202d81d003c0b0100c40003500e896072040580b14818119079200c502847c2002003030340c11814801021a688020705102c010080c4000414030b507045544080300e900f107603a428800c20702d040244031110b0303803000000e040600800e65a49070b058000079807140104001c1009000c0d501c029220754045042000015004040c3c164a402c01c005c0c1020082c81c680e2500b00032254640000d2940740d100c1c0600d0349205594440d080700c0c14000105a01808000c0e00301070500c1c00034940a4591010859042d0040028030082007d140c10340754000c01c40306aa4005050600c594 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 903102553 1250 903101303 903101317
    0x61303020f190c0608040c031506030b13110108100e04050a06061707050a0302010c0b150a140f03070e160201021c0e010c02011e0e030d020c01020307090906052202 72
    0x280c0b1071102142800520b0006040c2c0e594030076104096510b448640880d00ca040558000307080d403c401d2014000640740c443d8a11700c40c0c100140001c1c2540c2e803926410003000c4152844001100408000014050280f20030740b1062130a0030a4400e1f820001448801c686080c4100000503070840040340030400c091042c2c8540d550811310502105403140120040231440a6843c8100d10a18800241900b060310b41d03441100d80585a181010132603846080e05180e0080a06400d02c000d0707001780c0e0259541002c51070150070306051401c40119140248181640400c80d000c0c804d51006e24108504440a03241a50110105192005248844000381d019020b00560a075095000509074030415500e680b10b08a0302284d50000e0255a00b007410503400c8480c81c0e54014191600c81e0110b0803d04403940000f0041c0503d00d084034601491000301008030b810522440d0f54994000090251841d8070402d008041c04e0880003c110b810319010000d00365100240d00100552082c1c040f0390440c1d01150b05031100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 903103803 1250 903102553 903102583
    0x1a090a0b010c0f060c02073f0609030f1413030809061c1401050d170c0f072312030703120608062e0f0515130e0603010513030206130302 60
    0x1038108500d002800340c0005e09501c030040c41551800620942e8412941d014107440550302d0603818022036549a45c24611001814403900600d010000600d8031321809500500a07070b102e48000e028600001c1c90a02d8802034500303906000d01c103400081070841500304c1142d900c15007483da00c540350000b050b2140547c012401d144004900c8802d030210464124208044821a400d0360f075a0300d860801612010600c4081c0c89118041e070082c044803882001000850480e038200c0e00090030502d00c26181844a07081056a40580042c08035001d040c200b07165115001200c101204020300c6a003039503240644400503040010b030000f001441101981300384064903000080e244c0501e446c0800c5800001c201c8004454600c03040600740d1040c60301c0c020b01041c0ca9240d03205212540c90401007080841c02a0842189000300300601424909040d8040006005030080c01c10030349082820182102e400a260407440c039055411440000c0c3d010032440d911a004801d4102181c01504041b890541607038807240d1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 903105053 1250 903103803 903103823
    0x7081209070302180103050709111206010207150e120f0a060908040509040b1e16140c1e0d02010612021320090f0a03030818150c0901031a090a0b010c 66
    0x444c4004502c0340c5050b28080e0080b00e049030f43e281644c070200c580c00400310150382c20500840e03c4040100040641040c4140b04540c0021b840c0c1c52400c4000ca0310458001c0810301c0c0042001807820001c4038003080071203107009850402030003049681c44440340c01d002010035540302c00a008100f01c1d40c094402520000d41201c505107458645201101c00a94440130316540000807450a61160341a6a04ca0314001180401000a0700b000340e414944072b1420785003050091003005450741c03040200000070a10050761162041500c020740e41003004558202d030859041080074090794000d065810001e075070603110010080580d07980140104150548140c00e4100c41c06d40304e54200480014114a213001c40b6104c081642070303820030007040264130000380841c0c0c0c01c80000b000c916564801f220800d018100355201c401e0105a6400348000c100d40c02440f541c004100d00005503494440d0b0b01d0503400d5030200029103c01c91001a855040040c00781101940b01d00071131201e64443d0b600c0701c00ba035600580d500 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 903106303 1250 903105053 903105079
    0x6130e0609160b0a210204150f0813080901051b060a0c0909050705031b07060c0201020904060504060311011b0b0103080d050c03060904060f0e120301091b05070201030f0b1002011b0507081209070302 87
    0x144071300e646034409c3c070025200ca0042151ba003075103d0b0b03090003541d2107140d1900d042c040a00540f16500305104910b400c4000c0c5c003070210914024001648940e241d0140029006404880604019503e40000000341c0c40e250030080340c160864101c94002c150707901c0340000504c0303950071075000c1e00c41e80308020500350810b202c50388d06c140c0540180219007800c0380d09014150301c5034280000c480700d81c88081c0840001c2c01200f0095400f030805a460005030581800c000c0740d1791303207601c070303049030280d004507800303540000c0c025400a1148284c5401400710000307a881c0d41411000260f241c00c020b000907081703075641c890140900c0c005600010407800c00200740e9903000c640c5203003d038141d0800d1007a0001c082c1003070303104a00340c094405044000245c0e61a42410b00e805500114000c00e4011082039440e5541c1104030903558500116004018082d8004502e451524607008002c2221000c92814001d060200c180050b08480c10348030080008280004140d40b1100024540002a40003030b40010b0114040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 903107553 1250 903106303 903106307
    0x20114091003050709080d050304060b01110f06010504051e0402010f02100e010f0c02160e061c060f0e07060917150c07110f0906130e0609160b0a21020415 68
    0x20340c2c4101402c0c1c46a90807151b4078121152681c10f280d4040c00003580030000540041c030141c0c025032600c60185020280e99102d40d40d02403a0542d850030b5402c640d442000104054a81030182903449040360840740011041c0c107160b40c00f041c201401c020b0601c100091140c03400b5100f00300350201c080b903951040c000400388004150082c2241000100e054ac241201201d03030728000503151841039065500315000754038282000c079403e600031b00603540c040d030a0458015680c110408180403140900c00000d00070940c0140c1d0000c54015044500d51034010180c10806190045206011200100f8400740d42c101c07008030950a1000910b002170400c2210014841c102c903858000e00411441000044501c40550f42023003020440041800d522000d04400900541080341180700300c03841000c400f003a0b0305400080242030090403561283d5035444919681c1811503034802031070007400c03100c03140c2d0f1a00c3c60b0b01d50b00138034000d1144490720700c0c1c9000b80000005e20f0403550441d401044041618000e200c840540 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 903108803 1250 903107553 903107561
    0x4020a0f081303020d0c0501060503060c0307030e0c09070c03090312091811070807020414190b010507080703050a091d1e130b060a0b1b010516020604020114091003 72
    0x51000a110807001840c0e00c80c00b4410718140c40e8060b0000c102c18010b0003011281c0c0b00008000702d0f0b095480301c10008076520208141409100341d50661b80d26440c105d2303001812581c148800e059140e100c0300c00c465030b07131b00c0383c4982940149140c58080c500031624181611510000d92004000345420321909140c1d03644424003138244c4205052001c2110904003140c4103550910407401007202d810450a40004c1003c8000c002d060710182006c21915205e0701200160035080ba905074070b42e400d009951400085500c0742c8205000e09080c400e0801d03046803500c070f0503805102401400d2000c0080c10104040c000c0042c4001085511040380c085c2e0070500c42141ca40704140c4440e0a400800440d031500c0e0084c2d0300b8654402c83c4100711890202c80c907a219198685006800103421205c8500c0c00b241c3d4801c00070042c0916a03202c103091642107072901c17640f030071101300501283c5103c0e0380001c481100c1e0b07404903200303070055024a0407071280300d44c40000d2495440b41c0c1070f510342d100d00c100707158521568150300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 903110053 1250 903108803 903108827
    0x2011808132303061e1909081206150f09090916120b0f010b0d0504060f02040609050a0807061b0515070804110109120803100b0f0d0c051c0c02010b04020a 68
    0x1083e280180c075005d111286200c6044031009041d400b2000080340742110010b0b040040c4c89411000c12100000d0701c0e5100a0f500001244400c0c200780340c02c020762400c003080101c02500185008a14014062411101d07a0041c0c1482501c0f80299002103403c41400f004031404030b0303004010303250b402980c0320036441a03092146011100c4a031000000303402828102d920a040b10740000140c0d16140e840ca11070001031030020070850b481aa10610411801c58a1001c0c001400b0140c4030710504a050030304002c81c0d0841781d4404200e950042c4e9062200386d51103081190a00f480703207844038008840b0b140940c140301c0c0c46003141d4481da020b10b04005145a0000e416401140200c08010007e41c0102c01191282101e00a0ba480c0030140445000014005d40055621188031384c0e12481d51601c81003071070103585c444540850251008245a0518215032042890f141d106051040c9811036202807a08551750403c60700078240d076102030503c0c6a034000e40007000a40e400030011592401c0422002c0e2407440c2c140 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 903111303 1250 903110053 903110059
    0x90f0b130801020f0d14061c020117180601090b01050922090309050405090601080303070513030203100219030e07060c060906140a180c050f06040b0c03090907020118081323 76
    0x80400f00c3e481c164034500d940a1a4080e01c0c02801e1000c0c2c1050134402341101c18128108040010303000038a80040e02d58074001c40c0d4074140361b140038101e618003a14211060708103020803440c03c12400410307a044000c80351440401c0d5851581050041c0784424070003440b0001c01e88260420204604241c0c0c40b43c1440143c1c0c400f1503040020b500c54104150b40c2e024240240c100b00d900400108515502a10140038102c00600b031860405840354040303801e2007000004204901e801051140e1a03100c40301c0241c4620859150401c046481c941e541651040913100398018089140303248002d115650300580c0d80c454000d402400400c2e410a00061884400c503440005030745099507145003104003805c0022240d80007000c0011490618042081d07101c0203030300f0780b41d00040820000602c41c000c0b501510820b15200c0203180c403011903000388903044000a00120071a4540044013005500ca91600600c0c250400c0d540340c0c5a52400d1080f00c2c0d80c840c03e0300300080800b4000000a00043d0582d01c00d11042019 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 903112553 1250 903111303 903111311
    0x9020d0c0203070b0403050f0708160c0602063c0412030501050f090a0b01050403140a050c010806030a060b04110c0606040b061204080a0309020d0b090706090f0b130801020f0d 77
    0x61402281c81c3d0080f000018444510f010208010910030005440ca100d00140f2940c6070484603a11198141d002e10070203c03c003150308074044140044104c0100007081035001802c204d1618040c0d0031440c40700320900074511040790b00441d0851074110443c80e00d0840115031440346050504018030705c40c540007032038070001e030070400041018103200381052103000c009801c451040d2510070750100038140282c15a810014107200000224214544406000810700003070310100c1c2e82410628207181c000d2104a05215203442840a10b840c002002400590040000158a40c01c900003070040e00244000d095150030100d50805030060110790180a01002c80d420000001400705000146c000c62201d00f103003d119100045c0403669030300c010840e0000ca8600065243c0d5107600141040d501d000040e200120107408100e040030040001401030692414140283c80ca00380c0b03010140044ca0083c405105404113100c98012503030340ca88006002c240000790748901c09900307aa11550840381030840c1c0c003410 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 903113803 1250 903112553 903112571
    0x1c170708160e010c17121311010c122303010815101401050705121c14150f060d1103060a06090501020d20012a08090d0e0102120409020d 60
    0x80c15041e66006410b84400c5002629a02c0d09003041038017940100c42c0703d00400ca543c0722500e846800c0751094100c1051021000100e003401c802980500843e035062081c00c02008010582c01c202c0700104444078075040100c0104a0f454441d042c441e8203141c02240004000414600f401042c0390008050b804200446542c41d958940d0111042c3e100303841aa01812022a106500c81c0c4024a040c5016400721401003042800b84546507110800c40913180c49210758070840440d5902814400110b103031184802400c260769000201e0000b038403e0351007000340c12141c81c4140c880406440c80080c83d54400c2000d000c000b41004d8055004555040c4103002000002c22001e0152440785c06841040e8001d018207024001c0503518803000910454030401e442e07041c000d10030024068460040c074680d0017051454290854296205141c490010074481841c0030000b0f10030700000d0844446119107482281a0f92010040c1d060030909403102d40d203120000340220701e20b88150010b1041d110308820410020b24 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 903115053 1250 903113803 903113807
    0xc09040b1f03050c0f07150615080105130b04050408032d07030c0525020a05041e0b0d0f030306030516140f1f02070e090309031c17070816 61
    0x403204503400100341e05103598800510a500650b446004000030f10315040190b8841c2c422074112000481f042e44104041c481c1540b0b060050000030142243c101e4960700070341c80003808040d014002c40380074296404105140d032840340c0092040c203030003038000c0010703083c54246080541d0081b1480b00d070b1080030349164411440c811210300304402d40841d40d5140360f102c00e41c00718080c014000d24101009000d105844143c41079014840109944448515a6980500c140040035160303a014a21a41c03030308801000081030110899003001d1141800954489414001059134008800c05010b00400d16000130400d90035600004c103480c0034a048500311f044a8030300c90014a410f0040034680d08050217003d80c1c1e802d15864100b5424801031100c10011110341000b0000404199840010b034405242001142c0400b0f0820b60003001e2400176518000308640032a40e035130034907280383d1101d103912070350118024400c041c03040e07000e259001d4440c168107000700c00520070031040c0c0306154441024200b04440d24 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 903116303 1250 903115053 903115069
    0x61513181103061305040c03170706060e010803070816081b01051b040e0601111006050909011812090b03070c02041d0d0c0203120c0105040c0b03040b01090b04140c09040b 75
    0x4000f040780402060a00103900038050146c0111070f0190040740100018500144400301600d085a00548814840c00e01c5000e984241e4404002003d407800180044040441114519074124007001d81d94002c11402c07110800002c0d002030208603010405441d06031a00004074185008a802070005848509038050011100d801c039150281080004000f050007103003440390b018105040000d0030900842c1713502c0c103010340c441c11207482d00d40d1800305110360700c0c0240c0c110360004460320080101c1440301800c5e01d0100f00e0b000012b0840e966510309500c0d001c3c07260b000c0328080d18020026945a0a050f02c01501d844c1074400100d00c80c9041c89509061030100316808100c0c140381d0310051405818101003079411180c8500246c0e0140946045c4e9100744031400b0090614943d4440006414a0107013400e00b55681c44c0d811001902d01e04000703000c04034400c441c3c102d05541d410000003c2034600d4000180c0200944040c446485034590100200c50110801038848120b00340c030305025003000c140420140c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 903117553 1250 903116303 903116311
    0x605040b04031509170a1b0812090304090207060b090105190b0c0c040203040c050306241c0b070206060f0307050307030b15090405030a0224061513181103 68
    0x2100003400200040b803648543c96100c8042c0d18400070700380003d9207410010000f0078000807803000c4002040914507902410125400c004c0b00d0009001c80c09075601c446152180c4824085800f15400c003080b49901e05008540040c402d84000315a10b0f00949040c001902416950b42c1c4585045000007070a8101200780854504100115558460a003941c01469400944030018140300b0130000c0490768545100a5018500404020031224601800c042c58108001c1000041085100c040411800f9006130711442500071203000907040c414650b000c00014940c6001340540f905107042c481515004107809000e03c0055a19881012005050565a00c510b12481d17405500000d002c10200320059185070b0030032107400103140742d50740d464001076a404050b2400e9809420014990071282e404000703200000d6078582c260044013100400b014164003004080034091010032031620360310001d810494044180c14813980318003d403100c9100082d11028044c0301103903417801c151074064240300c009807131007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 903118803 1250 903117553 903117569
    0x40611070b0c0c0d0602251122050403021501150e0f012a080a0f08060405060a0b0c071a0403030201150807031e06060b03220302060a0905120706060e01060504 70
    0x79045040f0b0a1291000c050070054800603030a2002e0024103094000d10301c622800e0002503a80303244641040310580305441c900601c070350082c42d24400c1c00c803800d10340c125011000702400146542c8905040e0b003442c00b08810312080040d6600007181d5900300803045459402941c0e45c0500d2a50100300303204005104c0ba03101c1e4003041c0c5411096040d4000d140f42030400c04510039031070000c4070f03c56030b508410b9001800e0200110f200038800441044c0c1c00654903601c69000c0b202444142000804118089410b001e8030082c0745c1c002612440ca01400c01200c00200001e20440050100d110100a080e41050200b203005509000404d059400e802d0800c0f810343d03103400080c00c810f51640c0c6c1c85054105400e0410110300d0706c04010900807603000d00c030399070040110803242592450201030708101000f2040070b06c1142154215440c4c0170070750009010703512039032407a80000c8070034080c100285000c080d40b030108200c0c000058404c040043c1c1d03811640480b0042e0034102c8840c0d0300d40500342c81c00e02403409072580c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 903120053 1250 903118803 903118813
    0x20c01090602121b0a03211e0e0a02120115050118121a0a020301030303050f0403200c03010e0304080f03030c160602040506070f021e130917040611070b0c 68
    0x5807501c80b005104203103070600d52080052281c1513041c14608124020350210358000e641102c40b40c00c0d80700c030078005004c00c501040407240c46000c8400683e400c40247c00119901c600464407002d0800072140d005030000c1101e0108000102d0751406494a00ba14800d058803c1c880010380754090444420100d40b00f69110390210300341401ca100010b000c500a5500c01140003032056001800790986000e03141803200540d0301c0d070460401509403100a02000e020908c0da100b080042a0300c20140468410701c884c076442c2115007da0101d01d0300000f9111940d143d403905c2c0c01c2d903103107290000081007115850b81c1642c0c104401c440b010f50f1240002c90b4003a00c0d18000704840207100301180205420644107000c010700f040c2d02c42010808a4100300700880b089080e44203441b0a6280030040034590003420321038501d5215156005c100e07400c030750041418141d61903020b40002c100b03040c0c503901e190003c0890300507184c40d658840245220112003860b4054051440c02288034080d1900320390500107110300400d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 903121303 1250 903120053 903120073
    0x715051602010c050d2c010b10090311150d060902070b0a0513080a120c030b030c0609010215100308030718060903020a06120f110a0e100e130603020d0f03020c01090602 74
    0x30041e142c00f00d25112801c04901840303001d03422550010f401d1b040e00341c4c00080c12001c81c3e0103001c0c0c2d40b595503403800240b25500791b08000054040043d9581c4410035100401d01440703c000349070050040f14410700d812400c0c44d10220b0100d40b940e020301011400340700b848116072551211401190410345401502c10710862454021990010050490000510b001a41017141050440481c0c40b00307000040040c0c0c583d00c07200054a0104050314096108a41c000c1c41c000c2e0b03450020303689492145408945181c43c0c0001441080c40e071003d84010360300b014107544d43e4902110001c000031080703080a6454181e400c00415070503c104030741004d59501510070300d9420300b0400280c8444a41240310310aa50300d441000301c0040041c01a584008204000c141c1c4031009408090440b91020315554040d505100025484660040d01c0c0c1034981e805031110000d50102d10114005000c007a00041e40001080380d4a808001100c140c071003d0b00e000c0e50a5880e0340888800458120781d140c4518001a03200000c28 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 903122553 1250 903121303 903121327
    0x31a090f070e130506010f08070905010c0c0306050a0203040c08030403021c05010f0c180b0c060105042003070c14030a140307020c0a0b0307020d09030c06140715051602010c05 77
    0x1a00040c0381c1c00c0a90185500c2e600140c004080c0b02400c296058450701480301e2940c1220200c1d86505003030500c00c5080c64902030080c452070143c0f2a20781006410300c0001d06220501502d00c000d9504088180204c1c60303c2603400c000b03580280c07000c41c0c01d24141400041d10001c04000d98054a500920030792440c11300300f9082d403d80141800a403080d5680c1c009a4180e02c041e440b5080d07207050342c3d4035100745604078401907000329405a840740340088010001c0190300540440c1a0741910021035000030b2002d6429500c05e001c1c07003038507101d40602d030000090062440d00000068544c0344102071240c01522807146454aa0088541c01c4000c80e40d90f40eaa4134500700000080e40e805a524030440e0506000d00c07002a242044650004c82da0407000428000040d0341440800c446d0007007030604407100c07886c42d40c0d03010b81c0c0107061140c1010418040c1c10390b89031000c4a03003114001e03070708018969004c0b449130719803800506060302e1074200f0901030010108401c0c018007900642000130303207855051241303904c00c0d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 903123803 1250 903122553 903122581
    0x250803040b0a301e0f0b1e01080c0c0f03030f06030c040c051819030f11040c0c032106080f010b0f13090606090c120c05040b04180905010615031a09 65
    0x49080f8100c2244891305820700b080c40f40200f1340100800200303000040d4400c3c45152101c00d04040e0044410000c0b540450740c01282a036004019001021307a200d003002011810b000d81d0302000f48080c04000103102c0313524542e074a12400385004409489401e0254000c0008803210f0000300700204c0e1007030002141d49a41124900d4450328040c1c80c1d8a0002e00c407c03071b00032203680b01d500111000ca020040d950300303101280e0b400100817441a5410001e82c8448c60f0b01420b9042010b900500308000300160129044402d9074040d00000800310521065459404030f5480e80f28165003140c4640c0380103c0382d10070b80743c696000c4880b19000307011f042442443c0c3c0b007888050100502c0507a80702d42c17034986c0000c0b410001d10034514a640c681d90b0f510700c051100c811460070750318850302d000c08211040c40300b4001c009483d03003124200c034041074541001c1000d011020700500380300803001e40194a005000039240107800060180c040c0c040d5010010511510041d909980507018850b40065114000403007045100c40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 903125053 1250 903123803 903123821
    0x70b060d050703050d02240702070b030903090a2d060e010f231207020a02011b0618061a1e01030c02070e1f090b0102250803040b0a30 59
    0x4141d40b400c98407600ca41d031520415050250041c2d01c950202581d07060010a603030b10382100c0600d030000b503003801308009540c2e40e110700032160403803000004580c18090800c1202c000c1400681014030040e9203c1c0d880c0076002c80c0300b65190040c4510100e24122035101c240350b20640f070150325000c4105083c5e00044403451000c41ca24000d001d400d072021800c24a03907840c00302400e101c00b4581640c0b00800f43c6281d85082028200d103041d58002c81c1d4800044c0c0c1c03c2450407108040c404c4042c07140740c2c11800c2001c041c2c08081404403000d040c0411003001d0141a4020344100d540004030340400c00040c4d018058000074000070469803c00d0b50b8100c43caa0361080d0000c040829692040b40e036129102d1401c400800c0c0309541c0102c80360703001c41110554075050340ca60706c001d241e125410404003d0000002c0e48072954090250141111340c0200e94036140c0381070a0740c01500308401101e45541e140d000c0f03210194000006880070485581143c0510001018001000c2d1a400f03624020307488010341d4000603042e541 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 903126303 1250 903125053 903125063
    0x60b180127110c1221060a0b03090c040501170c2e032003060d12050c12030a15080703060c02100c1215211b081506010203070b060d 58
    0x100701101c11910301564003030200d0341103007941d900803000400e40f52100341a10541812418007280b4002c83c44444103200d51003201044a007a55181000142041442e0300204526007000c000d01c0107405001a0a12041000b920100416629180b002401211604000741c6540c0301012125403030400414aa80c1d01c44041e81c05440100d80c00c452100d120380791103e0400007542d910314540110790104c400100b81d54011000e91030b60905201280c600100010040c00b0036503084200717800c0b1841803040b02e04444803082990300050755038886040c10b501c151602103c850a107220700090b0208441ca42c2d0031944484010844641780d9a0354a01400c944050001075020b1200e241901c801140907507068105255210b00300640d500b0309110480301d0030480102c071500d11020038003030b21003124a0075030b101c81d88c00103101c0e940c3c0d00341ca40b9000c403005440560100450b40c1d000003c0703d00c000151080034411031040c110030303540c501c401280d03640510b601c003501030f240002c00f00b80541000000e01021034010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 903127553 1250 903126303 903126359
    0x1080a0f0c05030a08031e310605070e130c08060d0c0e0c030f090a030242010501080705030601081302010c051606030b040b030309090c04080118060b1801 68
    0x103000042e082208144094440f100d00008009a10509147c181d20101400f10003505506042a0320019000f200d100b00034150307120706800c01103c405482c2103d40584c02281402689407900005000c41084d4070761a0040d0f05000760000700714900d004082614540741e4841e491965248200a0540007104060f41e40301030417100800d4080200b124503100303404182800da600d04200850a0085100419015090300541c4e11540007a80c045850b40038840005101c00608007070901c00f1444051499042958070183e19400c105d0b2082005020304803207090300d8092559a4840c3c0c10740c0c403444200d8070701340012040f0340010800c00d00c0d60045030026006140c442c840ca07105503100d51900c0c5038202d480714140c0e8040d0081101503418001d8081d071020541c1d06001011220004c030390b503801280d013003e104022403400190460716001c20765005012850080c410101c85681c9080a15034000056800c207042c03001d48406800c000e6030b0001d801c06040c03100a0703030b40c6c60450840c0c4040c07800300c0840007441003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 903128803 1250 903127553 903127559
    0x6050d060e16052a1c0c0c091a0306010810050c0a090b280809280605060301110a0504060206060f061b03160c080c040c050d020f041518090501080a0f0c 67
    0x49550030340c0300d410103008081c0c502603880c00340e8072907000c07194042c00c001403008684c0001740c4031050300e0208c3d4040c00021445000e01604040014401c02d9460b815100e080d0000034400301c001a5990303800d403010350402003900c07080707202c106a104a8151002080c0c00390300c20004145c2040c01802c420aa60b60420340c5d820003a075001091060011170207000450900a1109000051020f1500c9120300c08018280101d8200100420400c40e40042d002e19034580001703a4948082d0407050101c00d0744078106030380b80c1c1441c401134810b800c14001c40d401481040001403180c1441140700709100030083c1400d0074031003440a020081103401c0043d1046000502458a50f0301d050300070f5402c1c0b80d10498540c1c4000e81400052450701090f07201a511442c1440800da08141e0000c007114003498444001689d545048000248244501c0d404002c11410010b000c8034000c1d480f290a181e00b2a6401031040b803141d603102c1c0d0100360351013800341100f1500000d03881000551025100c11403184581420940700e96 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 903130053 1250 903128803 903128857
    0x40504020d021803190b0a14040c090c02010c0c06181b061d0609010f0504081c18030809190504110a080f0108060402010503040f0b0106050d060e1605 66
    0x30a000314114070703802003100c1c0b90448260500424040082d8004c1c071000250308022080c5c0b0880d40b0000e00180c0c5041c021850f240302d660410b07075400e039007000c1e0a005402e20b403030300b0300300300035284282d8107000d103000b41c16410103106003d003125550850380e54140c1d92505481c0c040040994416142d0b1106200c0040340004440b100300c00429140f0900b00d0b28240d10b1f00e900900320034489010416101d098081006007995a10242ea03c001400e11b4055804121034400b61250300c1a608100f4082c8249909071801c08448541000040d4940d542e621104041c010b118005542e14000113000f03580600081c9001e017012000e01c6010001c80d00c0741c0c40301541d1880428102c65051020b414441c01c002410300c440368100d44841e4001c1c01c2818031588035803606a40c92744402000d44000e040040000100d0280039040c8007025405801070810452942d4515003c1d003580c1c41072100058140c20403000281c0c05c10303070008092103001e008050102101e01e01c04100c403694001a801900342c404080080140c0c2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 903131303 1250 903130053 903130057
    0x11010603050c190b220e09060412021501030b0c0d06080703170309070e04321204030302060606030a0e2e05130f0206090423010603020306010f0c0804050402 69
    0x103004002a180d854808002c0c0900c840342c10303c00c01c2c00c00381004402c1045004250440d81da0700c4104c0d002d80d0400e4850f92949842044681c0502c21110119003072040804002c50918003880c880d044800c59540080f805031380740c4e462100d07070801c60480c5000400125044a0032a50302511115080b07150481440da1801115840d4000d404240c2c08140c0c00e200304449031041c1d9010f02314551b10b8a08500d4400c075941d81e250101c3c02086040300343e28010604012400300340001e24005d424009800c001c000150054040210020424a02c51032240010f16a4450b00b243d01b40ea41560241c0b9850340d914044c80290303030002e17041ca43c1540c0d480030540307801e020600005d203040314545401c16151044850043d9101001d4540d441d450b2703e00800e0180e0101074a09151040b60301c00781d4200c00c160340f800001c505009040c0100d402c00d0900b005d0016440d007000d98100703c418800c140c005c0daa601c0e114201d0490004681c0580802d0024003ca00c00070b004001d030701c40180c400c0c01e80700c1c40c103511040440e00380d07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 903132553 1250 903131303 903131309
    0x29041d181506011112071e08040603020901140c030c0c040203160806030c090c0d05072a020d0605090307140c0d021306031a01171f0b04150314101107080a110106 71
    0x5c2e100c00300c0e40b0300810160809a120138030252450100480c041c0d1103800aa101da4031a15061550000c2d0320b100300c2c0d0085400e4106540569060303a250307454210300c50740300c5d230180000f44114000d105480d1041d00c0c0901c20b80c2d0052403005140010800443c0c3c050f01d800c000a096a070b418032a559010700c170742c2c1d43c11031058402d90b80d2400e0151035141d010002c00565101034211014001d800302e28003a4140c10302d20110305070b0910300d10341d4204601400841c2c814406000042c2c03070076040c2800c002140c0f030000020280d140c803501a031881080562203540d2900e0203092190703401240300801101503e09070454003a1803046c0390000480c5656982ca004032290941c0444901c08044030040122445144c5580f941e8084c480292451150441d00c0d50000f051282112805554480d201e00060300c1d9603001100403c0e0031903041b40040e40b02d0400d00c80b40983c02000c0702007445451b0445001c0c03000c5000306400c6c0000300c0706a80c18000c036961000b03420b0b0441003000c1c01300001522400c805890034082c000003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 903133803 1250 903132553 903132583
    0xd0c0203070b01080a0b0708070e120c010906050711091905100303080105040c0819060b0304050c09060d03020d12143d29041d1815060111 61
    0x254605520b00315a0380101640300080d580c0200501002282040800c5a44411940307000403480d80c5421040c2d54500055000790b42041510014807801c502c00240d030818180242c90703c5030f2003a40c03802d044407144910300d030090031032000c48954020381c28082c4000fa0000040640200e541e640b64000c441151011a0740c42c0b040b1749018010030516411503070321409400c06450078400c003c0007800190040d007010b803015000821780f1020b80f000c0013059218001414940c0c440b203569040c82c1c03c0071035440407070625a900c10307043c1401160140c9400d003e12001c0c1c95040d00070388840c42d501d29040d01c0201469840301505501c0304080304074000b1200540744220001d0b180a1018595440e40c0c0c0200c0911100c000c0c4030051140000102d119903504000445001c4101d03091000c4000261107000c0300302d00a00280c01501150100c0d154500000600320311140302c0c00395419a90340380340101181000c0d1880350003500302e09003902d0311104100417140d0007003060410705a500b45400b90185085031803585a00c03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 903135053 1250 903133803 903133807
    0x21212150103050402010e0d021906180f0303020a031b0209010b0c010b061e090a0f12060b03010c12090507030b130c0e010530060408190311040909080d0c0203 70
    0xc0400080c0414035502880c0801039131406600192440c0c4111400034446c013441e003940c000319524504a064010009001c0034080da55860340640203a14442d0040e24101c04502c000c82c801c1c050270080300c1100d800d03500414864040b61803d465030b600e00318848030411604500603000d078a5090b9024000c0041e100070315641c0c0c4424459034211440b01d0121072040008220070782d140b0500002109154013881034460340d0300e401400042039000d150b403000104280c041c1e00003802180c45c580301c64039903000740d60500828144800b0942210203100703030f07440031412040031041210416440400c44c603125000305c6d0394040d1a602d4070084147d0403584c1024100c0b000300b12508200c82c0f010740348002c04404110100c65410000064480b0341c01212604608504400d991108000d01d620200d02c1d88030142510030030f09050409203042e81c0441c0e007000620210f0504149844d12a1050078010009040c8a60400b8145080b0b20060140c40c1c0c01513980c0403041c030281120700002c1c4030b0008000c3d51900119 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 903136303 1250 903135053 903135061
    0x7050d0c1508060a09021602090901090507090903080106080a0e0f071d150909032223030c040b040204180905010509031204030e0a0e132307090c021212 67
    0x814180040c0030403808002c04a014481c95403190070301ca0b4240c4041d80405622111000070b00c111007440110702a6012540400b4850740c68419401801303041d0140b42a034030043c3d29841c00f5015188402001000114048010031002e44518480b0780c000203010000f10344400386c00701c0e85240180c4500d000300250084501082106443e0310803000d9075140035030746441840c24907010070404058946203030090211500250348403000f4000c0701c5a080b0400c00c403800b2800031b0f58514031403c00500582c010035002407203105d0b003103495409420207214014010000c3c2050401800003501c001c0340455001070b0248408680c41141c00a032044184106a000034502c2050900c0f500356035010305407075140e40080001d07010110b11a84c2040e03002e0380604010905403070000202d1550810f0307610513100d006800092040f0640c58038030940360a070041c0781014207031640c80750140b80640d411004002540c00300c1c100304003500150b004140c03040920300659040390061100008241d200c0391186101141c600100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 903137553 1250 903136303 903136319
    0xc0304031404172a0604120309030219060314040b041202071502160f080304061d04020c0309030c09092505190602060c07080f1b1c090e06012007050d0c 67
    0x40c0065440300656800c50344c1030003c10154851400361040301031080c0c0c08081458001c0b4540c0b0300035540600344c041c0050400714224002e194501803000081c4c101009000d00c00301c0700c85002d0185030000d2245119444e95503230140038407030380c0c2042d000354007443e800000c0340401d4900c0c0c4079000100b0703009000c141c003101301c52941c0ca100540001240350203510040c01950400400e9030305a075a241480150401c0c0340010340550510707031203120b600c81c1c00010f140588080200240036060029012500310203502400c03c00700000440c1c041c581903204a419905407c0c42e90307030745901c8680101480c0401502c803404205e00d8246200704900b51010781c1000c0104039810851190301c1500c51a030981040e404d1380d104581845102c036002c401d000c002c5805807110010700c00090040c070a1408480d040c1c081869020b90704402080840301040b1074480026892550000d101c0c4505ca0583d50320200d202c0f04200030040040c501c001c00194840c112001ca441d44540d065090014062803103103003401d10b44411 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 903138803 1250 903137553 903137593
    0x91808031e0a0e03030c03070903060f06031b0e0c09120604080318010c050a0c060b03010603110f010215130c08060702010207210f030519020f090108070203030c030403140417 77
    0x1e032840b4500f0181101d24400401a00e030441c0701110030a42c0c0313469800341195902400d0300080c24552602241d0540062a17a0140307084a22920f00c45e03940e64402c0e98120040d5800f48038640d070702c0c141c01e40003032104645080203160210000f03220990464500340400e29085003154100c50040300042449038043c0c010350300030417030508003000b0320494440910040c020f00607075007440240102c01c1e0320342c02002010b82103419500805030003041411b070b4900740700841c1445141c2090184944850009040d40701003101c0d001aa1042c0c503c2c01d5949032603081400c3e070842190181e8007170003c00d2002c00d04081c240107543c041d00c400d41c0056100c0684e802d0a414104400c8440c0500b6111540e4004031190042d04424203070509083c000341950341c03020305400b80003151221501c0b1a10018070109512403080250a103010280d17035403000c40d0745001050340e9a00c0305580c1d14040010600020740064801d010345980101c0020009052959401c4480f040b19461324648c03c1d15041800800756001158039 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 903140053 1250 903138803 903138811
    0x60b030c190b071401020a1e020a0b130623101d04030804050102040f030c0807080313170703150c020c0f1513170703120c0b01091808031e 61
    0x907400715100d0450000c2048222688508003910001082c4070083c414515864908400c4d44c400a42d9070350300e21240144080740410590142155502a51000c144000355040396158000c40d090b145845044e203101d00d42c0e52500044850507100c004034031480140c000440e6841a6100c1404081d042c200e042049540c2c00d40c000203590aa0000329242c0c400060b044d0303540141c2c05042c020301c01c0c0c446007099400792040350050340c1c00548507d000010400400c62032000c85003400141d8034010380360408940c4070f01c43c00c1c05401020117102d1003440000e25074800d011170405500c0486e84030030b58135503441070550201c1050340d400c00d035600c2408030a00c0c0c050201405002044540600c0b826a580024481410030211010004000704440d107102282d40d80321000741c08000c22012802d00b15904e407564481090104031032450170340c01001410780c000c2c2035250501e81d00502c1c080507682000a55001040f440f0304c110565270510f058400400e01c4200158082c451103800c0204403445144440c04151001d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 903141303 1250 903140053 903140059
    0x110f0304030914060a120603020a0b0d060f0b07170c1e0c0d030f030f180b0121080702010c1a0103080d0605010e0a0e1f0602160b0a021005061c060b030c 67
    0x3007a100f036680d22141103520381c0c0c4043c00c103034031680501a80d0600034545a000207421445868001c5285407065024020800c3c04820601c00750f5120786100d01c000d0514032402150304824082c7d83c000825501c0c03000052560901410b080c959509812440c2c0b141c8952002d003810010581a64031400600003000d00600c2a240c082c4100b2480e503000f0300504440310b4038405c141c2d07100d01181e060416a04080b25641d003d020203052450a82402072003c8130a1159401d407210080200d008416494a6846155008081141405440d03001940c4286103ca01260746411034841100f188000100c03c9000c0c5004004660f100c00381c0040c90000c4441540140d41030101801c40b85030943c0d1542070140c103403242d1280c9035200e600d41d0702400441224003900090700d84100d100100b070070341c1d00050a44100013404291551b00350344000d1447d49124010549006801c441d0020102e00e0041c4c0001d43c000702c0151200000e543c02003949050080c158030211160350320b403031203402645010484581d040c1411 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 903142553 1250 903141303 903141329
    0x150302010e01020f0c09060604091a0f011d060304030509030105100e01050409020a180b090408120c0301080a0311100f02220e0a0917030405010e0d1d0112110f03040309 74
    0x81c0c13155107111140040388200070410000c1d0080c2c68181c00e5400600d0001c6090105590302618100c4003410040d00900411441400b2203803503100b50000c0c0700c1100c80703a20f1200b469070507000303000302a41b0061055090100400544900c2c0c0c80074411170344074032106109402094200340c260f20f0b00032030680c4544d200310f04140110015a0714540100708917183e84040743c1c0d40c0903101c00ca01c0081c12840704030a038801000c9003000b050140210040c1042c1010308180074959985465003045804280a145950f45c043c2064200003402445010ba280d2444030132a030120750b00d2000c01042d80c0b060740c0e0169030140c011500f140c0e8060240c41c60390104140507141e0141c5400d0460a000030440100010911610340400740240448030804141811510030130070754925041c18035a003e84010400a00144107425030b440760684100200520118400200d5903507815101c011100b40c415021404240e95031080310140b10b01024004201100030004c1254580c580760401800a1455a00811094420b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 903143803 1250 903142553 903142573
    0x120f041a1504091403040608010801060b03070f050306150f040305010b03030304050a030c0f02040501090209090610050417030c0102040321030207030c022107290c0a02010c02060d150302010e0102 86
    0x340803100d601c6480280d800084a41150070300f0003680215540804044c04005070104007550b010640c40c2c140c40c2800020700803540c4e116400ca485101c203c440d00001120490100140c034402c0c0003c1d50086001403a1840e09040c0a2822035942d00c86c18020320084000a001c2003004004c2c0908400344004601450a615147c0c540725182e950b0031340002d08110008a0a90400001404542040f900074208102a6071120071450003580081c649a108a0a2000044c91480c0001c41c4602ca11420f507101400c02d880d1980c040b000140300c10803500107010034013a2181f40c88003440036000443c000c1081c0310441007040100e1990003062130307814003094010000f032030110303401c2028045110350680d0b4038003000c1d40c4007403140c039003003010b0400300100c1c00f4820000541d40013103292a601c80718065256100481c405909000920850000e402107800240040c4055801100000c20b0301c1d0000e41000d14069030640701d50100d403054403201e107000c80201c200307006559100820400c038010a00060008681d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 903145053 1250 903143803 903143821
    0x30a1701030c0b0c0f06130c2702180303130306050c0313030f0e0418060b0a1809030e10020a050c15090405090f03070c180c0c0803070203120f041a 65
    0x480c0d400340e03c0c1000da0020740e11901e11010010b084820b00e07028150b90f03180c144403500c80700d6103030602d50030f88a248003e030000c80c110003034042e0680381c42048051040e04a0841a4810180d0042c22034498007000ba0f11106070b582d2802d000900407182150b040c941707160300311310300134040300c0b0041c00c60002081e00f40100206841c400003000c41540c2c0506000b03207040c00710002162980740343c224440d00942032000c140d81400919940b043d96a2041c0000d100241c02c04013170200c10a241e00c9049002d58200008020b44000d40c1d214100e41c900a00e8000c5100280f08085148400c0d035800007001a4051136051050080501070030380c1c0a202215030006100081c00e080c0300b24007401d15075600c1255104040340700e04001b084500100788040f410380740c4502050902c454401c40301d1144141d10b9480c01400044c3c03660700c0c85036429849040e11080c0c1c4503d800d86990883ea00020446000d51004001006000001100c0244900e000e0000c0240915061404400c0c004013665043c98142d04941803202e104 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 903146303 1250 903145053 903145073
    0x101a03012f07060b0d0803160219080d021218250608130c08010f15050901060503041103164401090c09020702011707080a1a1002030a170103 62
    0x11001c00d003080d1614014140309005004100325107034050038050304602040300f941c002c1d510910110200b03a92140c280707070060f038580715181c1040141e030006410200000d40d910018040780c0c41c0300440107007828040b0003001000c80e02522178600300d1000d80d500d400381040400040448071110042d25001c0d042030100103a141c8098085d9405020b82840002c250281d90324600d03521903080015281c40c10303954405540205403185da043c0780b20382000d00ca60b0b515121080d0a104480d8090405a02d80c0e2030400100da150f0400fa108854000c9100804060765900b0000da44080e01d0000040301141c1c5004103c820b020f400420001c003400d5035241d40980441000012040c02e010303140d040f05d5102081507c58011700a803003005040401d40000403443c0300c680e07400390500901c04c0c0c03201d10220254a052030081d0030100e0390030000500d03030000550a86c403103400a00d24008074130702c15540b00000c00d0004881001803692480181c1c0003040d5000c0c02640649161512806548164029419515208012 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 903147553 1250 903146303 903146381
    0x6050915180411180405070e07090906030602090117041223030a05090f0f060105010c0311010903030b091302090f04030203130e04021302040605090f0102101a0301 72
    0x10003482040041107071902550494028414280119207140519000c01805441e00c0e8181c000c05000d003d1000342014112480c0c041e6800400a014207842e0a020032802100200200d0070420f400400107040c113150301558001d1485000b0151300d62064100040a0403141143e8203c030745184018440814410403150446000034600701c90b80c1006a0b440f03400e9500c12601150110b4000400c000d010302c82a402907016001d28400d907101701100c003481c42c0c0d0790452034010b285180c100c01c00401c040c0d805146a807200c80c0c42801e000d010340966203007841c01c4600000d1b09801181d1906141541454001c04c82d0303502c2100101c481c5491502c40c0c02240114070700611051400c00d40d03a011400b414001c0081e0341d407100000410710102921038080c00700c003040540d0b08a000700748005100c4030b2a1180d00a83d8259031043c0e90301400d0001801c100b10350350b4540000b050640c0241502c01d00008001c0c0280700240001d03038044455415503600f8103003184d0740c4402c810f01d440f40d5607808031200b03600020703100b00d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 903148803 1250 903147553 903147571
    0x9010c0e011d0f0a03140c0409051005090705040c050307140a02100f02040e040c0914010515070303060e070f0e0603010503031b03190e03160503031603050d0c090513060509 76
    0x402c205001c43d240c4000300c410315a100284a03000403c002008400d51846403070304041d581c1e0700c181300c0107103c02e4420004001749190405000000c403411180d00240c4d00180f1102124980d6603600042821568110f80000000e040041040100d0350411000e0030a00128039050b880d040b4104002500d801c0001c83d02c00c6583d498800e034011a00d1130f60183c8000e0b1191aa0129042c200352a08061044035032240d0803a00741003601703da62809680100c10704807900034006201d082a5031003107120360b500895080f414565110808200401e82d1949280b01e0303111070700e891302c05200100f405003400f1100c0b01302e1449418100010311054034040143c2e6881c051417403009040c007020781c4c0e110303085024103813111041d400c01840101909a010b00160401c0c80c0940654903444c04420009071609110302640b80c26078010024403440c0c1130070388002980c203406490420306002d8605800c1040e121b00038002e0000907801d4000f882685460f000d901c11200796514100701042c50000450007110004041c400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 903150053 1250 903148803 903148847
    0x9070504090e0705031204030510020909132301240b0904020c0f030c030406090e0f0c03090a051b1009081b0d0b0403030e0f0304031124030f09010c0e01 67
    0x50000c4003003048a016000082c11b440c0251541c0c425030300d182c2c01520094400344100342c400304000d00103200310341e511900900a003219a580b5650b84a150a1984017100d038200d14060752044580098896000212181d002040c4d414001114102c4900303140010031200981d610104100100d44040716110710081d2009602c07410300c0b0340306605010ba40301d100c00c15800000f07a21101818088014426100c05843c1c4c1c4000b84d4170342003410b0042070200d90140b036040c80da00108103540c03545400303990303c142c00e9022590000410340c0c0d40785c14269214080003184413000040c44140c034200c031240c0d5450586182401c9051300d01016556150340488081205562800403401c0d0303a00d03001c0c0c0010080c0c3e00142d02170442d0400740380042c0100034500b28424980640307442e1118482003c4201c3e01140d400a0b400191000f8080400c04002d54840356140e150404445c01482c007000100554450001c02c0c51380209450020a1030703080d81e0340e041b00c580401070b007000b4282250fa0072906d18015030020540c411 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 903151303 1250 903150053 903150071
    0xc07031209030203030304030203271309020a0b04080c030c19060c0614070c060f0e07052106130b1e181e01020a0e03010605310207030306140907050409 67
    0x107101c1d005a41c1003e5014000001000140b50b0004002c1c00055101031035081c0000c00340d0307100050170407070070030f1594090390207001e0628132a09604880e0720140010070090100759103c110464560007a03208483c80d400c400c10603c0e01c0c0c81d0030322440d030305140c0550f404c4516915031400d000103031066005007414060031015100c18081d06501240c030300c8032804a1380f0000e003440800a030202c4249403044900a0a200c940c3c055006203000d81c0005d00119402001e41c50f09182c02c0102c100d090b4400040036400c40106c1d40c48010081058500a03c0368409d80116407489051030416941c006040ca108950171441c40c0954161414000d54440c68542504010f204480300b05403d0903090b58100388103661440c0601050310041d401011320080a844d19440c40c12118103043c280d8140344a030b15402240d4601240d906c0b8050342c0d19030000015240c0700d41952081e00c007803100300d0704800c0c000da0004c1d0707441707005001c61500e8500a140d981c0d011200b000303241c41e001c1c0740140319120b2401a080c080ba16910a5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 903152553 1250 903151303 903151307
    0x5150a0b0a120f05180d05030105040207021c030504051305070905120a020315010927020607020d0f21031e1a150a0e010801081b0a0308030a060312050c070312 70
    0x780e40d034070040b50000e102426808025030094001503c000010541c03e1010b8405e2100010307a42c400c400460b2076003405c6a18010400000b504058000d0b60403080746a03050000030910408401541d12a850346607c441c1014203001c4414024488042007501d440300707001c081034104a407101104d6040f101c0700c1d421120345642070708050304518020340501c03075252902030081004401c0d60695000800401002c0d00000076241c5104a2603c1c07035410107031180d408005810400c0092007114009810040701035125901e600c1210700e4081c1c15140b40b085d00c3c0c0c80300510304294610000440d01d40c079090252030a0050000136104c2c0c440324400c2515a0307000300040c4200d01c5114446820002014101001242401c504440c0d1240c040040040c4055011401e00d40c0219803050517940c980f0010b041607618140e002d00e540c010640020760000b41f000c400000a03884000541c4114400303100806c24501d9803400010740041802e01000784141406070103842030f4005090703412a6000f450100542e0800c00741 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 903153803 1250 903152553 903152567
    0xb0a0c0e0d03021b03030412021203041a03060114030603060f0a1b17090a051e0102120403020f070501020106062114072a0f14070803180405150a0b0a 66
    0x31154024030030703641c1c6005058000c02c034044204814200004484020420107450b44114000d03613110418403081da078007608201c3c00c81d00c4c98078280401c403440d0030f0b1107050350f034643c124001e140c1c90300450010402106580c0032030114402c0c554441e5840c01d5080c00300c0001e441303580040180d81048030000000340440c0311604a0301410001e0110003c2e002c041180c00ad0804540040e29020000c222001c0f030035502000901e550388a402c40d000d4030f002c00a220f0010924200c28905070042d40d024402d68081c01c18014110340958400d4004000d54a014040d007420302140350701c80c605592400508000c03a5400c00741c1405000000024804400340c01041c02008040035408090100e03041e80800c02c51603044082205803412041030b0354074120302002100c02145001100a00305100e401640c0c1c005050311030703180c5644801c8402c2d14480d64030345941a03d150010a503013250100202c210700504c0c181407203610303004180c0c061404201c4001c800441d81da2132b840c0c8121145d0003800544840d8007803203010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 903155053 1250 903153803 903153827
    0x90b06120c06030a020a030e06160f0e1011100c120b0103020705060112140109031b0204091a241507020102100603110901051c03230d020a02010b030a0b0a0c 69
    0xb8641d180d040ca060305000a410041c00d00020a14102c1301030514480003d50030700c1784d00c0d1340c480303a01404000c0304112600c107040e0010105002c0d500991094581d1400120400d880440d81e0b40030300e552102c00c800d45441c3e40b038001c00700300c01d2505110400643d40a07084040d1511031030300124450010382c004800901c2516400391041c01800000304038406807015408004e4050804403030a44a410b404500300d50207200c000b8041000c2202029110b6440c400366a10706000034000144100262181c800b01c0c0d000342c0d14212028a051f007045040d1901c1c1c0340e0190040c58030000c00340741c405083c0110b18102c41107844542d010001140782011607208000f04114090750240038080c199072032504104c2c82002e52007182c852001c4200100d241d04002c070300c100042071018004070b2225410346090381c0d02d161225041c4201c3c2c83c580c2540807541c2c40302004021007200e044005a441503009070003802c4904a1402a2203a080501064081640005e00c0c0d60440c80000001484520701306094450756010b030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 903156303 1250 903155053 903155059
    0xf1302040e070f02061302010804060e01020706090b0112020312030c041e030507120b0a1104080f060f060607030c112202070605010501080c0f180405010f0f09090b06120c 75
    0xc0118100240d1000340d8059501034072040c1d052040d0703200070303070f241d03c4119100c1e24550504481500590303c6450100e820601814001034218010702040d13007664007610086d00e0b2a07440b10640d0040058141d916070041840d40031400f06104994006900c0701c034044000f03410046c011004c02c40601494044030300074002841b140c00c488956560a58035240039200603281402400000100c0d140038010300400e0351b40c02220841c0c950368100045000b4841d12a082010311000c1c040440c42140421000740404000c10003031145c0e280060340c03005504001010103001e40400d05c05600000d80101201920b190b02012070092840442c011460346451701001042c05010307800c80c6074482d0802e074001c08400e4010a802d0101ea80c0b910015610b13200700b81c03140f480200b02002441580000040132309144000f483c401c5045240c03060001c0d060303d1080e0007403035007800c0b40c2804006414004400030300400206900b80245091602d840300c6040000703184900807100490400c9180c0c20611420114010017 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 903157553 1250 903156303 903156307
    0x1012050c0c06100e150609041a0a09020403150c020a02100e0a1203030513080f1e041e060c0201020c011b06050901050910060503030a050a110a150c0c03020c0f1302 72
    0x1c07408009108921420701307a14102c0012174410140b203082c40b07030101405007006191140020031700c0b0003005100505140423900d09d81c1c031540742ea5118450f00c000c000504015883c0d90075402c01c0150300101c16000c40001c1d2400100d14201c6030042034903104150100c413024944c140308542602e008107144070540c3c0c4241c40d008013159a0f144d421007103403240d000345d608110325918500c0074a010354000c0c0014100c2442801b15450041d4980024101810a1085581000d2490024102c07940107074001c4003002c6021101154203000030324601005100502e4580f000a5803a0000713500d4802c120840d42c10402c82c80c036840741581400310a40c1150341d000000304094074103c18014020103003980c000e0244d024000d03c5600500341c601450050300d04c020041c600e010101030003558954406500f45007400702c094074451180800b8800c50150074005c5100003107882c0c0f03a00c0b0060444030342e60410b03801e002c86d03c9011008a6800210300b03410510030341e004641c00540c0700c000741d81e060300c03e10611403280c00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 903158803 1250 903157553 903157561
    0xa0606020f0d030207080c0d0302280e12030409050c120c041805060a0e040f0210022e0608101a0d05060a052806150801030503160206130605030f01051012050c0c06 72
    0xc592b00911880d1081c0d03980074003900c174001800550003040d40000001174907c104082d0149840c050303038a0303d0302001c41120703d01541c43d002d0390309680c4100ca1119a413440400c503500400d000c401c806500001500c030142c60315040c42c2014480c0c240045408041d90b5070380d0300044042e160400100c000d4281c12400d07119034a090b2501c4010195440800ca000d5900038012000940c000114083d4460f0300702102c5104803000064058010341c814454004241c0324103000480707000030306c40c04100403010180883c1c41c0d0b0708101c6003041c005407121418060150031044030701280c1c0124005420100303080000c2116115000081c60100e82c85542c1c41c051010200d00c4ca2143e00168810b204444040c8211011080702c01c42c141e41c00d01092002074000e070010400c1e40e0070398180010560303c141c8024170310b5040142c030900c2d682e2031100329000803000c41c4001050003481c0d0300c600301450040000f01c1c0c000d14440d40d41407000b066800d0701083c0d244201c1d107520214900c8200368081e0344d4005490022101c81d898 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 903160053 1250 903158803 903158807
    0xa0602030a0b0a050406050609040e15160206100f030210020a14010c120b031c09080a080a020f0c030712080c06090a0209092803120509060a0606020f0d030207080c0d 73
    0x111030b50440380300354100e650000b15070916018800854200a110904109546060101410590b11403100a01802c41580c0140100c1a160f900845070a6421001001000002307894990003a10b10711490500400401c501c103010601d040650394191000d100190700602c0070380c0740514100c001030442000b1054491170010540c0720803602981a5a403448510b17010203c1d40032504030030016901504a24082c650303816290210b04542780c4540b0303050741400e81c1e8111041c00c3c244107420442d912a000100c2081190741000b006510030310103005044024000c0002941d81e40d1140300f000c07055196240781c0001e00c14030030155186000315900b83c1d085031505c291035545507040c42c0d00423072140f01d0503c0444c0e5048400146c0c29a4003100c0d02e180c01000d5030710812500b282c48004000c07803c006d040d1040b802142201d005203809251000b00400041c184410740400751041d40d003000c01158001c0c880614001030000e088581c41807a070400503915200340c288a2654400d8030861103043c442e1001c900c030302607 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 903161303 1250 903160053 903160061
    0x40c02011b022514090702030706020c01020706060b212a09031204120b06120a0b01081c05040b072607033506120703030e0a15080a0b030a0602030a 65
    0x4030b1003400402050207450300c3d0280180180282001034400d60100c03101403e0030001c1c44c2e005401c07401102d040950039036600341030740e01021030316400780d4000c039500b41000468007804016082c190062810450446424140c000c3d040c1620760403034209401040c64084000000e040515104071440c0901c4050041403e096228110030383c00fa128642248401141c894140c40a44181c85010386c0d920003551240d442d8504064581e5502408082009180003c20030450624030b1040400d200c86614280e442c038185a1801058108420400080c0d003105510070100d07015995501d40340c0e9111401307401d050788400d2103249900159040c001141c10b200821101500280b4440c2e81c482c0200807400c107404050f45450f940d040c031140781c07004180c6a8400c00a816590101c809848052820941c030466440d200e06544140c0200b000d0407555003550500d0580c1710060048031190240030061418028508200144240d1200d0b607034903041207981d60144070801c1c0c4c6607000002551281880b50b2084014 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 903162553 1250 903161303 903161323
    0x9041b0306050126030a0c03091d040c0504151208070609140d090e0c280903061b091502010213060305071205040c051201061d040201170c09040c02011b02 68
    0x1052800d0184521a5120b88030b0307003401300544001d07600b0000007031410b84485103229400c4041c000c0b03245005c9204210380301d012140310b6008000c0906070926041c103803400315007500903d00890502e16450300e444800301d00582200c142d161150751200060600100074003c06600801e0f4605054200050100e000303081c60283c840082561110b21110006a450011903c9a040c403100a10000b4601100010242000138242e0301010318140410442403248a014000500072904410f028014000144074608008180c040b03d286000a1184040e10800007840741d41814011000307001d698a100b0340503194071a400a0040400c030361a2400600a48011100c1c4000110441c241009a80c9140103660140e0b4000030580392007030a0000307004c9000c6400450040c150b40b1050002200340412585040702a154030140c1110304162000400e80d02900b4003010f455107a0900b40034650704c1800445280102c21100042c00e1440182d069014102105d5400d00a07d140c2480c0c0d6907494000c1116488 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 903163803 1250 903162553 903162569
    0x70f03050703110d090902090111010f15090e0622050304030c06110109031409030705030a05060a110a020613020a1e06120c230f03070509090a020304020102030909041b03060501 78
    0x1209090603401d95600c0e0084d034200c000a4812000f000000119801031030006011325040c00c003503040c6140503082d2447c010f11410125503030101084900c3c145503840000c1c0c46005002e108031700d102c42d06143c3d900d0380a0850080c40390203101202212010b1002c0310055948941642c0c0c641c1d9481c202100010958803900001c2881081d4440c0307814410310608200d180d150311340041030a1064400b07800c940040f0009605440b070000d010440741e501b0440008200e00ca00c00074520351404103030354029900b9048065a207010140985820070b03802265190780312080e061721500010513400080c20b1020198403000e003414841b40f0406c551503041d403981c8260380140d158400d1090010a04204440721001d1000025101000c42c10702e0b810329a2001000105a1804074104070783d107102c2015980c410381d101e00c041400000c1414035070803d10382c00c550040c0546000c40c2545040d40001c2d4a9100d000d03902845121410002010000180a08145000c200e42c3c03040b042500c03031405c0340c010f0101303005481c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 903165053 1250 903163803 903163817
    0x905010f0504050915070e150405030c1002070b030703090c0806041718010e0a08030a0c1a0103030c0303021b071221050406120605100306090b040c1d06070f03050703 73
    0x15550a02c0e00816014051090061400100c2044403101080b8040c260704204440f500a100031582c8403651403030300d284c42040309540e4511303060800d4a4040348010280c041c0e01c0142180c00303255000700313000741101e0350203803000e82c0d17543c0380c1c00200d0050030a040c0007802a4184200401c0090000500a214a214049080c80c1c4441501550030760700500b00800c040001740013920003213510402013060364040c0075015841007074449480c0c9003036400c440400750010303d0741103601d41806541d02c18610b1035807200207410000d50540d20001c0180181c2e0a000e0b00381500050425511000b00d5001c0e150f460b00207003079550359901c43d4168440c1046047c0141c0e0a91020800c610b04180c1e514030a180c1040d01344c1300c03245868070386034040d80c00c100160040f0010a966190014058a554000c0030f50394081d590000751032410a9140c0d012640c000d10358a00403881c12071810452500b00300d070140e2541031040002440321074000001c00510035024001c0a120b242040b82d010107802c0340142c40141e209890b00c0c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 903166303 1250 903165053 903165059
    0xa2109140c0d0809060705150a0519091121010f1505121b01020a0f0309032009012603040f0e06221505060c0d120b18060103150905010f 60
    0x1100300700b84a6809031080d03070104028400303031034610700604a0301c0c0310784180c0c4c1d443e18000080b000c0c1c0f14400c5030b1010056468404000404e21030b0003105c00319032000041080a01c0315500c4c0d818889010a9503607000d40280e003442a001000c0810344500781c80c1d408028000421001c03d070170040d10034020389900001034045d01040354a01426441c210103400801441801d41d084085020300c0703464501281540a503010342008502100d400108442c0a5180c540c0b61916501c0c050f00301080030f0041001407071002070500310550703070074005c0d130304555074510100d50943c408562002d000e20002c1c607500740703440000350004402000024090464501c400b048071187d8038001844440d00c0104500b140440741034001102d0140e840d806480d00c1044441e1059980b506d0b0b002040303950b403100c06015856402200350300c0c50079030b00c1003202051821000d8148956100c071000b0034004200c014024a031403902c0300010302680d12071352050300b1f4040103660003074046075502e0584005000a006030280c000c9240804 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 903167553 1250 903166303 903166309
    0x1312020d1d010e09060103020403050d05030f06121902010513060305061e090a0905030f04061106070e06040e191b0306140603150d050102031f05150a2109140c 70
    0x400841c0341c103840f402d29422111040090201c4024503e6051603420321010000c941c0030050000c81c034002d034031496030b070f401c042030050141840204624441e42e2490300400e40a6404580072a1044036080f01d0b05c00c1400703034070069a580c040c1c10044121022090350028040f645034101600aa509403845042d0440041d00c4000c100c9150f105681c000710003a000c20b04e281a035502a0394103d00940c25241000104882001a9400382e4031200006500350300ea2400d1040c10f0140070b0f0810500e0404030680390417100401d1681c0100d200d0f103075840e800f84000401e00006403407080c0640c014144d00300701424115198030b150841d00800c1000103840c0060100d514048c0300d809030014480107190900b142d6482c0d0950400b4070f4010000703900280d40451000004101f4000303103010300c020204401002a41500550008116a000c40e1203440655105003c0c403050300122201c0c2041c81c640b80c01002d40c0e8025030b00c0c02894098400c10b0301d6182020f54814400c0c054038911000c0c20010507a50320305114020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 903168803 1250 903167553 903167597
    0x30b090105101707050702040903030903030b030a02130e1509030a0801061d040b01020109020901030c092f2b05040c05060309070603020c070906120204050f0f0604051312020d 77
    0x82d0700c0851118811a0848840024815800442d900d0034611307118a503404502500d103010021800b00741c8800c00c250415400d4010924900000e400034056400e040e0000340102ea501c4070000300135035403903841000d80341d400d00155140303002400281000b400c1c049101030b0303130b0381c404244103000a500708000b248140c0f0520080b00d41c0300c20403140c150b08003030000800004001c40c4049905545d61000990010b0b00c0300d480842c02076010744000d02d100f510b1304000c442550f000000c14120403060084406852822000510f9680049a6019100c960705c0c042c505803060040c030f8840b2126000784071204c1c0360400380c00807440b0314400c2c0d0f010400300d40d9900c18420140020744070800c17580c228483c00c0c000d29119501501d51200f0301c008503821340381d40b103901100f10703540c03600820f1854250561138010750906005441d003080701040f0a11262a24081290901e5405000144110780f2035000c01c0400c1c3d41007401c00c24480e0080e80c60542c1e1210340401030360342d9000030301c4880030486a00c00352410302d600d944 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 903170053 1250 903168803 903168829
    0xb091504140919151a0f0d0f020702030a051006050f01050304120311040801060915030209011401021507120c0e060708131e0f0504110723030a030b090105 68
    0x80c4109841d400c4400c1080c5080010f1071075003004442c0107a9250b5504030f000314030312001c0301440a0601820241071400a0042c1081c480008808100500c0c2d940d490394201c40c0e004040040c00291281520710705000b901c10940d010713615104140000003402000b192003503443c0280d000811036a0b0350361041c040c0720b0315801c000c1030220b9001d10005000c61031140c482226181030307150010f602c1b0201c13400c8a650750402d4100c02c1c0720ba903680c1d806000300c001c103214400f800c105403501000401e2031903001840c40c600502410b003425010700c2e118251a402040880e254840b00c2010b41c94a00c1c2258001b4848402c0b61f00303100c0154203140c001110103000d60b200c3c0c402070b00c028044600d0120350fa161000103074059001001d01c4000f03a8000079030340d1444406072442c007150310f5400001c10300d0000190103164a5400c403c0c400d51904040c45092500c03441152800c40e4401d900c120703486a0986101c0d1502e114040c0c61046020001c2d121000580c154050580d60700c003201c100e04140d0b00e400501402c1d15a80b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 903171303 1250 903170053 903170069
    0x3020310080a031d030c0d030507110a1701060f050906010f020321060f01080c0d240f080706090f0303030c18081c05480309040b100e0405070c0b010b091504 69
    0x1f00c824400300748590300514019000f9851400704004c0d0318045014180140e206002c030302196105200711400a020f003500a0104003094001d150034000080c0c0310003c080d08040c184080503001410040c000d03c2521044804448200052031100c170b2920104401151407038810f40d1008a040059805080058010762401c15a1410440c0492b028801000c186410072442001c02e4601c15605281c90100c8c1d001d48510386001903950303d400d0511345403501326007006060000e004e40c02e100b1454581d60a030110394051402144101269809441ca161603200c602151007200d540401c1b103440020312038840c0b070101348240f8844410000304807894042d5000c03101c440000e01c011120380c903010540420100c4083c0e06480c3d20b401c8400541c03008030b4403004080704940c02c0810b04064924040c0b00b0050400d4081d540f40c683c0c5160f0403001000e100e006401e0b0b51099503500003081030b29102d80b0404106c154070085944a035611303004200035940082d69024491f6052a41e501e00e480c4101c0e0989003124004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 903172553 1250 903171303 903171319
    0x40507080c0c0109050609010e010501060804030c0222090309060f09050a090203091c0906090501110a2a0b0c01060504200307050f04240504080c0103020310080a031d030c 75
    0x10140190040c0d2003094090a00e64130b5000d0400403c0081c40b4070f03406407500d4000060381e0b100c06e00c20719013901d80590208044c001000c0c108404650420400d0f900e156044440f0039001030103094003070b10030302d10300c000140281c640032070300c410160071401220686c0d003103440381e508038000c800003111900c00f540103158002200c0601000f103440c031034003c1e60700190070209072860400301c42d01c001e40000310500e051000648600c1d04000f01a00040d90348045c100038030307100c0f0003090024100b079030303400900c080100068158221031380940c1800b03031515003180041e04d0020702250b484402d5900b6400440002625519180c000200c0303203040c0c81b0340d144880908100e0540046042d20a401540000f000c00060200c00c0012845000c0a1801000640504200804400c0100003030441c07030401c40f00e40406102c410030061221400010720034604480074038002d40c1c0c0342da4000700002e070f01c0c24540c001070342441000290000c243e005402c0c601512489030401c3d4000502108069032030100c44e141503080100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 903173803 1250 903172553 903172561
    0x111b0607020a0f061b090f0e0403050a0f020715050d0b030a0f081e03010e010314010e1009110603010605120c12040f020d02090906011a0c0c01052107030b0f04050708 73
    0x1a803000111404d000307a1001480001540c9800b01620341c000819001030005802402034450f54130026000d001515820022850990380c058507621030503d58906002d115900540418420051000680f107901c84460001c503503030300b010b000c4c0d800a000320070f415420050240d6442c10000744000c0200d800ca640c0c8140d0f114580c07105817482e0703c03074840c840c1c64075800c1018100c0421584011402440c2184003080150f165051652203072101e0000c2e0000d50341000103002c5503000000e5040c40b4410490000078207000d05140c1102541c641004907504103e01000014000f83c218010380f960005c072030b090503426030350710384070495900c240315103500c0e0503024601240114110032112080701e40301404d04040204070350002016032908aa1f020070035803140005001c2d030050140c803101c05c07a1403001d10504001d00300380c801703880d00401c005e180d04200010802400001d03940c074080c4111895807035002e045050881009000d0086100654000c40115079807090720b042c1032194601c501c0065461403440c3d12 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 903175053 1250 903173803 903173813
    0x160b060f0d14012403060c020f0106120b0601020604111302040504050c070b070507200d051e07120c1202041e0510120308060103090c08070e0f0c041d0415111b0607020a 74
    0x14140b000e031f0701144518200c0685502d4240304030005851071b00302030003591a031484c0516100800034a800d045402a1007484001000c100003161485021502c0402050161249500034011588002d030b201c4c3c1024240104600c4d48070081010310f009191107039a0342d4404038190340074440c1d1040189862509421a642c407004841410b020f508018601c0b140c01100b621070501e0f0840da140c862030030717181c10072050115420800030345004180301c00d4010b505c1c130307543e403541c0f10300300018402e2102d00500802c1c0322003159201c0d4010030710b00300440d05450711b1b040c0f050143c1c801480b00300c8200c00c680e110760307401155440259299407003c0d603260fa2591900d036a02070044000c1d2942d10000c81d10010710102c0843c14000a20000020b00295010034100385064000b0440c070150142020941c0c1c1800c21044c001d040c1402101d24503808800440c007107507102c3e8680381c01010052038410218030300c1c0c00802e90f00d143c0c00d0001410901819108007080108000896840384c5003a035841c00540e02c16803203a00012 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 903176303 1250 903175053 903175061
    0x3060408030a0c02070e0a0f0e0f03040b071106120114040b0a061115070e010306050d0201140f0918090606100f0c0305070512090a0b160b060f0d1401240306 69
    0x20f81031050ba100541d940c550817803140c0068450784000e40d10b607d1148511100c6200d002030110705600206011900e24a0540c0c49201d140260072a1400000e103076014048038000201c04c01f02c001c2d05041d51103400c400f0701d00666400b801903070100004400a559549010700680106010043c94000c01500d404015214090449586486801441000030b1070084051a1500c60070482c0c4031405507020042c001000c0350100d401c4103114824280044015036400302200c860b02c4a0320300c0c2d182d41d51000001d100ca0714040c80700d0796a4401c0d111010320920b0407486449070301841c01c0a044901d561644010070504404800341c0800081c00e06282407000d9100e107100480c094043c0c01c00d280f0780800f0361545804d00303040c45c551081c004400110030201e814032202c40c40042031007002d580d00704414108080d03043c028814014101c18004004a491130740c41d401030210303080005082d85e03000440b600c4d0040001c103c0754507060311546840c90402500a56070100202c403000280040c4000d419981d411000b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 903177553 1250 903176303 903176321
    0xd03030c120213050d05011b020c3309060c070609050f01110606012109140c010503010b18040e06040b060a050301060b04230a0807031209060518060915130503060408030a 75
    0x15074841c2e0b035007111140400d50b442c56003401c275409003607003100460610a80003921090143c1c19200d40b00e040e000d00d010440b5038000e07020808061a07644856030700080301e42c02080b210011078040c20400090103500041d0010480f40150f8000c6440810368005441da0140e400c2d408210390000c00c0052600c2d031041202d4614021b003580765100544440c036806c000c45150700d03400c0392400f00042c03120001e908100f2201404050901e4518a99070425004042ca4040d0100951607465a0030015565523103a40261480c100780e4001c8480c1460141441c0a82090981c3c1241c02400d01180200c0d02c0c0c1018003841081e40d01000a141c90103103818010826031450312080781c1c10340452412409960303585140c80d4004c08059004080440c2541441ca4005407081000d40c24082c0c042c03400c0060542201c20b6603402e440216220802500007008141b40e0f20a031700043c0e0b800740300b4100301d01c204410300004d008612031044000d0215501d4800b071690720001a90090240e81003807002504807a07180c2c00040103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 903178803 1250 903177553 903177563
    0x40506130c1b0b0603061b071118190b0102031806070f0b0c0a032f030901091202010608070f030b01050d150f0e061b0d0e010b0d03030c120213050d 65
    0x81a480091038248405040b0040720444003010502c102841c08021140d0000300b07190400301c0e0f601504032103805900c10120010038030202980f1040b0b07183c0e03520105610840c0d060220215610307001d44890b085940354500540311925040e0403648a500c000306899690103001d072100002060981003240a80050381c2c111450102980404c00080644031401c0c012a10ba000e1365498052600700038094800d85140c000c2058420808910803004000180003480c3c1c48810715030360b81d03c504000714090800618058954140c190f40c030750300c096056005004640440081d2080d151b1944a5589411483e00c4094110200c400c0148841d1030030500551b6114400c4400103000502a0605001e83e00000d0b80034680c00d07030300d41c0e041903003a00c01d1100d298441d850421054401203e50240803407809a0090020b4680e921a50400c10400035408a1803500700100224506109032800601404200ca1620001050802c000c0014144c900a0701c0d84000503510000ea60381c1803000740980200d0359102074030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 903180053 1250 903178803 903178817
    0x1e030905011401151b080c010605090f0405070e07020a050a030905270f0c07141005010503030c0706050306061e1308030a0c0f08160303090209150d0212151003030806040506130c 78
    0x40000c1d800c100611880c7e42000003c2111880c050401024890041c030705036028020004110000303001040c0302095555503a800c40481e01d0700d5000b28075104624600504030f02c142c1722410141604440c10f00f003180d004441c03010600c0f05510041004040c3d50100000005444010400e8225101c04040c0c3c04400c0c140c40c0d5040069585a0382001c070356024080d015900b00360310041c1076100758081e00d40905000d030000c2d480c210012030460758070816803043c0c5017009400310106005903220401c07290b00d82c840b0b1081c0184a2020075942130b26038882645040c84805035000040c20543c0441902c04004050301c43c020005440d4964030020003001c0c41c2140c3d4880200b20a2640c610b0748608030051900039500050070314010701c18000e4560b000b8041c0311003203840000341e10342039960042a440e01c81c0d0641e0001d012a2903514100e1500e006d100c0600d607150740030001c0041c521441c24080707003101d001e66907110040c0c6500f0700384000ca5009544060b004492030f0107160031f80038107402c103100e140454601a4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 903181303 1250 903180053 903180107
    0x60d0c0c0206030a0510061403390d051621021b0c040e07080c190902040312020d080c030708090c0405010b040306051f12031e03090501140115 63
    0x707640342d4000c40d40103130001d039200306100703417020b2809954029007014100000b070404001c0030300125010041c64a04a41c051031009201c8400160b030320541101c1c0b1504401008985101c098096082040d14004683c5840300103122100320700d036082040480c035111b86c1c0c40c02800000c80c2003082411074580380c10640802414120702d408640220803060760b0805001c203680642c042106079041450076150941c040081480b1030800400c2851407414202c4448592500409903008000c00d29031140990510101c1e0000500140d00042e050030415035083d03c0c0031121100003502c0d1160161030500d440801400003a000c07a011b403544c90f0300700020404407510340707500e44002020354909800210392040080350800c1044042d01905422410700d01148005030148110b69619041c244240c8100c0381f0011404018540101d820300c00091440003048070501b41c6c064042c0c00b414484a00300c0d26503180080040300750040c0320720b0605951400c3e04210030f181e0481800c0741c00d0400d48614180e0070300c40f10f44003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 903182553 1250 903181303 903181309
    0x10120f270204054c0f17070311010e011803050d09080106030312020f09090103050f120903060a021e0f07140307020102060a1d100c09080a1203053309060d02060d0c0c02 74
    0x13010040c041d4010900040e42890381d181d180300c401e11048480d56121400c01c0c00090100691040150428030b0030458214407280104c50b42d180308051021500032101011040c8040800e50485e8501991540603941d07580b0070700c0c24201c03a4584030103000203031508821200240a0b8008180004042c00403d0030118600d0000b15621403c0e8000c480ea035100114100100710706102080c401403c007441c15007000380c40408a900c0e960300500e15100164001604003e00c82450591781426030344d03940d0a074483d41d004080c8170403640450000d41c2c624681c1d440305124032200101322090f03680d069015040946400035070b074001d0002c902c40d00040400c80e801614030144100b0000d00d00733588461000c85d500c900c0701d1028054450742d400c0004540c101c40482c0f404119006040c041540d481e00c1e0000703036569459000358281c0b0000342c020301c460519500508104180d1666050030741d608a5021816031900800c02c4141140e5040080d04020140440c407031901481d8002a007000c0305041201e8003000c25800 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 903183803 1250 903182553 903182701
    0x7060c0c030201230105090604020c0f03090a050d02130b061905070b0a0b180c0f0318010f0c09120606210c0510120f27020405 56
    0x4400001400d512a150515034240201071030a07070645070f00035441603c2909000000f038140140380c010b20110001c1150b68079264100c818000c840010f0719080c001c0a00915108c0e403101e01e809100e01d84052010a80e894031540c1c0c255070303982c02080d451003c0d00e11000340000d4100ea182c21644a003007405400020904541d0035281080c0030365079103075905d09a103030030074082c1c2d4090495000c044c504843c3c00360507112a0200040d510301c0c210380c2542503485544c802c42c1445010f104010031b040c040144002812a45041401c3c031004400900080c2140102c80040b100001990000595654400c1100c0b90210910864480c001d0a000c65066124440b1110040c0300c561101c1c2401580c6c40204103001c1c0400c034040103030200300d03441140e031054510000c0c243c040803030380c840f04075646500c59080384000754400c4160640c0c1b00ca0314000d5407954000c150003031030754002c240d0080c0e05210000309000706aa240d4000c090391341c110850720681060104042c04108590392201001981d141d2561a0795005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 903185053 1250 903183803 903183821
    0x4050a0f060627080c01050f07022110110f16052407080114060d0b0909012c0d05030903040e0f01150201020918060307030b0906011514040302010f03020706 69
    0x150300c031040d8420f1004402d010001d4503107110404411105018481c808200c28400140918203503031501d6400c1d07520841442003032402076000c564850030410102143c146038500001103c1078a203801884000c001c280d95220f03030250300302c91040250007a20a01d44000d8001a48c40f0700ac46451301d20242d8450f842e0070003440c1440d07090046204440d0000d180e510445501004503c0c103510719504d080300b00c540b84d00f40b0155807407240d140031a50700708001c841d501500c04a40c00030320208040c200f90800034000e01c0c0c42e0100030420610aa9090320024854210030360840c0030b81e000b00411494090119115000640080428001000001a4240030f0710a96010399a01c609a4986502d00004072042c00d080e00450420359005100c82c443c03d603900311404404954907001d03013405560f09800281000c49070b130001085101c482040c0a134580c030008240d8141c81e00b413402c2520703d4501c0b941c180c5501c4820501d641c1e61110800040c0b006500c200070034071100301e042c00d000d81000d250365980000c0e101121 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 903186303 1250 903185053 903185057
    0x30b010f300e240420060a110c0301180b0901110d0c02010b09070507022b0503030105091b07031b0804060819020f0a050f2a06010806070e04050a0f0606 67
    0x4030440030088140860219103101c01c400d5001c55525100245942e500100090280d504910114851a046407501710104130700620740369495102800140c000954408150075510440c01152042e0405108a0b11228208090b80010707500325600d840301403800902d008001c0d503d40a0244150751f4176006015205c00c403c03008610420a0705000742150b07600c10f050f074844e03028141880000743d0801d0031a124982c040da0001c442e83c3c50f460780f0384031000c40a00c000000d40c039600c00c140d007800004000f0314140ca2007100e4107039880d165641e440c240040e008407401d100c01d5040000c200004c0c06082d00403c41a880c10005440c80039944810ac0c490304070342d210001080c10f000800000080607024048641944c850442c101850f8000f0360000380140724108060000c001341004114101c0f030140c6108040c0b41522600103001003032290092016144030b031490348206400403c1b00140407400512410760303640c0e81307000c031180c2104020203005c000d01045403e40c0d5603401011564070501850b00648915 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 903187553 1250 903186303 903186311
    0x3050c0414120102070f12080c1c020d060810020c0c0d080307081003080a080403020c0405090c010e030c0909030a0807080c0315010e131b050702090621011515030b010f30 75
    0x140c01420550009040004843c13081200c2c0c80c10401c1c1c46c170041d2204480d07120041ccc0713640c5070907000d40080c0340d540c010406910802650f81240701c07030b0750001e00c55601c201060300c48600d10401480001c03000013000034000b03803003800040c0010744981845607211400218200109903251200c60280d444a18420b000418001c02c00c0145a0108000792a0040a031001c00c0589044c41c2e2040c2c48903402070986041000801000085540c04c1100e00c0300b20304010130449007810301070740c49507499100c805c50740702140a41c000100468011151140729400700c050075884e40d9203940a401c4a55001c8006a040c0032080444180b1030711043c940c041c280c800b407280029124a000000b1450300003c04100f020041d0030400e40f00103171103001c0303010b40200013500d0344561051100d03070552002c1030700e142131241586090442003414110712a880d04030b43c440b80a88000604d424001c8040d1981900c1c5940460204840b100e4558885d1840d844141d0021082c100c0703007200980445011404c00d602c8181582d11 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 903188803 1250 903187553 903187583
    0x810030c0b2106010f0807050d0204140f0d0f0b10081501170307031d04110d020702040606090815180f0c0a1509060c0c1706040303050c0414120102070f 67
    0x440c858021a0196005506220f440e0003800242144454499081046203c6010032002400380007910304103400100c0542d242ca0312801c024004490381c45405110b0180300c030104629091146182031034a4110016001425282d21071000c0f01101410001c20b14144800004450300c0502c52150f903805841da0480c4913502d001c0b18030442800b9040b2149041e00200107100c006a0084000d101c1003400000d0800d201010000040003086000e0303481c1c0010f07000046d241480d00b03c030340c0201192842258200b2103180c07204004c4402c5011800354484e10b0340300001407041452441141907000328100740b0309001c07450302c180d12410918146441c020990008183d1000f610f01030340c0c2c41000e031030726407400b0810492590000301240715500c201c8042c011009403446c00d00504011040280100921500b81031500c0f0340481da440d5400c4500741c00292400e00411014404401118102c48060f20880e02d02c03140c50007084102c0e000b01e900d4211640d800c06c92180010542d01107940810f0183c03100c0715079041 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 903190053 1250 903188803 903188827
    0xd0c120b060603090c010305041a04030c0b0f01031505281509181205070507031505061e010302130305010c030e06180a141e0d020f1209010810030c0b 66
    0x80c0034003a90300c140300030b00803c44007482c001403883c158182481e0100d4280c0325802c00040c45503002c5c0007100c2100c00c4104000525400c0400450114030901c00015a50750b0016521070150081c0001400038001d1210070054440b0364001c0d68200c02e00b0140c000b00204088000b20783c1103d022110140c550300c8041d1000a001da0b0b8401d10b0040148180600c071400706811f40488280f190003009010100140741c2c403102e244240180c8000d2a0b200c0100e030221912402c01039010820003600740030440c104400501d042c20400f550810040451103802c110714007907401136019400c070001d0403203003000ca15000404103c0901a004068556071000105c5503c83c14a05040c10380c01004d00311100c2000c10000400140022105202c6400c41860340c03001000c54041c03400c0030b01c03504103100660700c1e07100c1e006596500070400181201e500e40860316000d40100005454200405115544940130300c5013080c954040c0300f199034440540482030071300d40d460b43d4504c0c45029882c0c0048a04240104043c01100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 903191303 1250 903190053 903190073
    0x206181006170c1503220b0a090c0b120106050901031e06030b06060f070b04020f040510080712080f0a0207120639030b01050c0d08092512020d0c12 65
    0x144162102041c01314503040202c0e041c440a88041c10801011500c0644569610340003180c01e6809031400c81b450511145203805010803240c181c0722583c5090000521a440d58100e844079040442020141d80c6840c038262100d8010038403aa050580320140803840082a0403955922200c20100103403890441c1881014414014409805454108401a4000381a0044d100044c0d032144400b00e059903144080380b8040c1c42c0708150368100c3d05040902031951442c40151049e01c00440444500035911340884030460030444001d06403807010406128034003500b00050215860a0040318000355803103d103d41c282c1c5556409031034082e070322040041e03c241c05943d140e0071a60424100540c010701608031045800410702c1240600d80e481c06038030166402a810340d005a001c010a0b40c070a0202c0741006411820300700d4183c08140102048192080010807141820020080c5000c0100782000c4584031400120441030380e00036254402e000000d00581e00e00c502410201d010704500503010318110503a2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 903192553 1250 903191303 903191323
    0x102a0606090e0d020a24060b031e0c0901270f0f060e0f010c0f02030f0d140a140d111b0d02070b031b040b04060e0a080d020618100617 59
    0x20381c01c064444564243d00103480c000050700702d00e146407807100a00c4851940181c085201501b0781c10305800080300351001003d10702c903039102070a000c03401840703420200442030119030000c01c1d810f0a1000750701030b512a6004c00d064401401000c4415816080c0ea0382c61800d0741d9129101c141c0c190481480590b00142c1140c0051002d81042e00c900d102460004507509a10b081e15410860740c0c141c0da00602ca6407114110707a10350050142c94003071004c2000b154a800c6640c6186000ca15500c54100e01e510700c1c0f0b41142c251207440e640f105404000399031445c1c81544041040b921064030f0706680d85010f841d0341300504400c611006480082c02004842c0e80c01e0074440001c007025500000c0c004c10850744040100e99121844c54102e0458005201140c00140100c3d00061584da101241c0443e9080d001403540032083c90865401a035940c4e1202c4c440d680d500b508500c03500503000700f804200038403082c1026640c0d0b88010025101154048a00003081f905140d000c540b025420301401c1282003024402c410a03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 903193803 1250 903192553 903192581
    0x20d0c02010f0f0309020d110a0b03060a0b0c0f030c0615011e1b0c090501170712030c031b050601062703021203070c0b03190209102a060609 62
    0x85100540010303080901140703000c0244542841d1a03041c061003039000e070780810390040002c140e01c812800c205030607806155902d03014200841001c40c04002141c2500d12900340281208044c0341810f0038501c0c0e580210180e202a441105483c040c040710510245c021009010002c0c80185880001c1000030b1807441c1565042c011103030005509850410400a2200201e041c4624420b8000504030200c00c54440043c0041c2881480418001c290b504114102c9031021031318090910340c5004142c0b62016403182d10301510792800f200340001c0c0100d810800c118020f041c0803840d050400d6004440132a116021203554004c00018419641c0207071680c4003c150b440c03820762002d0340910501c1103009860002030311401c4a2440450010700070412500791640c40088400707025507403020b440d150b0b00190795108a03180100b01c558a0407501b0700c2914003c000080c00c621484400c80c000f0754000c035561840c10909402c0000020071011913100450035144100d00000d0740c0d500d020119811124624110f901c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 903195053 1250 903193803 903193817
    0x2130e18120c0c010f0908030c10050601030c0f0305070306050402041511010c0c0809030109050304080d090b120105040f0902030105090a050105010e040209010b0d020c060c041401020607081803090916020d 90
    0x1a42030400030364000743d50700c00c2c00d00d46030740d00c8000401d854030324880d40306803031511000030418600000480c072980c0444411105200c1c0d500c50f00015800e0307500041004002661140644a083e4840c0e045983c0003129030600146607500c403804503060340d1058200c600e072404100d06094a103548080e6030f034a150004802004003c0b0640c80c001d00c0030009450140c00301a0204e51019241e800f0752110400c1035000003107031754036541e170503110b51a0100c1d0010301c40800d40f21140010502040d1003200d12241084c141d044091b82014104030060402406800f0090b1f5070319800710040c3c80911429000c1d113140c6005080b5003445203803090070350300305030090b443c041001130900005131600b940f13460555404101480e2507000c0c00141500030701035200e54003841e00c90107091008211201c0020300c00d4070754051026280350560801a40e4801041c0d40c00400100713a00000755100080d03001c00712407403e003001641d252011010000c5e161860035640000c0d03280c9003d01c5d66503280d8040005051611141c10105 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 903196303 1250 903195053 903195067
    0x52150c0b061e040204090603052104050405090114040305180409020a0501140c0d0804060615020c19030609210801141c0f1a01050f030a0602130e1812 66
    0x38031603040203484140224003440c200e41c102c1540050000c140030014100315103a5a44451442c09407000380710540e420b0040408208035011032406011450761b00c003a000380f0701803a00b400d01005003c02401e01d2459580c03121701a14030440580c825018030301070368815454041c23000c4001801040504018032452030130009000607161540c0c0041215002d08280e01c400d0340c00540310f007151043d594181d00a0040b00028480d40b60042c84d070500441c003a1500300300076520b0f000c400300013012024411000d60f004500000080c83c1c80707401602001d0101000200a6a40c2d036108816614a008222419481400d801c50000c101c1c1303030b41044040b5589421085545807003030107a06141e15142c00b5005810004003a620f21070001070400c2e1240d484040d000305864181441d2506841c0000c201c16002d110768000207051803c0000b0411100e4002c010f031241060319600c0318029403101e00c001242c0c001d07000c0d00051003110314204134400c018085c41d60400000002c05242440f120081c140d074107000c144055 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 903197553 1250 903196303 903196313
    0x30f070f0c06230127050a0207080c10050a05090a0f060204080d030614091b220306021810021504060b0d05150907120209061201021b010b0352150c 65
    0x3d120302088440006d81a20340c1c030b1808010703100702c01005c0d1000c0000600708400401c000b0788a089040040700400c070544541a524099901c00d076281040355011000c03a0000c5a000c071280031410388600e40041c90542d94200341c505001003c030040c80401d5840604100060000196918002045440c044c4a1420320800c0000304400b64105148400c01708401072a40f4091007554030451540c4034480805607203142103030180d07000c00300800101080d060400d582d07043c004405d90312583c09801800d03689000b44141400c41000078403c2e9240c0361a01c00e120125220140800e204a008101409920704000c2103010200300240c1407803103030780c003610040040c81c4044174281c001590484494031141c44580c00a02d014284441102041d403001856520341d0000120a034015000000240300c548c1c00641056101d00407101c004880030f4000c5100c80e500341c40031100505042d02c1c4c8000c81d4818078450300444c2c0d50700b03060841c00b0003818806000d0020b6102280c203810b008034035140c40b4440140c56558 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 903198803 1250 903197553 903197609
    0x2390f092703030c040e0703140c0301030201170103080d0f06091a01020d050c1236040b0301050402090423120703080c031512071205070509010506030f070f0c062301 73
    0x1035410003841b5002084109100782c001c1c1c0c5c03002c00a014a8400341c202000340d2030301940203220413404115041018407401c0c0040004038100ca4000460b60b0406c1c900100c4a00030740400112110035594074034000c60910384604c150300d04051481c08280c1c610858000281c41e02d84050b00b12002d1040a001150b2200340005802c4003510f0815100390329109900c0d4a126080c0c1d140b2a40700700300402101100c01c040410300e410b415444201c405000444001c81410300300c400a41c1d029400010303d000140200d0050002458100042058104924004c0c903000f0f0804944001c4452900c04c0042e11006242c4c4c04903445400c12100f040d898035604044003d803082031303036010071507000700030f00f40b41a8801041481a80c00502c0c8501d5140161419803901c0c903102c0d0b419001b200c0c411f1003500000b241900b40801500d1180ea44482d0781c1d8802e4903644401c2d80e032074a080000c9810084808003007000121203010301007614043c0009440c0207642180101c142110503005075501440e4070a4180e048009625 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 903200053 1250 903198803 903198809
    0x150c17070c03170f1f05090a05040203030f0309030c0706030c0c14100606030e0706020c0d0602030c04090f0902030c120a060b03160b0a02390f092703030c04 69
    0x200900103000a20b03050b201020102d03549038454064000704860303000000901032044a01410084540544400b12090f1240d140140c80d04100c0c80310004403150003e41c00382c0e4103d40014102d0b41001815018000590300480d0140c1441d000030464a1140e40704000c2e0700050000c40c1008d110341105000000c0004400d00300103010700c1c6501c1c80010741c8030018014038191200b2404180320503510344001a020301001010b604203840b51840000e0b02c680302113001c903040d64000703020750f984100607101c0a010b0b4002038200341c101c0340100800500380c480c0d8841d40140c45641000840c0c80d10440c01090308116000403c079000f84041d01c4828030300d9030701081c2c02c941c26501810004080c10f0718000701345000307061050a2036410305002e02007103001260000e015102c021b5401c445403400b00d43c820600c1d0a0010020481303888800360810110210303080070100c0741c8006015a8a0100e07000c0015140050695030a01c0380c40701001d80205012804411611004840c1c004501c0c6041500842d03d40c2e20680c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 903201303 1250 903200053 903200057
    0x702090a09140d0522050607030c03090f0f05040b0103091e03020a0206040303050301080f0703050d0503070302280f020a0c0e1f06080f161e030605030a150c1707 71
    0x5812981003001d020b2041d000c030b0450404445480103006800f90840d48611103889000382000e0402044070341c00800e000980307401800c0c0c03c0c148000d91f60b042d2249800400214148062003401140074192414074100801e0428410b1180a1030002841708442c0341d0003040d41054141507072440130503844403051501c405080350301c030044411400c0032814142100070096101a0024000090581c0040918140c4001d0800d44840300d07005201d0380d0b610145d0b4070001785160058035000104074000c0c03000c1e65020b1441c1c01d000d0b1a149100507070b483c02d249203148000b02c00b4654140c440b0415444001c00e440e1180d503000421001d249500c8000007034881b07208480c07109044500003005010804848003660100e008102c04094907018003610841003100d00e04850b8900340d0002c0c02c5030490355015101e0b14100e0311184481900d1a00419902c001c08030b844080c90340380c4034006640d880070400d41013500c4c0280c181945200203001400b042e1741030542c43e1350400213411a5444e592a48500d41e6030010380034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 903202553 1250 903201303 903201311
    0x7030b0a1401020703022119030f23030a022503030b01090524070f030c0b071e12150801141f060318060f0c111c0c050c2805060702090a 60
    0xc020008451080480d00ea100d005000c040d0004031107600d0740000003407283c3c44e12b2441199225045035210b0700c80d150720f802c48040007001c0c0c2c0341d0b01200000310f410901a00c4054039101c04030258255040441c0003071400036001d1030b040703c14585c0c1403040c3d051200c2e00b4a0000107041ca00000101440349050381c20030303480119007100e01103600b1642294100740d400300b003030300503410b581c00c01428074205106d098408500c00780006008611840c172900401c018100038a483d0300c20500110b07491218210084406503035420300b88442e504503c042d0700140098070003c00d14448258203524000704c0500b1603181344c04c0000c030100f41520440c40602c1544c90074540052000c410fa0340b107281c3d038808002d01910f41441c0c020240c0c80c51056404c030510b0b0780e02e04d480304040582c41c2180344d40e0310300340c140324002c034000059021030110b8030036544e0840c2c1c1400b84049070b205010250020b40003400403c0440c443e0110080e04a4640004130103880041c40112607440c2007444680102c1c411580c01081c1004841d0343d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 903203803 1250 903202553 903202579
    0x3141e16091a040306180507094208010e010b063406060e04050d0c0b0a0b0a0e0a02040609080c060d0b1201060303091802190f050d020307030b0a140102070302 70
    0x44820b0f20300840e00282d041c4004c0c0040014603a20300c0c80400103440d180110000492024050301904070401000c08401040c124425503072002e40c1f000202d00503280c0c1c10300d8031103038403525a000000b011340340660000842000b048041821a000c0307610a034091002840720700180005440a262070049074600c40f83c08075900c5440d03503408104040d006007034500d40100440ca4680d04103400744594400e038209c03500d071000c03079005641c1805803007401051070f030010001481118598201d000c001c48081c00f0b481c3e904c1c1c0c4940d0b11a6440f501100c3c00d40300c145d80800c007000010380c460081c20080c5490350207800b81c2c0d001d81c40410b405200350450120175a440b80600785c41d5480390000c55000c10300190081121540368070f80142514200d00c502100c1000c0c0e0001c4460600742d600c00c403180807540104400c0040c090445c260340000740c2448501c240729060003640140322260005611401480e540010f6801042c0c04002da0241150000141441040d1000c06180d800245d40790035030350100c0320307200b80000c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 903205053 1250 903203803 903203849
    0x105150411070f0c0b0d02040608090312010b0904090f140d0504150e150a0c03080c0f030402040506040207050703062c19050c060d02071403090d060c03141e1609 71
    0x108542c032100d17082d0400501c0552400c582c0d0301520558100340d0751110305455401941da80c9005190800701d115006d030004220740b0141c0001000080d01c060b0001c2021001c940342d10403070f00182c80c2c00b0748505125054091200300c0a02c41e90800d4081400c0c02401c0c14100305520071004500b514203024010311000c0b19807a5503900a55000d41c0c84001e2605a445017110401808070085041c100c000c070f0071400108d4150820501a100744010401e4528115500c45c2c00300009810094007250f00581e08100d1803002c1401800b580c0d020314002c440c00305440c90440501e210321600840030390b1000050f0406510201c2c070110780e024603140d2187c49075044100e00e0801a082c44104903c156200b130000079460180d2899802034032030180103070311024a06c0912a0b03011303107a200da00000c0350f02c518030440d0b00000800c50752013014010458500001c2c02500480d06844888069800307480184050b84480640c1803043c00d0741d1752080f14403010246101001d1800b80210840d40507410326074860b000c250000340 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 903206303 1250 903205053 903205073
    0x12090201020c0907050a08010602011b0e0f09010e040311010b09040623090f01060504020a0f12090506011211030c03060c0a03110f090a08060103020906040b19080105150411070f 78
    0xc500107003c500345080800c40646141e00c42802c02000c40c01030380000500074018071a17000051603824804425440d40c00003240c5680c18030940b254440f040480b45081a00c614130850f0181021000e00511ba0030681000380c00e4000000709848940e0400b1355401c0281c6071100c0c5a9046035103d1700c0130542d01c4864a44c58007001620068041070201e031410010704440000d041c00e141c41030407000700201d544450500059104d010358000210300001d40001205104d14600720303034520406400155412155141c40c1400030a903c400b44019444400d04280300d6031594400c1c0c8c001085005004140340c40001ca5122240180342c031100074004541680c1c9039000303030081e01240202c0d03d000b66450041c0032980d140754101d001014040c40c501d10010482c3c50b8001942030503250000c004092955840b41008081d00d0941da1036074100d034040c50034040a030504144080584154000451b9604c1c0c00120a00f100b80d005801503c40d50400d040385003188036440482c3d000c150041c59544055000382040c40d042 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 903207553 1250 903206303 903206323
    0xc07021c050c13200702450406060b120114010c0209040b04031806020309040f061715060d150b060403170a090f060e1e03030412020a12031209020102 66
    0x1128628606484680855000851104c040101d428080c0e00b10a040d01083c00359010007074200f081100e002141e102c00d146042c0074180107100c403d05800c254100e410842403044c140180c1207514030240001c1001501840c0040c0200507001418022800300d40010b40c0c2c4d06100da1880011020708126150344248030140032160081c0004189091620b011800041c08490550010351411405202d50203110100c00840304079500440c104000c640800c801003140ca08031010b03a503941e031000100b08800c64400303801d801039840a081d0384078a0300c40c20210700200400e018481c6150ba0040e200098904848508104c4585400550320320f855000c2489481030f508094023010380030b031521a80d4140d000040007201650741d11101e605903101d2400d00064450300603103000c03400a690b98407441c2040032680480b031703103544d200300c9001c20108d01290840e4041d80100f01e081d160041740c40305509011680e00002c2440c4c4101003035000040e100188012560180c2074801c40d101c0c1c840f41f007503a01c00c018113024 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 903208803 1250 903207553 903207559
    0x31a130809130605121c050c0a03182301020f0c0604270207150e031e030901060e01080d0e060306031f0b1309150c0e1003020408070b0406080c07021c050c 68
    0xc41604146660303201307102284001e846c4103d0456000103440303401942e0303950f0201801011360b50740c55541540e0001224031028420b94800500040c0103400c41c8412100c2c01041e0495219400e11030002800e222140220340081c1c0e201507112400f0b51114421075044510303001106541103403441c941d12089030016540c0b025107002280480602882c0a0f00c4a255502008100040c1c03610307003c0507849020b060b0803681c80090588404200300014001140d11903a0540001809520350300c102c10800802e030025030a0798410002550712a4000b9205042e54204503184c3d411807601400003550f0700003040080f03c3c0c1c08112103041e18501c84540201100c1e41d001401140c004525000000080160040c252a02c481030310706034801074614484c0422090450f980c65000600c1e0606212a00403400084002c241d801c0100245502003405504058180e01d05c2c01d40c2d6031494108000c107507070009000960052002c1100600603510100e4011105458080ea06c85800803820014106181c502d00c4a030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 903210053 1250 903208803 903208819
    0x1909200a1a0921012c0706050d0207050d0f0212070506060d030216030809091303090b030c1b03031e0c030106120f1508010509150a090501090c031a130809130605 71
    0xc1c02da1010341003c0c00c1296004003440035a0756103034a92903101d500200000d07171500300250510a40d882100185441020468094500042c583d0307218a80b07803903024140c0018000d0300108500c90744c14405210f4000d20348100d241403001c035484240d119107001c1c0c002d80c8242d00e16200c100c1014028000c240c0750a44040049031815034a0601c00c482c1c2e070007040014411090302c2d0001d4094000640044030564240d40d07509260b81c20002e01000c0359001801c0f4840075a428000d2225411400359a60181c4140748051034590500b50406183c0d0001035101c0b5402000460800c425000d00744160f904440c135500e0045201d5440035883d000401f040f2061400755414080300290410000e120a41104d10f004020003550b0790700314407681c540354030b41051801202c0490104440301481e810040c180da0081d00000740c4c419503907451101c444469841243c1910341090041580f8901007170300f6a000d12128491804a407050341c0d1728a06104081050b4800c040280c2d0100210043d640010040d11004d000c8003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 903211303 1250 903210053 903210109
    0x2071503050601020d05160f02120a0f110d0308150a09020f090a09020c07030818040e1c080103030e010c0c0f181a181909200a1a09 58
    0x14081d20301151218003611440040b60905441281103c0c034004455001e0010918541d80702c648800e070700380d402c4c1d920050249190542070002d10094000612951540318000c00d03034500b6940800c803da80b010f05c1080351001e9040845e400c945c2d0150300041c1c02c1600026005404005000d0880981210f0195840414040d40600c4a0700c0103064080d001c0b10f08002c100d940b201200309a201d12900f005881e008100d0030000a01502c014160714022002c50041380a40e03200400c00f01e4014801d4115203520049000b50141c8000c1d0b91201d852040e881e000e120f545c115240640b10981c00d039005410010b4041c0d049003804840030340000905241101003001540d1401c0b0081c000003201440e8a85610b8812700e102c000c0d100c503141c600d417120301803d170b080c6100c071071205a040c00c3c00c000c004581030202c4100d0801400401e02c41e00c0d084620a035003003141c00c142d42100031061580313030083c41e00400c0e480006008402880f050b0382a1322060b07001d0710707540b40c20907330200740409202034241c1a0b004442c5040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 903212553 1250 903211303 903211307
    0xf1c05060a0515152a0d091d06060714010207050105070f0909020c0705010302070f0b070c23120a0311040806070e031b060d060b1c0f1e0c020715 64
    0x125000b16501d03011508100841410003506402d0b20502074126402000780e550030340c17031500b03210800a400c3d05111000d00e410700d15882c03c04a50415181c001004a1014091030141010308080c1c0d030484803100b000c030300d855400314000d8460180050000d80d108140b543c0384031025011100d00b2036010b802403106082204000d084c078815a10310002041c26000e012038040004d10070f9607420600d4000510510b440d00c801134009501800302078030701c54018051400814059032405014098983c2c0d004bc3c003202da03003002ca85403100d040d02504680340e04584689000400178015081103507452079079a42d403480e030009500810b0290158000400082000a02c0c19004220107224048648a1403000c100013800c01d40c450850f98007211280c004114086000d050150140c1041512010001b03001620b8031240c0d0840d810141000c070071a0040c0c1140c00e0341c488103008a100319107103e5018099615030b410030040304048442c05070f2410b41d40d03074201c44d4041d20800180c1c0092610f80399240c03040c00f44001c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 903213803 1250 903212553 903212561
    0xf0204171506040b21121201030c0b030105010507061d07080609060f010f0b0703091703180a06050d0b060706020c061503210a1e0e1305060f1c05060a 66
    0x100341e0348981207200091180c01d19019900c01a40c00401200800d0303440750003203e00954a00c03003a44070b0b02c140d4000300161003412009006421981c2100710320b562540c640b149035000682c0003132612003010300041280340d80080aa500680e400100841c03080c8009118000700c40d1442d030a04a14401c0b820b000805e2040804c403103006030300c420f05441d882ea0302d188400c40147c00c00c0c4514802c03000b98001c10400300c4080d40213001c0309442854000d01007603842c4c008010b0a03103280c106c8401600005032803e10000c40d03000c541d0a070181a941a1041c41c0380c04d802600a000c4d00244417032080c0c07030b0382075043c45a682e0070840e10030320f03804030741103458207180c03c4019513030030089900302106155202c0401c950320b0b0016440c50030356508a01100f80801790b00300800c058000c003904005010341140110041d1002808030b40101c10b25503503c0c401c0c2c08098080051a41c0c480c0442c415207880d260138400581c032000c89015004a081e074032003640540311340d8a020000303200d14000d4464003035a0103018402e942504 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 903215053 1250 903213803 903213823
    0x4030c1502120c07021020060c2808070318080301141c0b040f030c210210360b01090504120f09090509070902180907021507030f020417 60
    0x1405075551603d00c4880303d407040f03900286d400280c0842020907a44030308201818210454049041d081100712560300c1c000301500e40000464000c52811040e03400a18041400103211140b02d80b00f00c1c560002415405d00600a031040548441c801d07019104842c0f07800060507444000b0940da9a5034425541070301e2803041c0ea052140c421140c140381b10615118040300d0329504110000c406407a00d0b80d565940e00340340c4004070b0a100c04226050701003410b0001c20700104102c507038a00382c04619031030002e0802020564501c4018500403c0c82027a00901c0140e03105114000c551189102c0200c010b440e145c01941d500900081c00c5000104c0e0307108403500154040e502c154010801021092000e480000d800c81900b000111840801c000000c1d254000e681c04c001c500094401041d01d580c01030040e640b101180d0907a00042000341c0300030303003800302c0c409512600c18806404040a0900c01c88540e08000c1c04d44c800705500d5071411001c0c0c0038184d04487c000d090706400003001c00e58214903c0d0322809014 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 903216303 1250 903215053 903215077
    0x905190308120411101d0f090f041203060b040b0a17090d0e010305131716030e090711150703020d06140a060e18150303070c0311150f0304030c1502 65
    0x80c0d0380c0714550600090002c05e00c0d1150301c07809203501241d090b07805140320002c4c1550303005511058148281c1c0310f502c0710358056845030321034210360300c1c2c01e061100e03800c80c0f030644d4441090b1810303000700109070510041e9805d941408401940d0307a032007400c003110f1180c05180c1c0f0082c401000801d01c0706440c0006010100611b047d2a01c08504800c40010740071184100c1d11003506022200e001c0000030601c0c00c0301c0c1a10302c8031200250078100e51120340d20035107103442c20840c00300700b0341150740c403481c6080c4000c035038040c07003030311381130304101d025004040d01e030040d9030f80e400d48800030807010451140c0070350162084181d400030100001651000c0480001c07076010041c0b80104c49042002c60717050712590790340303841010182c65489682c000f01c80400c0c0b054001403180581c0c84070381e60b2107603181c0ea05200610070385005400400b083d60441c1014503400c800d1008141c403c03a800c4000c0c0c290750001106076104c0094041980380c40e0398036070409465042c66480700800c90304c100d03610301910070700540c00780008511036 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 903217553 1250 903216303 903216323
    0xc040518062701170d0c140a0b0c040302031603081c0605060a0503010e060103050103020f100306030206070501020c070602160510020c0a170c0303090a052e020714040c09051903081204 81
    0x113152550307210b090a10001c00018850812040856541c00c1c5060741000141d003240c1c000d802d5926056102d6034181d40c512400f2070005010001d500d07042102d40140c4a8000d08040d20620b9aa02c1c00801c1c41402182d0090011421070402035101c1540458010240500440c0d40e606100c403000381168024000e4a401e0200c000c0410b005510030301c01c03036060ba54054400c0b003903d402d100030042e10303090015030f00080503142d00022005841c4c01c0054600d10b0321032030000d600c42800280803424074140f50806021503101510040080181d50343c10002c985041d5400c80002c0421003049082490905150b40c11019282c40014441c000d001c603008049151815103295940ca02c00700340d200e12800000710340c4014560f505100d10310f00000000c3c6241d43c1a074035440d0070050111200001c0c03c2181021026802590007000751030400655208a410102c3d82000b04d40d40c900c1020740542e8007400750a010b40c10105030f190614180551000285400480880d103d600360580d000d030f07a41003104c003100d03c8007032 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 903218803 1250 903217553 903217589
    0x3042409170d1d04110c010507051c090227040212030c100b030313090905070b0306100807020c0a08160e040b0a020903030702120d03050c040518062701 67
    0x208200c4000746060000035144070003804408590140805050681051159504141c2580c0d81d102d1385060001090426842d50b042c00120340c21034400402d000c0c140282080000449000e0361140c221000101c4400500c1d031703100f8004a6165051000d000008640c00c0c01010520000825464410f0344210f070404610350056214a03164003621411180e10ba01c9001500f40d1003609802c05066100d01808884c1091a081d0003030000d54041d90003950603da5480140d07003845018000b12001c1e2035071603480c918505000c4041f40d0f01c240c1d510005c504108086001c100b160f0700c00d100b10754121000030316a154907501d40c00718588614002040d030b4404103111a00080d400d42521000d40700d1a000065664240e84600d04000a0f41c000304015505000800c6501c3c01030759440d02e02500c440d1240020007084841801c00703401c40c0c0f006060200c041c041484100081d5840d00c60b0840f02c4210405054195100e01c00841c0c60100406600e030b0021800041042285000001c0d1a04031a607620003103040080c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 903220053 1250 903218803 903218819
    0x16022107060504210f02030a030f02070b0910050309151611061510020f12120907180c050c0102160b0709030218090a0506190b0f101103042409 63
    0x40343c0e00c0742004564580c18a16103032001c006615000c02d00415840000c00400c1d400281000c6c0003480880105101d403162071411581000030300064030410036010304e826005e200181c0c400c04440106030421400000080020100380030503522a10341c0d00321207916040030346880e006541004009000140e50140807034400c100081c6407806104031040301c409804550007801a84a54042404194401d100c0c440301120410000b000cac440780c80c20409516030100c5120041c10480141182c60560721031a414400d101030b041744520078003594000080d40001c032100c151458056041208107651001c9104011b0340d40c01170a80060354840c140c8800c039036441017070aa602c0720381130102039040140303070070104a001025100c443c0c00040d018211075424075550380d0b840c0740c0380b400c03100d4402e0020b1080c0d40c0815007500b40164203281d2012108500e0340290070010800000304202c54000700540300d40071040300d0106108440251604c840f19406c840b203d12017001c8440b070540c0789900010200440025060 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 903221303 1250 903220053 903220057
    0x30204090b0a12080c0307140610050d12051e07051c0c050a02060d0209030a030e03191a062e1206030b06010c051009050f01140f0c160221070605 64
    0x16250703d00a0000d01e6a036210350109400801d001180b52004011030008503140308250380400c3d44042c028001417800b0385c201490741040342d002c5401a141c040500703000512041c40c241c0d00c3c01c000d10b0101c1c1c6a01c0d000080b14001200c0904a03900300c840050360006220340810880c0008100c011903940e0070030a14001c44618000010140140e040340b807180c40146400d40051028019424001d8107210040e0002820004401021400f041c885003a164181c1028450f9900c4070044081c0c0518802540c4c459a12170300c1d1100248a2000440000440c075503554107000c0120751454260a1441800398058680c02061100035004544000c62403400b00340f1074014101920381c0801c0150507a2517450041d11144106002100c00d402074a68902a0344454843c88500a01400003040340c0410003079040c2c01c448a2801c800000c0703c18404010310155955a419001460f0391921a42c0300060021080240c1440c0002980700304050f011200409080003000d55000000c003c0c3c540c0c1070744e00d203016103080c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 903222553 1250 903221303 903221309
    0x31908060d03030b03010902130c030b0619080606041203050d0f15030807150e0d080f070c080f0c01050106030903031a010912020303090a06020d120e030306210d030204090b0a 77
    0xea0144207100020303100750002d01c0880740c05400130070010090b5002545d2821135146c203c452655078005d0032525076141c003c00480d0341d020f0f50356034075041200b040008605180050001402416000300e40306448400450317000b0154217541d15800f51461a00030001d0703000c411072011003414a00b070f0442e0040d040c4981401451108035004480c1c0c60f650305d1078100d8100c1c0c8402d0752100d0f40c0f40e548594004440c0600c03e041542c080107402d00e0450080068480300000d81030b0000554410108811350341c00014100280d0b400251240c0c8480c2e0040d80d400d8648640921440fa035401c2900002c0c82c107030140c0007480014800d85040c0201d0781060340f40c00c5003010450513a400254000f100700705000c1448440c120391400641034910340a00c110124090041e00d901c0b020040c0e1245070500686a4001c0f05510001d1034120b041c00782c219103e0072a13581c2c0c0006040c45205080c03040c04a05604181001c00040d80308050503a401c403600408050000d4201c1c1c490611010b0030126000001d2078070550220503 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 903223803 1250 903222553 903222559
    0xc090f1f181418130f0b0702010f0b06030f09160312080c03190b010e09010f140604030327090e06090f0d082403060f100b0702061801030b0a060203190806 68
    0x99040c0f16465403030a22000740c004000c054041280a004c0744000a0310700165005900c1a500c5050004000b0301f124070155040c0003d03490400c0f012015500d03081141e0708010500380d00d0b4001d4682c0e4041e00e0800c1e0101c1c1303103040040d200b2140002044008560360742e40320145e0b100d0906075914143c0304c000c1480221606010310544141c1014180c48a0b03005408501040c9030084a8a01090100340648000e0f04000c80d048003c20040018039407070300c0301c00030005068801d541018130716030b0042d00e0b031078050704a02d6a04ad5800040c0e43c80c4001e602c0c0c814010301e1044070600030b10411120054803118140d0300c601c16406144082001c0c140e0000d045102801a1b98a030985555011241020006500038808180c00b00070311403060b0f9038040110901400b10640d1820f0a404c1540311801a44500e5000408000c81130005002694422040d103400710303104080c108418860380e004030014880b04a101d03a0100301d1060219650740e000010304404032003800b558800741e09001d81522014802c4904540c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 903225053 1250 903223803 903223819
    0x612110304020108100f090b1207030803010b03060f0a0e090f010606090611010603060c020d0e010c030504050f13020c010906051e07111011090103140c090f1f1814 72
    0x70042d44200b0b800c9501c5055241005040c0b40c440110b40c0002d01c199014036186529440520150700c1e1072840002078a0025000b4804d2a141d076550a4903400144500d03490345101200190a50300d17140c41e00442c3c108002d003c00b5030142c8800416084027016078600103140310703580e00715840040510807001941d81d140c4402c49000d2800c40101c2d114540300c151140d41d952609000000241b9902544c4407040b0150050010352101c00001068041c601e0555810015800400c50200b50060106c070107481d02a40c440400b0421078022034090a56400340c035440c20710028001c1410081035011005541c0300c0d410a002d5521201902d200a40d92016140ea00e00c2078007000c1481a07000380700581c1000327140415110f051051044100444040c107032030108945001850341695031741441003242c20030028282c1001800c001c45040c2c0c8038040d40d9007a038043e080ca0706404407165900f25580c00d00c1c1520003100051150141c1d0002e00d8a40303405841761941218201c04102240401e00803400d00c14058001c00d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 903226303 1250 903225053 903225061
    0x90305030318010b0405070e030d050a08070e04020c06100f12170705070f0605040302010f032f12132f01050315100206011a0921071e06121103 63
    0x960300100c0402a0740c0303d42d624115410143c8850040c0c61191125807510001181201c09050030034000d0001c440800504208500c0c2c02c5400148958003d21030b0b1a00c007105800300e002290003486102c000d07040d644600020082626281d41c00716090303400e4170004060708c5a681141100c030900c000d20091488043e0490203140000400c040d0a415000f8412209010383d201c245071004d20580e00810000743c0009414010365030001d4010750004030710301e020081c9015042c00d02400400d1101d0b0181e400c119412640d20011212041d1072800c902d400c91811b60707040105a86503800baa03000119199902152040d2108a180140c1d02c0048101c000200c030b1441403034011a03c1e680014108101c00a06050040c3c040c1c03107a800c4403034040b145400402065043c00b9040b10707600f01445a0f4208503c003001185410340320700c041c9a1400c031f0039410340001c0c404184426410701220344c000c180c10f0640c1c0000ca15000c1c1c1d55803441d00c00ca59040e1121360403124a031140d041550300e4100d40c0240d864040002c6 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 903227553 1250 903226303 903226321
    0x40b0d0b0d110301150e0412140409020301081605010503010603021309020a080702010e01060b0d020c030c06130b09010b060702060702040b100504060215060d120c0203100e0c010903050303 83
    0xa210040145800146980040c00041e080e40500501a50000034060034a8024242442080703801d0744480b4071704a007a45051084205c2a600500050440100304d13210410315000701c0290000080b0459401d80355526407900c44002e401c03d00c0341d00d9092041150800301c1c2c0f080202c004043d20811395507207240d0b80c24043e00341d0296020740e07403004101c005420001940d110314070240215030810380e03460b1060300b4030750002400e4403002444440a80d143ca14108000704600c005c5416102081e00b015858216903082103085005a940a0700f040c02000c003044213032402c222001204520601158001d5200c42000900301c88100300d615070460b104211040c050328011003c0c3c50032510007400031424030300f0720011681c1c820740c4091a00c007254000c11f040c04110b40600000383c0c4400400183c02c81c9140450000f034920580540107840d01200000c07003440d0358810360640840a070013a08845030704103103008500043c0040f100070038540c012842e8404466101c0c50200044076004401141180c0b504951 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 903228803 1250 903227553 903227557
    0x206100308041a19030221090c100216080a021005040605030103080706020d0c030e120c03030612070312021b0319030806130e010e3318061801060b0f040b 68
    0x1030001800c10a01030945000000040740c0000340c1c1999002d600c42003401f12251100844c907144004524a100401c80d0030200010814203140c0300715081c0344580d964040a034103100303440540e40071400c2c05000103d80b01e0b4000408080381c03807080d01e8504c115001203008541c0f038020340c0602c00024070100010808100440081c00e100c5014100041c03a214903480b01404407000c00041d88080303a200c1c0e05254400409100c40c1072041c169a03d050729140d0b4083c50640c8038803004107030038841c1d0543c40c6141040c0b0707000c000d0701000c0d50788003051581721440310401a58504525080c08240b00b00f11050600509001c80e00c00ba1088420407007000032441a9000e403425200104030030703000100801004580d15007400340d203505500100000410002d0952241c0c00c0c0071400707483c40c0b4440d8490107001d5101150380003c00c0d00c0300803440c1c400000d40740c44da002d0309584d5007a030380080c01e4400c02d820b01c89107100c590203c683d5124000000c10113290b50344420740c4280600404010350b0401444100642411180 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 903230053 1250 903228803 903228839
    0xf08061b040f121a09010e0d020a02060d1d0a0503121006170727170a0b1308070b04140d0e0d03030e0c03190c061e03020903101803020610030804 64
    0x103a140300c0702500001c0d13120700c10300894030702045a450b407203101c0030b08105001d4400d601c1224809844001c06507000b0400340c0c4580a40c01d011565102460410407801c0c994103a840388840054405c454907506055681c3c3c1c1207101ca0003801107080380815489801004401c08680c420745501e131840c1d07040c038019000d66000400d400700340300c00c1c900981c00702c20911808641617900c10705501c03070032410071504000c6003800101d011003542c40b2508000c0454464a1843c0c0d11805580c100407443c0700618016100b8061040000c0040740000e0a0008014640c0a014408881c00085450f044a001c50440354001c1013400c00e604003088010396030200e4803036003001000300c02d07400072140f014181c440420314100b0459103181481c21040680001c0141251000740100042d02c2c0c030a04004104208101802e502d8048400b131546c001412041d9480034001010414030301c00d0200044040d032101c901031100214012001030107060005914510301d8210b24083e01d402508807070500b424501c881881401c240b03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 903231303 1250 903230053 903230063
    0xa0209011d2e020f06090a230303040303141003080d091a0906090d020c0f0915090c0a02010c050f0706111201090b0f0d03020c010e010302040f08061b040f12 69
    0x5168600440745008140e040341c400d281031640002007500b0000d0604941d2403000e000c035044003062140c10384000481c4c08205400141c20304e0000e55043d0701005d40922480c40302c0c2c3c580030100c10481415019030280010351481101d21100d9603c0610504000c40240002070a400c801d02a1003070401107940b00c011b24901c03d895405160940c0042151441c00c2198400c15650009082181e091030500080021440900050481c0c4080c240001c0614120f12101c0d801207040c1c1e400100d41e201224000030340c0b0840907003404181c1c1047c02c01070545c1d6125081c1c41e40903609080100500520590880340e00000000c5824100200f03a0b83d100040d101c7d545010074036110034410400c1c112840410f00d402094801c03000945240c00c2000c0c03003000c15a81070303451700c01c0c4000b50220380429008921504c030b0f0b407000d181241744a03117600010f030024002c6411220101e88054404150700c1c400043d058080d5410140d44201c5e10f401401e040c1c0d540c81103026114003202108020000d1002502098034414419 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 903232553 1250 903231303 903231319
    0x703150b060301080c120a0c060503040309050d05010e070506070309230909060403030b01080c180307090c0305060f0f060711041b180801050903180a09060305060a050a0209011d 78
    0x38400056950b042a049002c443c2c1003a491902c1c01d00e4594042d52031842032402504038442241c4868240c41d069100e20000c1c00310000001e420544a082610045d00c00100f083c185040a41070150082600c0c82c112025841141d07408103e42c5030020079581d9603a4560741d500f1445007004507002c5500c010360701182c1488000c0e806081c1c59a111500a40b16104080042034545410304005051301c103642c2c81a13051006400c1230181d42c0800e80c00b03d5041c010449002500b10700d1000200e45070800540c090904c40d0310305021080308a5150304054056032084030041c040426020421645041c001d07505070307200004100c0c030000a12204690503004000600015000e000d84e044401c003e02e1290107440020000500c0c54400b80700741175050007804c41c02d0b008001c00c5c07a00c45c022030356a1044441e012244110307624182c1155036408542c0f000b4210342c1d60140f000340d0b6a850310030340d00c00302030700d8000142d4140b50000e007002e081482580d800c0e100580da500a00c8004000110324400d01211517908600701e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 903233803 1250 903232553 903232571
    0x503150103021c0c11070f050f010305060120030d0b0312040e070504050904080c0d02010b0a2922120f0f0201170f011403061308030c130612060e09070315 68
    0x9980b00d100080324258840a1600c94070401d403c2c14206d5903088241301902d06202405107407900307049080d00345000e0a0008403900d505006a48580031036207540740b802c1426040820358400400508038843d68118140580c0c0340381c108040d01c0300c00c419503410f103255090104100c401e440041b49508a031681c1081c514003611000401c500c2c00703007201d054030001c10002e1580c008200800000c450300c0d02910080103a00030450001710618100e10820b03010703429040050001c4000c50819900800c01211503590300c400b0f240841c40302020110a0f4000942c0c020b40025100b4030300344210150b158810034058590016681d007030f1502440e040d003a4100030315069001c031030301c5c1c94400c214045e2001100b0590f0740e40c07400d20950b80703982011600300d009400200502900700c803002000200e25a1107180c80751a980d801c0c00302c05090052982041c036081c58600d00181c04c50b0801d0724003004030740010061051644a862002607860241c4200c64968408542000800c0c501a462221882d9009000c269148 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 903235053 1250 903233803 903233857
    0x2010e03121009020c1b1905040209030c0d0b010518040b01150c050a060f1514060d02121510030225030203090a230d0b071215150807050315010302 65
    0x40310004e0501039002c015066404491b004090031b02138000c413030141c505039841491a0416405110742c60141b500840c8100f0a99424801d0460403d40980b0910f03180305a801e141000c180d080c0316450160350400a906c0c030030490700a1440c17007503030041d000c1c1c0c20780d03440d0188040c030f6940140c40000802a00c10081c20000704107200701d0140c5401500c001c20f8003080749900000b01c0799048500001d0304403501041111343c1e003038845050070351011100140c03a01400c4131110042c0c400d22010889903134440c1d0410800c0b03119480c240300248802d41d81d030070311a5410107090f001c91044222951240040d10b513051090300d8800f0311141c2580c402c4c030683e410501644042210040940c101c245410140b0003500c0300c0070850841c43c0d24202c4111908681c00382c96440d0700308030ba20f0140c803c0041002140c0c41240001841d0004030041d92203016561209684510503e0200c1206400600003000000492000c0c0d11820907a4000d001c03107500c01c09030448150040d4001c2d0300c0074900e65401d0300314201c0411419 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 903236303 1250 903235053 903235057
    0x61a1011190308090706080709030f05010f0212090c09060d120908010c0504060206160c1704080a03080702061006410910020a120503130c1502070602010e0312100902 73
    0x2920075164111942081341841e0f050000503000101041203400400040d03d52050822040340d8024514007850091401c20740e000d81070900e40d80700f01034000102b4070b40740c19102c4112449038800d18140e40308d00010204002d88600182e0b842544409819a0100131814450184244209600301100102e0303840103a43e081d41e148070140344c003041c00880c08001e400e40611502e54400c06203500550b4003009004003404040d8001405041c1107040c00602c58100d21003411580580a403400319008840c1d140381c010030811048900e280140601c0001c550b10801610454090b00e400781c441304954a81003400307609582a2401407c13804220803c4001d0340e0040d607000011600c800c0310095540c2e801882801400360341d10201c1ba007190720080f001c0d00840c02c10f4091207418007443c5800341e41c9440300395030741c2c91403500588090000d960b410b20008140c0c10000300c0e07480740d40c42a02901d803402e641d44016803c940414400030401d40041010740503034940301d250300d9030204561261a024a03200c0f1801c030226 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 903237410 1107 903236303 903236353
    0x80103120f0918020d06140a180b18010e0f041212020d020a09061e02150703141302040501090509100c050906070609061a1011 56
    0xc1e5110b40c2c5003000400310b150a20040c2101c00520030000c1d4041161074046614040d4002403244401c0c18800070403000900315050103143c200c48801071341d880300d541d00d08181d4460360314515a0343d2201450803000c4600c43e07014a076040c503400008502e80074150485001414082000240c01003410612103441c03031030491030f0b003c0c41800c2c0ba40070b400f40c07814a09140b80082142001903502c0030401341214195640c106e0000511000c0082414080a041c4016000603203440c070f40f894080025a04020246000140b0442c4101140a046e0060780c141c0088030540d2100c90943c50640075140c0505070035030b030030040b9040c03009046a6921402403409442d50722a012095140e0158082e0303688600050724881e070340e0030103141140042406600407a00f041c60607168043c1e80e060003d551688000180074071140d1191100c00b070b58480031021201420340b0a86880c0c3e020545403060070034403 = true := by decide +kernel

theorem cover : BRFrame.Cov 903057553 903237410 := by
  have h0 := BRFrame.cov_init 903057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 903057553 ≤ n) (h2 : n < 903237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
