-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1211
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:47:16.018282+00:00
-- url     : https://prove2.me/submissions/13c3a4d4-f4db-4da5-9d11-1785a2f63ebd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 217625899 ≤ n < 217805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 217627149 1250 217625899 217625929
    0x10f0e03070212150a02040927020108060409050304080a050607050c150703060e04050f0d0203120121050d0f020c010f023d020319090c06180e180705 66
    0x48244882000b40c94031504000ba000450011561001036030700f4004c1003801c00319103010000350702280c01c200f0380460b4080d40308804001102038001100046a1413000b82c43e000d8042c4c104100600091100d440700c0e40803e40c1c3d2a0420102c07a10b890351303075100903a038045456048480340120000302e92385502520550f02602100f101a05900d25a6084100e40c20b500818890800d519014000380c164581d20180c0d001e14003450280461240c840340062500e07441004000840d03104014460355002c40c98030841c15128182c2d5543d030480c5640c240f0020414030158080e02c14000e08108005036908182d40003280100d580a0744d42c0703000311100646840b001e45141001507008103512181f648041c80755482d00e99118032040c50200801e004034801908200da1455a0580c0002402080ca00c0340c0c9500f05005a00740091002031184d9844840403a054800c103400e00c61600c0c41c035240e11900010760b01c081d08503020611454901b180e400715245044403080b03880d5010b220808103540c24035680140c1614 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 217628399 1250 217627149 217627153
    0x12403030c14030909040f1103240c0405060a020304030c0e0103030519180902070611040503030702010c1a0a0c0f09030c140402040306110403201c03050d0c050309010f0e 75
    0x4006031118040044400b40559040c0410840c1c000f80b0340c0c4160800d4000d41c00b0f618420a0b0346030341e181561800300214001842540700340020103001c1540112150321050501031003180340c5500341010514012904025400140491518540c030b0b400405481101d0043d02c0c203290701c40ea14000c81c24004002e0101600240081046281381c1142c03000c41300880e4140d02e0038900070441c0d00c82d550303282c0030a908207042c03160300000d16000b4024603008a12408a116020515040c9040000b0345d030791203540da0080c1400201d1400009101003c05000c03058126680c8a4442d4580030b01c0c00c6004090000b60700c401b149256240909007071080302c430b0100383ca5011034070b60386082c24107250000035204512001d038825001c02c004400207400e80070355255003420a00c40c903226415843e04007a900304150b914000807051480a05240e51110000900500003501c244640f500074142102ca620403046010115420102d45201592307004c0c004510610850000300314807601040710106544007580720104907 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 217629649 1250 217628399 217628417
    0x11100c020312160218070e01050405060d11040e091e0102070b04140c03031804110a0507030302130b070b160c1110180f03060c0e060d05090c0a0801240303 68
    0x49015032008209140b22810300500e0801c1c40d038000342541c030080c40884042c05c01401881800b0f0b8102d004000080341c24204142001c0c01d180200e0000e0154800034582c40391201d2420b04040c2022044401901380041501c80390720b055089240e40b00340020504c3d520880740c4900d21510b25040c07003920409a03208181009a44407a02c402d09614201120b001d0180201094150282e030100000c05005000704204050004080100f00450f80c1c20403000315540c800300075800c4030540c004100d881240d03060500588521007200080305149094002151190340011078000b03100781d444d2428443c030740340c01c0340c2d00c402075101070212140d032042c4000403c001d05001c00310805160260080303060b25018a46081d1287c0700600b0040c90802c1c56000d400c07074050768001407007440301602414171901d0450a0020900003035001044807031090008001416a03640003062484805000c640f08141e4000c0541c142d46460360a201e008004070a40072056560600c0030071400d20045a0300c0c000c480d0591101864 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 217630899 1250 217629649 217629673
    0x1150f060507151d06061e0303041701060902040303110d11030405010c05281104050709180608011b09050f010203040b0309030d05040b0103060c171801060302040911100c0203 77
    0x810700403003a00740e0307a0030340b6040c0e813008050342e440082040c02e15610003042e20781003200500c00c09050300f0340c010010200510051145850000c200d404441011324240d134295510384909004002c10740100c513040f40005000018103a0113405415103030300c2981510301e10080c490040d584048001d4000250307410901013046607600490b100862a40100d080c1d45014a030013000c0c01c152803200442114403e10001d0b407a0500406034401c4540100a0b00c0400a074280303200040c2141c1101e200b002c0d41c07402d02206010088a0540001000b403031034000038001d0443e00001c0c0e00045180101d0000001c101070b0b40000d07075103400e039054444d690060300503614103070800f070f52807501d580002c1c030f5007107140310801846c100801c0e42d100700b6204602841c2c6480165045141c00e009562034052040b04000c40b010141c00300307121079075101c0c0c0c0240c3c2da031000744821200c01c01103502515850344060360262074100b0303410134044102140711406d00304491000d600015540d09959210311060080d415a00030001444 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 217632149 1250 217630899 217630913
    0x305073c0507050a090212070e0d060c17070e13020702060f1e07052119050903070f080a110a03030e090c0409020c0f16030b0402130e0f01150f060507 66
    0x91450051050301c903031588400c045881904e159028801107a40018003200300c000c14440207800030b41c2d914110340d08101e81c4c0e0000d500302c195054094000c940d6440210602401103000d030000032103c100c3e81c480c608c3c04c2d01c0041c2c103203100c60003160f00950758447d94030703803032103080c4201e5000380d0b0b0040c0035604003a40701150800c50782002c0d01d0083d52a40389890b03650a04800005081091b04c00d500a110601141c000c0c1e00303008407480c0154048081c00d0000000c07000010f000000d5641d95407500b1a1035160500000749015010345c0001d003428050500030440a0000c07400003929406806980003282d81a420b2210742c00f103c0c8400340016101107880c04c001d10300080c8594210905085290419407140e014504070f03841110380c203c1561040e20341150303080c41030000101804400300040c60003403a42e1500364100100a1009205255a007107800d0182a1940b00d001114902c10440c1d021440c10003006000b820401d85201411003030903c002103024507800c108080d64030564400741804455641c1c29 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 217633399 1250 217632149 217632263
    0x18030806030705061207020a08040305030301090f05041e0302101404050c010f050a0f09030204020a080f0f060307050910030c03120201150f06050c2e050c0315060307030b0d030507 79
    0x101140108c1c4150004910540041c201841c000c0019540c0c95150003845422101403400500c03c460504040201058840006010a100f805079440342070f02d03d860128106411407141072110380c644411440c44c584140350503407259105600300c1d401c4141410040d184186006818070014404000d00346604e841018a118601c03460b0400c00c80180c0c60381c1c0003600741d0304070922410000784428200140300025800094100c003604110507940c2c24004042500e0740b0071805140d0254403132401044140000c3c490504c011900044945201c40e240d00d0312401d260010401600150f00b41510b4001c01c044015440b4100da41a030181e0211624000d402e640300e4011105480282c0103c00e1072582c80b02c05911074541c800c040003040c603044600f070400c0e041102c202401c0001001c03814010030152800c404003440e900d8401307c2d04940c0300d98541c00704401415031404000c3d0000c41c21019541050703042000303020078902c95400705030103185020350090f4035000082c100e41e10f0301710180401c481820102000c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 217634649 1250 217633399 217633411
    0x50f15250803040305121501090504021605060a09151a0913061a03011a06072a030320010c02101d070f060906051309020d020c01180308060307050612 66
    0x5250091401d480e86940354000321025004a80e00040c0c82942c03126014030958001260282103411074034405c002864060b9a001c1e103406194002504e036100140c081c1306000866001d004c9886500e001c0085602070001454115081401600f10840c1021140070710340c803030400050824000340040d4100150b1201c040c0c01c1c0c14001400700d1080300801c2c0c41c1c0c0900cce0301d10701f142449482480002c50034517003145c103c0b240300510040212002d40d40359484130211403005410944100b0682c60102d00d8001d00b410311030030342245422400e00001059003100d5014003418400044030841c100000b04c5900303032040c40c8110801600070701e0301454616815480f60b0048401944c0c140c0e0308050440003185030503544c0d08030540d004c203095020004240c0c484c4010001d0400d41c981141452005561003290004d40c0c001c141250303401140b041d030b400744190b041d14844406c0c1b600900000f910900d40c141b50445401068000403007000c001041820b0004141301140e10140c29a843c0c2510105c05000e0740780007400c6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 217635899 1250 217634649 217634707
    0x61e0411160c05090109022104030302041203030b1503040b190213080f061b0f071e0f05100216020108060a0f06171308040306020913060807050f15 65
    0x314070186080074000105080c855501c92280c9800d2204100103a80c0503403100c0c4045004001c90036000c070a2601c0d840c007045000329080100e44491a05030083d000310380003240701d42c074400008014158140c1110034001009d82c0d10882e0000380d01048801880200c0c2c000d1710213139040700411003031a021448103c0e021600b4000504001100c42c65200b000000e40c442c01c1c160f07004081004904005004050300000e00c07403c0828030034200b541c06082030154a0f00566545d030301050790400d000070f9030013403000d01a0304048544980180d00d8041d0103e0b85541c4260384034401ea032990b2940b05403501c01c958a407000d030b04140f0f08420b030750f5004440d8080010f0080d500501c01c400c001400c220020940c0c0060300441d25203610003d0f440084942c41007005240440320303111a01808041041b003421a003c0c3e03504071401595914072407002c0354410300c50418010b007140c80c1400000d81e0030b4010407104103444086502243c0480e038034080008081002881134075100c402c0000280b0590303840402e107031604100c4c50f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 217637149 1250 217635899 217635907
    0x1b120605060313030e0909190c0b0424030506090105060706020c0114041202301204061505030114010905131e170a0c0809030f1c08061e0411 62
    0x808500a50003e80b0181c14829800d0004020142c0184080b25101c0b03059a1640d070b41d18001c40070940e176410f0240d0320401e6803145840801440000c9401c1c00c0500b44101005585980d28411010320a07210224100542c28210400c4206403107801024040c0d2002030810002c0e900345070030422254031146089944035402c00c01200519401e0140c8076403412030074070150051405042080d440c84c140c450f80000c54002c108248906030500b000411407c40c80062880c8100f521380c08400ca80c81a03000415001241004110800800d03400c826020319102000d00e00711680da00a150a03225412501307958004c42e0740050004062660205034080e503c0c40311741060f0405510b950b9003c207139108801c0c0c0e003100c60414100511084882215520303447c0c0007140d14000c3c0007500101801c43c0d210004054820004500c40503a1f400c0140759507001c0024203a4400300603240c820348811344400e04040c0410312610000e9007910b423808d0100036094402c5480c1c00c21180c1c203801c1000814080e12100071f0004240 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 217638399 1250 217637149 217637159
    0x1050306060d050f1512100c1b05061023040c0c0b07090509060a0305030d0506030f1509070b0301060f0c02011803060e0c030303060a1e030b0f0a060503011b1206 71
    0x405154001d44c0721140480136410181e1404444291810340d003806440641c0b03a07139140c2c01c2d00190741840040d00002c0002d802040e007800b141da041017035442c07601c407411566881040c008042400c901820581c00107100190f80d404000303000003843c4101e5281351561443c051101c1c101604420b80c400110318103a001c03900c0c19504c00801035404d80d0072500054503424140028140962030a8000c04100e6958080070324550701c4554a12503100c004420a44403408030340c01d502d041058207281040c6500b680c592521b500c0a85070a030204881c610002d100306440040c4018a40040764144c0f20243d03074140340580024000e0b110b000341c0260883c10070503005500c0000e5030810321040d01440c070641d00840c4120220310441e00d403030344106d51140b10f90410800e003e01c65131a01110421580c0341c2680c0900c40d9400c4500310000b0300140d0001c0c3c03444461004024600180c42e400f10b2040700001c00801040b5110800d00d07007203c8a000754501d600b000e210554404da801403006040450000b100400c200d902d807 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 217639649 1250 217638399 217638401
    0x70609050f072c150d0203030a03020a09050907021e1015080f30070b0f061206101403010f0c020d020d050f040302090403110706020d08070f02070501050306060d 71
    0x41d9410540c01d0300903100c1482000f11402c00c000d12070040e01d50500512540e01003c0544002c098000e07061141074100709601900ca0103090103689800600ba240c480004507009000f9500610009001819510b0042051710f800000640102510303030092800040320300c0310000210104004440500c214442000500c3c15130180d00d110004140d000c0e044286080b41081c5880d106121007102c5402010460310b928500007170100842240c459803002c0d40d00c820900c07400c1071082c101c001c2c082d11100070070007604201c1d18400a000f148191401119440d20000351500c0366420b4405184030351846101304400b000702c130a440c0901c40000c0000840c9a2145100c604a40b1140c0320000542c108580c0c00c031a0f2070f0148004080700d000390a105280185500c5240040e108a0000030b110b421034030042014944103500050384801c0705000c80342450740319174000c3e640707411a02c0641c0001d492000003524030342c0329900840e15561182c0040c0501da0500b8019140760304001c11003500000d05110085103c01d00f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 217640899 1250 217639649 217639663
    0x109030509040c050a1413050319020a050a03120c032a060c0207030f200a09020408070b0c03090d15020d0204090f02090a1406090a1503150501021207060905 69
    0x100340c58060761950460244820b03a0300d80b1901c1002e0010134090b601407180c110320840c80405003074861566980e400c0e0380150100c04643c1010b1303050b00c92251840108403000c011540783d9030080f198010316540d2802003212000c614017004040030380994002c02864021441079440c1481f07410145890228019002c00120300e00d5900741990b01c80481110a11003680b040210011a510140c01041d00395111001103682150005011001030380209074941740401845c001c2d8000109640c80069942c01d43d00e000c1d42142c0210600782c060000006581c414480480c1c1520312003601850502c1d9101d0f0800400064541c015a085000d1039080780c108000e07840207113519290002c0c0140ca070342c10050804212034081c2170080340c0c5403041200070801e43ea08841d0a08990010307916501d00900100401d449005480300b41d6084580d041000c9042524081e085076a82c0d01c55908002c86802040e42007221085842502d000d81c002d01d08565035000500e0051a641d400707400702082d413082541c6e5403498503070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 217642149 1250 217640899 217640903
    0x13090e070e07080f1605070b1b07050318030c0d231204081b1807050403020a0b0c160b18060c0f060f130305030114011107090f0f0e0606150403050109 66
    0x3008000f045480710045104c0760308022a226805161901030f0340260640c40744038006801503200310000790020601c0c9001c00c04001e010758955448080920b050703a56500440d0361b0500c15010400000c06274100040c521a540400071b001c5120f01110780ca400c060210002e4280070940c040d800c2d1550105401c000022080c10800701803a0344da46421034540c1400000320b015151101891145000c5548285981c030f902d012a2000000304d440f018000d440b58420741e4002900013584810020b09a400301d400340070052481801c0d5a044070b040c0f0400201c041c0c0d103000d42590010300b80103030160752600d6011141aa48064442480c180c900520305180000c91150058107902410800c4486041d0201c010f4103d07001200c990b440300180c0d034002d85180414005c40b0352620480008003031980c851442c681040f00a00c0035602c02e1034950301f0100240c080c1c4101c50300c14900300b112505980d115481804042020a000341615407910402c01020084901f4208900b9900340310101c040380c1b082c428202094 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 217643399 1250 217642149 217642157
    0x2030c03061807060234150305010f060201020a02070b0c1005010b07021203030c0909250215070c0c140409050f0a0501110a17101a090a090213090e070e07 68
    0x8024030001c24a04032240c4c01c041c00319003041060700040d80c489501010000800703100710300c8456003942803003004171066000342c0410001204407401103405038040c1e4141d5a4107a8400310580e15038100f6400e030f01c55840141c3c0141e000800800040500721301400311180d10030182c0300c2c4140c140c1204025640e0a8020784410000081d010b003c43c03801040c2c0d005000c01c240040c6056192804003090b440c0a50140c55010342c0c58500001c0c81c01d082503842000c0c03404c410f076070746042e4040d4200003036550419600d460003108034000841c8d00e9601035884201c00903805043c00642e02c2c1440c6150b00446000c0103160f4020f030303ea0400c10000f5405005000c005140040101042021410302d60309541030080942800780c81007221606059110035200344003045001c0780901c50316420301c41d90300e44a00d81d111000d00340b2102d020710f2802940100424003070508403001c6680c10f031141c00c880100d119001c4070b42c201c0c06140c4010086100c140d041b00c40c3e0101c21005a4045c03d0780c850001c1c40000c0220b84d0301c0009 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 217644649 1250 217643399 217643431
    0x12090503010e0f01050a2906070605070e040b010e22090c060807020d05070f030503130206040f1e140d060e0709050403030f0507120906090f081902030c0709020702030c0306 76
    0x2103442445003646c00a2014810702100c0c2c00c581076911424080c0c407494000740740107615040103840390012509505e90200003001185480d00000700700980c1b116080c4d20070f9082c40c0e0307002205e61043c1e41c0b0a40680e4010011400303425201d0ba18032849003021462002e06403110140008201e601d03207540001e01054440136864549584001d0421118003035440034020240100f90101c2e041002c81e8204c0742d45420309668076155146003008040c0441002540684000f030301248980d10303040f0b004101c1700c0100d01712000318a80760380c44c1c0c002419409240045490107594034040c0c5803e455001d440750045000045404000e00c840703080c07003603135088002071648460a02c01003540c50b01c14002e494080800410080c01c004030b00a20500d4501040e520700c545400500d010301800354031054100d0f9116105003401580c600d4808040e4005c18000d8000020b210303617400d003160000c011250b00c21442c1c07010b40901c50410b403a440003500a18400c4ea09071003911715071a0f454030100040303406400021441204 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 217645899 1250 217644649 217644673
    0x1c18030816030603050a050f060a1a0603060d0204060305030a02010e0a021c0c0f030318080d0f14040e09071e0806010b0a051b01051504020705030306063601120501030503030412090503010e 83
    0x5808000b4240034403090bd001e03101c099a084e019040080940210340840d520340341d01d40060203202030404c0181d4002e00d0032400000f0480c3c000010a0380c1003075030300280b02c1e012841c0c0e03a06450b84d00002d0043e400041480ca00c04180c0311100c40381c40304510a01e1200e4180b0780320884411190201c1d04100c0108210004e100f0700c1c01140c005440040541900804841c85500d800800c10648181300c5401e100c130ba200b803040070129500c2581c01031300680c148041036240a281c042c0d51481c241c8100c01110000305c4084070320308018003e0405988031813009000991030700c101103105621507a2141c1c1040310038465004494440400720050010160001c200e50a0078410345500e01d001200840c0306500c100006000100c0110650740d010808448040e00e411545401a0104100d004070804c0350001c422036400800003910024034a0b08280c1c2c60781110408800d082c803c0300e0082c040907020780d0040c000a400136501d4090b0302501e241d5860000642607403040400d095802000034101c00e030b0800984031003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 217647149 1250 217645899 217645903
    0x609030203042d3c05060f09090a02030105031203130803010303020d020d0f020d0507050106050306010e151516020406050306151806010c080c010902061c18030816030603050a050f 79
    0x101410441401d044699408403003d010702e1071202c03401c5078541d80d0302c4c900c2c48405013580c0010003c0c04090642c1d691128002100c022030351080c801e0700e1150f482c2c04007040c02c544161003640e059940c0600100f1504074040098000da070402000c0b0600d103114290210300007070b8401c02450085201c0e40050403002001c21000c1d080030000180301c42000b44d16401c9566069002400c0540c80b221820081d580f900729040407800b522440d0005a058810540009001e4002c4560340d0300c5050b452a40d030072504020410009844d011508000b000c0c0f50030700a5034000c0d9815013900c1011351000740002801d941d60302c0441d0174624116032600f600c108e007402e483e4003070408524151440d9000003180ca814070f081000603080000884014201c0c90300031039500c00c0d1481c254811102260001c10250300c40f45042c28000e80300340e03140c041292071414440d2842a02c2810480c003071215034152102d1006542d030388031007070f90700100302c0310700e0205500c5110000c0482c0d0140102d115860049000e8090041d188402c18 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 217648399 1250 217647149 217647239
    0x1701050a05071b0c05060c0303071202070506040618140c030f0a1e03050c061501090b03060d0624030b07081b0301121406093007060903020304 63
    0xa0111410074007041145a44050800009000c442d40c0c04000c40ca10306084c0f0400c001034110075080080062540f00c2000d001019602c559042d40e600209001c1d80041a0140d00810f00c006003550302041c00310b0700007611504041c0c0c082440c503000015601c0e01c0e03110329540c1c0740c40070121715460f04214070281c001d00b010701c0240407a4090344000e15410700d8030b54414603c2c040c4440d40500c2c0c14000701043d801c041c071490490300c0c482c10060469000d405c0c5200c540400c10200c03042580401c501c00000107026031480e0560344075040090640132080d4464a5000180039400c2481200402c0c401a0150705021480e081d0082d40c0298008180313841e100d880030741141c10284c200d80c100f03810003441d00701c81d82c003103030840781960841d410340c11100c3d000d03250801c43c0301d01c090074640d0705014240c20041e03050800640040d40e4000070f102c9824003010715007420b0300e841e0156110125500308020900104481c3d4020b02602c1717100e4411640340c00c0d524495001c1480068020303e000c1b60746412503602c0307241141000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 217649649 1250 217648399 217648411
    0xa0210020a1b0c0932060f1e010f03050f0f0405160306140a02070b04080d021303030503040c0b0a02030a140c07030f0c08010b06160203011e0207061b200313170105 72
    0x5a40031790720744040c5c4103400341029003c069004102c00061501e85811040304402d0901038440c401454140c90141040b034050300244e03001500041d0b407070280038030034003602d80180d03071101c030610060701e669014503004c24004100340c80520490741e40890094441180ea00207500540c2d00141000c0320302940d403018030f00034110154903401840200301086001036401e420650081c12240c2e01c0340c1c0d00c0d0709070020b07020380c040c2001d028890b8000001456001030003184180e00c500d0305006503030f444210fa5021400360111a01c0164800d0042c20010b500900329130035030151b0400d10600b410300e000060342c85d10360700b5001100c01241c4480050100100007000b00040d000e200b00074086005c44201083c0303140076614100c00c6401415442d04295102075008201ea14107a41891007455000800c5a010f5401040100ca41c00d01c0d204e602041e00ca11590700c0244035071941d0300c0d44a642201e0550701c2c56000d6a207200e0070701e4041001448401d01d005e05881c002003810608085100d030300d05d40003600b141d20040103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 217650899 1250 217649649 217649681
    0x110f070326070908250e10080114041a010320010309061805211e1606051008060f010504050403090909120e01030203040c03142505030c01050a0210020a1b0c09 70
    0x5a0740d1034101c03221845c4282d0b000c800d5400c00654542181162500c0c0d560701c401019403804a0004c13251420a030f211748100e02424034000c0c03517111216102080703c42488082d080c00003901001e8070b040903110036017102e08014035000c6070201540d03c4e00c100300d60f5110710b594070f840d00181041c410040140940690010000c011018900c0c400913024400d10400d00c050000702c1c680c4101040fa40070000c1560001188500c041480303009e1071a00d04002d01098800402500388800d002840c2400001c90a00c02c0880319180c020507440c0400307000142c00060012014400801004507a24503a8403c0d0f81150340101400c40c0744c80d0402c4009014600c242801c20704040c010000c000206800c241c0b40030449500413022040b03640b00442840c104550310984208030b2070000306115a05241110b00c00c2954001c90907500b5070b10b2010015140c8c1d100700340e80300000d80c001d40840c5e00c542c941c550203006212031900b0b05031a20014110100f1703c00d151900c0c100c1da980794500040c004404c03a0b1140c0c558180d90406 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 217652149 1250 217650899 217650943
    0x15060a120203390315060408010903090608130305121e040f02090a0b0607150e071403010e01020928051815090106050d050903070b09070306110f070326070908 70
    0x100c061914800148400391102c1041c40c007081326246e050458008003122402001440a0703490b0040a8030200c3c46804002420b1102060b48985001350000c1450b9150301d41500d0701c510040041c5801c50000c15040702c403048030403000c450b070100340c030814429440b030b500e042100203552040040d0300d40081c00d180340c86882d001001c5034a840c2d003021240c00c0794000c00c0441c4444d00e050001c2000c0d260700190010280544400003c0c007007440c2d005c20300582d81c00c034001e20016001860840c03c07806400905079110a8000c101d520711030050100242c010201c60f003c11085071944040b4a96010400c0c50b0070041d2524420480d07581605121304034015412a5010601e514100d0300400a000b0b04446450f0f042e500d0001c100b44036001c104465007a0352203403100005152405c4507948507040d41c132061300e6190070588000d120a40000c00c6031092004d03035201c5406c104098604650f01c0c0841b001d003012290700c21030040c0c01c040400000c1071180b01c140c0d650140300c03410420100c1c24060807441a4110440c200 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 217653399 1250 217652149 217652251
    0xf0e070203031b030916090b040f0c05070201120b03010207120e011d010315050909010b1503071403060d0b2e0308040902030619060206040b0f15060a120203 69
    0x3c1a010300000c11101e000d80c40340c8409049a04000380314070808201001d0080000c0c250201e80c0100032404411181000f9250200c90701205071030781b2204100001d80c0c10080c020040d800307030100300208409480b001031524014004a400c9074000c0c60195040b0b40181001603425501c4181002c8042003807901d080b00b407801c10358030000c040000b07820505242d1180059070540c065a12800000d140c014881d0180d410840f031424000c11040c0000e50041c401c000b048520300b00070f002143d028a0781a5500081c86215000c11070168001806055010006108201c080703245103500c140281514900e18005115902610807851139000c4080650b00c1407a0082020a400b14107880854003600c601607900d07600e07240000c903c1c09650900d4090303105600da002c04c4130360340001c00307511440c46901a001c041d03c9041c49d80380c10910455000f4035180c52810101840d06007480504405005410706440b04420010b810060342c00c111040106945041c02601784010181e02403030881010309a0812000742c10303 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 217654649 1250 217653399 217653421
    0xa031d01090c14030f06041e1a0a0516020705011b02130f0c030605090a0506010309050313030b1008030d090302070b040321050304020315091002070605060f030d0903020f0a050402040f0e07020303 86
    0xd00188c43c0ba44075002d1402c2034154a004010440e0b0701450101020b40d600500004540c3c0a8460104541c40c1c400040d5208441018002030462035400400a403458280110b1780d101e02806110002c0c403500170043d0040e100ca001c040d4403161400400f20344420f088180c10304681c0c03291a01020141044030810007070301d840a42603002005004045410342c2c1e4000180e02802420780700503c0c0344000078403205004144e2043c101a6840394030420320130346403054030b02c0c881259405007000c190400c108990480782c880c0d0148109501c00d00546044a66034400c0180079003059200341d6500201c0c00748114010300b1100fa03241d40c00c0b5642001802c3d410590003080d99503075441510550b0b400100c000c220b60250804c0b08031f031a81e001c044155034501f41071512202070001518030720b00a041600503050185400b00c1c40100255150b560b480c84540341d5020080baa8400d00c6103a500608503c40108040d00c2e140000e10180000c0c069000d209842c08e0030f4803403c900c0040c07450085400c140240f202103412 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 217655899 1250 217654649 217654651
    0x2071202010c0c060e0307050307030c060b1009050907030b0613060201061e030210141c0c080c0315040603080c0601060f0c0c06110f0609060612060c0a031d01090c14030f06 76
    0x2d07400085d56600100c44038558412000050701c14171002c900502055401840c100c10f1511841d01400410f111030305000c004c3c4840c421003c04190140000c0c0b1643c146075030503c1d0301c07120510700441d080213004045110343c0d00c15801c0c1181c003880b0071414043c40d5024041c0c84014a404040c0d02194203195454141003140c3d0300000313204001200916030024845c0c8021500c511110120310781c0c41000701c40516501c200c26108281c0d442c208560002400c0c040d034030340c034070070401c3c00710361860356540040c0540c4140140d0b00c40c9901c55618000480170501c005d014141900c9142c0c010704665061050103400c910703004084408000c205812200064259003241046034039604002603400e080409050500500100001c11841020100303e82c258001804502522060b15140f00d6040f82e064129210345c0201c4d141c0c214080208001c2003002c0c40f9a01139038615403088070118485042603900b90070344450400c2903821403403c5805211002c2440409141320b02c04400400d00c401403d0710f01031f11614 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 217657149 1250 217655899 217655903
    0x6110c0607080a0909060f030b090c030d031d0304150305010b070309050d0309030f12090618050d050a020904060b030c01092d051003020301030b0a140117070e0a02071202010c0c 78
    0x400850701a00f15070203101540302411682c00c1c184025038650040c4050090076200c103441c46101c602c00700d40e618202141c400c54140e00900a8800c041c1c203a80e00781e0240008600a4000481c0c0c05544000c050707040c40540060022004040040c0000120090550b1810b80054541100801a00c40003c2c0c0140c0c800c800c85c0c40596800340c5004039414191211b0080b80c0c40074004e00d0301c1da10f000c400c100d4104a005918601d40c0c55010303605840742070031200c885000d00c017907884c00d110400c240002e251003840b807542988550704544180e006607012038003600c810344044030083d844900b01344191905100007080c0305000c0c80c00260f01403501440c12440b822000301c3d600c00b402c1044000001d40c0c07034101503c014000182c64200103080100740280290710034481a140300c042100490328a201030f000d1130304c0d6000c0001c0e515009900780031024510002102c002d114a110341e41c00001c801100303070040c501c10b40100000507111101411320301c0b00c045d9481c07510800c59140c001003110843d00000c040c42c05a03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 217658399 1250 217657149 217657163
    0x4150b160b0f01151d120d030606081003060e010609110c2e1508030a050702041401320d140606010230120a05102c04080d0c0906110c0607 61
    0x15085e105d401c032220741c455039040d00006507581100c40c3e0000054008200001590f0400a050b43e400c0100c0304808140d8141c824082552401c0021a0554201c4144152070300d0000400303d541e4020306048440340b90110798015404075500d2021481030020020405c10382c0110601c00c41c40507141c0c0b020700504a452120103650b00099000030503402e52a10180c900c980c00c4030ba5802c039603000076100d500048c0c1d04074412414032030038030704100d6841c0d4454100c41401071036a4008003820030030b00200360725800390380c007158401012210540e00c42541c070403042d0289103100070800720302044a00702940140028151340c0210303074249040800310080e050a00100300200d00d078603900880300c6207a100ea2210700d1441d901049c00e01410a0444c0d10942c0610244001003104a0b43c81c814622540c401d64240682d003140c0400280ca95192226129442445074119919141000e51407504030741c1040880000900c1c800400c1c844580c001d5101114404100000d0241c1301810000486c10702c200c40c0700501c00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 217659649 1250 217658399 217658417
    0x513020403120305090f1203090d020111040302040b190e0103120e0d03080c07020a0e01060f110304031104060306021b010506010e2206080312150103140604150b160b0f0115 76
    0xd44014024a01419100c4041c1c81c52181d00031084d100d50b07002078603142c3d27450149022151801e0300501c12010f80201203c10642082d01d9902000010300c00d92100075003000c0e081880140c0080ca6450342c0f07028125480980f6440d50450800c8000d9923140e4071080c0500803980703043d02c0659518016103003415418582510240c0d50401255000d01840b20025004a20600c0110f0100c9910190328183c540c41d5440c5007404408260844620845040348c03d850707001000144046140e0305410010401c0c06400425010364a544090899102d01c0e02c1d00d0001181c16880d00c0001d03420700455802ca4800d1074840c2d060180c0750300080703040c40c10b01070000c03030b10305e5003e100e10300000d064222034002c01c0050306481e1960818100b0b036031000001c44680c2100b5210040f03030744c9698000e101d5505000c4030f6a203005010b94619040c00018000040307003010b8152462000600104004000c0840b4200b0310141d5441e0700300c1e86004512150050702c864400140c100040c040c0c43c0c120201c0c00c9084c2e03014500003900c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 217660899 1250 217659649 217659661
    0x9060501092a1e09090513210315030b0402092a070f0b0412090902030c040b0c071701090c0b030c0909150d080a120c0801050f030309040c090513020403120305 70
    0x41202a003c480c684491910b6007011203580110b000c00c129107043d00b00780050341c3c0b000010711300c038032200340b005081e21250081c60f00021016120442500124180010521700301140c80303c920035541c1c001c8840e822542c0400c000c40c00c19107211030f0070805c01c1c1400c1c140b246c22411005040828269a21701c200d0340801c02100303021403210540840c9030002c01c0c42041c0c0c241414035107000c0b110720082201007003030300200254000d03445c400c40f8881c220700d12907513042c00c2c2054868461035120440c0b0103c40d205145002c5400813005501440249440c8000108202245400c02094009600c140c82629042c0104055a0f8141c4202c0d007031404111960034007990b1301016004000c0642043e40e4001d110b0b00c0c2c110302044461001001401d0316070700c5032103803c101d154810007035540724405200024112001002503040403200c00c03d1203030f00141a00c1c1042d007041c000c40c04a03108040c0700f900040540c04c00b0000c60811042b042215281d001e815841d050031525240705417031440d900070b000c255a600000702 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 217662149 1250 217660899 217660907
    0x4090f06051f03110f0a0f050c030a0c03050d06080c010e120a0204180602040b030a0524010807020304210c050306090d0e060702030109050c03010b1002190606080304080109060501092a 81
    0x302c900768813800c1e5485103501940c0d84615085650395001181e484007400d40c8071401081038a00c1d00001c407004614041d8146070442c0d41149244017241402414405c150100d4a1805a003020708104801054034000000005060040f02c01c00c16001d40c2581602c002ea245020604a0600e03030142d50204142e40a2110040d00258500014007568400f050100d01c01102c6002107020b450900020721050b1614058107480880d0300d454200301f01d0003883d50f40c2480d40a00c403d41d40c0310b43c0e20f005980c02c0940c0c9801c10f0300c100c041c44992070744034240c8081d030a040101200c442d030060103069004000314070708001581d5461a50080b1032051041d040c0c07016074140c1c1c4000444148031b0f4060000d01010000c0d1400075511091558514425420003014041c14285103005003003080656005114403900d158001c2c543d00c49a00c07064034030725203034400031a07101010030080000b00596000010381c82c18504040044400603049103100c13606001c000e11012030b51100140c0c18403c1d100b0b20201001c3c070710300251 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 217663399 1250 217662149 217662161
    0xb0303070c0801060e10050d0b0a021b070503070f0b040e040501061724090705040b04060806070807080c040608060609040b031e070509090a1b0509040804090f06051f03 74
    0x1004210405070124026006402c10b20440724070210030044da841e1001903411058a40c011a80c221100710000e40210f03240b0182e03e80c02641c1c0c00401031030481d44100c044210020b400b4060090303801881c0400c0746041c00c1290760001c1001e0b6002a44041c10900040315901c110310402d9690006000031406100013075000d4401000310f4002c030340d0118406881c090701c81f010500b0103007804141110040301d01d90101007691007404050302401c840fa042c9010407000300314000d40c0c5a0015900c13000483d14035070401585004003501e4442d450a45001031004000c000c004211129030041800108003c030f810200c0e031600444112201612210b01001040081038402c4200d94503102e5408038a14038011840f0b445e50008000c015501f106485c0c80c10300a0024082e180c01c450f50b48044048400320325622515004410782560102c1c51075902d2000130781000c1d050714241c03036a84c80050100044920b40c03141540d588080841030003500d03e4030b800622003030f1060907e0040c05c114121081d40d038900c44e520034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 217664649 1250 217663399 217663403
    0x308090c2d0d0506011503020705060711060c0403121202310503030403020a05010e0607080406020c0406050d03090e071215150c080304081305100809160b0d0b030307 73
    0x5640c0a00640c512028401c0700089a512281c09442a0010741c144120162030302d0742c000004100591801341c00c03a50050580108808055081c00b071180000e2041c8002c038040c80071a69030300d45a203c02004075080c410050221205100d0070030040000034100e103a03411400507242050030f070744407000615502a1041114180030b20358440d99a21244608030700201c000c1703100d840011134460326582031581c0d91003280806588001005e401300300641c03242c07483c07202159010748203d04055155403101a1500141c11810143c2c1061034107a1f400d04080c462000140002c8403d03d04400580d100502440e1150164560741c42c0550001281c0d1802030040716225080c503030040040600383c94030b458034010103002d50004580c6c2c03038011000d0b662040d03220001c0300e5000a42070307280d500c695403280c0761a2b200d414000d2620324481c60009040ea134503408014103650503107034000b244c5004401d550916103071a0b480d603207644400b0014846c200845066440c00070000e800011b0305044400001d11f180191000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 217665899 1250 217664649 217664659
    0x601090c110d09080706020102070321020408070305030d1505010c0201201618020301080607210c03020d0b09090c19080d090815040f02220509070302030601080312040308090c 77
    0x1840600380d0b00034122000c80744c00c1410f03244000d8072000c0880c243e214110014001418840c07c00d2450300c0406401c105210b40d02c5001032610769030f0340c41e050514015074810703202c640000c80e048140640c540140e14544405485121482d82440000b03030500c0e40b00000030b41080103203142030200384c10750726400744030f12100002c5a50003940210801d40d01c602501405840100c041962114800c1c603009880c140d407400006403510f5503452900b2a0043d0302c08458640e00601e0240400071034009100f4030841d40410b903405640c510b0340c48902c0054a140c1241580a00d4890013006004900803c15000036078040710060b0f83d610b05080c81901240846d0401210303800784820041d12260800d04040894401c02c1c140e0300b2102203c00303410503664049401400b02400080e5060052418141d00c030410213140c46000e091079801106030003100c0088590300750b41da0050380c081c403c0d071a040140c1801406040000c62800d2414a0010440000076000900380321400340420f82d40300c3c05100c07680d00c0d2000a00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 217667149 1250 217665899 217665913
    0x18010c02041b110102030702071712391f060b031e0703090804030201080403031d011a0d150b13090b01170316150f1103070305060a03050601090c11 65
    0xb07400c0d108250311440300701052455400c10071020060081c0da00c07602c0ba0341c024001c80c074680b070b4006480e0f60140c5100c1c003036800364000640c4401800d0010f880300718907281805001d070440409003041107240004401c4c000c5148401c1714543e00c0009104440400c0310104402801459282d0002030412500404642c52000c01000980d10540c40c41d07084244040c608540243c0303a201c010740844e090b940c8050a60b080c2080140301550003102000c0c1c0080c4039280001d509501181c05402c404141d00f000031059465402c440040034265084508001c403c5880916005079030744d401414083c480c00390364015481d500170000075901c096141c001440d0792482030004001c10700e04010450024003513004031360120528200b48030000002e8405944080c003000c25086102e031100002d5003204d04450300140c1c1c0324880610029468003460b001a20b040c89000e48174104484040d050340c10042410340140c0d803e0b042000452000904c0034116050f0a8000601da80d079443e084802001c41c03034446201d4400c4603 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 217668399 1250 217667149 217667171
    0x1b05090f040612060b060f0f0304020a1d0403020d0201020c070302040b0411030106050909070e180411060a02060f0f060d060507030207020d0b040209010503012f1b070806070c0818010c0204 83
    0x1d60000c943d8860601000310082d10000c0021600170700c80403030521182400310501882003000115007150006040d89440e0f44c1d103158440f4450401c4c003031808203210b14414001019010030181c414a00580003e41c03c1c055101d02c0b403580c1c1d040074031002c3e120b80d0300c9024031003060301c90b03502604410b000105001d07540e60311a04d0151903940045501381c014030075680019a01c030303c80c1607000176802005044c45071414510001500d80a0064000d88004ac0d45000180e03007565200b00800c16490725030040d0001c2c5c945801d14210720f490007040700e8000207000f02080180d645075240c1c01c1c0520f90000340060546ca40d4036049000f0f0081d114001d4010240184940501201c2800d0a200303601c00c0b41c0c044030b6681c075042454265880b00d100310f078400411042034030800d104111250000004400380d94101091503001030001c01d0070207449441074000030030600402000380403665204006003003032000d0061650f90005540714241c43e01d074400303010001000181c2e03c100c024568442d00240244941c3c0340c08 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 217669649 1250 217668399 217668419
    0x13170303160201020406080a0203061503130302011812050a121a090604090206030a02210c04030c0e0403020d0518030708340608070c1506030b0a1b05090f0406 70
    0x16109601d0040c01c100101c50101d1050003220240d9206645414184e100c6c0040d0401030740000d802c2c0c0d9440b9041c1c041c502418180ca00c05984201d810180b40181101f080c180a42152000d000d10041d1201d980c2d00c00000c25005c010050b508403d070300d03000c5e13610340400804913490745030744401c00c00366402d240303100c0e0803034107045802903000c0c41c1196585107e80301c4c00300f08011101c41c40c4000b9003000d014030000744012480c0d4003a041414001e8100c100094071002800720844d002c60300110f540710041703001d005002213050500c0152040c0301130303514141444d80b0040c0d40c1e410314500150402000040000558607003c266203a038180182c02c940b0a41e4440c3e10494481880700003400203000c060400c0715070803407025510340000d541d62280364107545c01d0a20880320200001e0602051100b201d4160f400150013008d1408069500c44d0001401070461038003006114000d000944ce150400c00501e007803c2285c0c03086840c05009003072807644c07001c0460210340221405001194841e19007580051420a6 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 217670899 1250 217669649 217669651
    0x12030604050a0507091a040f0f031a04030c0b040f0b040609050c010212072d0b01030302071a1909120318050604060512070909020a020c12030a0c020613170303 70
    0x8111420700469459440e91011240102c0340c8800051803a48100001360b80c4894200010318445c031070501d055142d00048482a003550b0201c02103144080307041040c0085021482d1002070342c901c10361141c1c1031540f001483c081c0c407500007500e141c21241c046001c200540d46408151580503080881c5c2d458a810114001c0c0403008060310540101c1000304001e600c0418080301480007002d03031901f04460741d101c00c0c4140903903035503010154a1880d00102070144c800e807080030841c0f10f0081c500e0950306519000b410710750340c6d0344408120960200c0e60300d0400c0148040d00d400c4e60081c4c901d1040d40880d141c046070200071031740c0040d03601c0d01490404c000b0b26511207400010602d034103c1d80481c0595130b0040c00024400c6128080010b0030520008071b640a40e00e00c45038020200e8604411000d403202c013114120ba102d00b00000c050380c410b8042900c54200713107121850303082d4420007440c20800d0307035039001c1c28500312140000c1c401c1c0030000c2c00da00d10f5a03400c0e00c0000608206044030a4000c12088802e5883d48 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 217672149 1250 217670899 217670911
    0x7050c070801061508090313150207080325051f060e0f041a0916140f011e0507080c0d0206040309080607020c0f040b1002060a0b0613060c0203030c1203 67
    0x929030001c0741c40101401400d044543d80980c07411120034142040710aa0b001919086241c002081603406440307010441b074016021075000480c004000704006407408695a002e03074120f40040c007204020310304e4200e102c02c5598041c1003c103a41c0d0b81030710344039061441c00900c0c0840415004251140c00c0c0da540c0c4441e040d03c3c00000a01490f407245140040b030720b4000c950044c02044510004007400940c0f040c020f820403200c108035003115405400100c0c40c0b544175000304924203054102c0c0e038010b00e17152a02c0c41c41001c0c00c2c24801d082c01201da0000c04155503419450041c80070024011003008808411201034140810655540030407000c0000d4072404181e40580000d050013101051180b008070741c41d405401250002c0c020040004148652015000422507020769100714014032603c0e00144058600c10b590b001e0019860010841c8084401000a07540180c00c1441340c41c83e2080504000000d81c0d4203401c0c00501d07505144000780c5107106d03c0100034500c1c02408c0c00342908441c0030001d940981 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 217673399 1250 217672149 217672153
    0x60f050126010b063702060a0506060a12020a050d060806160512061504030209040309050406060c0809060d0b0604230d050d0e0103020c070b0309010e010212180a060507050c 76
    0x800425507440c00e0300e000100b003a0788108104054000d0350740c0070050300c0c044175403213000900c52085480100000900e0b40d00000c05030b0404000c002c4040c005108455101000f22085400c1480d42d5030010300c00003000c0c0c0c04406540d40010420380f07050140c0e0a541d0700c0341d1510014810140c8459059403a1b140c1600c2d002000b20680c0791a03110a40130300241c03a07440c050700242403159510361007000303040140e8032140107402008101c04000744c0c451004442c8668021741301c001c002c41c58101400100c0300d4940c04582000b82d1241c141c4000ba101004445061004844035074031210044d9425009141000030140d016030700040c00500424220001d074441840b900150141014201c18031500c0740a80c14001c015400409803c000140951482080c405040c500141000c403c540d0491500b021500301b00d00700355000c01001700d501003d01900d05440b469500035070030001010707500c2d07481e0040600349003110b0035200020400f0b490104441c50202d90071070400c1c480750800c0d41c4c001c0c0065100e500801154 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 217674649 1250 217673399 217673459
    0xc0311130504050604020913021623060609070c0b06060d0e0f01110313060f0b060a0e0f060a140d0e0607050919080303010b0c03070c0f0f0f050d020409060f0501 71
    0x4d40340510070344010442c047c000e241c2101c21918041c00960001c08041e0b40d40f0000d41360f07800442d00300030071040c0c1c0035040c0100c00c800d003110a089a00e0030800034901031003482c03441c04010b0300c282d0003800c20074001c0e03101010107200d84035040011614060b40740b201030101d2902c16001650301000a030301d90780c401403400800124544a0000b074003031004543c12034101d61205200c0c2e00003645030b40700c0180300e03690740d100142d003400040001d075890b4441010a030000307044603142502840c02c0802084001c80449409181509203e4040d00c61800c2c020f081c2c07605403000c21118400b00d401c2e00034110b0b40000500f640c0807403034071090282560704001601800b50000709162440c030410b10070003805881142d0011815a86004c40b201c0050341301c944040340030f0006110721030020318200b2452016100307007202202c009052a000016404130b95101150600400310304004985404030700020242e010b59000c034110040e41000c01c054208914080001031030030000185024000304c0c5a448808400f80c00201 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 217675899 1250 217674649 217674661
    0xd2a08010209031b030c040f020901090905040209040609080f0406030c0909230a02070b010e04020102151303051303080a080a0f06060905091b0304030e03010506120c01030c031113050405 82
    0x702d01500c00203c0d09030b400b192150b0704041c0e1074194000712200007003c407000601418085800d8444421501c0c04080e00800c10070807d40c4c10410000240103000307007c1240389400c0c0c0000c1c06421000e04050003290341d89100c1c0050040a404440140c50f40d00703480c5544960fa20402030050010492400c0040c1000c2008148aa45030045c0c40c40c1120340300459200c0c61560141c003040003409444030903010b41c204510350004121521060007480566420f180382d282500000e0b05003844440a20050303c040000c2100d451441c0c004124a070740c2514000d0784402a02d519102d1043c010340015000c024045142c1c0c3d8202c0c0e0000105109581150080c4540560b01c0035500540742e0340d028140201c0c2090342c0902ca03904180c05041d0380183e15407854a0004409488144035070720a64080c6d00041c200303803c112180c01d00b4040c07242c2018042d5030076a00c0220710b18140c0c1e1200d4041141ca810136403034001441540c0d1094016800011504843c0d41c0e840d5140151100c100e1440c1c460b2034000d600b86000110 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 217677149 1250 217675899 217675901
    0xc060f0c060c040b03041b090903021f090c0b07030c020a080f1c0e04020f091207090b060405061603031b020309091005010509100c080f071a06060a0e0d2a0801 70
    0x2113841c01ca00b190705589842da80c2040082510314184034018003050005955220303030007a002c02c203009801800b50402200c911071002260340c07001140392410800d2400024a40c400b01204a07002103075969210100c0d0b00d401c40c2c0080003040d02a5200e098000082140a0003081301309205140c0c3c0200c881c5101a040044001e07203c0c2c058160200f407400506400504098009180c004c4400700e00a180c02c540400255032803e16400c00c103811b501086080c01020128031031201c045004440c01404c241c82d082c0040c08a10030030919102c032069507440d0208243c02a006010b511003038128990001c00f0b0000025a06d4000c451498400d03102030000c901107403820564002510070603035459180100c00c8052104030b0b00035000c0b40741040041e05048020a4441c0068141c0c5c415500c5250781c2c502007820710b02900110a1100300c0c5800b0a4010700c03003155516011500d440300c843c108128440403400c00036003c0c0b01c0651016207080206030048044c07c2c0d142c0392080c0810120504400c4494496255074 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 217678399 1250 217677149 217677157
    0xc0d050f090c1005070609050330070c111806030d0c0b010302060c1005010f030317070207030b09010605040e010507080106020d080604051009022106040b0913050c060f0c060c 77
    0x2015504030011050003414141840f140348501c5003800d901e020300d0703550780c84104d48800030142c40c2a0400719000f40204174590080d0841c0025003810803003500d11a80740051080040e00030300622541007210020404012201c0a4090008041d500c1d0510702c6054101c14800440d01c152080c02800340581c11140101c540d01c08658100d103c02c0311503800d69090020329440341c120804e139880350400c210f8218456025943c0030b0090400788040503440d6103006444549010601c0042c40c42c00010401d05036800124141143e800040c140c0b42611554110750040c0116005241c100341030000302d406111054125a010f206103075110310303283c3e07a940c000700d881e52402c900b80030020322541c010a020b86405c0e0015038002c10003215003554281d5a0345544203e80c49820300c0c20f524100750040000d000303464410203030f2102c8196414042c07150b40c40001082c1a07c020201c28100302e5490400c410710004001401c21814090040c03a5228a4512014010340209400c00601d1003958000749460b60210300307079 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 217679649 1250 217678399 217678411
    0x110a03080319020903072408220311031210080a051e03090d1104060608070207121406180c0103020702010f0e0102160f08100b010507030f020c090c0d050f 68
    0x1609503141e1042602049020503141d0b40240c0e000d20800034a41d60500c089001044d0107004035540c2c3d5060f0021141c0c08514500c0d40003400418401c00c02c0c0400b1100c1c642d42148094103c07a20381c401185410345840c40300c101c924003144404140c4104140f0043c00c107502070144883d00030445543d0302c44d100c1c1c0d204a9901c009080d078101000e620a03543c2d0500701e50701c0fa002c40b9000e9070300f01150345021920441160340700b95420980d410816010342424400c07040134255a10b4404120301e0070f1103003c2c1d87c03a0000d1150b8805840c21803510018031821440001d000b080d48070a84820f41084035149406410310802420340c0e00441003460202d40c002d10846403172a50603180c510524071609000d455422641ca80641980111040d2458641000220801524800b040c800c0618244000b403883c0080b4400030502903890020a060356070f03000410354048648c14688070401d4030030a4070485c1000048002290419044024014001c0840015001169907034200b000303541d54070741081d20200e00070303603c03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 217680899 1250 217679649 217679663
    0x70f081e010b0f01080712090309210c1215020d060609082d100c0201020d0c03060b0d200307021f150b0c03070b04050c0109080601080319030e031303110a03 69
    0x3c00034455020310403650380003a040c02c03d0b10b80489200d01110580745006011000501c452005000d004039000d8411039940f44c56018091000080c0c0d10120101c003280113a07230b16040c01042d80c0042140f4850841383c0c16000000075901e401c0e20b14000e1010785294081c5d400450940840811340d40710020301c030004200b030082c62542c00110034803c0c0789101c0760203e40e071402e40540820f20300d05c1e503914010490340d41d94a50005a5401c45042c540080314500b180040c1014105001003050028003000e44210300c03070903040011010a40f00c0389124030404102900c00007070001c070400003866000310f50001800906c4400860060307040701a402120203080400c15280c6041c2e0085c0020005400601182d010320411689824034070744400403015822030381202c16034080c0307100e8821035a00c00c0c440002040282c000f09010350408405a1b100c0c01094242650076813100506003035140310b5000250401d0b00d12050700c2d07a660f0014941458545940025100141512015280c6081844064084071781081c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 217682149 1250 217680899 217680919
    0x90c0c0c21050114011a190c060b180703050c040f030206090402160b100b03071e03020c100e0705060705060708131707062d180611040303020f0109020f040b03070f081e010b 76
    0x10059030404041c1038161060781e03440003d140342f61038501e51200c1d2400c02032094100303450a14001015500f0041040007040d0043c08100001d170500c20040d010b80764100c41c5a9140c280390030100300240100b50045800161100b40b18041c08100b140140c040d07036028100304107854658600070601d02c402c0ea686070001d02c40002000700310541340714840c0549030341d00e4090700d040c000420240c0b03007052001d0a1452290364085403030a428042150300c00078181038a4060901e82541c45650b1103140c003c10003401d011819000440c034002c11409003200503031100000d088482d5030301c1135028a0308410741c200d405502e02a119804400f09440101800e56108944686044900384480c045c094010704a010314414809810001d075490040c4100300c0c10300f1107043d0700d9900c1c5080007450301e04101d0f0f004200e1b0340742c1002040135848401c0040b18034202982e002c65803110705404a03203002030540c0041d5107040c03100400706284401040b2407010f01d03009504105806100000c0c182244c0d102085203500000d985 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 217683399 1250 217682149 217682197
    0x70509130c0b0d320415110301120506241e0301020c0c0a0b030606070204020906270f0307050a170a120801090c0c0c21050114011a 58
    0x14800c1018800d00c1c0c2052074556070784080d44903030890072452001e951141c0c8040c1e040c40301200204000210800380c042000c01c4040303040307507082010304060004815085207400307650140d00920700901e100000655650b940721174284050704040070403a158040c081c080b500309a0039000c4441400e2041c005410880111010001c6c1429140c4a800b0300c50071119560700d481d9401e00c080c041c1525602d0140003d40940e03002c1119083d6187c00c00c2003085018014090303a5190002522050340c0d043d200160f944090800054441c002c0901409030100101044c001c03139508007880c01c004003425550318408212000806403180762070f0140c10741004016508000c100f40040c0c0c1c0405d4050020191000764056440d5002c4444503250020302103100c10004200400c028419184491002d2030314000b50407580e980d10b8610100e500c2140180c10500e02008404d00d40071a05400380d42e0b1010080018558911411003c101c00340718051140310740f040505c7c1c5029510302100d500101140b00c80840c0d032101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 217684649 1250 217683399 217683421
    0x3030e010e120903010e0610050a0f060806040902010e1e0a0b0f0304020f0d08040305010e0d0503010303170a0605040204120b010611062404050108030d0b04061a03180a031e02070509 80
    0x40f000e42070349507403203d410100040301440458002d11001ea0007030784007030604083c0400e00543d903000200340300384007000300a40c9602542c0f09030007140460b070114001c0540c0c00122038070003071007240c1c650000c800138403004903458540a040c0b500300240c60703000d202c6030742d002c00011a00508604020390001040064018901040543c5800d18000c0600d01d03007414076214201550816081128103070b56404040701d00304070402100940014501c2e006143d03605555000706040c0440607040031444c01e84021030100013036a082500a000c015004544444d60342d01d41d0824040c0041c410340f20000f0001c000714010f4841d01030300a03c00d50704001070415031501540f240426017609540d0306400c0048030300c107440760b0303443c00303403a0003444007000442e01e403a4400a2181100c441200c0da0340700d5407504104100701008601e8243e00c02580b07480c11364590b511442c0d03520f04140c01c80d070081928040c400c120f00030180c110340c41c4d801440003900311801d405419a001d80c5d5541d458090b15901601c140001500b03c640 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 217685899 1250 217684649 217684657
    0xb1309060204030503040e0a06050301150506030417180a0e010509010e0a11070c0e150a06050901090b0d0e100212061e0d050d17040b0f060a0312090303030e010e12 72
    0x440e40c001494a40d49403a140e045070856004540340e1140442841419000d030301400c0c2c0585000c070000c21005270130034620345001085104960042d880840001e0031302c401d07607505841d843e803085045a03545060313220103810281180c00705403245070b002d80b01080130341180c0f000c5816a40043d0200c0b080e64200103034208543c80041100303203000d0702c500100d0464000d090282c841d41d441400400301803410203501e0801c04500a20000311040d0160300d50032255100b81d4004200c0e030990606d1541d5001c2500100c1d0030308000c0d080f0300155400001d0605c0b901d50183c0c030000050207200d00392041285120500c409074411410800740d101954000304040b4034107030704409041d01c0750442110350a00401d005c2181464030762003d0700e5a801c120500c08089400510444c01c050f01541581514030303256856400c0b884024018110309004500012041e1f12000185c401a54004907000c0015819000003001911316000844c0024104801c1200c41c00050184194449424024100007110303981c84c10700742c0d00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 217687149 1250 217685899 217685903
    0x60a0e07090207030e09070c052a06030421050408030a050a12050f0106020d030207030813050f030304060203151206040b0a180c0302040b0108090d050304030207031505060f040b1309 80
    0x26105001450007400d01c01003941d14866101d64120f0304139201003010355440100316a0a2100c10486c80c00001c8011030950203600107100c902d20403020544107942c401c3d40c0f00c1c4529411410010900003400f0300302c400c4007101461041d0200d540c98003010111028043c1d841440c0e15940103004001b4030074025405020381c00d6851412504901a14807550140d400941e644903600c1c2c02480107004080c2d050140b801445a241000d510f4000c3c42d0f03a004111400c0140807800c01d00c50038403440d08100007400030414680e8038204980e00d900301424a00020341c42034881d01190244203c503c04281800803030b07040720305000c2c80648402e42d120340741c0403100c010040154a0711652112403014100700200704035656030003900085107541c1144140720459050340300c1c07079051000c4e10080021207800001c1e41290313030700a03180071600d90720790f40f80c141d10740041e40d04010000d910340001000c6c100403c2d807040d0300c921411685400284005c009200864511b900c02e16008001001d466000740c80070b8021000c114 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 217688399 1250 217687149 217687153
    0x20706210f0c02100b010504030809030304080f030c240c03060a080111070c0e090a031b05060a0c0f03050c030115090f0603051803030c03060d08070615060f080108060a0e 75
    0x1400c00d05000c03140303000c0750721880c40d641e1080d003080103604101301000c80715480c004005404107200080d0641c0218440240403080011b040026600d0500c2520f00400d0102c0440c0c40000da59030415850350803100c40b0b4140c42c07081d110303842c45080c00c104400000d20a040180001c03501e950381240c4841d8401407801d5082416042e0002c1c0688091082e5007031905842050354071285030b03281c0f0180c03110003644000c0304c0d42d00080500030f50f140d001c01c03110100360340341c200180c000c2010900c000c0740102040025180d4000c013801c0080c0e080282d00b15004a820940e5480720b50016007009034111602580e400701551010b2006122003120809140340040b001e0800d40841c9945140200c2e07106000d80040700040d072200c081c480c21200702c4a00c401000d918101031403c40c981a00c032415540801407106100304100b400900510294a04a440e5160410704c240000310311064540505006881540009003d2502e00c0c00024072804105050b16409809401d1700c0e29402c10300e20142185240000080c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 217689649 1250 217688399 217688447
    0x105090420100207060201060503010e07210807060b0a170706030b010e04020309010b12030a0f0f11010509010b0108060301090201091401051902010f0c0302040b070201140c0106030b09011b020706 86
    0x282c2d44900d02d100c00680701e64020200b840c00c22600900350344150f031005010342e040131500d40c42c0640102d009030075620901d5280410050034948002e001055100180401c4400910395051002c16001044424019280445615600d0032071035004a41031500c0c80c21908103413003e100051007030300007003a8041d052510841181c820300000f0104d07071050b01c0001950b99103426409842c01c0c0210b10071030040c40c1d00007447c140031a11402418841d0882954802c008604400f102008e014401000708514100001c002c1882c000960034000d100740320425020900c40300010b043d62505001d0003c000d50f069581004482c50a00b84070303a44502e258900e03041c0070040c01a41d001c00d400400410000c40d481d4000b2512103198098401103c980307246020030035004200c14000302c0781c034504480c440d547c286050008030700c90302000c08045c0600440401c1035400e000b40007092003c10a06140a0003182000f0000180c03070190180c071120050108001603040400108060303805007450000b90304040c41c5908803 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 217690899 1250 217689649 217689713
    0x9060609030f030301090606020303010501021c020307080712030b092a070203160303080c040609061214090a03260106081503150703050a050105030303011205030f1305130501050904 80
    0x810b2054028841d00d640003100400c51ba041d240100c50040c0901d0000d0742c81c42d414080001d44411f100007440c01c03c0b0012426803403040d0320800c22142c0280c0c00951f040d03200d500714a058140c607948410342c0d00019003030000110961030a82d850b1406100000001d84040e628900e0200c4580d034000901043c0382c0092180c2c10142e201030140e00c1c0314a00c0c035104100d015080d0318001e0602c0c04050f187c4a0f81c45410701c014041c5c0c85d0803100c08403d480f1079040034840c40880207031200140035030240709105a0701c6002401150700000a904001605c03070f40300c01c84000c1c40b100c0002d030703540200400015942c1034100100a818010301c3e0342070308582070013515500d0b0b9044a0110f49460003940c000c03907080c4007180422644940c10303c24150003424a28090149500d083d0000f641c0303000600074180b5603c2c0e103902200030000100102d840080c6c00e060305903240c6d1501c0300c600041400c00d11500d0b004030784012148020180e20711509040e2040245520110345464861540310b40301c60a0440c00585404043c0e0b01d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 217692149 1250 217690899 217690903
    0x6071e020a0204060e01030b07030507080403030b061e0a0f110c0f130608030403030e0f03060606030702031312020a0b030c041206060b190f0c1703040302010b0d0809040c0903110906060903 83
    0x8090003100170660020352440c5801600c007c2d0041600040514060034000303130b40d81c00261540c0064051a000c40c40d0014000014154446c1e00c8041c2e4120313140a02c2d0150b2642c0400150030450402d4030f95841224510809403200d0000d00b01d00c218680101802e03010b00e10300b501c4515046c2da406018407802400e00511541159079a80101503680c0c0042020810143d0108282c050f1180a45106240c400b901c0042030362210f014240c81d200e010701100040c0c40603c208280c814840e034000c200d500c0540d1f600b9034407442072035031075042c2d0145001a0010900d01d458034212801540441c420358a4985042018030324108002400c580709601d9410000381644801d01421603089120000340704054520f070060038026828a0b40400e0280f06550100400d00e0b1098050709040300520442d540d943d43d180480c0108580034045a01100344400d0009000c242e8000e007544800a4a00700112900c18000350303809226817100806450300c14004400e2400e08440e00d640152000e040c0c14180791304040024 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 217693399 1250 217692149 217692161
    0xe0a031103070605160b180a03030b1c03050d020901050405090106030212330a0e0f0403020111040e0a0b2d03010b040c08071803240e06071e020a0204 66
    0x40c03000442140e00142a240a210782c9000b4281410311602d48500d00300d510f42c015101d507101801010000b000180405135101244243c5c008040130303201840d80340d18028005003410700d959801125841d03068100307001c2c0030900070b40260305a208d59080028010215010754007049a02e41003240031300c4005900e480b04640f103070107030840d03440c0540c64408451000b02c0118001340076400c0d20341e58258142203a035641c40c201a485c4400e00b5014500c1231220049202122a40c0c0003000c841c0c00d040030862140b40d08011180a54402da000b40001c42c02c40703003454114001c500881440914903804034420400d50b9005101122000c5c0500c12400140c0e60070500c0c050803c00201401d0560314038182d800c1c42e0a00c213079200711004032410415500c03e0b84005283c040000d0136a000c1c42203100d1079a521404403041d0400a645c040c14102c00040790110050712010125520811a420031040c00c0880ba17000c03500300e110701c0c040d54920a800c0d032400750450302c020014917440b0950188100600c0075880701d000e88 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 217694649 1250 217693399 217693403
    0x20a1e05090a140702150105060d060b0a02010c170f0711011b0e03010e12030406020313080708070c0e060d0213060b0c160e0f04020d0227010501030506010203070f120e0a03 76
    0x2020f40c42d014030014100d900130500c104540120140d60396000d41528580e0540b00c040e40d50030340341c0c4000781070a402004190803418403108013040e50700341b00b43d0540202c1004820741e520b05007a01d08404a50404140655001c155000407100244103e03101da00c10400724040c00c00041800248549030880d1100d8503160388000a1045d00e5241305803d0900841900444140050683d624148200c403e0b600001d40014003071500007002c2a1040382444010103000d40004541d980e0307000a00d480003050703200d45411501c6101d05c000000b041e503042c0d40014450480941059040c80181d170070441490030040341c0f02d0715a0f5480602003050000c6501801300c03900048001c00d280803481e01c3c0c10140e41c8155000c185158520300c01c01c0200150f841c80d0a40096060711009294003c41c4001070003459042ca081c1c00a00050440050003562001d100d4120b541c01c2c1c03400c00c42030f01c035100126201d2181c50000340c5410110300c08400041c801d8401c80d0761100c0c04e46004030851103224001b46000c0c00e20707402 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 217695899 1250 217694649 217694651
    0x40906090209060303070803160e0a06171302030c042403080403060614030709020906250c051203070311070e071d040501060c0b04060b060d0225020a1e05090a 70
    0x40c42141401c0090307607001031084009509281c3d4551fa03510651000030a0210302e41c1031440341c6460b250090f10501c180110003059148400d881d0f04005210300404942c1c490301e522484003050900c209605014107598010b0b002c3d005c0d0641200920014000070801a044201c0501240058503412030074180030b103100745810390383c42e40ba5007094810b80e0610307007001d24042c9800420780099a00001e4041c01c84100c083d0141e1281d91321800929580200c88107509440110003000d48424716071444181018030070032600c0c404644920a101c07051040451030340d100c0d4410403d980c0868000e1896450b103984a1003200d9442c5d0312403441030117001c6d0580f01c001c0172614400d56103120b000031a0f5401541d10065800300720f41d6144c003000505141c0412005070040038440e0124040c00000d0700700928061025000c03664481140c035880d0000d5001e00325840f51100c50051044030021510020100340382c004141c1888581021600403060401d0100c420120406920018180c3c5070200382a1280c600c08070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 217697149 1250 217695899 217695911
    0x4150815210c0405130f0c0e070c06200d0b1c050609071203080604020c030d06030809010909061d19090f2d060b0105130e0108210720040906 62
    0x2450b481e007141c000351284644d04220401410341d01c0d280c4001c00c4190070a40d1144101c0c80c41c200001c4101c03440d00000c21012a4008014200e600100d085601d0b0380700c0d000c1003003da4011608001c0c903410072400c449944200b0041c11500c1d00240c0c000e00f00051008002e111400450a60000d10f0101c03c40c08a07440c0c1c000508100d00c1000c00e212001c01000d041c407155041e84417607500103000c3d28005040c244a95404200450a100704005403400b49202d081d08009080d16810428429044070030000e00091000781f0100f00001207005020850740f111000411740b10900c3e200c1d64184800900518000c240700c1d14202002e131003802010b42c103500032000070152075583d0034006803800c1c107404503a42c680058558031152070f41c800d0130084429048403002440101c1440126038500c681031a004540079112030100348514200301d4581216008400c8403680c000d807200c00340e84a16801d1100300c1c18102440054049006114411544c02e43c001e8202e05000c0018000750071145450f034140c5046036200 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 217698399 1250 217697149 217697209
    0xc050903060f010e10060e060d091a1f060207050f010e061206040c05090303030f040615081006140310090303020706020d0c0906021614060403021018060504150815 72
    0x801c90170b40224008881620715418a08040c0100900540e8075003e450000751001410500c1d900c101981039110080a40619016039000c03054803042d42c00c403407003802c0043c02ca0808501e052202c030841d89035401802210b1724003401c1241ca003840341103441c14858015600c081c55a03e4800a005454100001ba01c2e1403c248007808200c80780300c0c00e040c1c02d100d0100310420f002e55001050701e42c003445000c0741d111a0f50f41c070300d00b5502401038004203800050009001061554010a107070003501d050b800c080011981d1070491034101170715980d00507050f0b0040b07003120a64203a0780e00138000d0705020342401340c500b030602e17991042264409102511541d6444d410b8a6110768403c40b0800140322030302c020198071070142076a10640781c00d07200d5070302c0004412350b9807451a12600e0540c1c0046400800401c683c444a00000d41000b10030010f460b11900e00d907102041d00b038080d100b82c5d025580c28000455603000400d4055980450180440f5013280c11111032000c0c90340d440b6191840405650701c400d00001c000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 217699649 1250 217698399 217698419
    0x40f050f010f0f030206160c05060c010c12090807020108040507180c02011505012106090e0a050d020f07031419030e180105060909190203011415030f0a0c050903060f01 74
    0x5800024503103c0303081c800c0001d40d941c4401d403611a000010b03030054960052400701031720f12459014942010010804400c10403040d4004150840c8548850f40c1140122201e40204c602c41c0600138500c00081c4030b8000076500c42c03540d056002c0e2085081f81c100d642c0f110390003a41d00c10b8000c2003c00305900c541d21084016828000c40d80206244194000c4332410400040e1598030714100d00c0444142178110620b00301e40c0c3d50004c0c1f0051504107010420f00c0c0c800c0d001e4941782c2e01c8001042c1c40d684910b56885200303d100165090003540342801900c0d2542c00d60303075038405c100c0d021080c031409481180d8a04180711440c03043d601d1084c0c402d40b14100092040c5d4244280050600c0c0b6000c0b003001c0000040015490b41d40856081c00d008540b80c00d1140d5401d031a010840c40d030340c00300c5003041d48084008180da20300c13001c45031100102128803003024014481c50080c644822070f95841d84004090105100413510341006000d110242412402c03d03220702c010a1a014007102c400c507c04851a0041141201e2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 217700899 1250 217699649 217699679
    0x108030a0f030b0a1802041805011e08061302010c080d0e120405060d0504081317010501050904021807090b2205010201021603080c0909012312070e06040f050f01 71
    0x15081c240440746600f800100044c0e841d100305208074107100401403404c00194121307005412805046c183c1440203801e84002000c00740107104003110180b11b1010403403604043c04c011611120018103080d5105a0307900905140814124103000245c440000000c10385006818a1284014002070030040a03018510b481004100c00000690810091080c0d07144c000c220341c103400d0100800b01d640d4407240380212175072145604044000320880c40c0416800244081030a8480c0d0031002480780780d8880c1c00b00114020240c1d8025800b201c5102550036200919008950006540c04d045800135510300c0030074605c1d846080221095070300b019510448103030410010000d02400c1c4000c500b003a4282c160740107011400f000c05414030030240001440519258100c41410602030401e0000303513943c0c01e50014100040016000320000c40829052030b080c864519048115a44c0c0104101c2d03140291a414a400140009411a8950039010b000d10a6070140380d001c0e456403801d003d4158501442401d080d05 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 217702149 1250 217700899 217700927
    0x20712030b10030509070504020304030f0311030c07151b05070b0f040201091e091514010c170f090402030f040c060504060212180405010e1f0806070e12060108030a 72
    0x490001c210310151078810020011441e54100040d068403160000791034822070f9404285d001d40008100b00c10194408217040885250303403024841c18141c580145003c0c00125001190142c051009602103541404000b10000d020350000a5031a2044a0301c40d020b00c54451b1b88000c03960000d2040c003040030069445611012008036607c19080c15030008012144601c2a00c4012a43c0303e03c210200700904c00c040010301440078100980b1a80c41da11904040d00f5201e5503504121104042105500504201e05501d82c0300b15211440420703140120b0301500400a00803000500388664803440e10b440c8011400350086d072030759100c1883d26141c84620942076030041420841c042c00308100158000405c1c80302d035201e052240751550144c0031110030300c0b4044048142d006041a00024920b120200b0f020300034811140d402c5219010320340409072500d603038071441e90160300039000071300d5440c4a0314074030074411401051800c0c403202480e0641c1c5400d80a80084d11a0f0b04001404409103400140c0c03071003030790 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 217703399 1250 217702149 217702151
    0x1103120c07050108040f03030e0f07080601090b0d020f010315170622030512060d02030d08091002090d020f0d020603042f0906090603030417030c160b070f050a080d02071203 76
    0x8038186d0b4404150800c0440c0c01000d00d6210102910741080c103100c2c0128512880086402e442d80d04e403000c80d9101d0080c411401104d244c844040daa9040c03803840009200d070050244809801c12800460040c18101220031f420450510080b9549201c262824000203441000b4461400c0a05000c08050b100404507241c404a00341c1c00e20009030003c040d0f801e02454005040c0c540c2c0d42da2000b058482d040380400a42c1030240e002c651110030741080030035005080650441e40ca580140034007000b217100f0005405ea200003a0503e0100600d01801d203085803041c0640310508030a41c5501003862074005440c11180004250310003400842030003003001030780c0c0d01d480700000c00f101104041036524001804582c001c40c803400c002001c80c1c5040013110011300301100060f174107a03d0010780f6503da4010980c03841e00da00503c0303039021100c082d0510780403d03514540d0045142c1040e640c0c07412801b00c81410101d800c1c0c001c034507030b45000c07503c072802070a0280b042040150b030320150340c0b50031500740c0c4010b41804141 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 217704649 1250 217703399 217703401
    0x2070204060929010210050f0703050c0408031206060702030111071208060d03030f0e0706090501140a080c0d1503110906030f07050d06020c070b07120201021608071103120c07050108 80
    0x200504454010300b201c0007110044091503400c004031b0805108010390456141481e003800010100905008e2149100366400c200c90b885405030042c5520840c443c1c404140d009011001c103180e40a01d03042d4100900410191034001c0f540e011900303540750600c101c00b401001160001c2885116002070220f41410329040045142183c0010131441ca060400f80c200340d84c4806001410100f607001d0044807004104442140303541e424000c1904d0010702510340000c018081c520343d484034000030380e02000e00c541c40c0c0740695550780c0c0c1d0803a0690001c4100c40d00080d202c60517842140d082d204503c001d540680e03240f0260021842c20304c400c010001d0f000c640a988645c508001040010482900391a81181c4190003c0c00c40c0c1800030207405010101442805009000100500c44100400701d43e8850740c0c1c0221944080c000c203900300d01401c6145c50468280b030b1003840005c0d1692005046203481004100505d4107020040781c034007044980009103614001039038142d8500c0401c5680014030092810f5889 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 217705899 1250 217704649 217704671
    0x18061b030501260a0c030b1b030402090a0e0712050607030e03070201091806080303010b0d0506060412080304080c1504030207140307121106070b0403030b010f023d020702040609 78
    0x201143d8602900c81400f0340f0207062400395028002c08084e141c002000c400156164144201b451000f52903020b00300780e201d5005280710740000240d80c03096030024030003c001c1d2740d03e0811101a02280d03214400301d000d060f0021900410101e000b01450b40103d006202078a4014809800c54502018444003680240701440060b03911101010079184d40103020044202142401d10190445422007501c41c003001c800859080707008009803402d0003003040b060000752550030910146104034001e101045101d036040e0800f040080c001540c00c01c0c80b6240c0580f4115014264901704071005a80714403030700c215018001030542c100040070207000c0301c0b03941000c2885044002665660944107010300079285c00d84000c24046c5039407951a05590140c505540c44400f4980080000c800300e8049000c40d01d0218072104c0c0354864a1002c1605120b50001c150f07003804900a01c140490034007071105105000c62100c4440030903d00012880740e040c00001da141c40540c0f0400c403e031251600302d4203c5500d03104460707070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 217707149 1250 217705899 217705919
    0xf030f01030b250f1404061214040b0c07080d06331706060f16150c0f0302090d0210091703090307170a1a04060c14030604020d18061b030501 62
    0x1c0503070300d20f081c88000a02008000e95280182e405c0851700e925012400140c85600160003001e00c1413558400c101c00d11010044050700344058501a007190b40c6a400117106501b5440203194003400743d07030307281e080205e2080040b00707885050b0840c141f207400c2840600295005180c501e41004210ac40e811050321403400000d261004410712240c5841000010130b0441d103c0c8000c0381c080c1b00705001426580c41c6111400c0c440d05154407011154200c100301602d0310311905109401c0310325080c9d81d0381032000392600d000b2006900b0401580e07034824207103c00500141e4a00d00c1c2e4500c2058591a04d500c0307613140241c80c8924652514000595400401003840741d07580105401098031100c003902c10188012102c81032131303c900700b00d00030150a6000f00540d1464030303076806688158422102403100c4521210100d0b010381070004805030015003400403510314a05a0083e0000f00400c00d00060071203060740340001b109084042c16200b40b42d03103c4002d407403458446411850008581014003044d498441c50301 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 217708399 1250 217707149 217707211
    0x11010e03120d0902010504120506160207050901030807032007080f0106080c151b01020405040b0409020307030209060f06030406140906070503010b070606080303040c080d020a0b01090e030f030f01030b 88
    0x15040b694600c280c204581c06082980d0290021b180c0303010b0140320780c1c03908503500c82c0d044d01e0f140c3d03c5003000041d50714502d1000400c0001c0d0750020f000d0b540c1c20703442c60b0340b070341065002080100c05205a51112a54440d80d0010303040c3c800034807000625490340341650283c10020340280e26070903641008408d02c10090005851903102c2c00c10307120042d461680c511001d1443c0100c504007070310400d1901c0403020381c483c150058410340b50103c0742000700600c034904010881d84140c0c0000d405800c460740030005450301c0e500f40c6a11841c06030204520000301800a203941d402100d08032002d82e0766802c84005c070340030701c01516800740200c4018480c50404a01c0074009000c1407103107850b41400021035030b01b08452a008040103200ca10200c035142c0c10149000502040303130340520b51980c442c400d0040f002903c0000c160003215004840c0710116400c0082110181100140c1c003840b81c8401c10805400507580c4004521540c0d01031401000c55065207000107001e80b0240148001c00700382200142e003558010105 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 217709649 1250 217708399 217708417
    0xb06130302060a0519020105060108060a06080a05040c05040908040906050406050105030414070509010e09150c0f0c070509010b030a1b1b060902090901020408150705091c0b010311010e0312 83
    0x802d498208800f4100c82c03c0c41081d41d01c03d001942510800c0030180c05410050140307000740c0f24403070b41e50345034002c0c0811440180704000004d805140819408110f9501c2503411a00501540d48225262404101901e41c81700003100c400c60009420025180c151103490042c000444090089038a0b02c03000030020702000c0d1001d04025048001d03c4480d42041080400400d0040c0008800f9a525001445030b01c0084612900d18003c0ba03881030225200c03440010f1003480c01e0340055041144001701980150071440501e500c074401ca001c042560ba5070448100e00a000e260380aa9403071502a08880a5a4403081801d4034001401c1001040680000c1241d469000301410716101c9a8242811406005180b40c044c0d00000d0020601481c094103400501c00d8030f010303d044981c085588004100880b8003100e0840010703409002c01c165624000b441c0030140041c074044180c2e803191036282c501c4d0300701d82030340b08886030010034440309a903503007029030030b100110708a025001d01408016901c040e44240f40038 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 217710899 1250 217709649 217709659
    0xb0609070302070605010303050408060a06051e0612011401170702190807060c080702010608160b0c0f0708011508150411030a170703020c060301060210021c15090b06130302 76
    0x1940c9035209505950301260005024415560f407410701402030340c801e0080010f58003480002550000060103800112a070203005007448089201002043d5000b141b50313140d1042082059841d05c852603600907000c4d00d80b46032003000c65101800058400c0c1c003a0307220074404051010412800b1500030a4149440030761070000840c5605500e00b00102d40b19034000200700340e180441c5441e41d264407181151140d1f8142c0c0081005030b4490004564900f01490214840f5030800b0081c8500140140a0440c0c0c403540340480b10085905d81c1c1290038081540c05c658074507075413218040c850031a104c0d422801040b522020740414071080035040090300e401040902407062030040000640c604010703070b505141d04412043e980b44c80903912582d081e400128150018410344200d58030b2480d0030001c40341202e0013500205500700c50b084010010390000d0100314804004980c0003000d0040c1405800420140d030108403807500e040c012000b084500c80701c0302c54051101401003007404d0b6424211a426030b031f0100c82c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 217712149 1250 217710899 217710901
    0x8090105030a0b0d0f0b060f06071103010612051507080c090d14070b070b090c0108070804050118030f030515030c1903170703030c03180f050c06040609050405060d0b0609 75
    0x100c060150101040450f08803102c0f81a40d004d01045d1098954541d2090340031481d41c0c4c5400d0100403068840c40c0d0800d0740310400700b204500090102c40005402c0138050000300b01d082d503130501910300d000480343c181e035140c000d044040320100c0c001910691000306030512098a003400c0600c1403903401401d1403640135034048181c46040c4007041b208280c2600140007101d500703d45172501c44a80b81c00ca0102260042c01803800b2610000002c0340c040620306040e076076014650740e1098200da40d404081c01c2a503255680b00903c1040c04004000e26903418060f0b160b48020405108000303045600041c0594a105400881d003160b655000c0749410010200b120050410003c0888803140c0c41c40590000b880c050b0300c59040810721078203a01030b242e0340e0b01036102004004544402942512221291307003860008950f154400114419040c4d40114050b80844800051107004690fa0754010b4102c503000c40d400120811086c81d2034021264070190681d40141c2600541da61315143e28030151019128600c204 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 217713399 1250 217712149 217712161
    0x13060c11190317130803011203030b03121213050613030e030a0320010b04051e150d1e0b090303090f0f030301030803090f07031109060414011a1c0b030c0901030809010503 75
    0x5070046513056040034015590b940d580300325603d800b09800f02100400d0408a12000d180340100d440360901d440054058600b580416555880c01d100038904100303100c40550501c00b02c0d104000c52032103050078011348140c01c1918103000e0280704038150f600b48603038095070024001036444103240c2c00c41c03510041c2c0c002028400c0e0150354054201c0d41581504140380c6001c001c1c03486c18105608001220b00c4010003a1910303007a107403d8100803601c180641013001c00c0c550900042000c000d030304c2a10000310706001c0084695036014403541040d180d062007a400403090219480c0240841c3c150b1640143c024029031004008580d101c0c0414440035103025408000030b04103810a0100090305403803031050310311032902d0b8604110052038481d266800b42203030500003440c0d41020f04c21a0341021070780c40401703403503031030042c10b03817040402c80158601c482d505100107500d50052401200464154000104bc4250900185460701201d181c2d200e219000c0380e80100081a1204101c400000082c82c00325542e030340300c2d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 217714649 1250 217713399 217713421
    0x60a0e0717101a03070507030e040908030a060806100815060102010e030f0403050705011b0b040201140c01200306090a0507140f0a0906090807090513060c11190317 72
    0x1c1076a1151030000104100308080d103000d078041030300e910800802030400c9202c8408564002103a60030003240c1d00b00319002c040380c01907520180b04c0000800c0450103043c295128071498000396010683c458440c03100b0f10142030184642e03540069810195541c2c9450100440c2d603507220a10307075038030703581c01d1202098059100303402038241c103aa42c1c0d084030b03036544100050205503842484250342c03a0003022000b02d542c0d072103825201c10b04d00e413080c51014012542d03140c5101085003d4400c0b8140074520b5100320019500c10f004d008000304080000481c40f0100c14001460058110020101c800400030081030341e0314507200701d401c0034421900081540d1946001d43d03050713694840c0407209841c0840c20181c41c404120060040b402242e81d000701c4240e540d941031356440c0081c00384e841103401904080c824911594402940f01c08410301051700f0312225140c0c8001c88000b000c041c00003401194410309008001c03c17104001c0c0c80c01c2006104480c1003510010004803255014800c0b503000b40d400304400d4114 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 217715899 1250 217714649 217714667
    0xb01050d020d181b08010b0918101503060e01180b090c0910091a0a0b0d020904060f0305160311040b03011407020105070e181b0408010207050307020a0905060a0e07 72
    0x3e51000f440c41119030a203e1404c40380c0c8404c2500c01180e500000c0b03202c6006015a21201c1e0002d04140340c10b80321041d0038066403a607404000501e1203140350581c04075029002e0010b401620700030100c0418190309102d010b845a64070380d40c4190b8100344090440004c240015520780d03030401c44106888d02ca0007581c0d805c1500115107103234003903c210140329128480400d01c604941e09103004002380820095500324580406840950000d11200204034841c40b500041c14002e0543e00014604000b10002070100c90054005d01080c00c6002018002c11030204003044d43c9061281c3d40c041c82c2d81c40c640d140503000c6a100081070055884140c0001161801d402c043c1086a524010550702c6c41d150303000a0007080e007110310b44000349021a5410740e50600703411502807040c214102032190b5503084103d0302c09002d46401c1c501a2101000b002455100a10151403024403804c007841d40d031030042c0108541c15151b600010b003245e24280622180f035a0380704100303080310034012441c0d0311079032401c40075515015 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 217717149 1250 217715899 217715921
    0x2313050a06050f030d0c060b0a1805010602010c1103040501050f0f030405060601120b030703020405040f050f030c070f06080a0b0f0d050114130210050723010504020111010b01050d020d 81
    0x41400203000115615400c480c09071041a512030a804580c9000c245e40c52902540c610041221440b098011480b96003100c0c0d09444042d000c055074030380e03238881c2da07803074458034481c40c0507155850005005c89982030050208510712460034500003604020000d440e8403481c444d0394140680010340c0b40782015940180ca5101003503220160700c0e4078090402e2503d60034100d0700140081d00592052003101a14454410001e001030001d200d01402e542c24000104000f034030580300083e4030320708100010700c1048100d4010f00120040e5454a000150f003500e01b0360707203421100400003003136020b006450b8428004c40d40490343d0b00d000f0680d19003910100d200c0308015034006c0d0300074840003070b441d060010540101050b030311503620300092942c62880e00c00c5140c0c1e43e4103000354416035200350f91310038a210340040c1000a0049410788181d044040b62540d8012690720034420300d9440d0410001950380105403645124100402840040f50b0117000034081c0c41040f04a040d203680c00f24009110142c01d07402508074034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 217718399 1250 217717149 217717151
    0x50f01200a210903030f1116080f04051216154b021204030512070302100221070c051009050316051e07060e0603040302010b0a0e1b03012313 62
    0x1000f2810000c02a00c2c801844e02603c500b00030360b5004100d19081200c4810140c80f49601c86405660340741282e99002c4030b09c510181000307000c00b140e169107501d200e09903503042400a098400501c540b80000c0420f540c0025440a022a602000c50390442c2e0204004220303071515044c800b010801199042d942040d2210380114628602c0e15940c02250840b41840c00c02e408503800c0e0390a000007400280b2031801b000300030360400c1c40c42041903070f00200030306040e501c6401986c5030709143d40b0160003241c02030300004030609880015416071a6030881c026400c1225440c00034150000c035142e0b280e40d051f1546000d10810b42d111028001c1c40340c2401070701d03004c041e24030030036803400102c1c101540d03900b00c82914441d104000350941d98141d180010b440301101d106485841241c251001040b20070380005000fa002d65484030b56a4005548503041d41d000352995034800a080e0605040c24650a0803100740003282600800c0140081581d01101d44420308100d404203944c4018100030500000583c0340340200c0c5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 217719649 1250 217718399 217718411
    0x102030315030f0d081f0b07080f210402040c020a0506060108070e030618070f08060a0506010c022d010302120417040b0a020703060b040209130b0f030a050f01200a21 73
    0x40780d400218a03003d4005a210194890106c01078002c0d540f00b240f20b05506035034100601d1000a20b0314018040c0b600280a0540c03e11002050304013030b100d81400300428070801d403020003045180c02d2041c184120814401070400d0030440c0c1e1050380c1d4001c0074040a05100300c0400040d0510f105489010b4803036409801d030b40d0181846111880c140700620b0303840d4a035000300745010406c0c403c01c211000440320710750000c0503035440d15006080285000b80c607050400010003086009030311848511210011607102190481c4002044d0b44403403000d104005040500400545540a03403081c2c84540054006d014a400c0242c14892034a192089070700041080a010075001c002070f401060f9102124020300f4184245d106040401089100304900d2990003003c000d14001b142d031203640300c40c002b40d07000380c004003c8200c40c00009103421403000b0103c0d22580400c0e0106508002801101b000c000700b0760300054902040301564050b40034480c180c0c000c0003a010700d0000c02007040440304515031607400c010801 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 217720899 1250 217719649 217719673
    0xa0203040f0e04050a0308060105190503070f14091c02120d080c0a0503070e010315091d0601052404031707050d080903090409060902031b0a0e060102030315030f 71
    0x4036000307489442019000480000741440c2032494003882180d1000250a0140725a501a510581d010344032a04000c810b0140301071031905120031003844a9181c591548074a02103800600040d1034864410820044060f220a100d0008042d9101801c041b10000d44170000d04c84100716084c8034110295122079202c0e440503000b407002c0b4a154418281d81e6444041d580c0301c0e1484081d40c13003943c07070042c0000e030708000061450348a00c03d1000b113540305140114410348100c403100b410348100d0f007128401642e02d81c244040c424140101a240040d100094180c642c540000990740403074203031840142180110300c2503041d507803100841c0d001d10f522520700c120000080d40c440c103036a04030600481d031a1040400080c1518050408240b00305500802145410b9012040c040942243c0c102164030588954003e40169001e0004041141d0281e8080000c02c0c050410001e0199540d804a4901b036004800d0100a0341c0c08001c6030350100f40320740812410b14a040100345800c540d1012406039008841403428 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 217722149 1250 217720899 217720903
    0x2637021503070f020609030405010e01110609010204080106052e3506010201200a020a2f0607050a24020d0e010606021504140309100507061401180902040204050301020a02 75
    0x40200010f54440300d03400f0b0000026a0b880c1000e072841c40c5594020b000400c40740d84140b030300414401042c5003500d03100054841c150710f803010036658820240d4000c00c050084001c00d1280700020300d412a1034054030060301450340400d42103610101d25500f1101d04000c000303401504100d5080182e04100303140707002c0290400c00c0b1084001403035950720b28410003107041580f05000301c103203005126141d0441d141e221144544503910654035401940101420035001c100310009200140b0000303c111076000030201030741010781000605503441980140814408610000742c4000e0031613001101020304989020b2035100c62071132442c0050b14a0000031011201d503080e4000e84140042d03040203021180e1502c100ba40c07100e00cad8031034100880c1e10407000900400c00d1142e5001e1002004403e492901602c1800303c2c1042d42c0700e110b90401305800054000030400c1900c02c0c00ca010049003142c11003541481c4910300900145102012081d4603001c0c0d00c819543c50341d044900800004000b1561800380003c069 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 217723399 1250 217722149 217722151
    0xd02040f0305070905100b03070c0510020406030509060105030607081b04030c060c03030b0a1a1809010b04032d02010e180a27050a02060d152637021503 67
    0x1030a007030416000c02d24020380301c6106c5c0d0595020480c030b80d09550310880d0445604c00505005d071014801c0350a407207103100941c40180050101d9560108071450044001480c101040e44280e020303170720040402242d950f12241c07107600301c00740742040788007010502114032507400703250005401c030740440c0b0000030b0054004042005c81031090700e051192082281c1000240302c4d040c4503400740285904140071910400310300a00c034108800441d000c590070441d004c00c0420300240c004011000d4000342c00e006000d9200e460404e031904402d01c4200541150460011005890340003d040c00070040c1f90240d02c3c2e03240311100c00f4002c150340e0303000c2240c64081c0d20702014200a0410304180c25002e03480200e01a00300380c80c0260075810100070b2040c15035a80c04e0202c3d17580704c88030a2480c1035543c1514050907581003c80c4c4024003201e95000000b601d01c000010a0800036020001254441d1b0405402000860404104510340568495044180c08480c0b4149032603c04000e504ca0b07070414200c00d4012000b03000d5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 217724649 1250 217723399 217723409
    0x60303132d14030609120d180503162a0b09011707030b040b010314130203031e03060907030e06010b0f040e010b0c0f0613060b011202120406050c0703050f0d02040f030507 75
    0x4c03150794442941c55612100c0e44040d06a200c1410048943d040e410350300310310b1541e05440d82c1a0b50180d070a454240c25600038003030700c03100200c8514442040c00312402500348000c50025544c86d031242410710b4000c0031301d03a9101d100405840407810380f506a00550004510454110b00d8107414640044020010814000100e118615051403164103500c03030b21030034a80c00d1561900b03440940301c490b9030b550094503104081342d2503c0100b092042c0042c02082070b02c030188000d21060740b40c2c00e08904012090350003c01880c10103103041c01c1e400b00054000b60300390440303a400500c3c0b0764806003880038600b1841035400461b101170381407000180d0785000030000d0002c190f0310f0094071008a42200d1154a801003503a800101149140c1c130f00c80440c00c60f5100007040d45050500241c0482d048200700182d801446900c100e510400e0200070074440c0d54010f91354000d4206540700d1070140d06960280c05800f4407010760400c0c15022419000b0b04240d82d04031005404d48050a00c00c0c5035580c90072541d106514021 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 217725899 1250 217724649 217724653
    0x213020c0703050607051201090f020c0d02071d0c0904090203011b02100e06090604060c021501140312030903180a1d01080114010f0501030207020f121005060303132d1403 75
    0x41c1010f201c1c1c0305445044551f01050b05c4d03079902e0444000f02030103100f180071102070741c04c00c200c4025041c1005584800102a000b07000c9852400c00500c110b01c000b41c2801481d0b1600301d08000d0086094007c0700c14280048500142d09081800484e0041040410035808040d0822202c00f1882d00003540516088007690184601d21420040c03546130300040c1c84a07000380d03024002080001e04aa045058006594411503040d624107480f2111000700c00e901c1b07001c20920850701e4620340e040c2808185104e03620b40205a00c1d41c200420301c8e668a100d1740400507d281078404110106a84e8880102c1c020150a6030044216070903174041840700c0c800388107100c0035628000c012048609000c80c200d040f0741e01c0d150801e06241c50100154080c0d4050300d030480c0e100d43c041400d940c0c6039650000ca4800044901c00404600076450301d05000c4490181203284240d2050001b007645054140882054030400c00c0e000f82c40701d14904940c40c6811401c03100002d038100601c404940a6521141d080c1d0981c0200c0c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 217727149 1250 217725899 217725901
    0x3080301060c0b0a14040f050a0c0902190822050f0a06020c070e0622020c0601080127152307020d03050105181501090305030705030d110c07060c0213020c07030506 72
    0x1030003070032030751098055882c1500985c00680070982c1f84c1a40c07404a0b0084080c1c5291030840d41da1210b2900303603604140000e69000c0b44201044228000070032100d611400c0c2820203007443e0740340111b1039111103058003500e42d400303240004102003070000c842c0b4800c00e08129490100c103842c005010350444017120704e06120391407001400e81204c2d00414050030b0040d0a00d206590440001300d00c0c01e012041d1100c0140d0200a1001c5814082180c14001d0488400010300d07985c0d030304074010003d030101c01000b08250402c609c01c408144507040303030400018074910004002e0143e0aa104901c00030100710000c400000c1c003000712058000c20181c0d4500c034a0383e01000b55030780320030820004c02c00d0b540018038440d0380704e00002c07070300d1354110411192182c050410711042a40d90b56094915400810126103d81000c80c42402099290003003034102188940c0e5142030500059109995000c80d204400030440300c03107503520079500e50003c030460203040c00d81c00795a183c403180505990342c0510312003142c003841610 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 217728399 1250 217727149 217727161
    0x10501110a030f0309020f10020a0201180501080a02091504060302121803030a0b030f0a03020a050c0603090a030c150e03070b06061606150b031f06140304021903080301060c0b 77
    0x8600654080e516845410120030031640460061117100ca08030380044c500c3c4161701565071030a90440d41e005c0558000c000180b80c40c400101800181a0380c0c5150b0780f01c50500f440303280c0c0c200405a901c801c0701e04006850b00054800650340c80800b07a0740d00140c0030002004980154140c00404004000f0803042401c1e8484084e000c0602e00c4030458402150004d101181d9900a981c011840c0c11a00608545021000000203030034102e00c0d030000ca000d40d029000c00410072005008580e40c458045400d0303410341c030f8081c400540355000050001c040040e02102c032400c00038010003103c6500403948007081040c181001d20390ba03c1d4001c010a81345403c10740c0015031700d0326200003119440c900280c04044034000581c0c8080141c41000d028281440c0c0301c18022900c800c803500514442c658201d20320903860307440d811110794000e580c0c0100b820040c8030729a1001c049028403c580c0c00a5040e62542c80100b004100140031264a0b00002d048100010001991650105403013818600450310320200e52655 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 217729649 1250 217728399 217728403
    0x120a0e0316061505040c0512010e0103020a031205120a0b030c0301290a03050118031835070303030e0d110d080c1201060c12020f0709020a02010b0d050601050111 71
    0x400780c1903022000e2080c9040c00503605800c00c610380c0714600e42210074503440310009815100784100c441e000170000310704108828101200d071401403441104401303155042d0b4021a00100240c0406000703a92000d9041015a00c100304480c551170307880120030700d03d007000d1041c1b1029051070180c4610a00c500781c0a00700d03070f03c3c041c070510ba0948007a61281900f03564180c07600a8030403c42d4000340d0702c01000344000001c58000c0c05601105031480640307000140343c51601610308154840c2c100840000c03403005001d1512111442105004400304e1310034644488a10444800d00b05210b030082070207551400000c1541640140320800344440c2074411408044404403203201c5013410321556540300300d40004046010b604000c0c2c01440c440b080d2803611842505111458200307920a0000491804030301060080a12034550010810700c050b14507402540d210640d2581d50380030f014021035002810503035003030003584103c10b62000030300000300210040c1003164032208240318107404500f020003011884200 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 217730899 1250 217729649 217729657
    0x1080105160e030703050303041b060903320f01061820180d050d09170c0906011e120606050903060f100302150306031c020a03110111120a0e03 63
    0xd14100503002980e03a00c1c21a114418042401e8160081c4100400490b00a00083d8840d038001d4500d09846003003480c41d20000c09056102e0001c0081c0502c0500028806070580c02075400910f200314910550204080281404954840098070070b0031070212400c44190460703c2164400910070914500042d80350065800444003000540081c0c20260b001c0d0701000c0c0500101000501031500c00da070600049a82d010040c1000d44041c2e2143c4803d0030b040390b1002540000d0a01c007004007051140d0061410f554141c0c181d0070310300c80c8900500240c11a4801c0c21184c40e40c1800c500d1213425a6510140900380b0340d481010320708490b081a0f004240603000e0401c41c0c110400260003807916a4404103494162800030300030340c41e038030b0360108000056691019204820888a0090f42e40c90418008042c07904440400c1d98140710704208045400300e401060000d0441c0e018109501c0300000c0305801801000480405200e0640c04580321400c2540840520f110701e42d0014100041d00c41840410f6490203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 217732149 1250 217730899 217730911
    0x50906060d062406090f080a02090a050406090204020a09050306010b0a0917030906210708011a18031c020f07210503091e270f310b01080105 62
    0x20500c1064000b07a61035205096034994400002414007030303950b0541c512500c40d40303d44005180d0050034002d280d40d124200f002082c0c010000d1440310225170105051003001041500082d90340c0c070015042c861190003416200b98001d204560390740e410040030f071810310113002d281d0003031003510004211001e2070300407501c0d589450784802410710700c0c0c5510202c40782d01da0810b00780d482c0000c0c0002608d681b210006800030b0b08101601c030038100c50384d00300b654801d00c009020100300004031004019011a81421144c1021428001c50b582c026503c1103055160f542030820b81c1602c0b5024500a103012242c1e41e0341540605070707095500e048105089160794032058001d0120410010340031006078150a1400ea0090b403081d402c0d241445a08000a08042aa40000c2c1025611000a0300c1240b404a03070003400000c070700540c142c000302d036950460b00005000340002da10501c80030110b03034429004e00d03103010041e4100340090801d02d88000303908404034400794200d0349080c28400120b079805040c09011b100340 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 217733399 1250 217732149 217732159
    0x1050c0c0f0d05061006030b031c260109020d0e0a030207060f11030a080603060106021b10090b0c010e100b030a030c081309050103120e010503071404051e0405090606 73
    0x11a88040040d072008410045030300924000307445000581c240242480340039642550150f070740c90160040c0540c0d0247e25618481d4024210303c07801c0b1401c8170030200d4240e1840c682a02c0e0a005441176101c1e8140240003445990440c4000080f5110710342c004216001f00420144444a421010b844d0745445101006006d6042442c060128912030000c0d10b4801030341d440c05000c114600380440342550f110010210001d1110340c200725080c1420010303640180201d20040070340c0880c520fa80100980404641e62148041c109803c4065204a104a001d07040c049940307541d810721f030f00040780217000004451059004140b45001c6817103441c070843c02900000b4020746001c0b0a55a41180c2d070440740501100c03440d1061090251444040e251400a0210000000796550560501c4000e00705441146420460800300d20110340e6480710507030f5002985030800414100c0481c0b411740980c0150b8000c0c0d50401c0f9980343d000203c1010078403070022440152070402454071003920450f1502c0d0112506a00300c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 217734649 1250 217733399 217733413
    0xd06060821040b030907030b04050a031e02120d02070203011404060b0105041d060112020309070807150912060605040203072a020109140a0806010e0702120a0206010504090602070516090b01050c 85
    0x3503070103c40215402900394082d202e109440f41d03641c119a6409403010360300c42e40304180001c101500002c03139103801428440412900420604000e40d5000b82c0c00d0036106030f9074007060840540d41540c06580080358001d00a010700da01c0da192910b001c400444094070b4050414040a03010750140003110261058908810810005000384d81440e80e005019a4100300c88031b031411110510720b1000d03600801081015040880c9408251172910a49401010340b03c012015441c00c059008a01d00080f504006100c00c0c420a00e42800d070010001588980c1d0001c0c000000c1103209540840041540c0c1d02c44a103400380c08401c5c0e000340c8001550804024040303100382c442489003c001c840709184410000301070b0381c0403a80f103164060500b0380a84c0300341061404001030008454052100074910000840d801d030a04000000080d62501c0c184a081c1c0030b0781c1d0b211428024001644c0444007a41d82103411540ca4040c03070700f00841c0340181d620a05a1403490318500415541c0304000b1100744080d800000c140e0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 217735899 1250 217734649 217734659
    0x7080402031e0312042427170c0105010e011e1a130b07020103181709042702040c02071a0c0a0215030604140c071b050d0606082104 58
    0x61040c80b0741484480c2d100600c138865000e40d140c48075621075032142590143d26802c40700c01080001880420910b51400e010f01c8902c0c0c01c6c600001d840210001025030081001c1505040e40c41016030704900041000004001001c01415080b603412550090400c4040d40e03030f10070102404c503042d850210601d819a002c10011100288030000f44a0386010314980b42100041e1503078103c031981d60000703e94000c017260305419980c052041e040c105812a0400c40b0510303070f540d255603502401c0501170000c0c88020802d04821348641e4050040107588200840c1c0000ca403460460320714a88030000c034412814411403520092003c16000225000c0c0350740d1912903900d40160082c513410070587c1d2a107a03c1907010354409651100201d01804440340221035032400e003501808280c030103146180801501c44001e01005203008022102e8294101c12095410a0400c034100c01056459100590210b00c0b50f042800380842c40d070002c01200c1d0b004080759580c44541d240200404c50041407086078203c14041084 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 217737149 1250 217735899 217735933
    0x80912040b270604030b0103050601141003091e061506141608070506070f030e0604030c020d06090605151e060307050d140705070203010b040605150d0b03060f0405060708040203 78
    0x40b40d01001c1c0740044014a00c180440d019400c02c1c1c0c42030f030759460303140010803e002051091a01401200e004290780b03d44d9000451038030384018204104065840c95071009003c510444410f101403281401443c005035818100301600a80502c006e40e00150784001030564010014042c4292007900020700304041c5402c024038032440100242c0d5245020418000081c200740007851281005031641000c08003050401001c5902c0021a0300856110380280f10210b500030812510090341210100f54103459450100c01500d102400104070500309001d212602210041700e001a42c415240001c94a266240fa1401301481440582c0c002e201000410040da2051005008040003c00d01080b140e40074203d80981000c2260340c54001240800c1c03036000c51500703000341004103800702d500740705c424184400200441d00c1042c80c0e0554602c00540711904480d02c3e0444290350900900b031b514a40b401202455031910203c030126490f00032800004c03000ca00885a40e805190050000c002e0b5100884680c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 217738399 1250 217737149 217737187
    0xb030d0c020d1218060f120203130c090204140102061003110d12020c040c0807020709050901060e090f0601061103190e0d050d020105090a0b06040203040c0e07080912040b 75
    0x29820420b008030350008210400560380101c4400d95955135400581206601c4007a2240c20000c1002614201034544540c0006090f0804c11020030050360383d00d81002c50074505200400043c502d11040e40c0c000741c1c4c41130580c0a4012204145201c260310100d84c80126120003048480c03506a188140090000c12884200040100009041c0c200d81d02082d4640c50502d000e00c0543c200103038400850b9001505181c0100c0f4140322040c00c0800241c1409040a902d903482d502035030410a82d20030001d0841082500031034000d00c0010b0400300141071490005440301080c00a04650b481a640001003c9100d010154104143d4a02031400c0205148404106030800c01c40752040152f0204045116034504151801440c03140b4010260500100800303030940780001e003005500e400040160020a01d801d042c6a0b002c00d04840c016500c0d60f8625219248103810303008103189402c2041003003243e80d080101a03000d407189a080701e1010380d607110900454803c900070700c10404030511405101c4a00c980180c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 217739649 1250 217738399 217738403
    0xf0b0706050c0c03030f10050d030f030c0521011e0503030a0c020402090a0b0703201018060501030804031407030807021c02030313090f06060915020322060809010b030d0c 75
    0xaa46042c03e81201d0310301e182c101355018140c2c00b80c0c030402c3c0004021690b0101c002441e01ba107020b400c3c10700d141c03805000c000381c01c001d1809164035175105524841c45001156188420200c84440c072105010100039010000d00400d02c1c0e0230401c0c5650141e03c04901c0d84442250070050003145800840300c0100c2d004204200100d80094082c0039000300faa61f02c01d0044003034041030740b056443e40303c141030051815a046245141d03040a100550481401c0401d811100044a00001c106182c2115495041c000c80c0f00000c0c14030b629200012042052400080003208d0144c0c0c540010b1210300a03070261200d9039480001d011803c00c001d554014140100c11040702c2403a4140a0464100d41d0042030965005401d040d0415011100c14090030f412807003440c20b9000021010000381e0305060b00585114094015081d41c843d41d10f00c007075403203407080003204d90303000a44000b6185251fa40f10761854024090091b0310100d100d8000098044605226202e101040240141303e860100c080a940c5410b6800b42 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 217740899 1250 217739649 217739671
    0xf0a0f031202030a09021c03021207171305010f02060112030e030c1e011808030f0c07170a03080603030901120e1009080a09060c0b0a1a1e0306010f0b070605 69
    0x1c0c1140341018809540701d0b1181d108045290300092040008102940d04a081c5810141c011100465400603004c000d03d480c452505607100000e08014918204481c0c0f00f0203072910000d44002d01203280702c9480200d601c2a01e924070510709450301a0f0f260503003402a00080041d4410038030106c2d00c5000e060794941c0001d0280c0d55102c6c0c0d600301180040c02c900d01250410f070b040388085902540d104644c9500020406104240c80e820701908545a12032800824200c0c5408650b8880c0000c003445090010507040902d16091090302c4078498940604070400c0c1d02203420200042c0341801d01200b11021b03404140d46200b491007220000c40c1c014010710b0303010842131003600303081d01c0402154410b00601c1402050f00300c0d01c5410201d001001c0044641041c1e003080125280308000400f2036511a4000f0440d040101d980c0090444116810a81400f01d55005031541048251180354010b07920510740258180d48140e038850001d040142075601c00c40002c94001c00007000400e507036600241e001029510 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 217742149 1250 217740899 217740917
    0x4090e0c030307123b010e0307050a0506090a0e07021015050f1207090204030b0105030c0f090a020919060513150e0f06070c150f020d0c0f020102100f0e0105090f0a0f03 74
    0x844d045d40d544400d07103a5000360071903190b0440f6560b0041c41c0380b200080128001c040c0b5034140004154a01c1c090304c9030318002c1c60003181c182c46d103a6403680d02c0c10146c4a000102a2035140600e0004e6035492414580d0154514000c660002e9142c05807202c4180d401c040c1075001e20100403030a10031001644070000c041130003000c3c004280880d07103000505c0154000da03881007143d410b103410581031040708035826100c0c0001c000c038049039884001e07141c0e1740844201d400685482c420800b0440c1c11280c0750f0301c5600c0700e034840b40200d481500072000d0405140382031f105000391915925504100302d800c038070704008100040341d4110b6600c1e0280c1031088000d8040c1803d07042101c20b80e180202170059810014521900011140003998422600608075010748000c2c40036000004003d000d41a2050001d00724101c1d806004040d0790080100d89010210a82c0c10403038407a40040c90001006ea15405405035400d102c08070b807000d40c001401400c1c454404024140c80c00c002d644c2c500c05130001650807810f112440ca = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 217743399 1250 217742149 217742207
    0x9090601200708011a06030105030703031d130c030506030c1c0305090a090b09090304030c03080705030903060a15050904020a090216060204080d14161203020702040204090e0c03030712 81
    0x100c002e000800c1290000311710821044002d00d184441600e03d03d00030300d800e0004000a5030b001401104607501804c104984a14090f00109005200401c40b80c028036802540244006d1545c80342c0c1c58440c1c0c5030b50800a603101e0b50b0405840b1580c01c0c5d20709502402201030303a14541c0648007004c9072103100b42082450200e080700858070035a02c1340c1c41102e055940d01106162400d00076140ba50211b0040b01861030b003400c42d03550380501d21583c0009003062402140e000108003082044808400d4000c0842e0018500107030b4a0000e4050001c209612400941000416041c03072188507001d01d50040ca03018106090400c2200250408401007000302c140082c0600402c05500c02070001e001004050841c00c0391100740036142c081200040e00081c1b40030408141d0200003441c40d820f400741d006c14035401e4481c400b5000c50290183c54000381d8402d1000134002200959580700c401d0900401b400e4880078801d80c0209071f124040c04d0000303031400e180404400c1c117803407080c04c41c03000d005814034628174141000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 217744649 1250 217743399 217743403
    0xe060403021506012609210f090f0414010f060203040e0a0c02010902151809060f010804020415080604020f010305040c1e0306020307030f0e03040602030a0e0607050303040c09110909060120 83
    0x8040c000d2103249100702440600d09051049403041c021f44c4410100410742018003848078415028800c4402c01d000c502a01103965030580740d071b06070100038014014203150b40c1013184c03000c10a1040c0f040076003c4010000c0e8440c00801603c0031070f611040d402416548050420010b0601c2c03540c0daa04555a90690380010f0b130310589503001c00c07000c10200d581c0740c0a0903150380d03503030305e50411700c017482540440300f0401c59556122500146020a00c0d103900f0300c0d02c03144042005040c1843c1c0d45800c0e10144080480c01e0302d00050214480c0d8002c442911100750000d00540c1250829074010348580b044080074080700845011030b003c1800844020100030350340752202c0f400c0343c00c1520b149001a481c0c0381100040788150280000740d050000c042e41c178242c80c002002c5c0d660721500034040180402150304a45a544079400e6035419508042541d0303503443c0c1450007200800351030088142e01881d04c14255005c46030041a41c41202000e0b14410241e00e4072001512710001c480c2d000504000e41e040412260602 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 217745899 1250 217744649 217744697
    0x40213050d0510060e010e0a0c02070e010611010f06051503090c06070b0a05090d120e0f0304031a0a05010e04060504020f0a030c14090c040902070201050d1e0e06040302150601 77
    0xb400c06059280050307042041902c2c4154448043c1400c41c00051000c0d0002120b03054000d0440040012074204401003a0308102c1c0c10307441000003061160000401c190040008500084000020004103000d508264101ca0060103100d03082440303143c02d03071040c80b410001140c1008184081b21243c695a10001d40315600c0100121141242c0009100a681a5006e196045140c900203004107400c4050001c20007240d40e2100200c083e121425140f01e001d0a020049589000c0c1d800c0d00e0b036403501c03803c004800f10380005140c0701019040e07000602a0640744101c0d41a2000c01c480e000440d203460311201d019050180042e640280e221514501c0c540d64003010100071840b8005000f2164078108020604842c0406c20034000e06c641001c02c4140d4038503a04440560395000401078076141c00d800100c60790b000301c18185004928004441c5001082050180000810200c00388200160744244d952035070b00942c0c0042c09688186c140e203690131600402503030b20800603d003400c0d14107440b0b0016000100307 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 217747149 1250 217745899 217745903
    0x1923070306051816030209040b0604080304031b0f0303140909040b0114010e031510081b03061b0904090312020403060501140105030601140f0d021218061302040213050d 74
    0x341d644410880c50400880040078070021001c03407403031450008a04c010201d43c080c4000100f545c0015045941c0e41c5d264461740d10100d0250205848a4403020015070300d600c07a0009855141d280541203030001d18a92540068820048401103058515582615154060402041c0000e800e00281c0c2113602c80000340740c4581c0c000e032540419949401040031a0741000c038901c9040005500b0403030000c0e00d00043e00355006031039000004071541c80d040d4001c0f51300c0340e85c3c108800c140240b4000101c980043c13031034020907100c22010350f00b0300d8442101454480700886250b00c031074030081c060303100c0fa454642c4c014071510b402270815442c6139090304003040890f40550005c54440b40e440c801030201d02c007040342650280d8000e080007461401e2207000644041c0041e400c00780b050310001007002448901c1400e42d075140034103820035512070300c00e00840e0900c21021504810300d50070f90320082445c3c400c000780d102e0141c00c42c480000c2d0f14807566024400a5400208581014580c620000445469002a14281038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 217748399 1250 217747149 217747151
    0xc0a170d08090c0d11130b0f0603270a0c0506040609092c030a021b090c030c190903050c0d110d02030c03070b0a180308030a0c021c18060201020319230703 68
    0x248500b0030020a60000c0804210301d9281c140c1f400c0054960055500701e00004803501502c0380c2e00c104024080c0320385c0c6598440085075983c80d211a040740054545800d40c03040000c2b410703003030300c42d4113101482c050f03031062000046900d101040780381340c1c03640100001c1c0540071000046140e0070340c08460b003c20b00b81c0c003024240d000045208030710340e05008010342240c100342030694007004000010040c02c00540048071510340040460701c0c403003418040f103c909100380c0d00302c40e035103803000c1010341482014401920607002c0c0d071980c3c40552400321100903105a0003041080426080c10900c81c4210b03807014220703018400d103103c207840381c0d4082080340c009099a8000654419403040001e00400040283d40d008090b000e0043c000205104152035100f41645000500c90448030000c030301e004400307085200781c1291103e442040b141c0c4182e51a500403444c083e10120030350f07118004c0f4204d00c8221401100401d030f010103c017098229801c002d100c49840d001550540c0341c02100d22002c00c0c400c4c2d804501103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 217749649 1250 217748399 217748423
    0x10305040203211305030313030813030c03150c21050709030203100b01030e03040b0301030f0f080d0c030b100206010308090402040816030210080708040201081f03050c0a170d08090c0d 81
    0x690f0003032540744083c0505502a5062048c000380305d2030040514000103020702000b15a0945a110401c4c02100031900901a0360606031faa0800200680c00b01c070343d00d0480d90800705140c9480d03002d240b407002d04010030740c0c0360705401d48051050002485c01401c2001000002d980000241e42c04001c20340e0140e9801400213a9a001d420014084880e2519807264503081131104015075903040060701d0449800044400070190f462a10b07e18000c804040140f4000003c1441d004d40041d50b03120700303070074226034804018003800c441c2088001ca0860610038016400540141f00107490b103005001254000741001d805c0a884507001e0b428040810251541180070780300410035480d15034495482c101150070b2682c00340c100608010000309000300080d05200030345000c034003c9000c5011004060b04404031349007403140c807440e00765160790650b50030314401d652501000c01c0490110140807100303d00e5000038006c0c200b41502c103031202036000b0161202c50044221240700e1f5164080340e40280f520480307003e01a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 217750899 1250 217749649 217749667
    0x30c0609020103060512101805061b09060705010506040b0f03030711030f190b0a050f0a05060a08030409090b011403070e070513030305040312090b0f1b2407170601030504020321 78
    0xc40318050840d423a0b6030407805e1503001103030300812030f00d4001810300c3c0d000104010360f03060840e16204800030b250304413000007812024010103601030380c05040111414080d994100042040190b28070864540c59001040341c0e90000780405401400840058180d1f42030326801e00005040000309013500f100082c04510180400050072980c5a20054906c820030450030003154050705814028800000d0f40e54030340100d085980e8040949000b401001c040700d90b110344a01d006c3e400350100900845000c94000008201804186c881a0741600050010300100c2c4c0b51400011000c90050602030038080100a1106156803840d40079000d0740c0607440d540c0d078461861900010121011035003408010b0200c6c824081b40000008480b84441850b101c603403912900001610580b480c110842d20a200d14000482049080100190400440000d081142c0d80300e520079100e07440d5011000c0500f003440341c000b0304198083d0380040d4105001508494124246081d1404420781045030f9800e0b2190210310294 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 217752149 1250 217750899 217750901
    0x30c0a090504052503060b0f09090319030207020d0308062e0f050901020703020906060f0d1505030601030b0c13080307030c0c05030f0307171e0a0e090103030c060902010306051210 79
    0x103130907040d014503040105000a00301400c414540401003503e6103d8030703030a03855515005062003003207000341510342c1400c180000e650780c3d502c112a00403945200c8200300c17501700e0180c03081d01d60341034000d000e445a50700142c0d0200c0d440c05009054661000034440c03411003040301c0c0c1c1c90903002a20603200a0400c0d400034000902055403200664003003000400c076189040c0d030b020401100b01e0b981595800b456465010004100e802258040e0f0032842c800703d58440406200d070006c013000d01d409042c041c03130302d52910306040c0c03900c400740400340400d9050004101c43d040303080c0040110001c64801c48141d182c60b03095450071a40095016400140071325000710038000d0f111400001404202d0041c801b4032003455455499000da514060240340c0400b51007e082a100c0044400114218841e0324242c08054000040c1c0d40000030078100041c0c3c0140440294180341c10280c1c1a070381c0540341c00364082000d80c1e070034001d8584400c003281099102d22000a07140c0b10514081c06880960000e0310703111140008500c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 217753399 1250 217752149 217752163
    0x1506120b0601084213050411091b031f0603020711040c02070302210f070e071409061c0204090209120a020f010807110a0804060e030a0818030c0a09050405 68
    0x245130343c0c20300c00f9081c0300b0000e454014541ea0440c48504000c80b940301d543d0304004544000703d45d080103034100c642086010740d0307210302d100b5882890301c1503034800c540c400d111a2110441d4107000700250603549054001412000e15802465180000d280f00301d01d0b4103d0015444a5002e8004660042035603c20410001800300f1045804d4408000b0301040007c025034608483c0700190003a0342c20600722244a140c00440c04502d40c03081e00b11030b80b00d42c00d40710482e6070b1080b0344610044104004c1c0803450140c401c0c1034602c2d0f640128031000f0304269041d01000400c0c0e11010241c0c56080310001c240b04409030b00d001038402000446401610f0b8640381060041240c4910f005400941107075000d180141e40780c0119001b00c0740207191102940c1d90b044002d541c1c41c0f0081001c904540b142c203c202c004c1082880051095400540e100e0464000c1c160074590b41c0c4601000003010040107118a00d610300d003000d04001100b4005003101d40c0d0520805c08912103070380542054200325242c00420090210412081d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 217754649 1250 217753399 217753411
    0x3040b13080d091a091c0e06070204020301060c0311010204050a0302120102071a1b0405060a03020c15090c0111191203060512070306050c0324010504080316060606110304031506120b060108 83
    0x1b90801a9a148202010b0b0400f88043c40a12004042c400510344030f480c240c81c4190341c003501c11541c95031144c40c0a88602d802440403400186850141c403004034040c001d94044a1014000d0501c07142142d081002040c6081d10040071907609010b160003003005040c81a108a601030b404070700609041300b10b4000040c800c0b6840b821407030100020003154a0b0b441c00c482d980f8003a440c1c01030302c800e0081c0c0c1c1c143c00c0861010135140c4400200c414408543d1002c200f20041101c245c07501c81140381c2200c0f8454840408038244000740c600e5880f00070200e84040800c8080c106e032850006580c2c0d0b01c520000765002820010942e465200c5201842001440e11a0765000140b074900c0500b589040303c082003155285d501100101a418810141303141d010384151005807a0705404d9a44175680000d4503000c4500e140c2041c0c4255040000005101d0f0040d400c0d4102c2c006076101540c949070643c1c036a60020007580d490440c61383d50350700c0b00003003c0040d0030300130f06500c1c4108007503100c6051060004100038406000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 217755899 1250 217754649 217754653
    0x9030206130305161e050c1306031a04050c041416030203010b072901090b030c0a052803050303090607020c0301230405010b060c030705100203040b13080d091a09 71
    0x110086a000401c1e210f80c480c03840b44c5100418580e240c05246550304844800045490890350400c218002c1003c00e43d20f24103482c0d4078040076a00c05054280d441610000d45107020708001c0c1d1045c80d01c886000e6030700501400840d20440f00d0344e00814121091600c0c03105400300c654081c00140b5050845010309503855140c00e6065504104c440c060920508c0f000500c0b890000149130300420001845111842201160034910340c3d454400c10090201000554803034020419082064502140350f0340603900040d205840a05605501400c1e081c0b8003480e540301c005a2200000010308104000d500c1984140d001e8409800c050b0170103440c00348420403051083c1d0400c103106002aa00302c0320607011b00320340e4400003000e8450b4102580100080c0803007541240d0000380202c40c07100004001c0421501c0344045410858401c80e1882c228003060710001c015841884c0810500381c0c1c541c02c0300174141e02941c102450000c844d14410304503407405608641d4000e1100c42d8000301100b8801c25640a00c1c8240 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 217757149 1250 217755899 217755931
    0x160612050103170a02070e0a0608012315030c060301030f0203071a0304032d0509131e0504020a080105040605010e0606070221010204030f0602070605011a09010e01050705060a09030206 81
    0x50f802114035103c5000801d014400300c3c800b80030f940f00300b00320002403040b9141629a82015154140544018025510198200450072001c404444208124034160340041105e0b51a02c00090542031009410640d141c4607051280c400b03aa1118005d40c000d5200311024034041c0d0480c8181410b0401a501001d59100b094904d50450f480c83d00880381d2083d45403510200319028965201da8032611101d60052003c0d10004106200303400000410381c1381002c907220800e42101f0f14a8605807181d0086044c10400103072a12030104416401140d04248000c1c512001d4a4560b0b0724282155421601542c4103502d800040004a00c100c071800e400c03403c255040d42c50402c080c0c010885814102c80e820000c2e01d9416403c01c1d14100c290b056802442d0f000c40907002204050903da0003071b400c0039006840d114641000003c90b42c1c040010394030406c0240380a10f0400d2200c1006440b4000a00410707030502004100d25000188184540b5205070401000010038103040c1c1002031400c4401000d400381e41140340 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 217758399 1250 217757149 217757153
    0x302162001110f100f060e040c03062403150b0907091508010e060108041e0b040501050105010c021011070b0403080d05060102010c1d0a0305070303120c0c0b01030201120e160612050103 81
    0x1c613101c5240790311501c0110300b4032207024400004200b143c0c018982400d00009001c10000811408802c0381d00a08040c00704074050341c1c8211291312008a84041481802e00400000d60302c0506000c00c640d40780e20001c3e0448003080450000d00003180d0031000608201c01c240400100b4120403580040207190861a940c10b00102d900020006401030341445540300020382000180c40e80d004015560b0a82c00849101c0e51620741050030041c3d40841c3c255007407900110741c0d5480344c1e42d80c0c0125900205000d08100e0035060030341b50101130741c5905a4078051200d0200710042c032000104001d51203800311540d0340c40b001d00c0e041e086803006480c250469050039141003410b6404003520360500c000314100c0c5092181c0302c0c000382e00440300c0da00040107400b801c2e0000061503000354650044400c501e0b0140300707500304003004448005031114000c154404100050015501c104500c424541c0c070840e000803600d0646180601c0c00030b00b8035810340011500d40c0140143c80d44445e8203003800c80c4c000d0341808154115 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 217759649 1250 217758399 217758403
    0xf151e0e070f030b090a060204080c012d050307090803040626010f1512050a05090d0804120e010323070e0402070503180d0b01030c050a0605030907060302162001110f 73
    0x40c440580165030950200d05d03031310401d0005250340359100c14119640d07079071881810384906454000c1408540c3c40c20b8048850040110b100003000c2000c95403040031a2380300300c00e5800e40c00c00b8100b0b20030020340c0400414a03010801c024000741025407145180c0c000c1548a070540c100c21040018105d440c0c10380104250031002c00040142c0e501c04651421400d002e10b030446000365503115034003686042c0024028544100d43c4031501488000e400c0d101c0b2204980003d4640340030a0314001d00e41c0c00346d034400400c440e00c20403103401581d01c145000701d28101c00c104500300d00e20240c1d001c0e049640602d014010b1040d003005040c0300102094800354240f4600c0d0b11115182e00804560285046000e003101c6069903d0184880185600200b40b008550312070400d08403071501c42c09001d004030802d400104010f0b01640c02d0b00d11500b4640c000705501800c0c1042107003e0b4010302801010348210741161800200d541060544110298140e04520314000d400100201039420b120a00d81e0410b03000f1640178400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 217760899 1250 217759649 217759679
    0xc010c0201050c030f12040506010e09030702010806010905060c0706030c0c020a0b0c120706090204050c070818030f01090501020306090604151202060702040507030203040b070801120f151e0e07 85
    0x9082164884650604040c15482a0180c800341c0b2171000803411514481500300c1401180150100e41c3caaa80320301d00e0900d40741040c1e900b249203600901407040158801c050305544000113140641c5844d9580010501c0d42d04400640066900700d04014800c040d030510510b4403030782903480d00700c880605c4c1da0081490040784d4044c01d044044c000841180b400d8040225038081c0304c1c00f07102c0c07640d64185030526000800220100301c1c403650810000c94440004042900c81c202c0d005140e0a24000694103050480e010000c407054250007410580d8480c0300007071052005040c0900c0006d6660700d4044208009604d0017000c140c460707894808070310350b10b07213116184030107841000c68a070701c080079580002401401b558500075030042c100700401030000e602d50040e50045102d02c45046054407176080644014500b4080c4030117002c551081c4a020070f500c4100d05103064010300b040c051040355502c484060f641d4102881c80b1000101c80001180112031062101c003444c15000741c29068180a000803500ba6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 217762149 1250 217760899 217760903
    0x15040905090309060301080717030406050d050414010e01091e03081f090606090e07030b030606210a050706021618020307110109060f06140307030b04030c050610050406080c010c 78
    0x140c0c80e40080d00c200000c1003101c94450f40100310b25101d42c1e60741030050340c840580c040c035070030b00459154030044445c00200303407410b84030240c403154108451540d00800070400104103894641a01d4441342c0c1802081c401c00322149a0100040b48902e510f06100d11214288140c1c116569903501242010075070080621f50004503580805041c1a441d140700b0035598000d401000d00750746041d40014800e034216080304101d55118203022003954404c482a4225103102d050190103400501c00940c1c2c80c5030489040403080d003101c8101d1011034144220515102e003400003191942d0120320280312545e0104420300e20f60b0394a0500d44e4a0601f850b1303001458032809920300b039501e500131000c01c0925011705c061103170382c010100c002c10a861301414840c02030700503208031214580c903003400410625200301d60702c042d0400180c000c2c940e00380707140d68000011000030010303003c2120340513100e000a081031200d1801010300c440e40810803410300341000111505580304480507841041c00440c1642c2220040c0c2c8040c2d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 217763399 1250 217762149 217762151
    0xe0f0405040c0f0806040c0504091709130501142d1005040e0403020715090803040b030601051c1413031e1e0804050c030303040507031e020406080f010b150409 70
    0x1441d03910340441e000c00d1581000d290259614004036040ba070003e0704074400c034001c0f1044440c5039505c0b0240030441d424500301a001c4400c10104d44640c0c6425030083c001c20501514580c3c03110740d40c0f1151011202c0a030000e11401541d0070309d0303032aa1f10b040356510014011a80d25180e6949501002d0f44800c0c1041250070301480f08039112120f84c80c0a04165401040e0810504600e0714051a000307407190150b014401e112010540302c1c4c41100e215030a88416507101c0001185000d0904041c0c240c590001449207041000402041c298421080705001c94400042d40120b40094680c5848448400062080f0b1103c00c000d808000400da100c0050b404500795054201c80c01000600c0071541c018402c00d0222011200000803180d1b90340c00400540b0660084040d00c5102d02000201510391009540c0907101c3d81c8400310904c041104c0d1026122076000048001c0320414095012401b5078440c0d5011812035005542180c4588030280a11914148101c0d160b21145103204150380c018007581c010074240c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 217764649 1250 217763399 217763401
    0x90c050414060702100e181003140a050102040f03050607030b0f0603152d0604141002030702090403030515030a080301180905011503050f01020f07061a09250e0f0405 73
    0x80d00d60b41c0c126121641c001d082162540030800000c1e02d40d00d020581e06008024072030840c2c2841c0c040d603840c607000e64000c1d9043c400c19450358454101500c40c80b8071010186c0038150003040054000d100402c002d250120095000c1880e40c10101c2c104100148441c044c94100b000704182990303242c2d0681d03102c5204407480c503101c0c0c4402d0020f1a01803c03001c0460742245815048000c40400540000104403504d2400c19001c074180c010b0050500540c81056818500210618101d28001021076140916481181e08025a0303400003540268140c0b825400309039504144800620fa050321460b500400381c1c010404c1680654440d0150f11051080322034205012a05803034258080d00001c09050308907000b40020820000c01284040151008172958403c012030404682d4040c000d0701c1021101030001400c2c00320070344030080541142c0321000c000500c0381c1402c030b145a544840351801180314490300d01450100c01000014110070442071028001082031300c56690f42c4480c04285400400d640c08251 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 217765899 1250 217764649 217764689
    0xe0d0204052a090a0603090b060d0f050304270b090c0a0309080c070510020706022104080316030207080c0a12020d05030f07062702210d030603020a090c0504 69
    0x66540915031040005402e045030041c01070103000030300161070342141d05501d0700d0f03034442c001c3e81100c0d003030348008009a0302400090158a410001e008a5901418441c3e405010585d5000d0031940b0941160003600d4598813641010151042c3e080041c92040400304080c0380060006182c1600041c10b1802103107000600700d80d1030b8401c0d004840c40740c1d4026081c03522009110b2a05171924820301405026403048812003c00502c001041d0b811202c0c1c54000c0d0203003680f000700015007081692981001d19204000000d25904100002e2038500d83c1c6a046600024840c60024100b03507940d0300150042c2d000060052641da1840014000c4410100700055140018408102002c8840201610500000c40e680308076001c80760040034041e02c0f4a40402440141c07450b801c1009040044441500c00214106001810311400f10708803021414107909881d104035441c0c80c90144580c800c0c10009813541170801c110b0501085602c00b0342810801400f1000410710020454000c84c41240c60700c160320b481c071000c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 217767149 1250 217765899 217765921
    0x70c360c0e040f0203040204180215070203120325050414011101061a130e01030f06050a0b0a060e0910081c05040506071a130b15010306050904210e0d020405 69
    0x80d6400c40a0002d011000526030403c0003500b00300c409900070380c149100416803199104420000c2a07004002c20380000303a5264616207504298012605881a0764443c004201400c0145d44a105802448a8100f5456910480f4007000101c0344040c0300d418001030203030100120030701800c0301081c41c0c8440790302d41d8034002d81d0140640e507212100354220005ca07041c00c80c4094005000c40000c4002150b042656806191100c2038240310142031124034000041c001103aa400c1107401260341180403e01d90098000a40c4492142c6d21560200e88011510541c03403c1200d2043c5d400303040b006608015500e440401d42e00d0320320302c44408400748510340c0495507a60144081c2c1f03016100243c050340d1501c809203041c90750840280c48084085600748001044d0010504040920580c801c000a00e0f40e100c85010845802007440001e0505d42c6510000c215501c6410b8064400d600a020000307440c201030391501c035210050f566007410004058079031003103070b12001c1c0ca80c2c19255040c3c400050f1582c1c5c08810034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 217768399 1250 217767149 217767167
    0x100c0e060c0705030616050d18050f0105062e052b060315020306010f0e210a020405010501090f03150e1014090a0b0a020c12070c360c 59
    0xa5001034045000e0000c80000161101a200c059080322001d48614000e0030740803038071142610009000700903d00d08220181c1100c1c1490305044144801d8044556640f814030b00100b4010200313a55503800c0000704d2400b0010000c03055030050181401840d90046144403000b520322690070b1281c00500c2e80066410b590717940d000204641d1002206060a0f100b54010300450710094443e0f070001d0b48001454443ca10899004000584925502101c150026a20100e40703802c1564030800020541d81c0001c500c8814180c42400440603056050103481004226441a0040d90403c03454800074400303040882b001505690f00701c110410a54407449441018228200d5900c141e40106003820383c20618079001031b01e401c5065140c405080e0307207800c6003503903071032034401c6c0034100380d1410011034025a0680e0051508422003015200401e011684000c44c41d48001c804850b100100e65040003d481c410360224007a208070300b41d0403211900b48000c1001510329400c40300c40c0c2550703185003084030383c0540360700 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 217769649 1250 217768399 217768427
    0x7111506011715030c0603070813020f100324031a0a06120b1b1614070e040b010315020319020a09050a150306050d020105070b0a0915090201020f0f100c 67
    0x45461440c10f002001c2c84008100c80b9680284142d0840d5601884c1200960784a5502130f50381c010310b0354480e10700150b80d4a00362303402c0c1d0300314085480358641c5495a05021144100c284c4012510180f8114180301c0082c60ad668894040d607820000d100142c1c0c4000d5000000303011181002c240d0700c5812518000300001c0d80305418400c0748031040303402c00040c520028803420417180c0c40c1080c440c192952244a12402c05480301408143c0c103050001f407825564000c0c02c500c0b42080300c0710700d40c40d0b0f9201048400240c809441c03107441c800c01002049400314030b44ca115801c4840c00e41c00d604010f0340610003400d03001c04080c902038000c2610a103040c070030061031004090081030149410b54448000c00b124030162004030010b8140300c4045410305100d94104851035040c1e50b0280780c0242c3e40c94038003043c6d00150860000310b842d400c190b004103014203102800c5005070b00000940079014800645018503808955407582c06c43c000003410f8602c00309640000381240d050220f4403070025a422500c0c0761240103a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 217770899 1250 217769649 217769687
    0xe01081902070c05040f05010608060d0c031202070312022d03090406060f18050f04110d09080a09120c0b09010309020d080d27031b050109060b04050711150601 70
    0x15041032183d8072001e40102d0f50709030380811800c62a11104c500380c4509006400c00719030507001183d0107050080d62020300900921450740165140e9941d5a1580100081000140c1c0800000d1007400705c070028186034445a800180200038417038160405220180c6a5000031a040100901c103003002031040780e41d01c003002002004a152074a0014100301c0c0360086413400038424585002201da000d03110070341070b1078004208a88202280302040701401030188850707261081406030050301007e074090501e20313600c250000340c5c4401d071034107005080500030391000020300c01501c0114003140b2111000d00684e14000400f5581c0c102020060b001390050041c003d401071231441100e02405098405000000009002070281c0b100b04810210905256824091f10f8940e030b8000c0d00000780206000036242513501d17059a03843d030903920317078508461411009554242e12100ca12a66217014410140c0c840307940d0500c0c801c560b88540c990b660361034000d013042421056280201392503a001e258526030100003054 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 217772149 1250 217770899 217770907
    0x309060c021605190506030c04050d0821060112091b12060b01030b130e0a02090a0c030c1805040e071208040e0702061306052a04060806040603030e01081902 69
    0x40020b684505003036003650291000600071401d0b01d40301c951401c3c40d40f1001c0c0e241c1101070800342080b140c1d030300180c039040c0810810400002c15440356000804018040c201d1740c0c3e19649103d0642440d12183c0784e6458000380c40030108241e9a1f001020404071440031440000c1d51015413400d220004924600f0011070b018030000010f07000c500c221850900352003480103019441d052401502961707180245a40e0092404000b071240050680c44010103c155000b280d03031112654010814030901940c40e01e074031a8072002604c4025825001d104042c02e05807408051410303104040b04940981d5000783c034032079515442c1403202524104081c4011304480918100c00903690315080307030f0503030240c422038001d00441e8002400007400800c620340715001c41031100300c0c0340e0955038444005040007000c1040306448404844c440d0703480403508040e4440c200000380d564a05000014055000c0202403034851030030442c0070b20000303a02141e031801105083c00c140001f610f0340c080307900c1c0000d050302000d0300da00d00c08a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 217773399 1250 217772149 217772171
    0xa061113090501080604140705090403050c0c15031b09030601060207030309090605090118200901032f0307050403050f010b100c05060402060c010905010203090d0906020319080601030906 82
    0x90040495154100218411076a00c0420500380d8000744038180150308158002004201400d90b00b010788101300301a9080a078480000a480071819241580001c1001c0392603441040c08000429072803104540c0404080301c0c01003118110f110003010341d500c18040e80a84507011a1a5054a00c0b4010007410741e8402d684800c4000d603151414401600010403000d000201c01005105403415500d0103030114280ba030801034100d902c041031120700304515a4550041d40140c40c5800c08920f40f8100500303056580b03e01c48001010398010204519134500164102c009002210304614112601c940c0002d482e941c51100548850141e98406041ca00800101942c03000043d80b102c0707081c1104546000c80a1540304044858a541820062145e4040d00c082070151030808060490300c80031000200f414a02540c1c6c40342a40c200741c0c3d40211a034003503401c0591464211000030b020b440503100450421043d1401c00c02440c0714440500c0600c6a5140464400d0344a5000800b0381504444c003800051a40c1d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 217774649 1250 217773399 217773431
    0x13061d030a050f06011a04090b060f0a090305010b0109080a020f01090302120a0308100b090103090203010b06040b070521030103031107030605180c040b0a05061303050109050a06050a18140a06 84
    0x2c110f880c01da001c0c29001280301d01000a042080d5540d2a007074506007820448064000d100210b001544440180f055a000b100080000c15105c0c00c59555460010f18624210b0300391220f41e07007060b0510401c0310041c041c00d03800203030015405404032800b03c0740a030800c1c0143c480a84c1500040d4102c60301800ea01074218000a8001c08a03100c0d03641c40c9810b90741d260b001c041399192400f9040c540281008070b105298441e4204001d103500007070002407240c4450b0300141c003a0b402548604401301c40400c115042c0710003402a2645182000101d480885049215806a200c14003004040c00141004905007480402804016607401041082241848400042c5c0850404682540340c4504d44a650041c03c01c0e0083c4081d12101501042900d81844104a4030303402c45041c10803481c01c9800c3c0000441c00c01d0156404660150016010002881c18030070300382c4030020320b030074021814a1096828499840c8141448940249441007008120007005040c0300150a02a06860130030310051400400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 217775899 1250 217774649 217774663
    0x2060a08090709050c0901030e07080318030f030702061b0309030d030605240a1425030f050c0304030f03021515010f0206041707020105130303020102091513061d030a05 74
    0xc40c000c03144401e03030300c440a0080d44c0b000c86003250654070900c01080194040d8110440342c1071031405407400580c468038414a10b4100600e0b200300c83c118164240c003039080501009201c410114042d525105142d0003007034082c4100c0d401200382e001c400e10740c400350903404d20940c0c0a04400900f61210401c261500038042c06050180c18440c0341d120954040001d00701a43c8060000121081403e082c02120305841000c1c0d5404010300108080101940713298200c00024041e440a40f0000701030002428020100e00c102d030768490501104001c2c1801d40c40002003038030202e0780d11841d68142229949402c03810160050160f00f800c00410013030142024882e802404081c01c2a41e6540d8451042d5408903035601064070003400559110505015003044000100034080c0103042042c50000c02444010440d1810b0b40240c0050354081028013076171401e1940e001403802c0880c1a982040c0c0c1121184040b130601e445403206104940409003a8031b5084414150810401026203c210303609007070181d00e0f0a6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 217777149 1250 217775899 217775911
    0x60504150c080f13050304180e060919030e0409150e190f02121b1003140604050703060801060308190c050d14040e0115030b01020102091003110702060a08 68
    0x340e000200403546840c1d109046694400c2e50314080a80c66403200c050b40c112000e0f2040e0740402000c0c07450800704008100410051130000c0030212254812070854003200c0d8003041004a84d001482406007003640003484c0d4000d18038400c41815040c00b107107000c5d00c0e01203c030b40c00c41e07420a051000b1502440000c4c5070382c64032052501e03814011280d0000001da121440480c24000322101c01016002081c460407401040500c06055150301c00440070301c0c18039010034640041000d881003080702c00c0c1410000d07034440762240ca904091181d41680380304e20215580043c18a8021680c9000180482c0d02c260032003402000e21600030000c4a80780d04011a4541c411102081c07150070300c1e15800746262060380621146600040034001c10710034400c0880b100d80314103a003420300303101c148000b01c0e50020203560503000b050908080990660f00310409416079610000050559105000e21603464907000400c844550562500180c00c000106aa20345130007201000ba4001700042250b15404e81c2005410340504 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 217778399 1250 217777149 217777163
    0xa09150c020102161211060d020f18030706090303050c10020f0702030c1804083402091608061c0b010305060711011a120102221503052202030304080a060504 69
    0x1300c00d840140d03040030345a10441c080c00740b215a00030045180f00182140107040201382c1031909118079010b03c1170780c11a84514100f680c00291074804041c0610030940c0c00e52056001e040e1003490104050060350310f030710014061100004408580c00800e001052241042400840d00d4207464941c0007000d40200001301c2c06881048584941440d001054402d030900f0802296495074482d9101b030031b160852000c01010110001000b959201e820000300c480040c006c040c03207181281401000f0780000301406411150300b141202d040b6060b03001603040e6011405a1340300e100e00700304030a4102403641c1860080d103003804042c00402001030216140e80203110742d5544410f20070040340301d18201e91042c08150020140c03410f0642490901e001c042c0000f00b1250001418842070402a0200240601c1d0170042d20012240902c046c101c40c5030b410103024228a4200181d02d8034411000300200050b05c02c00c15000121414421554200300b150044c0002c441a0744040321507240480103001d00f940c04417401 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 217779649 1250 217778399 217778413
    0x906061112070303320a060501110d08090c03030c0706090f0806060d0602070605090c030105070f020a0b040c0f06030c020706141b071a0c06070c02030a080a09150c020102 75
    0x501000a81e107004003422940d440d1501000b55000d4008006456510500d1003c24007402082030080d03016804442d48000944440c0c5000b00700d00041307400c0342c2c0200f4148010b000d0b800601c2c1c0d40000300540c07d00e0f035a041050396078544116442c500702c0400b060680c036200c0091041c0c201600030030440210751064542c814105d032290004441d0308501e029001003a4440000200d2070f140c9428162111805040c006280c034540b034440409a5004a07a00e15072580942c400340002d007424480c59034480001d02e85030061600880c40251034a02c90312025140e1000d00000c6018420100003241c0180145501072025690314003001e0081e010341c40c4e00b038025000d140710000e0414000d5000380200c20104481c145042c48055400f00040c2d01c00c03006070920300c01d000b004103100e046815080d21419900340140c2d03c0c3d140001c0c0b140d01d042170041c0b00c0001c2081c82c5000c2c0c0c0c0180c030000b0706902c800da0720810080d141c5c0f00751041101e100d1a10340c018240103c00140441000d600070007080f20303190003a8283c2d120 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 217780899 1250 217779649 217779677
    0x801020c0a112202130506041403060105060c0d0522061809150509040510020c150105041a091e04111305010b0405060c07030b070e090112031403060415090606 70
    0xf030300c9840c03150755020000c0316107010f110a641e0b8010300006030301c00004410035485101140198216400c6044800600300d8091450b250800140380141001c0391500d190201030049613031991071440c0b11005100e000315004c65000c0c02422010300e05501c58403030200711943d481c8000e1000c2060080342101400821010540b01d0160080c2009966298504620307585080144980310700024002d80d000d0051401009100509000400f000070710300005182000c0e054803070402c070a00c1130744014403543c54550b14a06c030000910a614418508039401d050340d07903c04d541104011328107928420408880380030801049008101c80c000c4003000e071401c1400101c00c14a03002221020300a81d0805903050208110510709035006003449000703401a100881e80d0703651500a11101501c52001181d88a103019a140c01d10100b01d0b0f006142c0c0321141e01c02c02d28151805042500d920010103148a000000640c030343e02c0340e0b00700c141c00c0300c0e403004d1203075010f42d0b41c000290040807140110400075102001c0301c05 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 217782149 1250 217780899 217780909
    0x3030906020f15090c030709020309070803040e040206250f031704020d0b070c0c0e04050c0904030c0818030f0d0f031505060c16030309060912030804060c090801020c0a11 75
    0x2840c242a01c0140600418103035821240e101c01050800e07144170b1186260301e0307031320240810401000700b8240540c0300c0c01d050320160308016081d00705e083c00740c2c02030004002003043c10403029000303038041d81c00c01d070f64034280030484000c0c500017201c044005043d4406801086404200145558000c4d03581450444a05503031415006042e280a507010803406035010210350021070300ea8001d417042c20b2205800b9060780e16014920010791003000c00303140010400040c80007d00c035502180000f25101070803442d07d03540150221405000160590f0000300d402d404020a000001d600004010101c64190080321030595803024030800250000e000460084100c81c00b07400b50440d181c0030f50158107100d84c24101406041d8220070b400000d14418003881004600c0100400300203580aa034403c0812400c05501625481c12a0710080c9410000203861b03011907802102c40b50480c0d80300c5404642c54500000032a1480480d4001900b154030000b21500b990000264801e10706100700983c040c490b0080003008 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 217783399 1250 217782149 217782163
    0x70c0f1a070c02060304151d010b09011205190524271009020a0512030307090602120708071a0c0c0601092a020f030a0c0510110d020715050a060303090602 68
    0x2508840244042000511007102212882d02c4030440003504108c000410003150407210003025a0b650359249550302c50404004440c05003081c8a0422540004d81d03840c199038030706011003d6500c918001d1901d007041824800c1c2558404140d0006483e43d860509032030300b03036170181c501158505600c0da07000345000d62180c800400b524004081c00341540328044880142a204030201da01c5111100302007402ea407100a01410314144d800290380b28940001c018000700c80982018080d507114646e408480400502203400c0294010740c165110142807800700f0b0162030800c0790299500703641d8104401c9146410141001482c21005c40305140d84c1c404080c07084403410601041803030701608066102000102030140340d80d1180c8100d51040e114210f81c14116082a5180800912072224040c01d02008000c2b0309086181000100400426210018520720413503400a1055801181000030b00c0301c100007a8001c4081000240101c1ca094905080101a640011008507035800000314019200041103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 217784649 1250 217783399 217783403
    0x4090201050d18080d1e180816051002130f0305070b0c0a050607050310060216260106080d09081609090f05030c0d02190305040e070c0f1a070c 63
    0xc42c80c100e41ca0b42208041c1c0512407070012a035104a54100c0020313124402803040c4000302c40002100c2609862078100441c100c0640007129080481e14442c0401c41e00c0011503c0f0341c80701001c0d40d6844841180045c1e94461003014010703020301c050038865001d4603002405880d54080044c040f694880725100c028412601020740640e120b0072051000d000d94400402e07c000b1403104580001c200c0c0d070784840c070344113085581000040c004014001340f2600044207078040c00c5a40040c015813410710f6400c912000540c412000d202180c0000c105c240c0254052406070f200f9918000e2001544842e0350079507525090411000140140e000043c002c00d0200d41044c54119258404140038504282800174100b0b440c01510b1180300c03031141c0030000d0000c1006007000c0d10408045c24880c42540780103818200e14400c2d42000c540c82000e400006030780b0100300d4044d0745422111300c0c0341d615805011505280c42d40b1700107110581e0071a9140178801c0322088600341d098520b8441c00c082d9640441280c6204c0e0301440 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 217785899 1250 217784649 217784657
    0x4030e0117060603100317040e060a0501020a0609080409062402061003080a030b180a0e0303010501120203090115060c060615090b03070c170702040b030f03160512040603020a020c04090201 83
    0x1042c081e140c4030008640103415040790311262503c030344404080c81045110f85e00c06e050001000c05c402214000308581c010b07400c50708180708529006c0081d4031213074007000091181d655045a103081102e4002664043e0180800410499480300c0c1c1030008078030f021062103a00e90b403240c142d03441e0b184002031003032040e055000807400b204c2c51039071400c1e0150420301120701455120000c89850351901c40022105aa90a20b80c0c4144c0c2409040402240c40344002c1050542040005101c240d07003000d1102902070181c880140d50740e45140609005002c00a13602d40b05807000b1b2000501c281c0c1c00103071810301500401003005110307a82c504040001a005c0165030104010138410009589407070040e540c0144a0b0621240d05049590780742c40d64186200385a02e142000303d414815818a489201683d100940042000210042c503440c0e581c0510846c0500d0790006040100402a09218202c07640e02a0500070f900c4641700e9902a0183d042560300740014411041c91150f245094040d00c0c511a4060319 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 217787149 1250 217785899 217785901
    0xe032b1b0f0323071d09060f0406050d05060709150801060f020114070513060507111c050607020d0f0824010e060f070b180613230604030e0117 63
    0x405580010030a080c14042c55030700c4000e801c001c400b160191940961100700b460551804503005815040d800c0042e15401124465014054840007501600032604807800208050749100041c05489250481ca0301f10001c032060004000700056264010b072803e8450380344164440c2c00e10b034070083d60054071900161aa0004110a074042d86000b00441c545100100c1d00c00290b1000c0d41e6100801e45031500044d0000803001d0f4286030780c0034981c000d08514130b00a0b02e03118154484038405e0f08010007081c8154590300b91021280350a20100b031481c0d0b070044c151049490710364030207510740c50040c0500d0003003915200b800340704602c92115184a208000b42c41c00781c460010800001c80a0141c0340305043c030074815039031a490360720706014000b411012a0015511034240c07401c2e1040b10805880404026640c4010382400c0d00c01040c000d500c4000e60648110020960914440440d5101c0d03440300030031100030340c002c0341010104026100c0e078003d854030449841c60f18011034445182d160700031003204843d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 217788399 1250 217787149 217787201
    0x10327020f04090b0f0a1d0c100302040812031f050607030c020f060f031603180b0606040509010b0a090608070c0308090c040219111b0d060e032b 64
    0x32484100000c040c20019180d1902e640fa54030005090345e070703034040c2c1102e4403c200c02c41019000d1888040b101101184049041d416a50f41c0c6080502c1840d1282241229036000244643d05840c010030398441107548406010341c401c4007940c001e5410940c00c003d0001303000e0518201d2180c0004441c005800149071074402c0e02c0c11244100c42aa00700da0110f0300701d82c1c5250701e642d0500682140d080b076a400f01c3d56420b11030f14035400c4040a00c800c805040c00d1003181620b1301841c400c00c10449400c61078600055581d0f8000400904c01c60704030561010b5100c00202e00151303000040c0580680c545c0315078601c1c40d00c5010035680c070740044910b60000764075105001e0000e4468450302d80c010342c440c000c03074200280410000c0c0aa0300404040324a01d40c81441061641c1e60280c4105800c40640c4080c0400c00540203221000545000905002d0320855a268041020b11b521000036120103030141c94951702e8140780000d84040b8230750084c4c2e54a00301c2c0c0703003440706c00c0d5180700702210110110a60748540d0a41 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 217789649 1250 217788399 217788409
    0xf0706050402041b0e01090806060127180b09151309020604180b03061023060c1f0f1401050d02061c050f07050304050615130608030901032702 63
    0x248200d030016128130040484036111390070702520308001d8072074044880d24140010250085a4091542c07503201805110403640c0100c1c1080155440001e040c450144884400240c8902075001c10100340c0d18941424440f0304035803241c85421011501002c0da922210600c20404058944007070744a003c54240c0341d003010b640d504c5068800e202a04071800c2c555120300c4005605061841c006507a625510340c02c940e8a428407003107501400000c024641c030b50400005203000d50061791706440e85503182c0c140c00d040d5500c207000e40350305880798002c9501501c0b070200c0ca481504181314007100c10600704144145800030700c1c090140f260403228650162607181204001c0040c946c0d4000340c2e0040e20401604003480c50140304507050404403040810315003032000001d24008402441c2c007041000500500c0000359020036400c0c0c10500740e10300b11040d500b5007070001e0105400003e002e2003c900e48040050004404800f4010024098800b00088c140301d107110f076070701d084010541c0484101d045082e070051502d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 217790899 1250 217789649 217789651
    0x1e060e030622020405010e0103290c070336050409110906010c0c27090203061305100c09080607020705010c1e0602070305030a0e03040f170109050618120f070605 71
    0x2042e24442c00c41c034007500824101e9000703801102900910a00500920a40c9a004c2406481800702e6020341d21604904501c1400068012420352000054100034107110303940030309a491004990314410701380510080741d0380b03400a0b60302e240111001310029040c6020700c6138144285e000710105003c1e84041f810001e2180c9c1c010b02c0030341803040d01800310020402540860740941400c0c0c00302106c0146c056410b4148804403003596075202d0505014100589010441d031f80c100105080d03c00f940c550518015003404073f402040060366142942c480c58090340b2104510132505100c040e204541c5401c1803c82e00d40c009801014085081440703004000b41183c07400c0d6526401103040002400390a40e9042c050360b00c00d0009800050000c414403c203020300f44500030000c03400c02e00540c9080c0c07501d075101201016610401d002c4103818100159070f2403081d0400000705502206a034070b40d113004590b000071a0301071207801400d4410344080c054000d07545070480d103025107440c280d5828039605680328030107050 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 217792149 1250 217790899 217790941
    0xc0405090d1205040c0e0103030507111c240c170105060405010f1416030e030c0901030c05010e150c070312031104150314040c18020301050a030803040f0b011e060e0306 74
    0x207605d840015080c4c0982040c80e018510079521160344241d54180030440d1b20380382051034804d804450305904c541d40a07201f0810080d85c4907a80c16018030007000b002c00500c8408004d1134000b41402c0e81e40ca0000d60000c24800403004c200c6e1034452b035981fa2002e0025030b001c0c41c010107000c19075540c0a03c3c14035010301440320010240ca604585410054112200c0d00250960204c0c0468403101c1051141e00d410b03c44a40400300a85060750258034645410403240d50f00d208640c10311400903c00740407038407a144811100d884152055544642c0c0d04052039071034205100540310b4011020440424a12074083d0400490070301801c141414105600034076401000480c1e00c060569491349031023614132500d6868480ca0160010654440c940482c110113000380b450304e00c06071441000140300075070f40d480746641601d4000c0c01481d125a104d14202881e8081c11030050048a60303500000381c035045c4c0c00303141e00d814001004036900d403d58903401030761030810801c1800e5040e0400c10005540c081c1c2d504d0300f0500d0070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 217793399 1250 217792149 217792163
    0xf08010605090f101e0f05120a0605060102012a020c0613060e131508011508030d0906060f03080301090b060705060f06150a12060f030c23060c0c0405090d120504 71
    0x95445c6007082c034011401d10740c03900700300020004200a10078481910024907041d1101031004a60101e413036220200c8190003401c050307441010826a920035445200c20217900080c0c5446c03940c12030034060b80d03148030034240f00051040400750080e60510b402660a1002c8405100c3c140e242088010350b001070450001c03503003118004803100340641c220300894519210101a10a0080c1840c6056007924020b6494618500407000c0801c0080cac0000102c0355540c95001d000200c030003d0b0310340b40d0085d100c1c41d0701248009060b44804414002c0103c01103040718040c4c6400c0208130602010700c115401a034502070030640206002403195102c0340070031544000010216503801c4107601204215400c0711525200040304040c0aa400f05041e2103040050103a6511814050b8a103544d41000655a40101202d6107941070303640c0b9210403044c5901c2d05011000305000d8682011030b4004d40d590b003040c12018406c604040206041c20000310701998a04281d544440100c4d0400c0700c407001034a00500304035100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 217794649 1250 217793399 217793431
    0x7020106030b0118140c0910112505030109050d020d030b06030a1a09010f0602070e1513021e07020f10050a0f0c0b090303160e06040909061808040f08010605090f 71
    0x12400040b40c2d0b2140d100f1b45c0500ea244c1200c075040c000805400007918003441844110180401303070009450116005a00080c9890340b803031322140e15001c080d076210f15055801d007116001004004900c0043c0c1000715401c5800c07041d6001c10840030741e00c508241a8110a0400104d000802103400151980c0f0117443c60800301d4100318040380c50101300b684400900d2560200a0080690511005000300540c20110242e030415921042d02c9410b4045d4152058103420103031004000d0743d07016181d01c2d00f00148000f11064007003254040d01d6000e60400c03480b4000814604100c1c2c84c010000c0e1a22101c16134400d400c1031201c460949902640b1041e840600c03060140f9000051a281c0c4800d02c243d0582d80510b403039040003654210304c64007400151301030010351036110b0340a844440940742112101c0602007524540c2d0f040050007002141d04c1c4c0b00c02c5a034822000014445044020000c1351800200c01c0320007a03560384e1700c030f088074000c0c0995a81f0031105004034003040004170210307802241d0034a5070014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 217795899 1250 217794649 217794671
    0x40302060a061503020f1606020a1419030504150609140a1e0b06090901080106035d03050402030d0c020306010905060307170a0b0601080c030601140405130e0607020106030b0118 78
    0x20200507c44100c5181c0e400023500c0891907445044003480111515040b810a140d909810f0108a0b1040c04441055500d0000030207000d00d403003459085818100701000041e0f1540c644002400c404a0030416090240d80852181c40b060f00c521010360a64043c0c1490300010481d40341c0c003604103071400c2d0781d06c08024040c00c58103541c0c000310940201440c000010760640385107030005c40c001143e00c003025410100b04001d01d0312408881d00d04440d100e094aa04012045500c0d2902c48558234505408510041c000d66a41c1036003503807220380114000ca0031620a00c6400741c080b0350410303032004000d4240d00304000410030f001694000030b400210040585091689404a550003081e51514490284e0300a883c40010300403d8800e0355080076081c83c0c081c08a241c01d48103482c491001400250412802081d07142e00c0c41a1001541d01a2030b0007000f50490300c404d03080c0013000c0d2900041ca25401c0c05620003244040d4014400c0030202d0b43d1220b10f04609030b01e42214103012500c4441151a001e0b2124940302e5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 217797149 1250 217795899 217795927
    0xf0f150402270103110406260901090510020f04060c05011b021b0303130e04060608011505030105160e0d0305040e01121e050c0d02030f0a0b040302060a061503020f 72
    0x1010204500e003800a050444015101c4020078607810f040c1840e1005100342079440070100ca05442040c100070b131105001c10b40d81d20800c00341e4072030403d0141004042c000c22003019040605600d0003503048601d4014100c10034400ca00c00d0b1004200324681c00c0000f0803c1a020340442d000d82401003000043e4000102c45020195140d5480100142c1216017034180041e18802810042d40d0294011401c1096084c0d0541501d20980501004004d2440020b03042148a402c10400380c420748000340481c03007544074948429002409024841c0d401c081c0007070b0400841c8400c0759090803d0f550b80992003071402c006e1100c0108080c00540401004000204101c0c150108842c02000e505c200c2501400c05818152419485110f2400000d030341700300120003260000840c10754110044510011441075880020324198142008014130701038842d1007800c0c000400c0d13040d44118000c0e020340b5441e65940190004171001c90190909440d140050000b201d0300c281c1c0500b4143c000350441926224503030410603 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 217798399 1250 217797149 217797157
    0x203010311120a02030601031119080f010b0d0f0b0709091406040e010203060109060810080123220b0a0f09050705040605030703150209010c1a07020d080f0f150402 72
    0x36641201c41152110703641040704400d0000c0d01d00d40c02034600742c400c40d400203440c1e03641840003504050703088456002c0345d61009504070085014001c000e0f94507680d1001d07030303840303002820340107e06519181e802441424650001c0350160303440300506010512a580300d12000002420020810441b81707804224080c20b485110403010300c3e00130f610701c6480c090080000743d403601c2c940e00d00c0d1a401070040c89540d03600043c4040543c0e0580c24020169941c08009001101d400c1d4802070107507003080d14004200603040c0403442c44802000ca001480e85d04c1308000b000d00b4070725070b003808a0900074800c440013140e500c01c01d85030401c25064010455001b816003840984012801c00c0c1d0f09030b08910810021440c0c24800d0b80001d10f03007503025000c058610303111000d4903180324003442109500051020103036845000515016540301144924281034424003010407007040700c0e04400342c0b14148001001c917004255581c86564035030795401c1d465660010409608001521000201207541103e44003980c1d140058 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 217799649 1250 217798399 217798403
    0x270a1509060806010b0f18010e03030f030406111c0207031e120509060c09010e190b070b06010903120e360a0908070b040503040e100302130e0319050d02030103 70
    0x21592a0504500070f04005040e0301885807108108030f04400c1a40c1030b000c0d80c01000c04500c50b517194000210040e5424044042200d0f0300d408001014210b0481d900042c502503400384404016a510031500d04005d417280340301c1041802c05004071911a0132458005000c414407d203404407404190a240110600c0500840804603415000e07240296540d441031a0780700c83c818000305940d0601a440e5011445900c007881d041103e01e110071002a210160307400140313100905a1300c18580d03520242c40494000c00005c42d14a284400401c02541c891042141070b00d42002c00e0030380071705d0403103010385240e070003002100d400151084442c2a4000920340e4012001205020b00300340c0003803034140c0c180b41030004014404880c1b40c01c07038070808079025405807440c0903400794265000340c8035030410718518095a0302100c1c5c0700140204015500b014200403400b242d00c06d984480041d508082c0100035655501003815141d88184400d603c1d600307981002e51f0925881e400c01610b81060440c2d00808e0380e000340c2007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 217800899 1250 217799649 217799651
    0x10203070c0302060a0c1d060f0c070f1202030c012604121101201b100603060e0d0e1306050301050406090507080a030906180b07030914270a1509 64
    0x11a81c20325406001c0c00b40e001a5641040201d1401044090074000003601d1880c0d000e80f24561003c0240c84880c11105014140a03100c0d44400d0b00ca80c0541c1d503500c1d2030142d40a2000c00b4a00082c10f03134069035440300d01175801000340c0207421410004454641c010041d502c010b1102440044150310840a0540190700405180302030b44820b52000e05403c8602c40d00131042d078506013074200c6000100340100760f007499251615541e241500c50030622542040080e041c1406131050364414500c180c0d01000c100d80c484c40003400451655a2440d40798a2806000070200d003071a50320700c1c00741c43c2044154400008a04000500d00e441d840400d084620071a400c40b5810796841406c018098100445401070010000500a51140c0d59000303000c001680300d0b00061269901c4001e58281c1189c003000003070003048104a8460b509400e0040000840c0c0c0b05042c01d01c1e9007070354141c05a04014201400440c02d40401c85d261a04810184203261001401403003140e654500300c1400c031100c48070590040c8400c0714 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 217802149 1250 217800899 217800917
    0x80c01050114061e07060e0d080106020111030108030702010c050f1213050d1a07201c090503070e0c07080c0f010f050613090c050301050c1206060f071b030501020307 73
    0x110540180b0070810b8440e20805060040d80202100c0d510218480343c1001c08250b110101403901c80094040c0f00c0d8901e229010b031102c024041d55020f24074904a6a01d80d0090200318258a000c2d0310300d1000303000d4002b40750010000d5102550246d5a501160351141c0308a40030010b814100508040619405c45024280012110003081e041d002c510094002120382034502c090998130851800350b82c55003c00c0c17007a02c10b40010501c500414041c220035038410000103101c0740d40c80a840d15074141581a00c44c0e542120b100c0341c086c83c8180b11100940310042c000b082c1540c2000350134a1104001454a4420300c0100001c0300000c00820150110500c3c1c6801080d0f442002100c46094038200718100d45560b290408104450340c0d1038680c0480e01b40e2502000070080e007103080c081e52500168001c141c042d0300303000034003201c680c49a009002600340300c2580040d50b2510002c100310303449813035482034805000f802a100864072010540c45541c40e007155920710980e6035030328182039030400c455007008a001c9130 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 217803399 1250 217802149 217802159
    0x1e0108070303030b090106020d0813020a060806120c0a0b0c030405120304060207080a110411280239060415020a170c0a030509030f030409090311070803120a09080c010501 75
    0x70180884c4031008aa00340c0c030b03030341c14458025a200c0005040d00c04018004021884002c12041134040a94000d410b1440840d19140050141031052360024010811400141c00b0403d001c1050408130000404410300107291107800c02e1079801c131480d0482580410000042c40395104034007981c1e59000c036070141d40c0340c51406074003a05100c010340c41111280c1044100c0800200c2089000c151004201c1300020325662100243c42e00e4018081300c0c4105402107414100700904e8041010503201070355085485064400d1810302018420b200c3c1520b448244606541c200107440c403c0c4810b000000d40f80900309a52441d09813000743c506070030782c405608441944014042d54000c40045810210189850181e43c2c651007a0b5504e4014809001c011000c41c004240380e03810700c0502d1b40c0c650341c6011a500c55490b04a50001440340c0d4508a0204001c0c3d200c0c440220300110744101150741c490081d5040c1401141c0054500000602d400419960390903e800011720700380141003402040c8000161643c100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 217804649 1250 217803399 217803401
    0x9070f0602061b0d0209041503050d090b090918060f0703050a020705100504021918050633040513050f01060e0609061303020301050c0a180f0e1e010807030303 70
    0x50340026045401a400f040715910b9210000d10240743d80a0a640d81d44080e1a0044000e00500c00025402070900494000403410307403c1d01c0042c2d90048096030580c003030050041d607020f422842030f0245044140244045460030041c000d03071001e0355210110b010581c5001c40e508200701150080c81813500c0d60140840c895141c403507140d005415001c11898420705864a039650010125844400340e00d0300001000c5440300d40000503a202d0400e40081307040e480d0940445005401005c00002074549800500a4034085404140c40124200a0144180790441001844a40018000030310301c0070880010980c8401c84400c4182008a00026181c102103051104264042e81708004008140111b5800c0342d4400049881d901012112650380e440075240c542400c400a6001035410b520306000c05c5440f500842c0100a5880c4503603510440016061f000d00c000f020f00e0049901450041c00c05000242417402c6442d08001c41103280800f100c0c80b10f01c0410480026003040b00542c1140030108101070305 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 217805755 1106 217804649 217804679
    0x204020304060e161d040b13081e040e13211b06020a0906030e06040609060b0d060b18042a03080f09090604021905090102150907 57
    0x104c1603c206034205903c2001c0c9829141c92401c10b1070b00e041c0b009244030755030103903808141e5110342d402e26001c80403403581203c40310b2013002810480202c40c2349160f105042109100e5036581480002e508018000d001091080f5521810308005250403038581d4028413452015405003034210400c80d001000175072800040b840808545042c4503154006008a045984a1030200c40d03541d502141190449550345c00c0139006200882c5c0010000c2e0009200603004803004a0144c82c0140001d00c1c1d0300c0c580300100e030a640d6800c140d02e254184003042c00e690149a921058852405032201202d0021417410407548061803500d003540c00c44000c04c0b6a0285030040303100da88030b008104042c1d01540c022550b5900c10f02c0a0390010b01c40c0c1c40d003802226059204007080540034607180070140e569421113101789040d4010391985984403580040e406110300348400003049003905c4c100784030501c0f1403 = true := by decide +kernel

theorem cover : BRFrame.Cov 217625899 217805755 := by
  have h0 := BRFrame.cov_init 217625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 217625899 ≤ n) (h2 : n < 217805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
