-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2970
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:16:37.229219+00:00
-- url     : https://prove2.me/submissions/af9ca6ce-c7c9-480f-b6c4-5222681af44d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 533992805 ≤ n < 534172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 533994055 1250 533992805 533992807
    0x30a0f0b070f0f05281211070f0201050d0f06030b0108060906010806010b0a0201090503030f100b030105090c1612081b0909010b1606020307051216020a0803180f011d03 74
    0x24001680c05007180c0340c0340c215418440d07200c09030001e03100c0f03145509030f0a905442106000c0170b401150002d0305450421201d0b18240417003145100c4180d0300380603c0e80001c1c0707580600000c1100540c0070f00c018044161680700000341d0704c80ca03d46640c00f44d8145910640c2e0401c003040042c400410207010b415408450400240495490051020b0307079001e0500c104802410f0104e40034010314401c1d00410030003500501240d480b4180810340a80c0c1c007405441c03c5010194500c0700181a40039002135078101c40b002010b84000b90341d461035200241d4440160404c4004203600c1d20400901165008544513690369114009441c0c940ca07491080c050100071080314810a220040c0e00340d450003445410b54000081017521400e00301d0007200d0780d0742d036000000d22141c00441000403140d84040606070501c00000c82150603210142c2190f00c041244a00c02e0050700074080c08804546000020364000c01c0c2c00151a50980707030b203009d450030517206050751004c59440d4044203280360800d100a007c03511281c0055 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 533995305 1250 533994055 533994077
    0x9020711030c090703050c042c06030a0506010e04150c030603110102012703050f0d050403030b0a050f01080c0d021204021305071b0302120406030c11030a17060a05030a0f0b07 77
    0x20340d04450044c034040c00c064070b42001580303d80500c01a0780041c80802d414048a58504129445001c03c4070760b84072001e043d410002e08540350028005140035040406404c269081405000c51410001c0041d50078540c1c8118024061801e441942941c0906a80000d800b5046142081c10030340312000460444e07051203c541003009402e00348a45111030414082d80c0130229140540f1640500901c05500080100f81800300480135045288540d01c40d0740c0030451002074004000e051a40c2e801640c2c1c1054200d071500b0322550007503c1c21500403072103401d270504045000754241c0c142da106002d1070840c044003406020841c104418a0341445900070010310441c5003140e40100022403000c26400301c445641da0010030b250007403141c5c1d03020600d00d0726840d83c2d6907100d2101401030a8110503907030016030940e081e9161030002000340c9000d08820781c1c4040000c040ca2620030581080a8001c540c491b0b1002000905035600700030004040d441004195152490303801c000141d403100030920000e00010550f5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 533996555 1250 533995305 533995309
    0x2120a061809021809070602210417070503010507180b0f0901081911041511030d020c250e0901020721170c1c020910140d050109020711030c 62
    0xd80e2010030240002e05501c0d2400050050b00740e1848289861003201d0900655070b1000c200340781665540d400b1545100c00762081083c40c41c01100c0070310070100e002c0c40103009680c60f840540c038075103084c402100d501e1921803001a0840341c050307807510b021a1440341c20031700a1041c5140c04000700800d01b01c07a800c20440000180c051f1103a11076982c100701c40c40300001c8500b0405091440c111100840c20484400c1c1221800619403290103800c00d0841008400014144110030044108820350095400c0c21034400d151000b0750030441d01d6020034000c2a0600388000d0400e00540340c402044825014101c0c030781051107807050301c094040b11185e40100442408141c842d40a503031440d49035082d03850305801c141c1c001c807802940360400014202c140028040180703c3c603030203000102d407240900ca075500d182c004407000b24802d0440258100ca205812101c84a0041c1020174402d104082800d103030001a1041c40c0072624240c01c60700d5001d90124006042c403814a01e150050b070020b6004000f01404880 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 533997805 1250 533996555 533996579
    0xd05060406090201050c0a0507090e03071115040314070501091d010302220207030f021e071205012403111c020409020a09020d061706010f0311030a020d0602120a06 72
    0x10019050710745403154042103901c07460845680c3c1c4c114400780c4108110b140f070883e803156001d1069244260804c0240c605004001c011160034a6214000c03a2042060b081404158091441411190303102880008042098490440403082c800405015150f00340030015100c4440c41e0018181105000110001c0655404040f41540d804070f51800008140d00c1010042c0d00310b00280e500e00d42c1c00840c50300105034002500b805140e08640a5a400003241c00704070603450300d000044005544a04410459401ca420f1031403912801100042030700d40420a03d48480503058848034800c020005003003042c0f221104a00010480413a0f1410105030020045000c02c005054041e110381d035074521901c11555100708550040c00484e5041d525101c4000a540080480b803041c0b44003480d01c0441c1050900340030440d98181c0e200c4400c2e03415054150b03111030000640c60300c18a0f806114110b80e540140e03640d101c80340d044c2407041a015030744491068035404217040c00341c001c1400b1400c0010030300004400c02 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 533999055 1250 533997805 533997811
    0x1022107141e0708070f0204141608040503040e090d1d0618040f05181c050a080403093507080d050a050d15030209013219090e010b0d0506 61
    0xc0502e0a4420441160406501ca000c40c020080c420004580040107109040b41d40e1007070080700c08016106c800f04842035503850803904803401d0105070354007102e4203009408050b0424010380c112400c00b0384803400c400a0017001d0395850103941c4103503038a0722241d40c0640c0c1841c0074aa0a080b0340c004c2c2d0301440c040b030f445000d41a58401184c0594241001d07645035a8803580d00d0000026007400103040c0308108101e00504004480f04502606607050000310030005e089400400c3c0782c3c0d0302d030b142a421590459130620064000c400300700b0020000900d88a60b00700d010100c4020310340035410107850410302d850081c1144080380183d040b001c400c001d0b8281c0420059020005420002d5403001c0361841141e0f00d10801d51410340662074240e5001101c003181c1d29810030703280300381c2d80d4030003503603c03011460b41d0095104407641c00f40d03181400b00c030241c04403140c510740410405040102901c911110014100000f6007040d2029642c031642510031207424020105009410798149005503200d41318591548402 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 534000305 1250 533999055 533999077
    0xa06230702010e210d0e03010c080c040b07081b010b01030c0201090c0b2203050a050c031f0207020a03020d110a060512012d0e07170622020c0102210714 67
    0x13a003020042d4102c071103000200d010504180c40f903000202c032002d0050b0350f14424440c003961a0412092910303001e500031178010500c40c20007908040ca0450a60015484050200c40e041c105010004075007001e140045618115080041481400c8000042c01c48210010040440e818207122070003140c1c031003040c42c2c02d031140c0e40555070b581c000300d003000302010300100d01426500010031000000e2203c003064281d4010312031416142c610800804060342d40e100e0301e41c0c14540302ca40c2c1031000300070320031507005001c040d2001d0320706120681d482d0009003100703843c210305031180600142401018074003101104068001424401d06210b21440742511240f0b05000700c481d5044581280200c0c1110f501901e140d170b0800300304054106480b00084040e04100366442408241d03040350b10f640b031030101850144101e5014110b0340011a601065041016102d40d000041981c2088a80359200d003c0c0010282d0400740c4010b0401808240911240b030100145403108101040ca00003410280740b0044449100350 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 534001555 1250 534000305 534000319
    0x1050a0e0f0d03020c03070b0a050a0e0d02090c070b070807020a0b09120a0c0506070f05070b0a0623210c09100503030a030501050f10081b07020a06230702010e 70
    0x6500e001c034615424800349564401200605041059800500340c610a44150f050381e0f034050b9541412841801859000e00c0032840c144040164103104107908101100f0003020000241490340100e52401030a03030b0701402142c000550b0200340008040d0b025000841c0d450b060aa80c50308060094403144008001052220101d0115001c070b0010044c40726503d40200079035513a994550009172050601d0002211140110340004201c03030700500000b1420308403904d61500d0001650f842c14691a0020120303640c0310340c0d0740400300d20f03845442d00d203d8080782e5402116082000640411502c00035000480007100c0c0c2c49811054011030110306405451401d41d4003d1302d42d19101101004d15540e60800c0340c05200c0400c05000300e5605400c55030403a0f0b0195103c900c1c050ba91814030101c00d4076042007001292440e40070625603401c0c10040d110300d0200b84842070a109250340010000c4201b6031204002031344d00b04440c010400c0c0104d00042c01d030300c210181480c20070207900103041000514100c5104220b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 534002805 1250 534001555 534001577
    0x120613060e0d020d0815060a050c0f10020d0609051b070512031e0610020706080a09020a091b30020c01090606140d03082a070b07080c070201050a 64
    0x1190851601c81c0c40d410140c4103450740c210720084d540d04040e04100c0000d182c500105203041e015a003c0105001c0c081c021501d000644401500e282c0d100c0e02c0c1b00526880b40203c20568440280003c0440c4010a440540d0301c18407042400c0c2603540c0b07a00001d800c02c0c500014003150a030003c60225192030b48040041e100d0070b00342020303401c1c0003007801c9198a0390000000c0144501030155806540000000100107d40702c0c2c001f403203041003030316a140000d03a02080090002d41c2c020082c80c2d0744012218800305c0e82c11819404581c0b145841d40c0011800761b08d40c60f0074a0504600d07607245044002c24940b141ca141d02004248400c9a8150305514010a0180c104841070000390103d98039040210000d02580807240b03000e500800003803040003441c5a2880e408592407501004105459805503104032070394607081c3e9404040e100c00741d600c03002125154204080c12260b60054502a130199180324254500300700060719444008040060300c0e1002c000690060fa0004240e82c5010ba49203000c0b0f510030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 534004055 1250 534002805 534002813
    0xa0219030e0604060512010f0501020606010804020a381c050c07020406080604021302030c040509090a050f0304080f0309010f0c0c080609010606030f020a1e1403010b0315120613 78
    0x1402800040c0d42200b0001004140300340c001000b06000c002d0700c5040e1550b41c0e039882e03800c210b0903081d0203001e0040c1c1101c0007160f030562090440c80d0708680024082d0500381e83e14200c4141052480014140881030307503460207250802d500f03114031071011280c01940361000c1100a0002d4054005030440306035502c1000c20030603000c0000340c4400c1640900104045902d408415941d50402c9908901c9007003510040740c9014014001e0703c0c01440303c0481182858142810030060441c028a910303854440c902c4030700d020a104008007291040c2910155a445080c00300b601d040c411012070011140c1d02c04c011210159034032400e0f40a0320764132440e00c1e85c40502140341c400718280c1e49900902540c814041403000c00c0c601940101c08950140d1810402d02001c01114802d03800b030703540311101060010440c5180101c9142041446c00e60b1031411103034204c100c06018820340c20030f0300900186ca01c04800c1010744075050088082d1010201e400d00190301c480002e055664100400cd02048098500040100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 534005305 1250 534004055 534004067
    0x42d032604030f03200c160303050d0b040e0a292502030c0709020406170103150b1504030b0f010605121506040803120f01050a0305070b3406110a021903 67
    0x400807110442c1c041c90321030748850b56400008a02c407447c000c00c038805064102105d00340301140d80c9905d07031030304114000b65802d00814404407080e8001c0d0f22500e1114100c034050050440705d0340314641ca0100c0c248010080b00d4000040454020004840700c24005120982010406070700389030398095040641e480c100303c2c05d5006503003210900c3d00c00c9040100d600001c9070060b00545d882659072080c4201d034000c418000300804e20001d800c0c12000491171000346107a80000c0a0f100c805401c0000c400c000300e80390109a4040d81c81034401c01902024007508035420040d0900611030b5240142c01e18aa4102c1c5800d05c80c806448000448070080e840004c5407220300c2545d00520024054984a100e0b18003808040741c1308540c948a6904002c001080c82d1030030707220030b03015240c1040c003d00c0c215092a521200690200240001c8220503417442900b1800041084e01701102da0402c000c80c0401500c0e0000996800301e01c001c4000c1c00500000e10060b900151402044400440c0396588140c6401d0541d01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 534006555 1250 534005305 534005321
    0x1d100f080c1c080c0604060b010918050a0204031a0105010f08040506161101060603140a110a0e01090f261b0d020402130e010807120f0605042d032604030f03 69
    0x22100007203001101300c40f020814074442c034000c801c14860002c40c00011200e00c207240c050b00051070b04240807002400a142c0c0903d501891401c80186010703225129401c0c0140d030007091040514a000050246503031120200071101e045040402c05030038135036500c946402d1300502c060034001c00340b448107940501c00e040c9000b0107283c000007000724a8a03448010060103208040c500c1d00d40003403000c40c440e0915446102c1c08400954603003410501296400c030f40803203619649a04005c0ba0010204482484007274010003850410b4094180740c00c00c0318103c00001c41c011182031250030104c10703814060059010303402c0d4500102d418a86090325032002030024043d2001034140102ca01c080465030040340b48005060314155012201c006030303211800a005540d1a40041c2a50f014501020005030160441030f0818407880c081c00c56900a4030440d1144a07035031003025660340380002400141500520f447c404188807410b0000311407202c1006461f8000040c3c0018208074030700d510107800d60700c641d0246803 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 534007805 1250 534006555 534006563
    0xc1302031e09010207060b12030318010209150901320702010c060606080609010e281b090501111b010f0c0f03050406080c19030e0102041d100f080c1c 66
    0x40329051542005000b074000d03040c12152281f034803601c0744851802e000d182000d401c1c0040190324590710400ca20707080010b504040807a5640034080040f82d651030104803024071903c0d03401203456089540004080c08080b80aa0700c020000544203238807448007440d0104403502d8040600c1c2c5d250268401290102040400980310b2450038001150103548036403480c2c007500c41240c24101e07903604d82050b01c0c220001658000b0717000241c1c081084980030405c1c0c64280c3c01c00403c20020340c2411030805080040340030000d090004030524824003d039030f0131441500001c46054010b0035501c40c103611490780d500441c1c0c2880c0c10f201d01e0100c072810591007445100704070f40e480012000c03e45003514001d052a00180070303000115403000300003030000340e8082c1079500031000850307014052a45900243c00034540d5516822641d5020407022906220314403c6400d2040901600c0441e071818807440070100d025034000e502145001007013005217100001d8003100010080780e5480424000c0074001c1122440c1c004020 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 534009055 1250 534007805 534007861
    0xd08030618090708010e160e0601120903020c0a08160b0d060302130207031209052119022d0a03181a030603010c0201111219020310080f0c130203 64
    0x42e1084010840d032044450480081c0403841000c102980c0b28645428040c0041400c904104a010a20810150403d2044c14000f240b0200c103400c410a48825142c10f8016901004564800d42005054813004140100182070030031414502d84031a071500e8401e400c4c59076800303c0c80160580e055880708004550007000398822481c0032004001035003000e0800d41c0420415200d0441000705802280c8030290b000001c1d00ca03102c2035508d40380164114038112203802e0000e1050f031000304130a4544c104031444540040802d0001c10f08600c40c00c0b104d0949512003500e0101c0e00a07404039000880c0c00b0000d9041c1086a10000d1800c801e140ea03540d0390f8005154032040103510305000041c03800039401218282c0c0280200000950241d081c1d50110400031540a002c11160710032608a01c0700e2034028024141c101200d01642c0d507100b0036a0401e072128a8101801e650400007488200308400c001d05107080070f0411a5940c0f00000c14015424000d03040440d00080054a410381061100004150382c0078a5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 534010305 1250 534009055 534009061
    0x8030a05091c0515010e0f1603090c080f060c040b0a0809011803030605040e070e06060a2f1501150311090a0f15110c0616050a03080a05060f0d08030618 67
    0x15541e58100c6509600d450368249002003a071b614005c0005110b001c00c00c60154050710b40102d58500440580707074078003c15950312420400941184402e000510506009100f00e1020124a500345100030340500c480000802080000c030784110256103241102c2d080101455442c03003100c41c09407074a44694030390312034523003c16810503425038488025100191001c0003801c0200003019078402e0709001c0d003608070007544001140351921400405181d40c082c41d1014268101c200418108a07445a100b16400c40000100703008280801c0368840e0341c034503542002c8295241894000c0c1c2203107200041410161a2034491420040442c110f640306500030b00325003100c1e661414030310301c00e98841c056185c0c070030440c2906804403031043c1007182406d250040070b0300d0240b40340400c00c88640d000388520b0361105008212a000300350180300302c0d1032240c082d03101d00a1610b8021114004c0f500001c01c0749110300c03100d1440303004d40e0303c4041c421520b460b4071401150f9603032031303c2d4001580102c0803005003c0380d0280c8820 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 534011555 1250 534010305 534010313
    0x141204031709010c1413030c0801090b072c0414070207050103060b210414070b0a120603030c02090c0903100605180613090c2c010f08030a05091c 64
    0x580190a0902103164020b40c80d020905801e03521600d55030000190824640d90031403880e1402444400c0c00e05448074081e81d170341d0f5144100c00041e648100d03441e940d40c103684000e000c51126610350000e6580b4142004050a8107690000400d030150104006900e4503804600d45903a03201d00c0c11610303c40d040d15070519120000a6076014580507080c000390401500040400c1c120042c0d0f80303a1708480d00780d0603a10002c2884000d041100410581f600e04105106d80703c19003050010364081d100c03c0e82c079107079a1182d807a40546060050025000014500041080030030361020585260b141d04680181c03c94440c01c0c90590079009040d0b41990502034800710010100840d44100100da0040e00c4150b20f28952942c8010421800c4800c00d400c0641e40c81402207081d039030b602c01076540303200307950880055441794881030001d0b081c54992070211802902c2412040c0c407000025005145a02000050a0601c007500e48c49000754803809091000c0400d400c2d075907035070b00e6402d0341c070b20410701d00880090145414 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 534012805 1250 534011555 534011567
    0x60906031002071e2306070f05090f09010303050d061e0b090f030d090305070b0a050f0d020c030a080103060b03060928020d0609121e050f070c03120e0f030d14120403 73
    0x1a00040107850805445c1184a000c50400e200340e04e59102e10380c0442c65131200b80e845500c0207000c03652000f0300414500c1681d4130031803114040c50095aa158036948560344160490385281c1000306900101001802070480306840c07030060301d40001d000d0391102c50480114035100f010000c00c0c0c2e418001c403400110803c1d800004042100d015208880d501942c42051554034404c0012040004900304010a2201014401045c44400d0700100515003601e1174949800c58100804a20004070100b00400c1480064000c08801ca4030403005083c0320706048a52170360f034500361240b00181c459180f400864102000c0340800d030306500500001116005480c03e0b400808148908450103c0d5400045111501c58509800c000000e20064800c1c0c4500c40c0f4155110707000300803149000c0c0303400c1000800088150010400440c8100030105041807445c2010b0903d00c0c40c10480c0307025109200409403160350001d003003d2410b059041c860701e024592072040002d4440e0b01c21282080b220300c0c05000800d03900030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 534014055 1250 534012805 534012833
    0x1101060e0a0c03020324061c09140c0d02011107050405190c18030204150b1603020f01020f040b070606081213170307060f240509060906031002071e 65
    0x1202007068407000c12040c0d08a0109071507040c0141b00c00800091600888242003c64481c01080d907800c18481803402c0c03622841c2c00c9030901007241c80b581207500300b02242d00003a0401940401400000001101055603442418000381c100450150841414841840b0100181c030000d4814007003490104080507480a42c094011805842c0803001611284601141d441040b812403000b45082d28580802c03015200d00b808416032807420700d1001601c1030040004000e003c41c00700c046610b10388603050107401c0264042d8080000d9004100020345079070100f04650584890a9915885000034241b070300041025802078440b038840c4110440c02e520010000d0074001504845106449880c1c541200041c2c0f103805003182150b1061040d00009403803608520000c5070342e92700029040462120403000081641c1d1101070001a1040a1100b810194102d0381d0100054505144604060300032030782d241c03902110000702c19400301c0e4400400c054500c0b00e40304c1038100d1003c4084100c6508008505010075 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 534015305 1250 534014055 534014071
    0x4121d04060b092106010311061b0c28030f1506180501090b01050702100309080a0906020115080d0f03092003011a0303190507080c030406020d1805101101060e 70
    0x204001c02c2020341100070302c01c00313904e0300c00103071106034a940d07901101c409480c401035610420502c0f07440308d01100c084024900740b28220050021140325410300c0f0504c2d00ca0715200000e130100c416865401d21002a08200300c0390702c089407011188480c01c00d500c0c2d1040c80c8001000301070a080000900d8001003807400300e0410711170400c10050b42d8654680c0121020012000c0c0850810703c254005864858840c1e110009541004106000580e513000415842030600e00040ba241e4001805081c0e0309200702c0c03004103517410221400300d00b0031140039519405c2800c2e01c410403031000300148020784681c00952589900900c02c0f02c20210515030340310003141d440e03202da000e50700c1c3c0034000745940c00000b03140c0704ea05400b401940c0f4146c0d5003c1c41145450f441f224410522004202c80790000782480c0c0201402c5e1040c0002c0e6403034604102c0c0081c14100e810b915881040040611620300c01c0402c074035402151170403501c0c103030303031109500080d9100d5402101c1c46540e5440c203040010350740c0c03110400c20320500b80 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 534016555 1250 534015305 534015319
    0x90612010e0612010506090f1302030a120e150403121202070f030f05090d06020d0e0a0606031403070305180f0301020d0c080c0c0c090705072306070804121d04060b09 73
    0x120030fa00500301c8401710358403a40228440082000004502c1000743c0051303028040040300d01250300464517280c00901d04554580303054010101c10355010f07030300d900780d0310040f962075200d49a270307844010490007070340400780421075420100b0300c1403030207078004a480da00c0c01708080d51280b60b41c4c2843d52401048280c01e8001c5440c00a0b03640c0224480c9080b200300750f400910398600800c464075440f000750020090140299603c0c4029400070f1820440700822070710400c00482c040d401c600e000001c17150300300d61b600c11541c030a103c0c00c400641c0103415541c044000030281d84880208070005101c10f84001141074140d4400a01115521140e402c0b00d1010000383e1a0760140e0344a1600c04000780c440c42030601c042d604030340340c040101d1811483c241d411140070301d8040d040c01801e455410180c40d049844440d1400c40252440c5046814442e95520600e1030030f00055174907050b21440c5800c60005806410800000000000c0742e1038958040360240c4090000c03c2180d850300081c9038160b100d0000b591140c81 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 534017805 1250 534016555 534016579
    0xa020301110a08070c17040b1e03040b04060c09050a091d0606010212070203100e03040303022b08061f05120907050f0904031103070c091401060f05090612010e06 71
    0x20100c82180c000c000c160b030b41c156469a591404484445805c00c040b51202c425140348101c145190003d0702c05014000a4607555002c81c0424150401941d1104442e41000f80100000700b4191000e41368026005500816000145582280c01d550543c0080742d010440500220360907100b41d01c10411201085c2103160300341c2c0c41c44000366498004440e0f40c1d0041c2d1058503660f03500c880b0788010740001840034003110810681d440d003101c1901c070190404a0f007948081801c1007459410048419800f06440000c55441d43d0604161044440811884148840a0003241854464045926410f8006e8020701070072102041d00808940c00240002c032900102c13000704610f51008200401118030040a0140080d500002c2c0007005500a1003503061100b080503c11008405100a2442520415290300041d0804440008540400d5200b40000c03410100511803160001c451701c0c40d4669504200d51070b4801f1000203840c0d40b2800d4905034841480e8000003500c1d03440003151500030141103c000c0710480c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 534019055 1250 534017805 534017831
    0x7180c020105390d0504111c1104020a11060720062e0f09060510080609060609030c0409060b0108011208090105090a030f1a010503160e0a0b120a020301 67
    0x140380c00f10030704068094544590030040304401c20041298407180440c14010112407040c00c884044800766441d1303032412980c21140c50b02520a440d81108070b1102241461503845041c540001912403500580d4001031000203180540340c0c0a20704000082121014030f01a034000b890b41000c103407500c81c960404815007600000126500740f00b06602c0512241303040e00442c0004000b1228507500d2b50440300605e000c280040034601000c007611800d0b4000c68110701e0503080c041503203a600d00c0401000600d409001e403940c0c0b015802a00039900300c0d2040d880b1130a440002c1d0a005d90420000d501900c0d1a8840c010405c0c2c0f80c210901207482603ca50806a9a076501079103549598000180103030f8041040e103017290300400c090a08190003418103200030f81c03a60ba500480d8070003030b941034441e1411252064041c4564408860252034140c026016030364400118400f054514015011144110800078070b04660551003008042c4008080452142d0032002c42da8650a070104160300a5003400700c401c2642c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 534020305 1250 534019055 534019081
    0x209010b04050310090c15020f0607080618060a0f120203010509010b03030d051b030103050c030f240c090d150510030b0f04050a08041502251707180c020105 69
    0xc1e0b0000d0094840300c5042c90b4084d0041a003414101d501d201c8003c4041562404840800414403150300185240803100b44ca00f0f10307006008142070101300c0502d08100749a00c4a07900701c0001c101d503030b403109040d40b02d403c0068040f2038103411841403c20401400900ba0007032000d0300103a94001d800812442c0c47d00b00d100c5090302d1110740391a805030310030800c070300d60150145c1c8081d40c4803040208a4094070b103055107140e141d038800c7c2d00a03500e9a100c0c094461091906200d80c501521810004007024941c020030241c02480030708031141c0440842000812040d40c14040703800c0301100504204003080d045c9402d8032505170340101841003d02d000006040715041d042d074172064a800004c0c0702c80d01e50381c10100d101103d00060040341c09000712002d060004030386101900140c002d42d1500750006c2e071a90402854001c00f500050340030a010030000750f0308401c2200b01c038165403415072140d1420301e1031000686071995540c4669021185601d018a00071f01552040c20f500846074002c0c046901d0320b461002103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 534021555 1250 534020305 534020309
    0x408030103021003020d090303020309014d0a0207030317010e0a050c0d0501141009032001051c231006030b03011416080714031303120203040c030209010b04 69
    0x5040200014005850448071900d64042c0f00d01c0c0151401c007006a00600ba5000342c0412004260040140f0451010030700440c510074101c02a07070890f00b41e00c48980c011980c0c0d241c29003060b180d1404e50525841c00c400b1180e5803400100c0c892541c0c1c5641d207180c0290740326804d22055000425411614402c912106c184504845003081610010348071024040b00404000c2c001c0050342c030042180707001400f00c07802a24000c00402c40c00b60044030b4009c0074003601c60443e03045181002010307030b010700020b0f01c1d010046d042a07015a00141d04005402c0068441344280038003402000c151008000403c90f5580002c00303005440c0e088024203408138010307400c111000307481003450021072680c144001d44c820340c0400031300d1000a0001c5801640707070030114542c0703500f510a0514206485580080c154100d0040c81d0408058030701040341c000c49042c021040d02006e4401490031184140c4d5000340f6100c2d03011a44c001000540440d540e080a142c100040b071054071040340541030080c0006007950101f025101 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 534022805 1250 534021555 534021563
    0x2b11070b040902180d0f230a110a1a0a0e04060b03040b2e0e0f01060c0b060310020d050411120307061104081f0e0d0504050d060f0c200604 61
    0x104082c01c00201c00084c0d00310701d00840245032403084034011907507000100e200301401801c118099081c01d080005070b184161011404103240103440486890002560640817900300d0310940074406140001084000142c2c4040a8011645562200c059400340100460b200640b5078034040312034601070006030341143c0306000c0440c0d4144001008103600c2c10303c841e401101003402222405080000300e0210088504140041c0da40032014044442590090394014641c016002d0f5550705d0007000a0000400020092200c0303002000b040e00303500d08018883e50791441b0041591140c0172401010000c040403a0161141c0114402298860500300600445880c44c0780245180c5140c503110b030009042e80001c1c1705e1920208020010396840e0501c01e00c031258858a41d46101c0c811402c44202c03d43c0e100c52001070054010755401c0001d50b400000700c130229070341035540c4901c40a03982001c2008242c140945038110781444c050383c807401d030300041345040041416440c0500310300c841007865581710200c1d0020 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 534024055 1250 534022805 534022807
    0x81c0e1f0503060a080d02070302180105150a03020903070909050d21020c030c01050c030f101401141b0303070207080c092a040605071103030306100e032b11070b 71
    0x81045841400110341c412800b510400c482c2eaa0f5a0b102450100012186e030010f03006240b0500440c07811200000229804061082a550421001451014000d50600341c51003000608500c1c4a00a03019160100c400901b80d845403569241c02c1c03030103000070f00411100780c01505289408103002d030382c41d010780c40038110240150488a41360040294000001000e90b80700178081403440c80824002da9204100c94040981c490506844441ea10500903051a014903c0e031032040c4020305d61210720651b4501d09180201601440c032550b043e0f94400d0408407100c41200380201110040008021401680c50760300700c0d0074403035503801c3d02c548031112050030035407041c20000840c00c40d210b080781c20f0181e07840520b54480c65072107151945a00381d220b5444070012500c08100c0301c080c4500c00f0800c002200098014610717503e0150700040300f0704a80c4001c2c000344000c006200d10ec5807010805500b400c0702c0c584005003110100d0f08082e00901e024400e200c002007480c0c1e10b6142001c00821000120b911000d092 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 534025305 1250 534024055 534024109
    0x606031401060818101a01051602040203070c061d1606020c13150e0604060b0306030d030e0106051302030a0c03110d0207080f041e08062a04081c0e 65
    0x115002c01019242c0113240411807950100d5030020f21030380c0c0c0280b810940015001e01600b510f902c150030b25030300c0035040c0942444186482180001d210840c150304407001641e9950b002400c0d079144a100c03202905c1985080c001900c520500c0c80d218100061580803605142c103141585007440b0101c1c01003100580110961a42500b81000c45464442c0d4284020906062151800254502a612008403680c41c4810301c041d90034540b2075080503051100c080c034510b190120202c0d40d1400141160410035079264200d00012400b94841c0c4080d045c000c00d04c03140c03000d5600b002c0b4042c1d007080d104141443d182004a4890500030700c214034804103050000c5082241d0503070540003d4005000503911880c040080c0b00310300c3d044000900150490307034659078140c09018100b400b4005540c10403900c55020a042c04220700d4440c0415840c1140c0c2540b1826582e40900803000c10302031940b01014620a8180324103150000c0c1040214134401c0703640356072138003800c0c00400c1600b6a500c211814990109104 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 534026555 1250 534025305 534025307
    0xc03030605061603110c10020703140a1109070c020a0b0d0b03060403080609040606030b0c120711030409021b0313231005160b010906080115050f0402090d080c0303010504060603140106 81
    0x85c1582034500071040d529a5241600030814041d5840c0728400140c001120501c1007201d541c411400c01c14900005012821455660900305441c180a40b482080c2c14000141c010f4450580d1613002d55000d408440503035640c10000c00c45401c0b407051060064280210480f141c100052403521454166603412456141c02051241c11070300944165a5a42c070f80300d0200c04504400c5415008030040c0c4521903450980c0000035400303401c064030110030440d05c0001840030340340001c1618207660040d0030050f80d40314064081004110b0102a51409010101d8031010381300910484404541a000c1e02241f9050103c160600010100b02d0320f590007540f4000d03400000744620085e1003480f613200b00880041d0101e80f1500c40345202644001c24040d00c0743c00a00240c0020f00070400c0c0e0340240701e502032400e0b0503e000a031500b81c0e007007000750155501240444040c1c1d1001100224160020030080d070361060800c0d2241c40364024090240160b04003c00042d07107a00c02e1244161301000c1c1e0042340c03081c1e424594 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 534027805 1250 534026555 534026567
    0x1e09021008061c0f060e0a050d0806040603061b09080d0c0312141f05040c05030103080c0330010f06050d09060b1c140708120a0c120c03030605061603 66
    0x40d250f00301030000c071406030011442d9058200705000b284e41c2c504d10741042c50290265894100c0005294004214240020300c000031103200200c141c3c1022a102c0d51000f0210b001440240c0c00a0f04080c208110079048000c81d01e561080d8424540e50f4103401502c614200c3c2e46e4603654491a0300060468014001180c819500d1090354400080041138070040381c0620411418107440030440c040d0403c0000c110080c00c0e00d00d000040505850174485079045241c0900203010511014040007400920a010701c0d209004a0301c54900b5005280641c543d050084454100c40c5804103183d00c16000002c038402d0080e11244040310300c10f90303441d4034140e002019070000c0c15061404590054480c4402d4640390390b001a41044c601c041100c200101c103803811b00840740c819044400b04982c202d58000d019550000c0f8204041134040d0701304581c0e0300303502d2801b110108009480074040d205e16581480c5180d0f41b00c403011701524000c0da01030001c1a03c600800900c0d03ca0071807a00c4480800b03c903e017000a009038 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 534029055 1250 534027805 534027811
    0x6010f0f0e0a02040b0319050f070203180a05040c0f031a09010b070606051e0316060f050304051501181406030c011206050603040c0e090303040c06031805101e09021008 74
    0x26007015035072810321045401c16140c41c1e560749601c4d0f58007d6008010311440b607104054400c07014140c10400303400f940340e102d03d0541c03c8074010214441c024580382c180c610401080090700401868001c3c036030040400d403003810349400080c2412800506d04543c181c0c1c0c1c8295980083c205c3c40c09901e800d100a0440d801154201c0d00e0544038000007031701e652211100c82c07802004007413003924890020100f500f0700d80b4051518a5040b000e2105001480d4001040406540036040455490322a82425454224990004056403e0404c004940041d61107030010120307143d200305000c0c2e003402d0503401411540c100d5101d0f8150f40030385009d0ba429842000c1a1200c00000c0c88000340468403400822000e07801244c0035035604495000c100910800d03481c040b640070124102550440c1015591580c0d034010600c00c180816440300b007074000d4010442c8442c1002503210088590300900300c103815024044050456042c10341c07000d94200c82d0074041c0954100c555008001080218085806640700d440c05 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 534030305 1250 534029055 534029071
    0x7020d1e0516150507020c03011404030e1309080702040b010f020d031109030105010f0806060a0605040e0a060b0a020f0601050a0305121605070303020606130e0613140a060b0306010f0f0e 82
    0xc2c00500d000c500500d080425000388404003003050310342075001071311b4030344500c1c1510301030307898400310102d02d000518400387c015074903191906c00c461fa00c0b0f0010360003082035071a80c008245403001210810034000c0003000c90320320984040c804044c20700019a0440410383c1013801681102c00981810b612039884038a011048900721818070b42080e010900310383c402d030028107803907925007010310842508000d1540c4c0a6000c40c1d04918240c1007801c000d0080c0554410b00c20910f1907200843c1c0d03c10b005401103c043c00b80308580720344555444100035071300c40740703030171022401d00998002285c1da08040c41d614080ea0380210041100b807995030840d290a50010520451403014041c140300010700500080b40214003ea00402c40c609200c4d0411400000c940701400c0101d04c0c0400f82c801014010540962041142c200b00d408072105040030003258180c8500d403141400b41d00d07456802c1106560084003541c1040e030441d1582c2c0e072505030f40c598500c0c441c0500350241d01c05e58020131441a600000961010b0b40b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 534031555 1250 534030305 534030337
    0x10021206040642050c010e06060a09090302100906090213020426010603021f110106050d1e0c1d010503030a051e070b040804080f1c0c0206090604060807020d1e05 71
    0x1041c0320141800c1141841480003413800602c42000b0b6900f405000c00110221000e031000e810b1034000600008111b1113a02c0040e070310b50030b5110501d402400001e1541010204c144144061858000000e21011004a205130394070f8a10002d081f14078800d9905540b4206c46c0c00c100d0070313198600752030880d4100611880a64842c02c010005890710184440d41440c007011114907681158030150a800e15001c031606182e240000800041c1d4600308030304030392070700005500c0d03003da80f9840b29811a10300c0040a4030000c0f0040780010401c2c0002d80452076500c0d042a014056600c0b242055101d01c0768025170030000f00c00344800c041c04c00042d24400b07800c60102c00000c3c03406245640b04d450104040302c1c00d444089010600300b080140900c120406161540d0141c012000025080c2200d0b21110352002f04200c0140301c10380c115110201201c800b010014071302d0391640d6030303890020a014003c0722400014000c000b168000280103400756580c50b1000d442d40c61122080754000c4a03070340c00240700c0c080c02d160 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 534032805 1250 534031555 534031649
    0x105090105041e02121e16050706020d0908040602010f0207081207020f0a0305030a110a090b0a03020d061203020d051207120b060a090302030f2107080408100212060406 74
    0x1840c07000300385c1c5501070b560317901c014902031811034031003e102000101d101d01240104160401081103000e41d401c1c107410721070f807101100c0c1040070090080b040032001103850003200340148040c40000d070003250b4150b4000c0c4242600c800e003202c142d00170302c100100802000c2c840f4501495001c185d04d90b0103401c610480b0003e928645401e407500c00424019004168004288081a00b95010b21800c0700c1158402d9403902114207801440c180b91031180441101e00807549113070141c8240c0440d440b0003082e010500045450f25881012100e0700f50089016111b80141c11070b1441c0181e060303800850a0b60f00c001040e07540c8110940d81401141c02e14428150740e45503041f641d80d2940090b0800840d5660380060070f90a504c149031518499100310303561307680009005e003071412040e54042c6a640713030300661b10b89803a01c1c2c1c9083c40103801250004042806420a49000b0000c0c2d58043c0c011717144000a040076070307151402400210b441d1805800324100b20700700c2da005180074590301c3c4001c0b040080d140351000c2d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 534034055 1250 534032805 534032861
    0x90f140312031503060c0901020c04050601110d030e060a060302010903060c020304050a030501020c01050f15041505041103071805060301060503060a090f0c031506080117030f2b05010509010504 85
    0x7902c01c645103050000512005080703410304206055020f40d10b5040e0354540300c0c03d080081d50366880b4038092440b440c1c880000810701d900c0342c805441329405607011a0300c030a4000ba03000e009841c1c25060113469101d0040043c0e094031280c015041200e4060315558181c03400c58446401070800503001c51f0640c80104400205030b110304214a00841c001c0000503100c11280c2880da094650150000c800b41c05400103116926500d2440307038a0b07031034017290001405600158140003000f000c0c0d00a940c807031303d032088000c1e00342c1001000714800c415036a140420107102c0c10b804200700a080c001c60350405410b0005000c1c1d42d001d0401580c110303d0040800ea04546e41e0150340d0107442c0030000c0604082c3c1c51320001000c1540501401b881e4030a54070003010103508014000301004014400c4150f014222600360184103414812569000da02414280c3d4444c0d10103041d00c522983d1203001d580300e40d256801b4110044152042c203040c1c90000303040c210180d03e04030410014044001540c400c01c01400d8418100d1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 534035305 1250 534034055 534034057
    0x901081503060124092105010f0513030f1407060515030a060614010309150203130c091e0509100c030608190c210303090c0e0f0115090f140312 63
    0xf8005240900021004101031513003214120340440140a40080d0501038600c842407590000ca5060300341044010003810180e0250440030070310110140703080244441d150111840c07a0754a4001e4580341c000180400c811070304050001c8410a868030144140000614141c1109400079a03114564000c240c82e040040d050035855141101c40c141d562008100400d40d001342184004c80c2402c04001c110601c0e02e03080c00c0390401c60901c0507001ea0000c00907921204043c91081d400c0e40105101203c540c4035031401d0000c20010b24400d003440110b03803983c541664a805000d10440e419000390072601300300411070000c4c3c00e2213150b20003459111321000c1500e08040010741d40310540101d01c18100c150504040040140c140c04c0f598015a2410843c00390f1500030f1100c1c8240d544c14a40001c10110078140b5607131811094205240c0c07121844e041c00340240b80718911f54141c41415020481d00307118640300380c414000612400b2041404010100030307500c80c14400c042940c1c1c001d000d540c0c000308507023060022 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 534036555 1250 534035305 534035309
    0x1b0807090501020d020a1e0803040506040215090f0d2603100b160f03030b040e030705010e0601080718090813030302010608070302090604150509090a03030e0a030509010815030601 79
    0x4151508228415034080382000090500b800500300e0740300440402500c0e5000c01e0405400325402114102016000a102d01c0141e6000050f4546906040c074000b903e51500b0382d0b00b64411040b071100141e032000d41504842d80d48400818a0001c10142c006011040301c83c0c0c0c10960700303031208081c441c1d03407a40106421040c0c0544612156035a181c0b10300b940000d841c2541220340615401d008038030180c82d4050100040d035801c0107040700c140d00c841c07030214041d000c101400c2c2d8000e4180114524201c2c0c0010140242d98454070091000d450700705019940c40c0401d11072000d590780401020040121034400d880800309409602058404180c0ca4000c8240e10203407662810403d80041081030580c203210304c402a00e404170217080344918540000724071203009014144207a40e1420b101c120020341808040c0100b03000350445030b5901d401d0000944420412800741e01003410a41a05048500803401c0c010099041e11030508219208004503404a0004d05c42080c1e200c0743e81c0c400e00e00c3d550801000f40 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 534037805 1250 534036555 534036557
    0x3131508061e0f030d0f030e030426030c0d11060f10050d0204020d05070c0312020f190e03010c02160e0c0a080601020f0f071503052e09021803120406080c09041b 71
    0x120411501b807004040741c000d107100c1c802c0b642003808240071995404000c0501c0c080c441000702d0780c00300894945400d6110b00e81c5485407501c81c0032009a0410f40081070310b81e4400c018404c1d149256038400f0014078001d01200d6030302d910003014030240200d1421445a4540c00d0024100604210312114900105c0f0410740d84980403c01c1145a8002c02d60f01c810000d1581140d0300e001e50800100103030400d0b007400307440c212450700c0c45840c0c0d42c0c07140b0a00c184980b41c008a4028003e1041081c18440651030b450b400320703100810818401c022800c4c80f2402101d50003442c0c801c207142d280514090040712505009000e01c0d045015010b00310802c0d0500300300314003031400200c01600c051450240d401c134602c00d6060380c440038035041c281040030504400782d4080b8500400d104095030940541c2c1c441c69220f8554000f000c900d8404500c80075146600e00c50001c03400425000c81c1c0d5400603081c002184c600442c81510005046100058040480300c001b500c81c80c90302900109040c0c60b08041c1e00350110103200840 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 534039055 1250 534037805 534037817
    0xc090c090607140f031809060105070b0a0c0f0f0206060618131b0c0b1305030d1415012a05150a0e07050a0f1205030c03131508061e0f030d 61
    0x3e020504240a40c59141c89118011841c04400e000b00170100d13081d10741411301c03035038000c000a0b41a9005800301c2d0b08030351303010203c46090b1400020210003020b0002180000610200030a00103500980c11590004c01d550000e014550302d503410491036601140c1140c0c5820400c00000d00151a40c6504464031482a00040399251040745894034000a03100c04004202c0640242408200104482ca82144012038900c01001c01c034140f80b4a18840c886080d02100c3c80c0c9002034002e40d88422505010f0b80c20840700c08003c1c031500004681000c500141800c039004043d1264418201400c4c5840d0803a202d84140c0b695615044c511409105007203941588140e10b80c11840c9604806100c3c0101802040311203101140c1400c46070a1098054060600d124500401800038000304000781c0390140513180480b55a440c103040c00f0b81c2c3c03140c00c5100d080f0f03904074002d13450f000460040700e00601c5600050328104081d00c4001c082104510510b0000c1e41161180500e02e01c1c584041c0140c03101c030f081c01e480300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 534040305 1250 534039055 534039083
    0x60f04110705060c070b070e120616081605030126030d090b0a0c09050103020a2d120e3d1d060417070c120b0106170403020c090c090607 60
    0xc5414070314001d100d1100d0134010003c4030000342d104031040e038000e400361402c0c03021456004046044040b0300c4071881003910680d0100b2240690040318110684101d80da20180742d01c0305094541c0303040003240c101e000306030284014800e450700c8420040c400d115a4002c24401c40e1001245411503211181452030307280c4400d08002401449101d13650000031200c82000000c10b06031000740340c98a00d00500d410141c000522944203032160204207100c441075010049141c03590311f2449607441d5100c41000104004510140441481e4072135680040c260001400312142c0c115407160148030f042c103408000c50081c03884401000d4a0104004100381c0f1403c00068000012008812004071096200c0345980580c00308030008046003030401b40007850b225410307103e03176044ca480c10211205400010840745101d000740f0038080f0b4041014101d80312501d440e5440e0459080c2c40c014188101d50242c0981d2203c80e0060300b0303090504039503510180314080c5c50f0400c541d65000032903030b520a030401d03180f401c404045 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 534041555 1250 534040305 534040313
    0xe09040f05150403120e0a0b0103060b0f03031b0c010203030709050904060e0114060103060b0901021504060e0d0203120f070e0d060213080309100302040e150d0611070302060907120b060f041107 85
    0x3403a201104100041c42040003954a43c2340503901400010030790394540302484000c1d00c2d01c0b84a80b40f5a100141070f69141e0486060301d00600701c08201901c120301c915074411404c0c2d4004000c80740030310b625649103a032a908010502a003001d01401c202c5289903a0345402c00040028400d600030b0f00e01c10343c1459440c2c20007900040c01c0e500316401680d841e130f01c20050b80304540c0c2c00007001401442c1000c40004135599600303009008281c40c0c0e03a414011300807100000c06065012004141e03240507002c1c4005580c8400d0746802c0d20880c11507405020a080364108005c0381760001c40041180d115001c094a4040d08145041c58800294401c801c0c03680003080f804090f282090740890510520300c0d007141031901d40321407180c5030030018080c03040b40e0854001e884020344400480c8960550800c2d014401e10201038484074240d80102c006900501070b14012941000020a10004581c000380f18030603403c9540d10340e1142904080d0a01e6401070b400500c0151a842d01d004162031007010502c002e03120186410 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 534042805 1250 534041555 534041561
    0x3111f0f1701060207060305040515310206030705132706240c0c330914010e041e060e070305100b0918010305010b040b010e09040f0515040312 63
    0x3010070180041e030401030000341c0e030018410b011140c1501e00401c06440302e0515a0030b045c0c00903444003000c20061304210041a5030080090700d031943e035403461101d800002907a203044881581c020341c03010040001c16141d43c444c801404c484101003150043d15951800050a0269120100d0001c0c25075003080c1524820548605001084007071350b481ea1942642c14070103c4680d50b40d456000b1b2043e090191003d002c241d0418002800000e0000000c174125920180000700001e0100b07580c0174240303a580841035105200c031408035181e4181c0035016220107001580e0090744c6091a58000b6a06c0800b04607a030450b071507c40c1602d86111000501c4d0381000303542200c0030401480310061605080c284913100c0c80c600d1009d4112000c80f506580c82d01d410b080041c119001e85042414041540c078000b1080c00b07810b500001424900310b80400c81c815070b1400641d03020440114055022032942e0000d000310362207503201c0310858401c0b815502064540a000034050350203540950010750030014007920b1580310300c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 534044055 1250 534042805 534042827
    0x5090105180f150c040b0f0301030c1e030b0c270a06090b0412030e040905010f18080909180d0305060a0e010b0a0e150f09040605090105030703111f0f 66
    0x4005011000c95181c020750340c3d90103014100000701d000d8400900d02607210819140078015024049540d030f443c2c140c20240c550400c2c0070680d4403030740820b0b001858004810102c0c0502008400c1c141107986151103401c1000f000812850700f1080401c51206203600511802e10729402007001d180b100203d03039060002546141e0050320a101000c8003d0000c1c00c0b1301d806a074100e030403d900b014540d40007072504481082917940441e40160500e00f00300d04004041d0015078843c0f44504c410030000c4a900585031104046440141c20081e04010b4000c0c941440c0a030781d0ba1000e440488000224100c03403542e441c15044844510000c0d41d40c2052000c03901d001e0003920300604403d9480015075052002020f464414082c41c034040c00404101210b87c1e07114500365a01244080d9115a00c807000f201d4880c0c419446101e01e240701381c3c0380180218561900341e611030705841014005141541c00c40ea41d140c191900c004103203a20030f6a003408118003000c04048244481c3d5240d59600f1407508582c3c2c0502800140 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 534045305 1250 534044055 534044101
    0x50d0e0613091509060503060f0a090b090c011215060c1e0b0a0605010305070e101808011401240c0615030809010806030a0803150a08010608150108010207110d110405090105 76
    0x10203800c00039680e002844c03036002500c19000c0c5c0b0068403001c808ac0d00600030000c00404079518030003001900280031400300d4040340c0a803119181403103603499020440300d40c3c02d0801c0c1d18003521141480340c1481111716a86091107400003201d10761180318450b0f03404100e0501102d601807140d0400c6a80150b0b40540c8008100a0800303000c42e0a2060700644000034009101d400758485091071105940b2640200e54114003942c40080400e803038004a5010700b85800703020304103070f04000000072030342950b2202d081000d111005801c070b10035041c501143c7d1102c0c408000e0b5020781e1104128104117819070400e000840c8a84241030390341c0282030014281c3c080007414503209802c481c2c441c01c04140d6640490b5807007561449000484882107002030080c5409030031009056280801c041603420000034450050441111845100ea81c2c56103260300740c0c881c84000501c0c0741145022581c1c40e05015810040541c8100c841c8440c80103070b08080f508550f41191921450380d101c1050101d420707a00078070300d620600c003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 534046555 1250 534045305 534045311
    0xa0c2d030803010918020907020313060903080a3911011b02090603100e0709140112080901030b181902070503031303140304050a1707050d0e0613091509 67
    0x1468844001c0d50105102d01d9040d9511410300b845803146020498480340d40c01041220f070b5040040d4000c0d602d820010540140c0c0c1d000d4540030a900e40502d0643e4100c9900c2103c2e1441c00c1c500c0303501200c2500d007440e0820082e1095041540c41031280c0310300484116a244290050302c400c0e402c04803100300c540d021480c14040365800740719144220b100c007585007503010380d81261103440c1d50740443c0c0740c40040f1000c608000e1a100360359520400c04174140046034000352013801302a12504207840046400e20542290300c0e1003803800c60000f600c1c68003031b1030062014140003690f1440305004c1001c0c030450b603041911401c002c40810101c90710100c11010400d418003802c41c02c007072141d42c426a81340b20290940c0f0301074401803c1d10301058468101d520f480304a0b00b843c4c50701c0e810585051651022440b004452805114030329001a00c011015a015190000001c00008000f00c074207840f6080e280300c403c1d400400c10002503004c510001c3e4290000c00810740005550740c075640c2480030341092600080e0070740d42 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 534047805 1250 534046555 534046559
    0x12030306170d030b0f04230601020312071107030c060201050417040b040303030f15120b0106020105040816110603090c130204030305070210030f0c030203010e07090e07050c0a0c2d 79
    0x880020b94015102060030001080703c60f1000207020b80313810106881c0c0c05802d0104204040a24496948000350b42821910054175143d00580e101c0c0603c415203ca4901c1480008815034421120000c49102c0e18068500720307501c035151303d20b4005041e0003050145c0e440f4000d100400605d801d05424002c0c0003544241420308040748422144103c0c40050100754841da40300341c00741440d034841401016541b02c088105950f0b492042800700509070182d8403044414000100c0314010b000c0c80348a564456941490824022151685a10006c0e0b055071070b828016248100d1343c0702c0d00e00840c080ca0b40800140303c031020040030401e02a00d40b4080c840c51500600c420000039401c00c00b40c80711203904654a0200b82c80f2607500314010452044080c00c014100441003c1054240c1c1c0218140d403204960810150344144094509030120310415070000409400903c0325849007001c1c101e10501d90054811040c11501d802c0c01d00c0a00350032890400c60000c0c06404100091001401503040d050750043c01300d8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 534049055 1250 534047805 534047849
    0x60c1d03100e0f03210a06050105030c07051c0306050418260d090f0209010b13030602030603190b0f0f010f1214030c010c08060f0f0f060403020a12030306 68
    0x110303105007000c1c0c0d410707201e006001c00c42c8001d00c00c1c03143c0060a60100da031220181c020b61081c01540e5242401030803c1e200200c1e41a0516000f550107454068458900d50380b601c0340302d03d1031030740814016941c90043d113660125603c801201040741403111398000c2861130900040008568903201c008003030f41b40d1401d094000500d800c1d5840c85a409044076091480c0180d00765400c02c0c440c0d80e6010828500e40480c1c2c008024030102c0d840ca800b0b009880400c80d580e00c5140c081002d01c1400940304101110b03220400005103035070001c552180000d42510540600c1801e5001400b5031380300c0c00c0780e030b040da1b8004000f105080300c0303841070740076a44080b18861540f40c201c01250b04c00c00c1e4040c02c040b0303440a00c3e01a082c400d003e45c2c404d0105890340101c81e5100501c01e01d5900826003aa21540000c0b41e0002281180c0785c110103016007120020b00581440400c20204242040c00010361500402d09101c0080540d58554040004000400c1100b9900c4007a141c0102100d0858012001505044040c0c2102c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 534050305 1250 534049055 534049063
    0xc02010b1e03120409020a0f030c0e090c0d0213080f0d1e02070b040e07020c011d060d06030506130317011202120f0d030903020709062d03020904060c1d03 68
    0x1c449115400c0306055081c0c007090030590003001422030035034009000104004954001c041c035000350356901003601207400f0101c041d980c600c02c48100250780c5961200d01440c040003000c1c0c100300c10006662800b40c1440101e030981e08114421048000030310700402108034144101d82090117410058031080388800e40160a0900200c4802011601c40c1d40c0042c0711030082081402410201c460551a1541c43ea14007144071000c4407001c0060060b021405100c1d40103280e286c0182841005c440c02c2410f40c841440b003a604090704110005454950000c0416018031580e40150112008061030000900b00681000c070b2444148061000c2c120040180344400c0010380c065980c120b03041d40b0150070740d0107080c2c606a808003050407180501e500200130f96802d6800004258030940995000d41c0d0f4844c0500200d510b40d1242108905174500c1c201c2c4a220089402484030340d02a074914029030f143d40101e00c10f5441150211807565442c4142030041d9041010742c14029020511a01c5a1200790007190325 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 534051555 1250 534050305 534050329
    0xf03020a18200d060b25060603050a06020d0b03072306071a01060f08090604080702041b270b031503030d0612150b031507020109021c0b07050301080a0f02120303190c02010b 76
    0x961b4141040c000400161340c10810003103400c9012a80403c0090403c13100075404a03e01c5000b080c5003c3c4614014140411904202c5144020003030008081810004400520350000d561041d010042038000403c2e015207208042241075042c2005d40c1441c202402c40d401000601041c03002d10f404200720000f0014690345c0c091b5101e1070050719460140b010401404144000303600781480310240200d2554000641d036483c0c038420040c071500c0007428904844144540c055103420500801c000741c4040ca03200003505a2080c00360882e45050030348680502202c485800041042c25040391540a100007540c4100301450803e07020840b00c810000020390b207101d9040a41c1089140c00b00060300c2c0c0e4000c3d0300c0714200c1c0c0c0d0094411840003460340800708a0a1408500b2540d1185110124450900c5081075a06132100b40c4018a0740b203402d502c907034000d00440b410490384121190321000003540140091400b841c0c0d040503840f0200480140001680c04910080c1e08680c0350889540380b907a80c00840c0e0030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 534052805 1250 534051555 534051607
    0x1815030f150605060d0e0705010c021e06070807030509041104060807140c0d0905150c07030305070501021c0b03010e010e0a0303020d0b030f0a03090f03020a18200d060b 74
    0x1001541d4403044501034030301548850381c0b040c4041019252040160072071014800e1b110117030380792581c5a00041d1145c009500c0047e400102c1482000314040c08800703271360342058009102604000c440e566080d6079a00c0b0143c11400101e0108440d4098142401452000340b0f40e1050f00d8289170400d02d0060003414001c0581c010000e60192040c09424808101c4170800c540c2000c0c2e07200c5460740c00c8040c2500303585108440c0914082091881600e00744801c0c1c1d5880c541e844003404c249841d40e14221440d4010740c4080e192950300704000000307d09510264040912004004101505010b0405084494180c1c00704010307410001c0780b0005000c00314444040d103a06050040c8c842da00c03088200010b001100311180c051061250741c076041800050000c0c1039602c02c1d0307180c42d8550b03110708608031035403001e2000035009443c40c130050200ca2092241807121000d04400094400c050410981d25441e044444600b5040c00155100810080b40181c002810005030722902d801c9902580c0e020f10192010000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 534054055 1250 534052805 534052823
    0x5070b0703050f091504090b0a0906123e1f120c0c08070615080309011205070e031506040c02070b03070f091e050a091826041815030f 59
    0x812a94170310300d450010541e01c0301d80a03200c0382c50315207020082400d000c1d1703588964448100090303000c00740d000f0b2100360b5400350b1401c0c0f4204a559500e07141c8600c0a01c130030032400c11088507502e13040d000c0c95013039048108185c41082960001001d20100d0301e420450200514401081e00c0700390354000e407024980f40413210700000d0160441d50200c46020311010014640030000034200c2c2031102d990000005400000c0748001c00030340d1044031603664480d0380030b50790101d081205080343c100b00583c0b08036406030140c03e01490f480a03250003c7e091406040e194800001d0382410f2101c541410312605140c0c000500040000c54108402d074402400002c04031010002c040c01540003251096440c0c80007482c401007403003d201805d4111003c00c4015024080c0502d682480009010035940903801d10070820b13030405152400340b171f1620598802c41c00b4001c1c654408081c84d40d03610350ba1940043c8000c0c0700088602c41e0140e0251542c030152944a410140d140d00300c0b800520100341d41c0407032451250740c041002 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 534055305 1250 534054055 534054067
    0x509010f1a3006040b010f2106050606090d03020d03050c070302210705061003060c0305070806360423060a0e0114131a0c0f0f09040203090a05070b0703050f 69
    0x40311a51600b10309415008090911040001d034443c0c2c2030581e024100025825520746040f0f0501104c01a0107400c0d079031580c0d0242c0c010035550760003da00001e01a000380d20303003031882c4042003095508280440050b8403400e10391a85a03494410341d900b0210050f5001d29100c0c00d80c800a660f540b0060300c800c2a030080d80010600303403c0c0d80f401c541c45d20780e000e410380d4020310b000c0791528145143d41c07005071036583c00d09111400c201d1192080a105a0894603402403d48601c41880b9400f001d01c010f0200820b050f00402116042d50140e5840d20442c400d5282c0300340c070306450840092101c10361076003a00c4000644400e500702d4007042c2c85074080c071030001c0040c8503024440010b000d01140c403160318100c8012014460000c429110021907036000d000242e41d020841d030010703140c07860101d83c8880d990344144200d84007050500f004105240509516a013000750920000701281d00c19607440c04941d0150f00800204001801013200514840c101907041110f2074402034034920039040d84a240b0b800010748 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 534056555 1250 534055305 534055369
    0x5222904020919061808070e15010e030609030a0e0a030807170d06030804050405150112022b0605031002090d08071b090e0c03010e030d0e100509010f1a 67
    0x800351a060f203000003491540d0b40c000140440c01503d1000e0044a500140400c01600000d00101100e0985101c140259620340d440c5e41c408030b41b60603a13410001d0716100b1200750f580810520307000741080400756640c1c124004003e440a0140100d9038000c002e0f620003040480d580300e05440c8a04c0c0c000408070b155060a4000b1503880c0714103c8030041084c50000e01005005400c0050b00c00c3d40d80c01c2e5810001034451201000c0c290043e070700380038005103100700c4141d07100d102500502902c00158182c2d42c0340f44511700801e80c80c2c000150099158550f01c207010095407608215460300560700c0c150071440c1580600c0401d66191104401415201e000a410800c200288220407919001000104061034441c1480c401030044418007030420f124140241d42c1525041c8102e03418101114011840c051032031b8100c0d00904210703400b05000c0e00400c110007564210074040c103403140c5801400010790b014201003900466003d1701d02c106002c112041d0000d02500d030030b8210703124200001d1a0248044030111 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 534057805 1250 534056555 534056569
    0x5041401022a1f02060411040905071403012c19030503040b060a120501050601030b04140103061a120d1803030503181e0a0c050108040209040615052229040209 70
    0x10300e50808448203020f0342c614075404142035000e20311503200f488200e0806820002604e51604020b005504200780030040c1c090400512101110040d0000c54049a075008008450301000341d900c803403500040784c00c7c600240a000391030140301d1200311102e0b50410341e10010014000188020f045498030000b18100d590703042c82120061880e105d401900030b085180c618060308003500d0f05401319041000640c1070b407425018008811a0300c64240110380c1c07071a1078a074040e01d48e1a5010b4042c222001c4183e41c1c54030340b404070040540c805001451404e912600c0140384246445016900b54078203a428800254400b0840341c01c0100004c2d0720012400b8030400506023124818031509005425454407404100480c81d0140b40c0e0203071060045040e62100117485104c0102d50003948542c508000900041b81c9500070254080c2d0044d1481c04280c441000c102c0201829101d01801042180740045003051230103012442401c03060602e03955040020101d0910340b4080441b440340c0d8002c43c41070030645410b0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 534059055 1250 534057805 534057829
    0x7060918052806052205060604081f0b120607080c0a0e0d1416140607500d090302010f1b060f0207050d020a030e0114160305041401022a 60
    0x2030140c0c0c0076845c0c0c400d901040200241a8112042c02c0c600010010302c4d040c1c0548003118010000f03041d00c036440800036191001c180b0b081060f002d030382e015181d0071915903180040c115001c590090106050200c4064030740e20703000340003441d01001088821b058650112134200304a0003950724040401a0b4580314290a10b601317003900c7c8511a6000034004002d03003200c0c2200f1078012180804d401c8070000c003171020310300c6860f1700913003243e4034081c0612194010052450007848082c01d01d5801020300000380c0503022080c1806003204030b104282100c4030b44240403c84034072813281081d80303910b8990380c0082c2c10081c01c900c000003846605100505c0d0352004d00d03000000181e10030780801c0031910b4600a14020341012809580d1407003075400c058441030000071500c00e41d40d05a01c1d1010210800b034011511400c4010101c40c2c1800705004040f0f02c4c03210582c0c0a402d4a10945030740d5162400c01c3d00480400c5081c40c0034604541c000600c4000c002401d41864402c03030031402906441500c101c0203d50300311521 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 534060305 1250 534059055 534059059
    0x1801051c02010c062c030304050a030e0612010602010906050106030506031f1d010204030311120403200607050106030302060c04051e0604081f050c121302120706091805280605 77
    0x1220003034180c1846011135045c0740741c6000340049600501c0705a15524001214018401e61009182801080c0221005002d07050001c02030f925100400d58140c102000a0f0300040c00341c3c3d15004000704002540c002d03180035007607034941006a850140006030755000311031451500c501c0c600c800f42c000003105402c203118821040c02a6000000440c050301c0c001d40c4244826000100619400f07000120003086807640c106109924074105420742d112160051507010b0400c548500c1005000746c0d98545c100541341290143e000010032601c2c5003408ad0a1103070003046809c2c240000c110600166030381c0c03145404151400b2100b0000e902d101000708000c1d12a6800800c20b41c0304610804c00b088441e01c00d03c3c500711920100034840380c0c031b5140c6611514042c3c0417515251780342c02400070f507240c1004c21000460900061a11490100c1c1510340d50600d0340e5500101e0028000920500c0002090041000c031498000d800300a01e14201d02d68040802c88071030640d11002040000600e203000681154005e4440 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 534061555 1250 534060305 534060311
    0x40b0607030f021c0512070f050d02090607020904080702100e030a03080603010e0a08031006050301150809010f06181103040b04021e061305120d0905041503050102181801051c02010c06 81
    0x1084402030816001b0103501d5400101c200002100c10f4411305101591740040c4e21103d041601c43c9010703c0c0a03411010300107401a82c00d005510160740c1d401d0501d0300581c051a40d0a543e40c41a005106d403012220b80d400060094400380882c0725100002c5d101d40494052409880a0700e440e0002400f4104c202910748181c0b00e03014600c002d01a8581c01180900c40c200c0c1050300160b80c0d8003043e075550000744a624500c007000c0228407081c03405040081e60000700200006501208055402c0c1218907580150f03c1d841341800119400034154815420b9000019000d581107141c40d9a401d00f109100500090041ea15560318400c0200681d86019500c00010925903c6508a201c0d17400601003a10620744500b01c2085080406e202c0401c07140015070181d40c0d81e00482d81840c05100152500450840e207200710b000e80000880c40038405084000302e81d10394802030312103100c1040001034083e103140003506014801040300b40d98941c000069409031100380040e0502a000680781c4c186807410241c1400c0c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 534062805 1250 534061555 534061603
    0x919021c020a09090b0303070f03022a031b130b031002211e070807050918070206100b180d0b090703050f0f122a0a11040b0607030f02 59
    0x9401e8014103a0501c80742c3c3c41e407a0072aa544140002c0c1d6200d81d05854264004000401c049044c0f1a8042c2e4524042d0049030b140d05010b98400440c242c1011000600f245600034003000c510701849160f1440004004401c408074200c400128541d40035080c42e600c3c00c2e43c07800d039406103440521801d914a10075150441d1149807140c410744100001c1450702441e103031604001016a206002004103082e190705000c0c485682d1208180c40c1d200c00034014005004047c0b21501c029900c1000c01c1d00303030105a058225240c107140e1400703031138084081c000d0090403d20b00c6003404100301890507035500010002c0c2242e80000464080707414103042c00300140100d0010010003c50030000101201140e1060003140c070440f02e10084d0544a00c00d221085e04160000407121502d0140e03000546100c0329610808071010709103240d104021307288154003040d141c1208068201f4011098044981a00b00707850901c0241c4503540001c030b007031140030710090500c01200d4000c1c1280d03108002c0d05508a410103000b40d81c0c1c40d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 534064055 1250 534062805 534062857
    0x1f150f06050403020901170d0c02040b13091401020306060706090c03060f0213050f010e040504290912040f0b0307090506161103070e0f041b060309050f0606091902 72
    0x1d80710340070a034010340b1000c0000030402c5400501c522906c1c0624040c08c0341c9450205c0840b0b1b58410300c0d20580e0321580f180160601980d41420444458103501c00c0040c150041e4036000100d03125003220005141d20520800400c1d844020484c0c01c0d05510030070000d0306811902e860400404150400ba0009141c0034280304880740587c018000f106e42c0c4a104041d169841c010450961498985039001a42140343c4001074200754000540051051a500c3e0000b13103050300e04c2c1488107250001251001400701801a800e5080c04003d0f41d0940c005c00325481c040c2000c10400c03003000036100d05020b0b0328000001131041403091400e24058200100350595901441c5850200d98007003a01c19240da560681d003080071880d001808104036022031141120325a1415051021f04000800561703802004040103050b00103a03081c41c03c060912518001500401420050310304813803000b135000290710040600c1400e699606241d40c0c01004240010304100d299102c1c40007902481c40060b10100d03005000312048 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 534065305 1250 534064055 534064057
    0x60306021b01060522060b12040309150903080901020f0a08220503061b07060f05010e092b02010609020f030f1f0923100f081f150f0605 60
    0x10724111010201c01041d12416003200d4080c410280e205529100c0124400308440120007030b0340784100000348480d900e03503510301d0a9016a2a0039403100d160020841019041540c840180440740004030798030000940c00342c01510140406044100c0128501c40c1982c0300700b104045101c40a0141c96440071030f8544112103401040381c800c0b980810080030314100c080c001c0702408542c0300900400c9262241c0c65000c580203103000000e9918070041044001292140c061204011034404001420358506000c0c590120b0000d0f140307401980201c8060403925400300d40e00240480c941c0700441420002d0b40083e401085036501c0f1014890000c11b9120b20603044c00003862003816001040c0001c0d5940a00c141d400c1801064403d10f4443c05034401e02151031581d000840c2d995074a204900704c40071103000205c440703200310303003400315198a070303030103000c400303a01c00b0030300d0003044100d00414800140340d07020210444160340130100c0e1a030714401801c0401a444040300103151091000152a03102c083c01459 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 534066555 1250 534065305 534065317
    0x309061b02100c030207110d08130b0307090608090d08061309060b04061d15010c0209010e06040e03090d02010e031213060e061206010c0f050f010207140a020d0209040c0906030602 79
    0x1010300e0144403050f510701a000f1180b185501481004101c2002c00400510040c01042980c0c4041d042c042c54a04d541c03109040409418524085500c070303c1d100c10010020f054580100c410884102c0c240001c04c080041c0b01207820328103040c0070b4919510340f4003042d80d016070304884807642410401c201e81800481d6105000e00360050b40c050003041c0c0c58044054841c1403545984101038000340000304025002d04407807021030014500502592030784d8000600e00103082e08074404e1020060140b000301e14291140340700710360010b0701960501a0410020300305030000c02c401f0741400303902c103128001c6550034800b00d103131030100f0000181c4400d0041210881211345e03000f000046021070032030030301030310300041550102e140e540b903503038000e5507104011601416503602c216507205000d9165030000e031040c0040c40c1301d10003481c00144c07a8025400c1070524080f480001503401e03004000d02c0c001588860001656058060f00c3c81c807050b032107c1c980355403640000c1c0d211001140c0740080c04001c00880b038004000d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 534067805 1250 534066555 534066583
    0x30a0c180515030901020409060e01080d17160e0d05010902010f02160603020714070603200309061f08010e15010603050f0402040b0f042c1504030309061b02 69
    0x31406180141034415a80901800d9802000c01600001c084400002540e01812120015003000c0d550042001600c6158001281c0d41aa02005101a032010410030b61016803500c0d0006485404840b0100841000341403000c1c2c81c100343e0b203039140070341c06202c1f0390340c0c250006883c5246002d0176003070040c001c1800e184100d0004000003091400030f4400613248285901403042e4007262032401e44164000d6100510031a80c03041514054050340a09100e150020f0076951000b09800c4101c400240e200403555000060100e802d1044c440d0f0712030001042e5a010076500c1201c079100c41000100002c0604942c4203d10540c20403043c6114040080362032180c001c940500050a40d880d03010503020f07107004075059020f9400c1c400c001400740c80d06800400034a10080c0001c0c500c1c00039003003c075050b250004110340c0031400340e9800300c0700303000d100442c80c8848030070001402d43c03c100c01d0210141c02d4000380002e400c02d500d40c0c0d4504203000141d1702c01c01d2504034030042155050416038000c1c0d01da40c8400d0b2500707 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 534069055 1250 534067805 534067817
    0x160206090a180c0e12030d05040f12120e0a030c06050c19031e06050306040209040311120705070605090306010b092d09150d020d050f030307021c14070204090f0503030a0c 75
    0x3160174280022940c1040d00b4140c0a542402d080400c0700c001000000d00507140540001d50010100d20050760095440001d50340e0080c00f030000c880548103860035800c5000841d8000585d00b404282c1c40200c506ea0b927540804017042d42e40700c214240c1c4042c00b42940c4030302801060340a2600440e055440307013107040da9004410903102c000320525000c0381d501d4070a20303806400c0500018014500000c40a5000b4402d04089a0069803492000d02d071411004e480500c6500000d07001083c13000c00c0001c1c500404580c50440c5c94601c050021076203a0314180305142c04a940440c17140c28540c1d03904c217041c1502c0a00c01a80c0d01d00204500010400c603950034101d030044184c1c00102d2452028980402003e074005005811100900e6007401046000d141040e61580518500c00391180c1090000b9805909994001c00c0500c800c40b81c2c9171021000481c4881c00d01030311a2405003405402400d64100315012100090080382c0742c00c01c207034421100c4c07c00a260f404000108603011031540e00050403560150354070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 534070305 1250 534069055 534069077
    0xe0a120c0c0f0b07080a0c1e152a05070503180f0f031b040b090108060f241002150a3810020a05070f090b0303160206090a180c 56
    0xc448650085907100b180c104803d001043d00ba00003800c02888502e4007800321240c40e111601c00107c0c0030844107a01c030703480c0790b00307814450560800284100c198804021040780e5818507217010072b01c0015031102c20704900340b48019a001b141910000f58205099984d5480c0c07141081c0c2a010035505d4051190102d440100305074105a079102c4182103001e0b00400240307940c1b030b20f580c0da0401c41e02c0d810795100d41c840c0000c90154480c01ca58500038100c140040003142409000e004100303000030f00c9010120b403803400301c107200d0003031501c076020250701900c003845401750300300b812418502e540103200001500c107801d000b035035001d41d408481041070b0140028107009010101101c0f444641c4840c4102c0303800035941e10250301d080303001c0703041c0d05038140115814103506541c0c040c01c0c0581a8400907141080120801400446005007441c0c2c00044014510f4140445850381d416034510130040c0c00fa000c081440c4065860b51280840944103902605c0708124842c008140504503503503014000030460102 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 534071555 1250 534070305 534070319
    0x50d0f0f0b180a050c280e0603150f070c030c14070512010b0105030406022b0b0f101209060b1203041707030f0f0303020405062101050102030405030a060e0a120c0c 72
    0x860041682d22402400310a41c0c1714040010f01030312110650800351034000c1140840c1400c090b01d10080010842150300d600e04401010704107140807121282c0c10504408120f44101d9440c840c80e88802c0906013440410703070300c0c01e08607030301e44110b1001409648101403062114038000b8104040300e07021900102010704800d6050f003a501c0f004501e5002c00c80c180301140004440ea0040e2090311100e082a0b031101071400d001d04040490035461b81581c80c3d6805015105040000325001d80d40c6099441143d0b0015001000340b0101490003820002651041248200580c2d508001051040180b0224180540908150f200c2e40107108900c0d00e10a032206000915201043c00012280c03c140c1030160900d03162074030410400c01000440400d542000042640e54499010f0040030459101e0303000d24007992521203641c1c40040e00020705641c0148000c000640d000111480b58036401342e40894140b00040d14a4a096100c20004017110000031070381502e241e0040c2e42203401e500800107210b046a13a250 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 534072805 1250 534071555 534071563
    0x303020f0c1e07180209030319050a14090a03060e0109320106060203041e03051515030f03160302010605030a0321020f040603111201080c03150c0301050d0f0f0b18 72
    0xc1100c0d44402461800c1011240d1035006d807181c1940a4252450069000c1646030001c828514500200f14040741c04402d1692010704109010303944941c00d441e1103241000500e01805920004000544400c00502107020030341080c40000e9001181066a1034003640d00f041d042640082d1220401118415001a8405008130302c1280c1564000c0c0d881e0a05004070401102e90801240e10000d140300c600200040c0c2c2048011b40f911403c2d0b01d1040d03142009020f610340300c207a00c0d0303034644294880c0c4d4aa18107550044200d50746030580e5800c0100203034041c502039016164540c000b40d814000c1900b60424940c01141080c000441260303007001794810100380000301d02075210748400e091001c0c0320034080607009034045126203440c00ea00174140010254441c6481d907090300300c107120790881005c00c1543d040070081070054106ea903610500511b00000c09113004c0c041407103101d10888541000c1d5080c01080c0c403c801d00740d904801507100f205041d0800b4a41c2800958181940c136054080c04c0050a03004a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 534074055 1250 534072805 534072809
    0x1b061216030b1f0c05030c0f0102180907120b030f030d050603010b100e010c0c0b0a03091b030f080f0f030906071404150e040b03010c030e0105010b031605070303020f0c1e07 76
    0x10608042c0b03c80040031508210103032801c650a100401800384071510401001c400c0204200015960764009200e64449445480c000fa000e2240c19060181d41500404101081c100003c8009041d11205000074a0b208001d689940b00707010003e50071000455a410151140000303400a00041c01500e003408070461039003451200040c045090002d840d8411001030080c80d0040034080b85050302d602c0e1080899200d4101480400d0b500e400c2e02c0200203042001409442403600c1aa4816103540c41c6e1440082811000034030b48400055070600c06401e640076689154041d05034151203141c0143d01c15030b6907200785ca0700d10128148d94024450000d01c0811181036922a101452007040e4890040c0c413810506103445a0081d1511150b0880b924241324480b8610840c3c0c0d4003041800380318083d0350131604103070010742d0582010410415060b40e6020140d40c0310b00245055036940001341001c4000340920020109400c0c4002244c01003400c00040305800900303501854104082d10b01082c1d9614080d41c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 534075305 1250 534074055 534074089
    0x2c07020106180f06120b010303080a0b15030709060801121b0e010b07050c03120d0f0e12070b06040209150310050d0b040b07020f0c01030908040306020307170a0c021b061216030b 78
    0x6c00014030001c0d20841c603940d0080c420b150041004502080010740b1501c000811a04203031011017003051803584200740d42d0042406003040401941010308812002c00b09010140a034620241e00c420b01e20810041880280145d10000c0b00303035611809811840d90040c101941c51380300b00e001c51042e0385008115904200320140300c0600e49a03000041502400404800703106c420741da1030704040d02c0d1000740500151400030780c4c00690380f08024a81300300071140141085008034418012640d1544800d4100c3c1d0900810907619031700d82d40d4900c602e40d40e0721201d0f00000d03084103c41c0b84000030813208001490140b032180c1d0350f050303180d44c42e40300480e80c80007004154101e030313404051407a0440d4000e0341701c41c2d6450b0143c070340a481e041d100e80b5210281d0f40700b903c031140083c0340d0755a4002910404003c1d00d03001401e240742804144c0004900a5840300d20f60307069424840204504045990740004a600030701c10400c2c40350141c41c2c406800c4d541060484100c202103420801800030070318004510007a80728003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 534076555 1250 534075305 534075323
    0xe0c01020f0313120f060c0e0109060306120f1e030e0f090f0406021309020f0703080612070b0f0d0905010e10090b0f09010905060f102c07020106180f0612 68
    0x44d1036400040c201d460001aa101c0142440c0040441e48501070a00344900b5030310b903866250000c6000604410172503200408042c6091001d00c440311191112140c49500040c803540c904030141800b40c6008101c500300d91801150941140030140c00243e90080b440c021034105211242107800d1114a00d01150342280300a400c60014001540b07a501610070020b4482da42c00400e0780301c51420080340d008140c003884402000c02c2400c1050b500c42030540d40844103883d041c10214039000760130740c1d0300114000c0400c2501c001c15115461b2480303000741c5404e5102c02209101740400303424158002c0c00085041c2003680a06070f583c00482c0d810703004611840d0341c0003032503104a69400d440394070021070142501c4a00e540351007101020134001c000c01401800c00b88a68521414062485544448142e01400d00e0201d1b500e441d2000020b0311804440307000b85200c4400940d507416504900500c00c9402218241ea03040c41050f11561190b8010310104c203c0352401c000980d01c801c0d11411418901400178000342e0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 534077805 1250 534076555 534076559
    0x30512130c091a010f0e0303070b16090302031507030b100c03020105010e011a03090a1a010611120304060c0e03030f0a14040522020d050106110c09040308011403030d0e0c01020f0313 80
    0x100c91003560f030381ca04070382ca0510351b0811500c0000f401c55100030300030303540d0b6130608091080810300c0c000c40014247c0c290600640d00e61455001c00e84901d8180c07000d401003440c81c00000c170002e00039004805031160040419030030810454000e003802141c4441a0019845c003400821500072a2010780d043e6540b1403083c652403007180004810a61000301080214000c22880c01f0019040c0d203410814401c0700d040c2040a50b040000040c80704011660003241c0c0e5102211030a400303054041142d810580000c00407403c004507500c01e440c29100040c4d80d54041c440003500595010042c070192450190340d603036034403402d4109044582c4500803805020380c4882d100c1c0e04801c02140318220510400000c684c05800c01c000d0003000c00c11240241d0100b00403172001108240001001d100c840246c60701105c0c0340c0c0f09824251030040a034801401601102140d40c15074002581d4200203580d2610004038081c8602e0b00328044241e2a4000700c00414094440c403c0614050b01000c000e40303d440c9012446608014 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 534079055 1250 534077805 534077807
    0x5091005041404500a11100201050f01170a120e10051e131a0d0b01030e060f150604140901060206010303050a14280e0301140112030512130c091a01 65
    0x1201814500c00c0c4050399040c540e4004c1090002c8800140075840c0c2400f040030900500480b0300b4801d0102d42103901d00010440014100f411407410349a0102640c01c0c0502c164001030325100202c4005000e0184540384501d15503030100c20042c15000a403988101940f124802752030a00641c6114030001c60001a5a81000440400352076994100110703401003681d1260f5100c4615a070f0340f1400e850781c2000544000c80019406010903120082c0303030400c81401d84036012600c03500003501900d00b00c0d40101c041842c115541a1851081034003d001a940356a1054a401c4087c00c21090714044c034501e600000e015800880c0c028120307509901c500340303402c5001200301c034025100d1105030b0704590188062260045103007000201500048108816900072000c05007040c034101c1c1c5a144207a0500080384184400941070a046035000d80c07103003010848905d4180d03410301811504001501081081100e00e541040054000d02d010b6903d44244a0710b6401d10004c3c0c40156040c9a01e000c400303100c0c1c480355 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 534080305 1250 534079055 534079163
    0x1a03070b090d0f0314030a0e0127060915020c0a110409050a1101230a02061b090405040204020f0f0414010201090c060e0301090c0909140c090105091005041404 70
    0x185209240c501417803204600c802110741c0040d28282c10145d61020f1071950742d2024410b0400c4442e0188030341030038204005c0e41042e603014640c40140304949030310207a0300b0029180c15480900604000c150344501c92201d100d9070b240110310040da2101c01c1c1088800080c01d080c850006d2580d00440949898101501c4151800e044549141e0402001c500c2500195150000203003108010f0403156544048a1400a00d810405081d08404404403020b10803c0c50551085800c40304050b1070105680d039917070000170001d02854408100000b0009104000030145000910640d104007d40c0c0f4030b84d9404e01c0049088449a450042000e6180c8406000381405046208000c4e0001000400d041c420341d510090f411015a20036400c6a41751003503030042140d40e0036010201500305006005a8414400094800704103108442c09030400f40d01184940761120402070140c100603005003c1e62545481e0002c0c8851b0841e8203503a83c01d40c0640c926481d060081404111174007071043c84030304280c0f03100c90300b1034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 534081555 1250 534080305 534080333
    0xb04080a020a02030d080103030206060102070b040611010b04110408070603020c060403031d1b030c0103022a030c030a0f080c07020a0506030a060f0e0108070b04120f11041a03070b090d 81
    0x107520422403041c006a42c100103540000c2e29590703403000c00307500d1442c003e440d01d1000341ca210f042d90044e002c00d02400202009441c115003603450300084003000b549210340186090b0000700e80082c2408160301c1a14180d81c0100216070310b41040312082503454804900728021074600d80000c0e00450b01290101780320340c212030042c0102c2200400301c4402250390b5460242c07122600c50030921300801244040c5010310205403122000c2c01c0562620018120001c0104007400004514210041e20449088410000e43c1c803038083c01e008a0340d40301c50f034000140400c40f142908200040304038000400811818055401160380034000d5a29a41458100000380d0401400001040d82c0c4210009000c0440c1c203039400203100240650701e05504140303019042550a030004051020704000400503036044c1d04403c44880c0d000585181011070926281c2c103800d00d03d1030025889802c28202c102c04000f903824004803444110100c0d44525516000003109000d55030980f90301c0502c7c0e0b40c2d00c40c0802c503a80041d5103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 534082805 1250 534081555 534081557
    0x1203030f0f050f0a05060117061e131e060503030711012318040c140a0314010602061504060f0b1606050108030d0f11071b051309021305040b04080a 65
    0x141e48103000c0c110000700e420444115052555400502224011a02c681034115800f07280804403100000707000000c114014007841d014000002d101c881c12086554451840c400c02010318140c250440ac0701d501400c0f90342e030b1141522200320f500b0b107685411803195204441014014504000071511145000b13604041401c1c10301c03005402034581e031700d90200d01c60a00e0510700c4c900c5031034030840f4400e0316059468000721b6000341d00d0407000b00344654002d8254207842c0d1007050700da0359030070001307a04130080c00c407082c1c215015503000800402c0558000c03070028810005454130044240d005804c00c0143c50300351080c1040881120024016078074480c008109502485c4000c1c91202e142d41e450b0000c65000f640100130a403c08200d041c940c250900554800d5035000740c0038805c1c10075110500c6907501c104480200044204085850350b1030186c2d0880e0020b020080001e04681d0441036000040c0c88900000c9100e1240700021007501c071014030403140101d03040000e840c1103035102c0d0b480404945c04050250 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 534084055 1250 534082805 534082811
    0x519180f0c18140f150f07060e060a1116020301180b010e090718020c2b1211072d08070b15030c01080a060308030915101203030f 57
    0x2103496030502500c0041c42903680c4558840c0d05500d946440120150040c40c48660300c141080b8250340c40380250145004111180200c1c1303200c00c40e01c1c099500c90b00d402a0b203080c80120701101400895849840101b5100098a40b00d9032410408800c88608618106001401388108101007201511902100d44060700001d08008541c5034840160203120303088460341a603000621a5980121140d03803c80031a10041c40840e04080c0c0b40309071060080501181c4644c0030400f5405200d0800c00304801c40640907041e041d4035407510000c44811090100c440200b03560712000c200044e1644216080906540b04850034070b42d844d62030720032545c140108406080f000c11031070404040e020350702c001c14610030342d5519a0383c4018a4801c100c69030062940074001c410414100e000c2d200816411200907091915402c151b40f11080c51004014130340028040107404010401500c10029154121000d4081505503560780c4c5c0e0a0201c01e0140381c018242c0540c08005e07070740000703400303a04569418002d088000c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 534085305 1250 534084055 534084071
    0x6090421020703050703060b21030307030c0c060e07080115050a05100c081b070509060d021318080d0f0b0a06050c03040e07030c0f02010209180c0d020307080f01051918 74
    0x2180741203074031b810a484155840d0b250807510314040d0801d86d0f806551500050200c103409165030303101e000041c0300c1002c1c10f445160803000340b4814800311501c545d0000701003000d428800000e581d00c9015000fa04600e42c0b07402f058000b1381e5444c812580c1120f2000345101100c0c0c0c00d14041c8091841e85840381c0c0c061000803c240c10000790010040c0c50040c2d50f800050804468020b0b90909e0544154802405006500140141ca841c2c01c84e02c01f440b241c0503110361450201c00800030004148820980c84d00880718a000810066050010045042035201c203204164801701d080d4220350145144562150307250004010b00e0340120040c1c400b11040c072096070304191707540032009036010040340c2c0900000d5a4012a40c3d41d150820040007900b0081d00c000c40c1409295004642d00001183c0d5103010001c011000400450140d800c0358880e8543c140190b40701d06068001a142da4002d440b50b14200b10340300c0000c42d20b0b0825500c0f90701e490342c4054919441600c1d00baa184150103100c1f11120300c01e41c039038802d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 534086555 1250 534085305 534085313
    0x80304050114131e09140c0304020d080f0405040f06061704050a0c0b09011715010c02040e0a031e031808180306010806011703030405030904020c030d0e03070b06090421020703 77
    0x4410300420100810041804400c44c1c0b121058420360081c00301c03c1d1518046400d9801e0000c18294000c28000d034141c0e4075151400011150b40075400c00800e418800118040c49014820140013150002e503020700602c000f400709101620150b01607000003a800b2201c603803540c4000e0360010b400900030820f84114044c50f0b141c407448400030f41c0208142c010300064070881568408003000b1615403540c1c00c00c503103042c6010510030f1901c002c0344a9042006440c802d400359a43e5030301003011468580101d0f00c48040500e00940301e02411030301d0318010408002d142407020700a0182030f904603180f090407403004400d951003681c0354000200e948181c11180c0401c8100c0d4400700300303080c0600a00700080020303614080300185866a0705159240320340045c0180000541c001054a81603d021240540c5464481c03070070700d03c3d501405500301004c83c00e044501090301008401000018041c0c4074651290b43d039002888155502541c004207212505400c521460320302d40507442068040348140d07a00d40e55a511 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 534087805 1250 534086555 534086587
    0x2150f030a1b0507030e01081018060602010c020304060e060d0b0d11031b090402100201110a031e02120a0504020319031d1c030e040213150315080304050114 69
    0x380518116a07200408204100b5001110201040c2071a00780c2c5410070995000302080d00d071041007411320440201243e42c07441228074000192689941910031160040e44000c083d0000c0d11134000554a8500e54002e014804801c98050356a25150200f074048464103000c419030000750038000703150b03584042445580d80c5071180401c407805448040484071202d400c16040c00768600604441038052401c0c6800c9840e1900b070b00781d02c140c0454903ca003007104043d042e8094100c88001d00c01107540081c02c50900354046c0d215240c41020100d5a6102c5140c1103074100480c416002c0c40c082c01e000c20400074448101c90b41103540d1091001d03003580d070881c01c200085500ca046400b02100030404018098264000c00610b10502000441d06150f2440001999a0301420f9102014081001040030301c03485444680441e8160328001a015840701c0c0c0d01c0c03000b100714071288100080003906044008200d0f84c58804000c042c0c40f0542c02941c605403919005440500110343e040c5400741d820700003080c060750654 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 534089055 1250 534087805 534087811
    0x15141e0f090405060a15110708071503060e0708062110021b0303071b030924030f06030510020913090f02182401110a050d030b010c050a02150f03 64
    0x400c8103619031910300100000d6510090189008150041d0208441440c20f07070301c0690702e01181848145880da48a1550a1103015044003031188900c000004054031508110401020b040e9000c000c240c0d2255500c03018410709441c1c0030006040e00b0f0100f901c4d4500b04445100b01900728070000000f09080040e03030306011401010034486980403c22550754030315150210074445440c0091480c620300003002608103458800d002c2c1808010345410130030540140e444001407e41d072460810303078103506515044410007050034800007d0600c1111001c440c5280584c00542c1e5011010f40882e00c2198102c0b03000390452100b00d80e00c0303d041080030510321000d04c100a5418050713104140003080500521900c202034800184138041d01400304035500b0101f100e141c01310360003c00191034070610100121150717440c141e00e00106000306a506810007100040e8a128112180c40900080301c804005540303016004601620315000981700d28010b00d4084c03d020802c00440341c40604100c00c008665003550421 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 534090305 1250 534089055 534089077
    0x50306030a060f02190903050a06052d180a0308040312060504050a06031b1a090109051e0418050a1506081203090705060705032a15010f15141e 63
    0x11042000890320303045e403420030340350300f08001d0403817540e1f0320269035001c4c0d05000f030001652003012400d44414801c010300c1e10998251185e8030401c0d4081990841c50781520038005039101c5c525403501142d0082000b0303041940540b14265642e40302e880540c1d101d03544034002c00aa0743d80340c07000f10b0036a0b03503031095030700a00300e0741400648103003585800c0c44c04404040240e10f500e40581000c200041a00b0401003d8410401e1980d45506c21072006940010503600410f9112401d02c588040001d40b05040b8003504000300c0d018003070540c40c090100520200e02101900355003140c07004502013061a03d1401c80b042c03821f800060031640d20000241018003150188000000000510041507403c000304006898111912403602480e680c44594034441d10140c4c02c44d030b0001002d480000b1036218022211003101c0030030754115200409822805010900a030306030070100c500040743c0b0b100601e510070010341c03490300d80c1030003145040e880f80c1c0c0039041214032008a60040c50b1001a24403003801030400340c040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 534091555 1250 534090305 534090307
    0x1f0b0a08060f07030e070b0d140403120606080c070320071d01060504120f0f02091503150403080f04110307060801060e1207051005041d1b19050306030a060f02 70
    0xc00030060000b10107400c0804140c20000d8100c018040400c0c400c04583d0090303c9555200312401c282009081103019003069044124204001d16801c00c0d0440050040f2a004014a9448200c10380f210001038482c441400400d00a100009003e041c100c01110444512504a81c1580c01c409103400c4154000715001240480341a00c400314030341350507026000c0e90510758146070520111000c4c20402840250510501c507022a0910520302c04043d40709401514620302440c00300c0510030b214410b07040c02e50207031087d0103c119012a200b0301c0980201c0e070660b10108652210800502c0700d030406401a2800055082c110245075020002c60b001843e058803003000541c5082c0300504071101d15040103018549014003880521400b140135000d441d030072200300c2400800500c08481c18001c981003115a0761a049940031211020300c00c0511600c00d5000c2d034120302011001d916004c5c021602601000000f1070580f03002c40d0300070ba01642d07100f407000d0105d5503204481e458650560382c03010850104164 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 534092805 1250 534091555 534091561
    0x30406020f0d030b0627041d0c030c0f062b0501150e091b07020301020f031b0412060903030221010e0901150b03040c08071503060e0106021f0b0a0806 66
    0x806000d500d04055031403d0800c007102021000c10014410700310b010035070054990000c5075076400c0301c2c0a40b01440000e4030800c0f8a00180304000901c00d10000b950100d84940905040b9030f150008500990103405031585828009400c1800820303049000c1c103540000303e408038195100325154002031034540303456010034607525001c1c01003514540082c0920410801d8544d2882c41d85407031541e2908965480d030b00041c01c01000d45410514021000d009515500003d02440c190040002550140c40e40710b0701903401a482c81180c1001d8400c602c280075074100c0560240e03022841c4c40e03100030801800303420090701d00695214086c4201484001e0320808040e00380c010b100302c04445c00682d5100c80303258001c004c00842440c0d0041845103900c142d80d40c840000001508029070f03014a400104006070482e007946446040c2c0141c1902070301700c031400280c6010f00c006600400740e60854100c84050b0003401101400c1c00e0900300a5680e001801039041e02d82c103041c8416240da1a01c500204000c00260125003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 534094055 1250 534092805 534092833
    0x3030412081815070318050d03030911010309121b06050a0504120305070c02120304030804060504090507050f0d020a140414031501080c1903060f0f0b01090f050402071403040602 78
    0x150500426019440da96400310042c5010781c204e40102d40c145c01e1101032450030024040c90b1100c0ca40142d03030044c503551016000c06030175410040790b00c0d00c0380b0008048550030308011002c5030304400b40500700719009548501f9441c090f6504170b0101141d1069091041000d4540d038058400135034401e00c40c40da8542c00c00040c002512089e600042140c903043c00b05040282004251000585002e44207020815511202c074404104880c000e686c00007029071030355903c41d00a40b09030041d224682c0000c0c20701c00010800b621910031181c0c0e00c02d034001c0240c18104024001e40003034001c00d500d03505105055002d00700c0800c01c00c1c090401040e0004048031640c00800606090012105108459482241c01408a07020204540703403030080030b03140561000112034030074000c440158005000c0d54039040c00c59505422a070404414444050024490541d04100466070f000080c4101c0002180104041c005450560014098039001d82c1c44900701120b8960010300b5903000b5403045015038468600c1d078144c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 534095305 1250 534094055 534094087
    0x6060e1501180e15010c050607181703030411032514060403050304090b1306080714061c180203060c030f0121060b0a080d0e1318110303041208 63
    0x21103a10b4141094249070111480500e80003802c560585840120840890b9119400420301c040d04003080303c019051128001d40082801c030041e109030b11700d100e030115942440c401e2a44a8028000085180d0307901c98403071500702c000b0799036426031501030810170001d0003d03011004035074401001e44120f1001e14201d00c00d481c00f04001040b501036034050100700702049020080d9411500246800319074454460001000c14400d1911102c90924200c404600d0907400038440d4103880c030729003031629282d040c4003c201c8180501e100445418104031821146101d864014881a000060380310302030071083d034000303420200100c0301c045203981d0100410280e04084110180180401c1206c3c9802e41c4104031304031150301c0304a00140210b51551410b914079214942c01380014140981580c82c00e2030350440041c542c43c5c50301e482c0780c4500400c1c0f011000d408191300c00c210320844c07c0400711591440c00c2c1ea40070141440d80b600150305020a110014050130480400c242d21880740048560b80c0030058900d00c60703 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 534096555 1250 534095305 534095327
    0x905061222030c080a0e220605060903032205030f2107031d061b01020d0e03030730020c030403030f03180308040c050301020f0c100e0c010c06060e1501 67
    0x1180e080803415102081c1c0015a4449044d0401c040543e42c5401c1142075a502c1d183d02903040e0842e00380c1004401341c4a900780c0948210881150900050b0380e120304000c4280560464640d0680040100030003519514103600300e80c1150201c03c9125998490001e401c0c910407400000701600711410030074080390f00c101122414a148040a4200921520001e0800365503547c804480c0c0c865031548000b0317540c0c180503201003400044141e07074941200b5840728040d400040e04c2e0f442c0d40f42451018a010302021042c1c070300c110303000d59a001188000145820b0140c2c14000c1c50150302003803c010582c0e03c42540024075905498000541d52180b4501d402006540e25500c000100740c600028003075915415151027110f2a0545080105034449040612220166034819a40342d8400501c404003000010058100310700000c00750b8003054a078804140a59034424109401900701e03a41a41441d0f00a844100209000d844009049074030783c22010714a076003d5400c60606200041810002e40e406140450 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 534097805 1250 534096555 534096601
    0x606180614030a05070608090304090603120806041a042003010f0609061d06090102150f190614090711010504150c110c1201020c1509070e131209050612 67
    0xb031079a0044c0c40700340e00da40380750082100300100c003030201303039408000c0041d0740180c210f00c401001140d60303070314180d0311007050004140085030981d00015500d01d0a8400c800414902c501070a0826034018100b000800740040d60382c1100350891080440500881c0156001c4c1081114003000c0c9400c110010340304031410b07071016007080154980e00c050b400d81f4408003c51010142c40e01c5465100410060b41002101000c99940020210030409003a4000e941540514007020792102c000c1c04038422001900c0181c090b005800040e011186158104805103c0d8452030602e412005651000403e900352041601d00f035843c40b200406100c1c00030010321411007440703101c0c02c0882d4200100c03403503541ca03116100e2074244619111140c18840100a404694181f5941d1090b9000a420311860210015090307032412003602c1100d0000c546035070303030700303034107030052020030244d254480b59540d1304041080a440c211041218000b0002103c0d103035a000340c40c915441a0703140d0964500b21f04003605a40810107a00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 534099055 1250 534097805 534097813
    0x140f040b130c060311160309060e150301030b0c0909010306060e0a0509060610110304090515010905061b120a0e03010e06070c020904080f0a0c030314010f12060618061403 75
    0x220025180b8001e5004603003090401061003068041d110405010705036840d502c004200c000502055440800d44003500c0442d1a60b102c609103034000e10003c3e68084901c504803050800050000c110030310825540700300340070030303040c900220080455a105400e91040302c80da5207070001800910300d10149658400b00e05d8500308490320b011200940d4946016007018000d507555412802690301c155580c2d081114041b00b103e13a541d503904200401000308031110340d500151003105204640c811890030003103540c010581e500340806d82d0340d0a0340380c448003804580b55120b958112683c3c015500c01904200304039803184010b080340102414291203408146101070f070060410064490f403c00546507a090b0180e07080040c695903440c081c0901d20035110b0a01d0b02d40740c040f96400b5059440b090240c850340c42075405028000d0303141c7c41500140301c20301650741c0d0b00802920034001d48520603c40c40286000f40742c040f0340c0540d144d00b0144503074200c0b050341008640700d101c10f00c101c5490301d4a032680e00b00158020 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 534100305 1250 534099055 534099091
    0x4031401051f170a02040c021b030105092d060403051b0c060a120b030601080f0f03030c16021315050a05150a1b0b0903030415150612140f040b 63
    0xe52110b5045010b100390001e4940741120900104000c0308540640c090400c00c41c14071040c07806991800c0d07491004505000c8225174001505040c003c3c24041d90b5040010034141c4c040d1140c24043c0580b54403914136005a04414050501e0108402070140380661240d03a070b103880900541044484101860926502c402017038402070b201c04080b20803040151030240719203a4844d003120060b15800d00001e074940311320000882e0340c042c0402c403c15100404000c5034400a013000d09a51280002c40d10480b03584418455011590b0002d1907403240244010940050b00300c030035030f0080031203520801080b140340e4079134401e000c0c1e420907540b003001410084508002000c2004201071140c800d200003481041074101144500000b0a00342d100c45984c004090348091900c488203942d607400884c1d09444212100b04c092032414014401d190019001a1080d61914100282600c03c41c8001040c21080c40da1200c4005800c80040240c5000c1e00441e0013031003050170b050800908011010b04120082075841d514 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 534101555 1250 534100305 534100351
    0x30501060e0f010806011817010e010b1e061c05151918200a02011e06030b181c0207050906010207120605060105091206060306070f090b18060403140105 67
    0x50507a00003070910f000ea80007c030b5038140211119003541305400c14203d03510200044181034100310700f08030441008210901d4080108184c4250320034004800d4940790544821a04050300113100410341042d20141c8000140d00300c1d0200d5404417a058200040003114084034070702400f520342c2c0f0004d0340712140015400c1009045041e000b5640211070256988107240f111074030806800c0a402c1740321300e81a29524078034000f9001e4030031074451019100c00d00d01d10312082000c91081c0c405aa4004420803081e544042c0d5100c8680042ea48108240c0304010901c04225515002c040c2500d10a9001e403080d5890403043c0402030700c01401003419900700d100c05025221900654804080d0407000c0030406444210040c0d816100303029400f500000c9020505040c10000600c00780a81c0c001d0b402c6564035a68103208a0742c84131540c00100001d90041020040c0342000005400d0f0181c040e900000f10040403030004070380340e11980c0129429a0300d01d00d0780168410a22826a0200161106500f11801640 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 534102805 1250 534101555 534101567
    0xc1a070504050f0d0204110d140c0d020a18060c060509010501050306160509060324030c1509010207051f0f02160308030403020c13060f050609130e0a05010c030501060e0f01 76
    0xe0b550040d40d00114210240da6140001581d203600034004002201050080548503400300454002d81418a140501489081c1c4209072187c42000403690400c5208040c580c06503011381c800104200c40008641c0d80b90039240520310040c640f030780303500981c5140b9160040030394000808403c5c1507450704004120780c2d10045101139209000014071001e1280300e800c01e40b285c0c0200400e0603007020000c000c0000542d1240700846100c445d0200d200d51600d802c2341010390340c0941940481d041180780102305404031241c40907042814050055800003626171000c07440b42c00c2c41c078410340c900440d08030044000a42000e08240d103d4031361b10182c288403800308014513030a2410711000384400030000014042c54802d000c185a04200240340022001d1203c4000f07000d407103180151a002a0f1824000034140307004801c56514120150085003d5180c180c003400c01401c41084281c4140203501d07403440026420f100b0602010340503100041c480d4127242d0010062040031a0300d5004d0501d42117a03c035240e801c08 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 534104055 1250 534102805 534102809
    0x50f1206070e010203040e010803090112020a0e060d09020904060902010305130503030c2113020103060618090911030a0516060509090a0b0301200315060f030a091a01060c1a070504 79
    0x1042c0500c440540000403499031180342e0002e07011450304000030074807031000b10051130514800d981d114070904c00c150849049104990140b008644041001409400e22001501c038038031141c0390006001c81960049203031044211021100395036540010400c42d03805114141d00300c10130340c001100740c1c003003a41e660b0f50b28400070300070811507040411483ca48101c80081e40d1100001d03503c034507049080c2010500c040c203007046d004030b0100c0e081010125a151082d5100e40d154155906018415850b040380c80d0010641d03030b5011f0f0780070070035001d081b00140c4003008035942a42c407640c002e094039102c84e05a254856129040b0308100f1070104031320141d47e5140c00045411080e07101001a501c081b01d0002401011094081c2c80001421a000000c0101e288007030740c42002503003007032207900d00c800c420070489106151043c5c104031414404205440b04e81c3d402000341c14811b980350019181c9030780d040080014241d202c2800650707804888010020803c600d2041080c0c520005a07160a207014040d100b80030354 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 534105305 1250 534104055 534104057
    0x821190506040216080904061e14040e0a0803011d070e060c0f070f061e090314010f021b010b18070e01091d090616020a12180f050f120607 61
    0xe4004654030780e54a40c1110b0390030700b0200391540724441d42c0c030b048200380d04a090554411403034250001511559005003062500030528640c40e101e08008425a114807a2480d01d0b030055a40c5c2c17002661054200031074440700e809100016125031401ca540c0d0007034562001545503001440041c41400c07600b003000441c21190845000d03444549101805103850001d1030050080d201d051000115800b80c850740400b13580c2150307907074062101d1150404210380c80f150203000004102000c10070200b0501010b19848128130340000c502c51200b003580b00d050381c010340300c45281d070002d040115811040912078244c64420984590700e20300c6100304107100c00c810080414090003850080c2100740d80c0308a03104030150550600300010400301c0100d80e80c2600045401e01042c1c41003101213600e4455458841c51030305c07000d45c0103007160304036640c42c0c98448098030560000c0c00010f058041c40040d07010b0038400545110488004590b01c0c2104100c10008460000b50044810301c5c031102d40824045406a400046 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 534106555 1250 534105305 534105311
    0x1020d141807060909020f0723100902031507200304140d0209060907050403080d0b0406081504120504080a050a020f010c020303190219060e0c060f0a0305040809030307082119 77
    0x9019101c0c19036108030440241034200041d2030427581d40d244050300905950f00070450780314800504200007141c0f10120040d40c19031000c0c620800d01c244081545901c02d0306460800c102625641c01074040c200c1c0815a292a50030206040c07143d0000d246088404400813250854031507002e8001c0b602103d005400300d4000d11900f400a1401d500640403100150751000e40d0950322001d14000e040188034001c121841241801c400054420001502d40011507109030b038583c141d1903941d0b5800c8407000b40034070b450500005020000d01010180020308507540200090407280740e45104100d007029071111014140403280309844050b0310300106a64081031422a20000c003e8a06001d0f45806144410318544061001040c410005030303800000c0000400c104450180c2c045104014840c040c02110100001050116126441c402d405c1140c00a0080c4043e03498030f0a07200110b81503a00c441003e4070880b1000a01d080030300d4207082c0c103d603035480c400c04000301810b146090807620040f0212030410651 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 534107805 1250 534106555 534106567
    0x10c030c030516030503010305060a0903050a0804020103110f1201061416050a02040e24070e1e0301020c011a040c0807080a0209040c0c150506101101020d14180706090902 75
    0x80100100d51548071030703c2e2003101c00702061a00502641c001d0000301c641c0d00580022568040c0c43d40124000564181c885034102801c4220031504c42c0c1c0010004c1c2c2c1016180d0b0340d000b17200e000e9907006110710229003124564880003440c01003404841039110204000da00e41c07030340c80c510002c1c0b0142c50907521585064100c03000e05040540c5400b0303480c0e9010f0b5000d454000d000300d001c0c0000401c000c02180c1d6502020501c100701b16144013100b0b085071308001041412220b81c0031458401c1c4040590800c02461841290038940841d0880c1c000600d0344c5203aa5440000160400350388407650b0000d40c0407a82805250300428008181d0140500450103003c2060082030b1f9061480d015500b540402a100b040449590307031340244285805031007591010400d03120210030104c2c50144600c9014003070715200c41081505c1c0200c40e850032044d5511599503091240c940074500d0307406600170160311035110485908082c8000700c0c400c0a05440b241e259031008404115240d081030080e0115440b2840041e1600 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 534109055 1250 534107805 534107807
    0x102011a01050f0d0608010203070507051c090e180f060a061208070615031208060108010e10140303120406050105030c1f0503040206090612070908012a03060e040c050102100b010c030c03 82
    0x42186d800c44400c40d40044100f082082e40b010181603010300a00c11075820f0722500003003441c0087c200c045400014402d0406001300040003518a420400451821031900050103001d8140702c681230044115800060034811030902074000c02d40a06071100b40e064401d07c003076a506100e403158030b42c02410b9a0f201d00c810202031440940900085070032159170302c840b0b00c00103401805d11108883e00c07070105103c140041240a5a604194800c0c40c081103580d40c0c190809941610802201d43c56a40c188020001865001030035400385018910400000c0360a5060108160600040c403607000e0103000b603000d001004042d0b0301034003d1405001d0910560760f0301e4900202c0c60511501404903042040000c10003c0740241c60000d40c0f01d03a40c50340e41e144017151609080d43c01c0c1e4601c2300d0444007801146603c8003580240a0f00c980f0300c60b490f8100003031071903561079818041d03550845050b129560100020001542c05200764500540c41150030440040101c0019001d24020440501008100c5e1110030401d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 534110305 1250 534109055 534109061
    0xc03180209061203040b03101703070f06110408011406060a081302030a060e1006060509100e040b040504030c03020105070807140d0603150614300102040b0a0e0102011a01050f0d 78
    0x3d910610166540c0e503441e6029a80e03280d205807684002c0c61074280000882840640d880d00362402c10304050b602d0300d45540c644600049441c9030940741e1940d00c0240384020220708000300001d048010000c103000c80c411545441001006103041d008007030421604102540c85411141d00c044600c0c05c04600c07101c83d0000c039280204d6064014030592816030700c0880020002070401c072038883e02c0e50500c2100d86a1030216103074000c001846800000219950840b90301440d00040c200320701410004500d01400001000c3d150140c0b025004500d070340b100320051543c207003e219404405420850018281110010300b04111404401814407010a4102c0b02440300d401c003c00440e00401005501101120078000404151194400440028801e0300c2e690070510850303800c900c00902003c1340e00303d101c80f000503201c0d00061000140d56003007001144650700d6602410402c0d00d02d654804192014000280c2190595030740340035442d4508a09060503030744030b400c84119052540d038003a03c91030354481d1000030f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 534111555 1250 534110305 534110329
    0x3040e160203042102190303020607030b120a0f051908040b0a020c03010e0c12070b0405012102030403030f06090510050411122a0a14070c12030801090c0318020906 72
    0x200c055a07135203200010b1001e850403986140201c40c07580800b40d1500161036010164800100540c0040c0d000400c4540030794021a54100b028215030201030304e6495441c00d21010300821540040b042240c54180701003008080c4140200001c0b2503c030440f19182c00c3c200d4066441030b1206490002001304885200380000741c0f141401900a01543c0010380805840c0c4e48095a414000d4404690910020000103409422034018200142c60241041d00440b00e40040310180303a482d011080c40c0021041d51440254422400b0b40e40000e2018194008042692160751000c00041c1c1001c09011003442144501c0e01100c4084500042c600d000c0e440d60949401142c0c0c1248083e0f0303401c020070907100c1d0858102851808440b0340300791003260103220707090b05005206942000800c00c5030140f208003180402401c40034025a0f80b220700e0750340c409142450388019002100050403403001000500894010030800c1c0b0f80a0805100d29101002006c2c00420b40f400c000e4818a61880491617980303d807420f282e8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 534112805 1250 534111555 534111569
    0x6080c011d0f0d0b190b010c030c12051b0102030621060f0a0f06031a0f16180b0d0b0307080105011503021c0c0f110a08040302061e0408100e03040e16020304 69
    0x2d0526010171011025130740c190038016018106485a1001e40c410400f0045040c0d058a40e604450701946a02080e00b960701c4006092040401510300382c51100305942c49411012800503075685400d806000065200e840c0b01d2004c184210050f00604c180803464651041020406443d640d82c1e0080d410040c116078484041484c0c42d1034030108c00c1c84030f0b50001134450400d503003003082991908841032800314411a0b465441594281c01c100b032141c410030070b80e51040c80c1d20200716041c1e40c949548048075805441245165a9140705c0030242d814203000401c010300260000f0000303585800403030407074000c1c1c17965244200b517400900c0300f4220040b03492040c244200080c00b00107040b0340d090b0107480c3c980b21902001c0400c1d0922008180707840c001520305051640410740c41c3c00d281c5968240306141d04141e42e07000c406500c501601d2903078030640001d040100034010050035540381d54002e150444450340002c030309a4000308414030140c8005281181c0040d8641544584115510760480c1180207940040e5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 534114055 1250 534112805 534112823
    0x31e022101060f0b0c120705030316050904230906040c06031e020309070e09030c030a080405010f0929130212070e0c07020a0e09060f06031e0106080c011d0f0d 70
    0x2c5660041c0344c0c081c00d1184106130845400e510f40000c01d43c10382c094058000d20303a500400000b00c0c4440500300301008141c1c18101603003028890b90029095030080705d225120606104038400e103a058144103a50400c01e524040c00640c00c15848138a400708040c0110001d040d180c0c584003900d12800d504010030880c600c10304545034180b0302c41c0e040d11010300b031141c140304107940404a0501c006c08000c84150103c1e090056152108002c010303203e031b1000820940b1155611001c90900070b035075001e030201e5640300d4400864001001c800300c0c409241c07072002205910707041104101080d500351165083c61a0121000d0303042c030001141013845c0c0820380d085002a05907000c140074900d0780c02406000042c0c401c03154944021f03181c1c4d20060451a045484141305c0c0d201d04041155241c18000301c0c1e40107840075003640c10403010000200c1490900582e140f119030f550302000c01070784100340000017280c80240382107980341c0341c00ea80d01c451080711101038512031740c0380030940c00842d0381d6003d601c1c007c02d80c804820 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 534115305 1250 534114055 534114059
    0x110918090a1709032a041d0a0b0916030b010e060402040b0d0b040605060316080405010e0a0b0612060106021c180801020a1205010f12020a030b0c0301031e022101060f 73
    0x201c0300c9508034207200c03402441760501d56080c4c00442d811040445480381004d01044140f00304010280c40e0410320f203858101040344114607090180580c07120b0500904000d003c40c101200103500d010036510707081c1140801c1042c1400001c5080c07000c0750460f400780c03056240c55150400002d00a01c1203a05c24a8001000600c10a1b00d811640002d05d401c50308440c20000c09690b24103111061004a4962102c06c0040d90390340991130044551503042406100001080d1031680c00d904d140c1084008140d0f10384203501e040201d0b51030100201c4046404c040d0262015500d01140a55500500d80c0f014221a00c400110346042e8403c50036041800540100c0c000f41c40d52310803c841c000d600002c0504005401d20402002e40300e00e900820b4100d40e28001c800030740525001071405d0003030459034102c0e8880130003003000000c9a000310101c0d0280241080e0242c3e69491481c080e03526020700020301e000d11440d048140d016035100005e00e01c40d644203d01d0926242e50000c0c580d40180903941000042004041e80 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 534116555 1250 534115305 534115343
    0x706020c0304170616140318030406050711030c03070303050f1e0702090f01050112090501230915070e04020a1112030a1805100209180a090204110918090a 68
    0x30101c02c0d0441d5800340d0704c40d61600605200030180311181d49000c11040342841c1c0703403004610000e550003003008503880e020005603422141140d000303500c800005007021032040705110307052030a4183c1b100d00b1002090b0301541d07100480d8aa020620026052000100b85130690f00405001c0310038030700b03ca41d242e140c20034100303105911503044460141d0080c60b0450024074404a00c15509050740c4058603181c10040c42d41011401600a0040455565485144022440c64001d441d4600340c003001e1704810281c9820071141c0e14103800e604010151000220910a421703400c4100841c13403000558003d80d03035009442d003c0c0e4074520310300c00d2141c00b40710b113891006003201c00d00051401603082140a000854008103021036003c1100da02402c3e640069242452442141c2c1c000e02040c8006854440b0304003414445000d0150110742e4010f960340c8445c494411880d061054134010104052a2030030040d111010500c041c9940400c8080007201d00c01041d41c942c0c00304900d0700056032000d5080365071140104 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 534117805 1250 534116555 534116579
    0x204030b0103140609121308030c0f010e0d08130807210806010c0c0510030e0f030d0b01031107020d03020c130b030706050405131104090222090b150706020c0304 71
    0x210a40d80c2c0d400c103240d80c65843c00f010801602480c3c03590000e001c10301c0081c0c0003d040b40d100e202e0b40b42d801103110800007800103060018143d8400d991018000380c40480300342600756013040d1300c466910742012400320b90007904580304580002c40c0a4040594010900e8203550900c5070000180c48100c10310040c003132200c08146242d410160551f9078041c0750b01d941300107507030180b880c40008040b842102d41c14061401c0200003a891001189800b040020b0601882410102c00906101d010703040058a418122441c5c002d503090303604213103002c0000130b0000a1016150150b000020f204080381410f402c01d00d407003001101c4d15464010300c13444600210846040c01001c041101034068001c9100019244d0b0143c000e490403180007511304403042c0c6076805031000a04000408880743c04e410700021804100a10240054142540035181119040340d8480c60b50340503948809442c509140949160713485901080e031015043c0c240030340e101c01151801da000b13801202c1c400e080c0c1703200100b40003505c01c040c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 534119055 1250 534117805 534117809
    0x9050f010b2b2003060604060c0804150c03020d17190f060605040e13081207020a05032106040504020a051c1407051e0904110d0c080c040b060c070506090a03060204030b01 75
    0x510401c0350b6443c003c56540140001c45902d58800303410310003000480d004841405955100f009907a00c1c154440e8401e070400ea071407121800028003120303224410903130100107884807540c641c108030300101500101c203238149030000c1042c2e12002940d10014a007041702d401c00d501c01c10f400d040510025032260700040454000703208825a284081001c6031450002c00344010601e50044c11551134585030040e1a050240054a190704520801050b800458414006422400c1c100304d00300e03c60040303002c880149240045c017920300c40c03481c0a007800011ba0300c140c020300c11200140c4a41d071510141004140d01a03403141405006400391407110f48551a000c9110410b0703580c111075071030204010401640c5840c0303030840e801c2c1e00702c101400441c02151101071850300e81c001c01001c16401100598480e002611182d0049640707600c56480820a0324242c01010313001c01c000d990050510070500310030742da110401e11909014440004444280c1e499980080002e17640080c030945d5103d03528a40480381d04824 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 534120305 1250 534119055 534119081
    0x1021e0a0210060503030d091424011d061302040f0308040807151b1502120403020d020a0201020a140102070507030c0504060504020f03071d041d0709050f010b2b 71
    0x652810614042c42c2e10800c81540d501800560074191401c0e90000100401c0c4e0041d142030002814552610b0b004000030410a182100508612003801c20018500c80c0f0680048202203020684200100d55100c0032540c081000c49020385803228a2a60780c00074421034009050090b141080402440340f108020310071103c05030102c2d10501d40da00681a000740c102c000200001c1c030300c10003040204003151a8038000300d014851164458850015202c1282e0105420f040c02c0c002e041d00300070501d501801114800302990002c0c084401c41940000e4846004034801050122506806d03620300d0000d50660303011540c000101c0300c815071a420f080c3c00942d84c1d8443c05201310305140300424241003c1c001c2ea00028105540c1a0135915654016180071301604601d040446442d200d00ea010742c0c0d40c0c040c0000481c0a03040302c8914424400d100d0b4201021600201c0100b81000d042c402c1158080c035850341112001c52000b83c440035800d8075500790011000c0c90702104541c0f000e041440500b154000c81c145888 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 534121555 1250 534120305 534120313
    0xe0f18090d02161512020721091802180a080a061b050a0302030603010b1905011202030402010f0f091a0c0c04060e060f01090513060501080f04020f0d020301021e0a02 73
    0x40107400301e80d210b11040c038000d1100d62203c02008440740e8600725484000740e50070400703d10140040041e00301e130462541681c80c16800c1402042480900e03c5004d40429507140c0010002c2c00d05210200948000c18a603191650010303031030346020100c60141200e940e00411080314a50354415080e81c0e0b01c05c08905846451501d490039424180042c0704410b141d03140d03121613050a8050000740c4c0250001000740e9099522100c41244690f150240281203143d00d000304043d0354202000186072403681c0c00c08008481c0b042082c0030140c1c0e0002041500d01c071a524201c007a1111f03140c01228441601e52001c0001c200202d40542984c524901030421010120300315803042d007103002000203442c444d00c5244504a52400441e01c0b41c01c00440c0e0700c1c00301606060a003049a0744a020990300c0b07683c3c4010742191945e80206000541c0d01c4000c0030380111764804140c455040c0350300000d0f1294a200c448600c2604511034850440d1020340590b00140e00550040c41e01804000b41a28950300c160206401401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 534122805 1250 534121555 534121573
    0xb12070206010e010501030c0e040603080a0e090103020a0e0c04030b07080609060d020904030f0309050f010b0109060c050d030218190806070507050619111c2a0e0f1809 74
    0xc80001c0c098129100700080403004c3e442e08005400403c4006421800c00079080f07070080260b1114002d000c0294401c400700c55507001007420052002c004c080d00315105900480042000d41c0d10540441c0c165800b00842008648032012000f40d2441554401841c411780881000b0311740b500525030902c242e0095955903003030340d548000c01404602050000f54400c50303c101281c0400c5c070501e945c0415000314140058a20015210149001101c084610b01030303440e01c03011407903560b011340103000804d150b00381514140595502c4641711700c610001c6008044d03000c030715034100c000007280718035030b107003028003000313031214845035140f28240346401504840c2c81402d010038242c502c200300316a10190003a0180a080c0c80e40c1d02c541403034100d6406d564040644410094010f204800001c000300c0b5042d01806101003509214082500c03444003060b556601000e004000c401c1c40c01b0100c0e2240d60207881c0516240048178000340520380900300d401d0700300e0180180001d0801c4000c4985008d01000130071101010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 534124055 1250 534122805 534122807
    0x30d0e0304080a0f11040626120d0608010b0102030f070308130f110301060e0c040501080c07081207030b0105070c060305100807180b0307030201090e190c05040302180705031b0d02040b1207 83
    0x611a803040507183e40c80313043c218010340606080003100c46148c40580b24481d03440201c0300071642000d80a032001541d40c2c00c08212021702445070424404081c0091800d02c202c030b0340486014007a0b400054244001800000c3e002d000615040700016030040c9082d410354440d08000559020315007450780258070340070012418402d250b01c03680c07140d1554010545068180001101c2001c8098240c100c0386109001440000381c07600040e244101d0540d800900f540b42403000101a82e0000c24154188481001340c10041b0745811008010340d0250b08010900740c48000740a0441c03c040da118025034098440301080c0c03403480c2480d00e028200755000910032103c1d071504160309c1d4121440002c1c003142c0d114904103c400a803150fa240d00c103110002541003400c24090000c1a55869403400002a00015040c01149000105506450500d03611b030b440314502a030002c0c20701c0c40050070f011a0004e036102121070326003488049940c0742c09010b0095440f80d039500e24209040d042410800ca21029420003d8151 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 534125305 1250 534124055 534124061
    0x31b09061805060316020a02093912270304091a0f04180b010e010501090b030f280603081209030c100f06092a030e030d0e0304080a0f1104 61
    0x7842d401080c0a01e10307226002100703000d0920201c400150f01900c0e000340056550241c0c2c8500c90052603e44200324113402459801082c01403a5202344150b0f07070a0340305a6403554406503032245440c0302824000b40c84900f40140e0b0b8100101842701569002c0107000e0010a010014101f2a0403c40040c40b1a0380c1038244041d0100c1d0942030a40c0103e031302e000c40080d601d03103500720b40b03442100c02c060024007160350745400101200903048546c0c0383c07100000400242d603011b6640001003508130a218110b082c58115680e50090103850031005004003020272654050141225560800c0810208025507480c9804525500516020001090a200055102c0d00c0110440d041d101040f405804608188591300008000c0203a4140007a40e5812000c2031148030761184036600b040b1414140481c040d1500c0c502c049544004048080500341420140e480740000251f41c44108803803c0030420801d174071401455800755501036004d82c8901600380c0d052050415034004c0b182c2c06043c030000390513140b2040c0025 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 534126555 1250 534125305 534125309
    0x1060317041406031b040305030a080a05040807020f0609040c02010b030d030b010813061503261e09030a230c0a03030c1b0305030d1a0a06050712031b090618 69
    0x104075a0741d0000b882c07460004021540480c51100084403020541c1018110b03400c2500211b845900000e20700100079040b16205a00c9841010180710500d00380d501ea0700640102c900090140035455038802d9166104416105030740d02c094000c00ca1403014003030080c041c118034000d1900038009c505040010354840d00460304c2106060712031401030740f03503218201d40d0240703080030a890309591040541c00c0403940c150524003c5001d042c4032180c107115858044002c2c2c82c0c44402c1e4440e4001080428044907003031805410205880800c0e0b9141c10801c00440d0400000440c000c1c68128141840c240000c5000c02c00c201012001c8101d89030000064140b00c0fa000c030502000e404141c41203042c400040c0160402a110b803c84465110807039035a540d060714503040701c180c2600a5071036500a140001150368182c0312100d04030364406500d03103800005000f510170410080e00e011a003254118016000790032040705259000c1c00ca40c505044000001c041c41540d001e00300000700d29640020142ca0b54100f0441 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 534127805 1250 534126555 534126569
    0x905090c031603090812010501021e060c0c0c03030c161502030409020306011709011a04141f0e040b040c0608070e0613080a0c0e0906090d031a0904050106031704 71
    0x201e140c54a8403900d01403401994010308258a481e8110005005c100c09080b04c85412554200745d035041600190401c00c0d42c8213800c501280e1000261800c010004046801c0310303413460219502ca448500c1035092400ca034030300b10b130548400910030407a03c0300019032200041003c6680302405447d0f603001046012010141001a8402d0000f0710001256900031900200f05041c91404070020400000e03002d1002c4400d14020395588440d00c240000c240f40f004421a800c69003044060190b901000803100040e1582031614000c2000204c0200f0340702c600c101401e1240320a900c98540b074070b0b20703040c0c4410868085401e4001e20000051243c0180b09043c02405180c0b911000c41940b2410700c601500844131090700709020300b5002031514001e0140a111501451009944508001c0340224101d00500303201b04070751010b0104481201c000c02c060b080c80d541481c02091110300344911150b0070760045c245a0703000c10800103000c1003000550105048a00c03501c4400c031840d0040c008071406002d94480c1075 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 534129055 1250 534127805 534127807
    0x4031704092d051008060406050702010c0f0504152003070210030b03150403030f02040e01140901062102041a030f160c03210203010308040314010b0a05060c100c0306060905090c 78
    0x82c501c40d4003500055400078a441c80026220350f03407a091460700c041940d044c0d4890395a0f03001c2c070414660a00801c5032151003400c08038610742d80c14030010018810380c4240c5000d260044011440c441c868010b400b071038801400440407a122252401c0e45030340c00500200e10404100c48080050341c003901a122604130001c024084d14002c405816000020080040b420903a49803a64020802c546c4080c2c000381406114140c0c85604003c05a92100034500d41c00b486058040010031140c1e9001c01868424002e5064500002030b1305915a03019000d6030f0411942400c0d88500302c0e01c0c41c06d0980c051071240d5140d9000a14645413800c1009519000154550000e0300c0d02c804400131034041c1c0c010034580341c0d42010009101c5a50310019040360001c0c1c00454050340005410070a0012001c022010894400c000304180d40480c170018400c04142e20465006820200f009200b41070300b070040d030b46a181d501d0001d001100750441c2c0140100b00368050140841e0948001081609040300d05612901809442c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 534130305 1250 534129055 534129131
    0x7060801050d14010f060f0810052208040f0303120f060e220b01030309080d05040b0703030f0f06060e030f0a1505060d05030739050103050702030403170409 69
    0x801c414035a00038a0355840d41d02c4003804100d61a540c440c886c01026428400500070381441c1055050200b015048440c050400081c4640c6a0070011000d48000a403c0003282c4090b940c500841c04d40269442040c00c0d84100e04000207043d044a01d420301c02c0c01d107080400c6542800e600c540c007120a00d0007001e58101c0070b600010881080a0700b815008494036869400300782007665415883c103400d8008500003145030b40208014502017143c8600a00c807810000d080504000030303042280112940542050340b20040042c5004440c3d00200c1c0784030001c0c506115580d100d103009170402050b420842d000b4461001d010380f64000203c0e0780381c06158044013160f91040303001c2414028090140a551b4414038120000e03002503800c2000388125171080840d00440d104000c81c034001c00c8078080081c2211010207240c80c60f5041086910f405031403090900141c43e440d81d410032071450203140c10090003408140b0901900302166005803085480d510801c0c40854a0390326415454582c0e0040c2c03050b140310300502 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 534131555 1250 534130305 534130313
    0x512030a0c081605060108030a020f030406020d080703020c100b030708031c050c1c09031713330614060901050d0c02010b10080f07050c0a031d030d050c07060801050d 73
    0x8028180d50045043c1040d58191201414000203911131403c680c40040c02c00720f5103405120a107203420350702000e035081a1514001944408400035a40c0c10081c20100040080d8000e506030792528010304121030b40308000b20a00b00080c101541418841e114080000503c9a030000072074000c0e005080c001c40d880481048031794050030014144030003000050150403680b0000e181c8600c040090358401041e01781040c240038003665000100565006c00d02c00c03c1101d44020108110411342d40048280d0003082c000e10701c4040d269070300c3c01110a142d4142c44148030101980c21400c240c034480d00c4903075000e0501c48100000c0b4460007041d01d0100320144074921124000d64842e04004070b0382c0c000803030030400781000548da40c1c01f500f03055401310340040144840c2c17092a10b182c640c081e400d0308025241c660b0504039103540b40c492000080c20400851a4039000840d4030803106010396019040300c0c0b03004002071010b0919008000103123800d10554000003000c51190329490704030b44028100854020f01522 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 534132805 1250 534131555 534131557
    0x905070f150804140f16090b0d020d050a0507150306140d12030b0901090f0509070605030a0209150d051905010302130f23010609300215070c0512030a0c08 68
    0x10a031900c10f049200c40e0b45046041c8a1180b80510381e030068041d5034002d031480e2011000d1504144200c0d403034148c0c410703100c0c0ca4143c01d4054150f01101c021031340035094074065103000003010000b0300c1800341660010724051182424040f00d01645c40500240f501c50400c0340400c1107182c000ea80c00800070388044045442c45543c00c541ca035045c5408a00600c0780004030f84401001e80c0100d03605a607403a039000d0380c0a22441043d400021200180c440b8514241c4020040d00002e072080d0900c641c0095465129900e50001a162043c80c013881030b01c4910000002e4024502102c1c0994602280627221520725854400c240c141d0717038020a15000c3c80ca100306000c000300248891001c026640303500c444101e1107000841e000c0c106102c6060a041e40c10f280c0c00a004106590120350452240100340d0212001e042841d0142900d415100c2c440341040d00002c0d9405191440d10920610001012030a100c25091400e06031807080c4d500e40180d52409202564900c82c00b0920000a80985030b50700c00604008 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 534134055 1250 534132805 534132811
    0x100c02010512010807030c0b0304030c031b0c030f0209061012020d060b16060b1518030a02091303030b090105010203030403121b0306030c090608100b04140702010905070f1508 77
    0xc900725060030900e803000d10702d5a9081e0072030201c2d80d0010400f003007001040d008003800307041410070803419070038142c1e0094040480008000c0a005da8100c0342d980b4031018407444001c013a044030000030010390301d040c21680c80c61902002d80c014041840050428202040301a0b02024140c0c0c0c0c40d10444172504101c0000e4006407038550b22142c0711071002511055850280903034681104200303001120030301e0401c0c12592000d0841d8014032285940c44042c02e10034013610f080340d030300c2d07005003600b0142d40c000241804e880b040d00030360000380081440813000003004000340c401e1080d1410019040d070b030b208206a0200c00d00ca500d005078801c1002034000707031140c86111104015480301060854a02d00c0d848110300d041580030000a41d180c00402c1070003c580140d0009040c4448100001c5007822142070f150040d09855651b030a465143c40c0e103ca403142e0380324202c1020f441c40000e4030f030b0a0686001b0701034401500c09460074070500b040803490102c00007401c001c881d03482ca1801a001c21550068a50042c01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 534135305 1250 534134055 534134057
    0x3070305101509090b0a140c0409020d020c06070917010b06180d02090901020c0c09010b1b10150501170910150b132102060a0806121204170c100c0201 66
    0x6203900141500f0741c0d004038822244200003050803460034a000a045130701c01c1c400c1d400c00100520130b204040f10007904a6041d11005900503a03070b01c00e000c510001900c10200c0c54450740c410a030420280030f43c8071502c0400d0310400710108480d65002024582aa440c200c4c44a501c40e03820008069886264040f203099507001512281c48900703c7d80014900110481c0c0f1000d490350000760040c000d68040c4424034920804484c405960750400c20944514000d58050f141606061400c2c1d02c1d2012003004508071400280c801030108907001c800605890380e80384501c03408590b10349146038a1b48072804079148103020502c0280740c1a015954440058100128207210340851900082842d803110401080007044101c030041d0403518100e541900e2007000f14107185400028450700005070f5929044a240401324540303520961940c4002031004581c0211400491060381040301d1b130101d090000c0e10440340c8119055009410540005440d00118071300e06074400c0010003a80790440c081c4402d00011401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 534136555 1250 534135305 534135341
    0xe0307090b0d050a0305030603070807290d1e0f0c0c0b0601090306050405150f09030406050d1e0e0c0d08040b0d09021825020c01080406020c07031a01050307030510 72
    0x40ea212942060f81d44c100c207400003040041007107914102000940c00400040d00100b420340c1c40c280e0704114003042c4a061f02083d4004901c0c0e4481d00b46120140c4200c0505c404040054400e1103285a41c504058550351580703500302115102c40c0034407807141103002002500c40c4500d101c415a9284180980100814140302c48044080f012800c0c520a641c071461140006101004614181c8280040c00400906245800b0005c002202d0808030985085070b0440c01c206880d0f20130f40e0140c2001e00107540186050782c0002946d1035201680c1c2c0c202c03006041c180c9050b240e01880d2070040c05030000024002034003154080004001c944481802001505140707000022011066070008e22100309071036580190540860901c8019517100341800d10460301c00e201958a454440000f94551454111060510003000c0014013400740c2901141c0c14003603200c0c2590b0125482c1d241c6000c850080d00c074015140d6090000110301810700090300e43c2529005030080030320b402d15034146030280002c2d807504042001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 534137805 1250 534136555 534136579
    0x807020d0e040f09060501090e012003090c2205060105031005090912030103050f06150904020108130c06030c120c0c021011011a01020c040501052421070f0e0307090b 73
    0x81c9070b00c6800b500e44d11517500416154541583d01040d2495074582d00000d0b45003c0c8c142c05e014a0ba10500f84a0603059807900b522956507000d25414550744421043d0071800308640d04c0450304500d64410880a81e45004108588412004498502040f281c4803154005084140302e01d01d0125002e66000303807a5402c8420743c108005035009aa002030b4011107c1354000b04c030700040708000b80807955000d410040728612007059140042d809000c090800380c1482807050103d00105010224150310503005004a04c5565070760500900030089002d1110016a4000818480c540d0a0185007008011a070300d08014001c01d07020081072082010646003800000b001f0f10034810710030f0213036141d894401044420314003440800a8108841d00b062184554035200040c80a0340e95002c10180310381030005560007030070b44460145a944108107990911300e80d0074401c0320345440068081c17403184031140d440d44804201c00034140d030150350700500994150401141400144843d602064030200d0040000d10304503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 534139055 1250 534137805 534137831
    0xc010b0312040518040f0b2e1e0b0301030618050f0a060507260a0e030c0604030207050111030d0c0c140a20060d05040f0b070c120807020d0e04 63
    0x1924503200924020010800b0080c9140507040030700c42c44c241142014041ca40740e500c0103402c0249a20003030030701001c0c201050300500c6220b0002c11b510b8440217080034166004503298181e0b0810b11500c24100c04149040c9600c410303032114101150001c110140c1940d003150b4900700a0701505100c0d40380c074040d216850020420400c245901d1208000150055940d40c2c20f045043e00c600900030401d1002d5024114110818001000025103400390706000c0703074807600480f1001d0480310701c103241284400716007800390010204131140140c0c071a408603005a966140150f0301040c03039149480007078000348280d00308031506070024510084580b6010140c83c07120343c1c030a0081d555542c2109142d81c000b07429a404c0000d01c15100000040d582010842d110200c0d00081d02c40c42010112014540ca03800480c00304034074000120125640700146858603c0c0c02e200080510f1801003081d108400d07400500c040c000e0050f0f1141d070083ca400d9014005a0082003401d5a440c4100030940e0b0300142d460140b5881e074 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 534140305 1250 534139055 534139063
    0x1227060e060304024b18100b1209100b0604060e060409020a21180312020d0e03030702060a06030c03020118030c0b1c02181302160b0a0c030506060904020c010b03 71
    0x10004403448280500c66500940a0540744100c104140080e060000c035160313103103820544040a4404481c0c6c90b030342c5071401c030714050003291f200f0b401c451404500351071038810403000d41d44164103000498201c02a05940c40043e590700705581e03078002c44200400d0249034030588041c000498041d120514141c0e81d41400c50407640213081c0000000e41c2d800020403149542c0100000f908004101488290150084505001070409000b03040c4400c8082c004040c03041ea4040d5900f01120070420002d4110260005482e03500403542240140550300016240c0c800f103115203030581e90060b003604030b16421039005499500d804050300e00b1040d820140000001c864010f40c0d009854000c1100f51202803510a003410040040b16115406005109400c42501285583e00c0d84881c02c82d401c0b040b040414602100a00c105201210f0309031300c85001001b400f143c1e51040b805041c60b00d0701003054014926049080b14400d54581d40c0c03012003040050317054a8241c024004040c0300100010316803e403100002e00d4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 534141555 1250 534140305 534140359
    0x20f0714120d0e0f0d02100209010207090f0501471306030606090e010e06060304030c050a0c030215190e13090b01030201110f060c0f071227060e06030402 68
    0x609500d41c400542c048100313100e05488921084000e018025a9900281d02c4040300510010819400b068480d09030303100f0401030004110740d8408010050450325001e0181c0b10034003030511000c0a450355103403050903080fa400c0826040358520107040030015440642d4507174044d044c40742c0d11000d10a0783d00719080e24180900510b400d840025406103007078006440c000c00c41d40012040700741c03007004014800c2548965a80001d08a80e156629504c40c9400d44001288510180c03291054698000401018900c44001e4038002c8861030004002446821560b115000d03030300b008030f20701404045649010384030f106840d010051100000c074085604810884201c0002900d02021000c010429941c03ca03004002400c50703d000b4003000381043d040c0d0ad5803024054410502c0b00700010724030210303104a60540300d5107680203045038a069403052008100f40320031408248a424402070f011801440a0b5440e0100d640d25218503007950262070402516070002403081e078103c00b0008071110070080c0300c40d020b20 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 534142805 1250 534141555 534141577
    0x1208090916021e0712050a0515011e0b271215070302131502120307050c0c011e110106050d12020c030106030b061002011103070203091201020f071412 66
    0x145030704110009140007858200308405031031514281940080100d0b010042d00c003805024000508185412441c02e0700040c0050480e0203051140000440c11030404c2d4100c50600190030490021000c100b10503542c14450702c00d0ba0781003041406000307001c500b19003d090403a80ba060201141c00800304002202007000d42c80c541d000ba4205030200160380b01da150308403d1360714045051942000018600c0303030050295000202d0000041c8000e41e100300003c0c0c4035201200b045070340b6428004c0014295400283c5118058000e00d00319000035480b407180722080313003060380c1d0500941d40940c000381d0307050818058013641035486840100341d07619250031003d0030394400da2180428001001c0c4c000d003040584046244680d04101d010030124800c180429005a0308481c0464191004c80080c1d004003c6280d280c0001c201c04000c0101d03258020024191824054803070358040031607034a1440c201c0c03081c110b20f9814103900307100390400b08a1880d102c0d1004041d180440340c803c462000c0c514000d40040d41152 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 534144055 1250 534142805 534142831
    0x18020406060c06140f0103080d0f020a0c2a0b0901050f040602031c14040320071e06090e07050705030d0603081308060609040b100b0f07050f07080712080909 69
    0x100c10000140301c4c080b0920960401c0c4200d0b400d01c0c0105012040c03040c400500500c0307001c01c86881c0030241b40c0c0710b040c004012000442d550781c80d009010301941c01c0300505640060401d00300442541030301c0051b07a2801820781c4000071032401d281d0821100e80009181e0750400c00c040c03042c11a110692001000684101d400550301c4010102c520440c8110000f2550442410030140c5014003011548e05a041076150905261298010742141c0920340c00000704401071107603880014541a6030b5014180100039060342c0d0320040d40f03519082d41d12403118814422400c4204000a00107403280024103007007485030042d2480c00801180000684a26800a584151000494411017505218100001c0130605d02a00c290310b0024009888060014805402c00c2c4400703000941d845c042d4544100a8490fa196030354582d413441d8907540c12900400c00480c5c0c1ca200301040071800c030f48000380100454001000501d000c505058024258102840c009c0b104840144843c06403965403a0006100d103050329001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 534145305 1250 534144055 534144077
    0x7171c110330090d12090204180b160e091f2402100c0f03050402031204240801031e05011b030f05010f060e060306060d0212040b070206010e0a1802040606 68
    0xd0501009001c0030743e0b95201030808601c4a800c180e505240d00c40829000402d0995400030402520300c2945a00c03440000000c00409c02c41c4002409015292809541c202041c070008141d82074464810400d62003a040301c0054918036101c1410301400d8003810001c0455583c0303424203002d410000104024010fa00c800c0600d40a604001c000c8120054060074402e0a48000c00034210b0260007244c0400c054070303000050155101040100c1e0b4203911100003a54640d904c503071b550205445407241104880350403a04020403842891558160b0390031403240c5000204004101080000c0c15038115150b5403038034545540800142a051b43c0f040c100c0c5c8000c94600301c484840403c560058011041070000b011040c840e640d03100401d080710507410703a4056a00d03110040015074500412452100c0c0b180002101e0720080b80bd1241580254800d81d80d902c0030748c40b603200503a164002405510f401410f180c000940300c0023550800006003d0336090010724080384e8003c501501d07420317080300001c100803017170b5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 534146555 1250 534145305 534145387
    0xa0b040b0a020a1209230307060609060b0405011101060e010b07051005070e040b04060506030a0912030207120507060b10050c10060302060a0e06040e0907171c1103 72
    0x406a001d82500000c6160104403140502000120340040811968a003103403020091506e0000140c3c0b51812030300500c11040c0fa4000f5034030f40c09130b102224034a0a02c03c00040c41c042d0f500940c001c2d50b040743c5580381480d003410011a01c030304030300c2046126503407150300000300e0f0f5200d0020303a03019056184089a503a146410000e2906184601400b41c0d01d1038002000704280c0e000b00e00c0c80d0b044004031400b0070b00341407020028000d00f00300e800603980000004244402c8404a60014102070f215582498601140c1001234040740200710b40a464450194200c9041e24441c000420b1507921640c400508403c41002092034041c0c10701024000c68000104190500d00030040e07040c00741c1d01c2c3c010500c800d0741542c0c0400c0c20b07409030501c032406210280c0245182c2b130b80c5048c00c0e9000f41c0600c40d81e90300a46802d0700e02e1580d500c5180b08000e12205540c2d00b02088a078042944450707100490280303120104da1100840f07906000036580d0440380010302200d84c40000c81d08501c20301c203c1e1601500710344251000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 534147805 1250 534146555 534146573
    0x12060b030f13110118030b0c0406110706050706051009050a0c021c020309040203250e0f0a061d040f02070303022505070603051005040e01020a12180b06040e0a0b04 72
    0x180030001040001c5000024144100900c00f0120a1821000900b14004600b00c00b08003900700414614141c010081400b100d00301500072601140c1d01c0c0950400c2d1007502c0d6490740010f0103000001201040244040707040c94001ca508507405900103240540e80348524800c850050340e0042800d5120400c1e00c0505a040110403151031060325148045052035a000c0e5403403042d101102d0044e038011000414005407a110302030040c0c614210a03c6011005400030600004000024840c1d65240e107401d01c03d052211040094030038513281c4c0d001c26403012803085800c04903140c03031650040c2c41e031001c0c620700701050002c2c14010b882502d0150f02c070510600f06900d4400c20208003030390002c0401e040d202140d030000304081200d0450a0001e10303501e80800c040d0028025400c07040d08103041030801c21070410154000c002804148e0394072120500c1000800b004d66100401005401000b00c4410700030982d07038242c01d0b403c01001040020400100c080c0581040c1d0320000507550308004104010602031010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 534149055 1250 534147805 534147811
    0x30609020c07060c0606050d150c0504050a0902070501111606060e07050708071e2111120a0203120c090114030f0f0718090519181212060b030f 63
    0x450640c1007802807010640d44103860b01c2510100a8a40e100c9400d110440d40518050240904982000300050030321803040740c100d625280d40c0390f2600254900c41407050060350305032031000300004801460085484d0113500311500a4489550b2490b04400c9218590000e00d2402c030b0442d41400c05481a0030100c0031546181c2c851740030500407004000516921201301e072030640d4000c02980d11003080c3d081000c0580390950404a012041000450500000d10740b980302907140f05a2428528008080131607018502400b110501e40c40054074500704202900640013000341441180e0518805007103505640e81c09031100c40b00510700040307000c05941c2c0040d20f20f190181c884920b9246003400941060300714401004ca503040d805200204809511458402640781040031740030b0103064072251750400400043e1541c4c0c03641c8401c054030360707000c20a9016245084004081c0800c45082c140c45500108460410302002c2203034070400840044160712448000c0c01c419514241ca80c81c00101c100050740c005 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 534150305 1250 534149055 534149069
    0xe36060a09050c0f07051e010b040506120a06020a0516141203040b01051e040203090c0306010807030f060e01020c0304120b0705030105031b030c10020109050c10120513080d05070306 80
    0x7000810500301c0400040728003665030640301c2a82c5404a00b040c2e810320003542007c03400721015402100b40307000150440000c2407401c48042140c1c1e2100c204000c1c006807204184411904011000c9001c07650755030282c40c60390142d0910f20714000b62508619920385007110b040791805d615a50419407030804010700c002c3c07001d50329030301c80c0395040946800313102e40e205101d0300303101c1c2c0f00c48602c00c601c225840141c61070640300548199100c1c00c040526684800c0704250f0301d8020311418000140524000581504803074201036141001e28403034540f4806051989401001c540d02005283c4401c40108000d00c024035450402031003c401500e8600243d1001034052010010180014001c0d40c3e40807030302642c412100f1180c00303844044603010034104800e032045603a02190801c0c000d280341c1d0b019000400780c1c510500503500c3d0303129140100000f9462104107080043c102a8500e211110ba1f98030880e0040d01c403022100f102111596040065407003640414095903c44040c80803d036054020b010143c80a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 534151555 1250 534150305 534150311
    0x1909030605101a0a12021206031614091003050f030309060f010609060c0f0219030201080603010c0e1908060103080a02060a060602060a090201050c030708091f0e36060a09 75
    0x190058401d601a1408848425180300040c08a000c1e802040400c5140300802170a40d110380f01d5002404031018102d0f04a0300034011803101c015048008100f62007034400300c02a25400341e1016081c0b20291748001d21010450070050f0700031000c14001c1040d0000034440b40021552403800c1c003501c50074154007510b66440c2003000d00042c400a60042c100c2d0f410b41d5560300c0c20419000403420f00003644d41a05001a40040c408401c0420f40d004980d104010303a4000c0c1c80715207840e100d58041c1400c0301c1cac40181c00d05c00110040c41b070500030f1502e129201c02c40980321045202594503844982d04000e400e910848038a040020b001c0110b54051144c26408128540700304005481c104d0302035200c1f1001003504036100d41d0b070103406045a002e501a02c00c40078038241120340315144c80ca0306016660140204511074038400d00301c0690300131959605aa06000c680e162124510503909102620403800c88010f03520343d44000030400785001842400c03800b01051540d080c00d04018003031201da41207075007243c41200e00b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 534152805 1250 534151555 534151559
    0xa0506032e0807060822030f030b03150a0e0f010c02010b0108060f091501210606030605090c0a1b02030616090915120204020c0d020a020f0603040b040308060402190903060510 77
    0xc1040030856481c0d0a102c9115520301b05455601808110280001d1a10080c01000d06521481e101768601c03140e00c08000203a00c040030556540d4414003043d44413100000015100e0445800200b9440291404c0316413115a0500aa00b591203003070b41d42c4d00507175440c510003942d503901212164101c001996075484200b0350801003050000300400c1100d000c81c442d009005540d02c076400c00c2c9011302d140d8400350003010b002003c0c81c0c0130706824403448000909200b00426a0300d003030b6807141c0c0202d1030300c40a98648038105c1d109544031050072140c9044040c2c0076030f01c0000350b2800e100580c8240070f03170044c5101001c580c4c00c000d002d0309100d800140120b03203000192103001412481c4941651a14008042101c155100180c040d108420024410f4000d01000f002c5541e00000c11400171740c0308444441c41002c11406006603130004442c0a03003444a08030105010a0103070003880e402500c05003015144c00020a5042c03642403d01c3c3c141000031303d5882c802c0003400740c54860180c011400500143c1418 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 534154055 1250 534152805 534152819
    0x6130b030c0118050612090106330c0c080a02041a0f090c0c010603140c06130e25050a020c090f04140a06050f06040c09230a0506032e 59
    0x1030000481c55050203c00d6002c00020307034400d0880002032100074540c60307840c5140c1c0080c0e28408019190040998206000072441d03801c840c03014100103007041124440c5400e8003c0c003440b400d03810585c0b003051003040e4210030003007504100c0785c2001e403001034000c05401c4035520510088030320350340e014180908030b913914442a5540b44440c0c2c10404c411114441c441d25024115095485200d014000c00d600e440740c00800c00c8514107950325002003040c20740340040b0601c024000340d41300301103038501d541d00c0c41102480400d1860b0b4825401014524543c401e044050b1134152210b0030001110000c5040842c03d9028242c2c10818203140c0e801c151560212402c0c2000c1c6a0010744003e480200101d2583c0c45a001c0d9441c100554024550080c0c814042400d01e2444103110240694142d0700882c1003004002c52980155804c500b04e40414025124441140480007400d030f01d40c0d440290f03c082c80c841c0c0040c85585190186000d5150407031080b08052140440c0c80403031144131402f8501c100c04100800640d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 534155305 1250 534154055 534154063
    0x308130b06061b01050403170c0306060f03130210030b1302070809090c0d1b12090302070512160e0604150605070308270c0102071d060409080f03010b0306130b03 71
    0x71400e980203a10b481002d0038208003d0307a1903000412641c83c150800091550100e2500d02d03034400c0b000000d0280d101c80380d103002e440c031085403141e0300060f080000234044071502004641c01000001d0001c02040141c0c002047c68040141510010341c688000c3c0032a0b10345000040800c181000003140741c55001d41e0303106c5c0e039401a000c80364400c101010004038107100300000c46649820f940c5040103000444d5401e80d602440b40c010150000b040402c2c100d420702401d1240d50040d43e00b40c2c0090100394a001e0810601c00c0a400c51413800380100c03540d90a60580008504000e04240340c100070080c03418400f400101c4243d0000a16600400319040007001c3e045821114050341510f0450706581d152600350700240d40010602a482880c01c035503a1036a1004100084107503026800e0324031642d5900c2d03454481d0003002c0c840201d0000306c040401c03518a842d6003c442000e2090140c40d0802103015600d040c0394200364400d140d00300c000010800c0d44e1602440421059886000c10000e85500320301007a91 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 534156555 1250 534155305 534155311
    0x60b0609010c0f020a030c17010b01031e1d16080f0a0209041b05090a1a04022704110412030201061a031302040e030301090207050601090902280e0a090308130b 70
    0x103200034146143c2c05544441d1075030720241d904203074000d60441d540c404244100b20304c40c1e403049180d460026029680d6100e40110b03030f507540103a08600a240d140e00c0d01300c3c0040100c0003a981c46131826082c00c281e40c00040c0000750040e469401c010501d01d00c4c01d04201e0910b41c021001c1d1200e500f0901901005a451b2003600d40c225402101101ca104c07003000e01404824400c2c0c00482d484410841000820041908032180024248051a403203201500611042c0c0c041c00044c00e00a10a115884c00c5105031040340d642280b42c020404240c0b458070143c0d00c138484c0c0c4035030000904407084c101494185502401184001c08544500c0c689901d144009078406000c080c0100040165103038004d802e664450b003207a880701c0658401e0765540d50351050400020344c000c0c1021034a03030003000000144c2411a100b0183c4040e005005107014011450080100d03c0f11040d44911440d507941020401c10a1551802c0c0314409441000520b0080c07401c0281a0800040c9815020004200d410000542d10382915070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 534157805 1250 534156555 534156563
    0x305071202070305031204050c0f03030d020919080607020d050f2502030114100807080709051015201f020d060302041401052d1306170a060b0609010c 66
    0x3282800403070400032558005002d501c404204941c002940e41100c1303010f00c1c420000c4410103100c141c10301000400040b0a10391540003070000d00c4100f042e507002000254401040e2490809051141c00301c200c0040d00302d2480c46d4031400c2008406c903010030911140884034203006040c441e280400302d496103d032590700c0782e151070004880000c403c24a108044451b070700400034081084105000d0015110456428011058842002924000100b03404c01540c84c28006020300c0c5080c04609030261001402caa03007c41c0342600b0000380402000170300401c40d8103070340e81c0441d00380424288498082402010703c405412003540000000d00c40200341c00900300300e60307001d62501c64a21400f40204065480079400505003180b26040c413441c00340f5141070f214200c1e0030603041c0c81d030f0300011081480c1510354003a0507014517131500344911b041e44005450308501500841c1c4152070b03140d0300607003007411024079460b50301c401510010003501e800307412400001910903600740b154200009001c1d502003078001c1c2c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 534159055 1250 534157805 534157823
    0x90905010b1f031e02030a05090c0a030b131b181104120f020301020f0a0309060606020114011703070f05100506030c0a1e091104080c10080a0b0a170c09010e04030507 73
    0x4010110325807440300b601880d041c11512440e0581d00780c0088c2400300ca00c1215801405501001c51a0070100c9100342c1e070300447e424645540c2d2080808141c0c440d000306031810102c1680798a4001000401c0c0d501501080740c0081c40e070034142c1031260580308114082c24000005000c144480d20703800804000440c1c0158491000d410180086802403184802c003040e81107000900810054150b001300c40b100348900c2080001c02d80e985812801c17210b400024407582484030380104401e8040c100c1d001e454148000969142041c4d0303030b40b400b01418001600f1540c80e0014007591410340080d01c03501d54440c0d41500588900404140003841c3c44802d8011201c0c00d00c0d00280000040700200188006030040000411031a0702d213060900ba80d8119129491003880340811100301400c128940c2c9170300000d183c880981135201c580450000d0100010300a07001092201e0010700c80c00c0465111142481c88005024804c10320418880e04410503048421070454a005000001e58040201c13010346400c50492 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 534160305 1250 534159055 534159071
    0x621020607060e061e0906101a0408030a031d010b1c060612031709030c030301050f010e040c030b030f010203010503031b0f0a050d0e19051216090905010b1f03 70
    0xc004200f03810f8840c1c214400d41c4104001c62032200140d1002e04820b0384104035580da404035181c0d0312001255006a400b4880344108032003880308450910710328081c08000d08080c0c079000c0c090b03e07680041e40410006034076000d11a1206481824500702c0c0d01e8180c00a000d10411080814058030301e9006850351041c0102068040c00b0b400d030f101300e000d8248200c0c1a1003042140c1401055052400c10202c5450301e450301003040b415001088900c2445500d01031411a80b900c8200084c0e041c0058005040c4403601589151940d030307a04c20b5000400540d1000130b0f104108006040c98441202c6615000d07a00c1000107008550780002500c09140414901d5800d000130b00020314107102c0030b08005211031041101318130030041302291080c1511002c3ea0b9030700c0ba00e14030304104070000c81141c1030749000d000c0b41c401c280301c1d908000b014080b4403c0034008590301c82019408026200409501c88001030360b40c2d1450b0000c000080c003170482c07200c0c003c403100c4880c04aa041c0b0b0319440441c0301895410300d60f4844007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 534161555 1250 534160305 534160313
    0xa020f06041701050601080601110d05090a03060518011b0210150f060305090d03060518101203020f01060608060105040b03060d0b040b04060b15041818030906030621020607 76
    0x1c540180c0184040c41c0c2c0019040c0c0c580038080d080c01d440715070103d0007440001c0c48039403146aa1403840100030f002400442c034001825100c170381c4008a0503402483c0e048022010034010301550f406680703124502d00390b6902d81c900ba5401c41d00c822802d00d117500c01c02d070240d1015a600007081003840c09218070004807000d041c0d407800c402c400264402c51702018041000102e8907090b52240344030303143c00b01c192490761944007800c804503402070140650210320082000c03101c83ca20800103a12080302482810f801d0344440c140d2440d21044002200164803004500116400a014850052805081114103070814a00207401c0e40194001d03841800d8011000500c165200740b488503500303403c00101340b030301c0c10309003400740b6a1081220241e9002e810040d0615050802001d03c0005052000354581014204101010b002032480458690030340c0f142e1000704020917070021000d9051007a1980c00e04d1914020300030b02554032613403191035441081280c0c09582070990f40421081c40d41103c00780c1d5074000c2464 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 534162805 1250 534161555 534161557
    0x60206070e15161a060303090117060102010e120703090803031510020114070801140a260715020a050d08011409041a010803031801020304050a0b0613090804090501170a020f06 77
    0x843c0c500c00340810051007040c0f0002c4004040c0c0381e600d01d02e0408482c1d840406060b030f20b116841e1034900042040c186180800160000c0340e821807014400450b096010b9905245810074000340740100b00300001d060420140c015140360010152003002c0c608501e841059110618400d80c0d132540181045400111198800c2d403140054002c1a1401c450304c1c03c1c11000200451001d00418520b02c0324a41190003074039001105c007007105c00c261450310b00c82c41d900182403581c01c844041e031103440c4940300002c90030404184040d140601643d000700f000c00b4490524902c0c2400b11140c0e40284440e220050140300c40f80c816000b454402510103001546076032034012656220320403142403040b01003001080c0014080011402400401c0100591000c1408550308038482a00c0003402a406040c008001900740d50b1340c0e55212400910040f0b00c149000d071050140c0c0d422437402c48940000203801c5c0980c0c2010b04c28240940031030b0200c100003036030080f89150349040098000c3c1c806d08042c4042205a0b40d020 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 534164055 1250 534162805 534162817
    0xd0f0c0c0e0703060909050d0e1504080105070314090606040c121e06090614040e07050612060918060a0b0609100e10030b06070b150a1e060206070e15 66
    0xc0c2103035040c25500c000700098000141c0318000000d0500800050060303490181c044650b42140240c070351950a03501c180d42a003251803a00d900320080117010451400351801500050201e0000840e01d4981540c00408885800c120003840d41008414401801310000d6055440074090b20002780607122500150352281480681e5a2124140b506840340c10301d401c84003000c08aa0700781c042c0103c0f9210000744042c0c41840c050044a00e40340c0e011005507103000c1e080000c041880c0d90507100d403240c4607404503206030310185040c03611b08003403414000c0c40e0510780500c2e03900c007103441021828a000d4001c6140c4406014020b100748d1612402003605e00d50fa1901101e07185c100040800405040c10308016101c0720302d240185104415003116010b203c1d01038002c51f0b422020041150780b91460300c0c1c1d9800140140503000500854181403040c40c69190100e400f4094406200020b075030b50f140761b200d6506c404440d0400011504513806010050781c02c4502c06009100c11907201011304013540024000b03001324 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 534165305 1250 534164055 534164063
    0x8010308180405070f0824040209040245060927190b0406060903030810091d011802010207051e0301060e0709090216060902040902040921020f0d0f0c 66
    0x102c4240202c00780c000d940c0308400d0001d40c0702c006c503a82e80c20b00801005400340c190900e018072840c03070004651410390b00074202c00f00000d00050810b0041c13000340402d92581d0300d4600d9854845000078038051034501403500c40221020003180103251140208410780200c2074014040d0380c05115814041214000c1c0030b030348110b00481c104192800714580004006081d9118019500d419407400c035505050141c1c5007900c0700c41d01d030380210500e0350340c0468050000034003a0605031000030300410703841c42d0360140400d80341343c0020032201b05038840c00103421508602040801c1e07034114480303280142d8011916008031f50f0308407492249090180418400707a0f60701040c00f0750552900d000451407003204804180100c05c1c9680d848602030712100c000b002ca02c210b00344980c04420a031010000510707990004400688090310118030360240ea130105064904a01003100c00b4440d0850f40c5001c541a600404005601d6100400000e01380c03664494031028128854020020030b108410392035800b404030b00308030310b82c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 534166555 1250 534165305 534165311
    0x4110907020610080c100f02070b040f05090a05130b0703110d090c0501170a0b0103090609060b03101406060702191e050607031215080d02100b060406080103081804 72
    0x400c850003900d4100440348084044030350300c00401c0700f00c00029031852440b0041c1c22143c0d10b0f090514152016615170b0060411880b903c140030600c18941030103000100090b40a0340441400c0c0030070040d24032001031001140901c1c050070400c031030b083c040d102d00d1990b8000400e442c20351900034045010701191000b4164800001508060789981940400111401408140100380d2104011503924010b00c10400742c032031210b000714a41c21181e502c8502032031014100012504080e5864400b92085480d064650a41e500083d600da03080070312081ba10400d00c2081084452500341a4402c0c459010303021a001f0b500c04a14801151202600380300d1400b502c84190340c00c0c1d9680c0c6088000344207109906811071a00046c0010103080400c00c0d1414203525440d0403041125509544004140aa0f4812024040508000340b179641c00d018005030440b880d80501212498200110240c4014201060140c032041004020107540304840e281900d0348120b405a603510b0f0805001002440c15000c240e001c1d207 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 534167805 1250 534166555 534166561
    0x16081303080c07090908030f070c0c0e07080a060510052a0307031202280c06050109150f050f130209041401170703120516080307020c0102120a0207030b041109 70
    0x107807040c064078044012104441425886641c15420346544800081c0000014008075180406461055910841a107030160344d101d01b41d1140020454254040c0124407414014440c60310f5020148981c0640d00c1031040c88018904004680302d4034080006504210707011442412640d4048542000342c41c074030030b545400c00d03040304126440b68480c0b47d007100450003154441184031114001e6135003030484601d154156601d8003841c142c0c0c008001c192101000310001c10103000030703e80d02c03489010b0a09501e000603403002c6010217090100203500003107124801000b04114950b202d00d000c01020344203840c03c004031a840103441c03001e8050780241c0c6074840c1c00c041110814040b1020454100e0b0310403c003804240c024403081e641c48803854000500307a0f440c3d035104100b05034042c0008000d4440500e0445000c209a41c0f03031060160010360f5840e00503006031008015560381001200721251349012120b01d040c00641019540f14030600c001000f030703040705000900f4001500c904420360b48001e800c1220354a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 534169055 1250 534167805 534167813
    0x7020601062304050a030804170705010c080723070f0617070e0105070606030b16111b030c03010609060e1e0a091104020a03050a050c0a090b03090a1e02010815030316081303 76
    0x24100740500c11400c2220309c814054183c0000f502400c941d41a11480444c24298841811941c0700a4081d56071092a4080569030010b034003184d440c030b0f04d1010140076003600b000d03c644803821032030707000104220041d60540a00422104507030380080183c03d0807204100464016105400703194809002e40f480d0013400400c3c4245c10041611901c0405240c9200b840000d40644040000c08440501544200340c0001300060080d0039a030301d40310040403038034400300400c000390946030550003131502c2d151140410000003044529840d008400003141c403902c1c0d1001d10090704840c0e0000d1103a0b064684401d4100140034607001c5070036102034003410a45d0b8070041c2c048003030040d080548048455034509000180321690f514141c8034007060603a100e0080501d4504075029a030006000f095050150065680c0003e544241c2410202c00400e00122041c0785400007400303040000780142c140b0b10300780c144820303941e40c04000c50700f070071400d40b10301450103242d820000054010002e91284810780c1c104088144 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 534170305 1250 534169055 534169057
    0x14030112050d08130f0336050d1e021903140601090e03180a090c08041a04020d02060a110618012009150706090b0f07020601062304050a0308 62
    0x140340280100c80001c940b2400481e95424116840300c0609035401c1c41c0c000141d501000030003510301a14203030300d0815100305c0922500000502c40110749a19100c100004401c548030364004001c1154000c0c061085070310b401c0300c00e926040741c000c980c05c5405014000c5680300c448460301d00d091665103c0d16191286000d0041012a50040d820751180e403000242d000118050049042402d81c041c1d401d01e4100c40b001c4441c6000c180d5071a510000e0000040b403880014031a42980d485c0d241d440745001d0515060003814a85036025060103180c00000300700143e00e545660502c25039043d9406070343e601840b0012074072905040500d08041c002c80c41400500a488942d170218044050002c01458600c8840f5400c2e0501040440e10700744c100b403100794031a02d0400e0b0034041d028468811a0700d0300e107565449034200c50001204807007c8a841d0288130071815003818141c0d10000d5400182419410a90040c3c03102c91060400d440c4000c015541c901200e0403403090320300400d00503100d91031440e101c0c640440c0d1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 534171555 1250 534170305 534170339
    0x8010b0a0921021825031107060b1e031e01020705060403020c03072c100b0f0414030109020a090e0304030b092b0e010f0c02090703140703090819140301 67
    0xc5005443e0715000c61003106201c007400b413120205104801c084580d4280451820000140c3c10306540345807840242c0e00000023004460708c01c0c0f0b00013480c1d4003000e04001c1c1650000304507082007060740c81ca0050a490000f0800028010b00d1a0300740030400010409019100e0300c08010598011003007404201500000c01c480103560440039100c1941e01c407515801c958041000d00392403294510307030a8898004401c03496401c070200c2054840180e032100e100700190303403003440c00c440100c1c8002020800300c0141c03800d6502c440002c030002c4c4942c0829030000703201240c150043d1500c041c1c0d22a03080135000d004004a0f030046501c070380b03070848a2070700401090f101c040c0404c0e45000c071700714a0f421043c070b8040341d44142030715042c2e41c8035075407038411703407001151011030841004007404003100c607560142e51101c5a00344034146030707540465114160108109082400f404007400e15041100060014034600c0a950719011142c2c1c110107440c180c08000c51b80b140200040c004001c9000001081c24208003842c510 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 534172661 1106 534171555 534171559
    0xa11010c0b0103080d11181e0d15050603010b031c030609020d0b0f0a1503050408210f0105100c02010c240b1e0108010b0a092102 57
    0x3a042502c030010041031710421807000707004110840d090300c1d80301800d1024100c0c940c50324003841c01d14a40b182c07420785251141600d5500050040340b00003058041c00d0031039400e1030110001c044400341d24207424580007900030b042c140102040e0b120041d008000500607a0b0540b10001e40d010b0f003140415840c0c12002545030028000362015244ca004005001e410721701c1084060040310304000d02403450050104064240603c10a102e45124203021401c0d650b1482c00240c18030842c00d0048030603407000401206c442c50000c1e000d2040c1038560118541e40d8881c020000100348d42d118500008802020791401940b0034040c50b440036200d6010441ea4042c50404d44003c04d44001092460a45d5060140703000d207015546003c0d610301d2120003100261000000905082050080e0944003900082e54640680308100b980f0003050040c048603484000d00d034032084d4220042409034 = true := by decide +kernel

theorem cover : BRFrame.Cov 533992805 534172661 := by
  have h0 := BRFrame.cov_init 533992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 533992805 ≤ n) (h2 : n < 534172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
