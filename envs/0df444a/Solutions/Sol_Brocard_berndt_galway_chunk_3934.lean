-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3934
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:06:21.090628+00:00
-- url     : https://prove2.me/submissions/be9a125f-df2f-4603-86e9-3a2b61ee4bdd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 707374100 ≤ n < 707553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 707375350 1250 707374100 707374159
    0x30303050103140c010e040c020f061006090e060105070b070201021b0609071e030605040c081203160f081f0902041805340c05160f0503070501020c040509010902 71
    0x84043c0c031186545100070900c42c1803000161660000781d00000103200180032840010800d5000740318462100007002c2c001a0301c18000c20740d4500e11642030045c050600820b0340c00c102842240c44007004000c7e6004001c86040c9900040b0b010035503504c507041240644030b40000c02c4181c52020742d11315284c900005400e4080c0c401182038500094582004411490650202060390642010b08002040642d800180c101c1d01440802c0b201c10b44a034003031440d2030b144c40c2aa91081d5000020031542c0000c0504c1c10540d81018505400605010540108800005023400c00003403482004240d04065510840e0700501ca03200b015074940381d450381146004006001d80c2000309081c903002500a0000b501d2a85c440500c444013400742442070a0303408202c0c0c100801300f00600034000c140e417000c640704000b503a040e40d02c2c802140350901d080118081c080e007010f5001502a0744601000c0c01540e80100e0303036030840c40050b50001034681e201f16409001d4980e400001c0d40101a0243c4c080f9441d02c02d030390031813540 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 707376600 1250 707375350 707375363
    0xa020f160606060e0f041d0f100501060c051c0302041206060e1e13060f061518081009020307121203200412140607200102040b07080c1006030303050103 67
    0x10350740f03510a480d000b207040102a4441e4800e11111028909640240e0ba8041000c0030040e05c15034440c40342d0700c2c242d0001380c0424640d020151403001241240111b0380500402e2404600301e40095a84c2039581d101d004400405160440e030031415030f44a42e0588008003c841209000284a414900000e11081c0103016800707007460b0000303040300c0400360307440c0c2081909442004640e480500c4005c0c00c0450030300454078a6110741802c480d4500c24000c0340007402c0c408080111061900401500d0201064800e003104580700c0c9080002281c04140c1106c04c2c050400d0203d50085148002400c040301500072101401004a246003809180301150b0f440c0304141d2800c11003000c00c6202d03201d000001138640303801c01e50304110502100704203500c1101003611401503404a84030140d10181400d2040f103c00c00022502170844a00050b1a0f0f42d9040c554042002140b4190414409150902c1900c401030070791400096480c01d00385c0e080007800040901010308001e05500c03480c008014200c00c1c401540d11 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 707377850 1250 707376600 707376611
    0x30112051603030203070f05010f15090518030d0c12050411090901021213021804080306030d171f0801060b0703030b011e1404080a0503090108090604080307080a020f1606 75
    0x5011216440700999405030011402c140180d6140e1810805c1c844040310155203405003948800110b00036003a01841300303800c4580d820b040ca0109012900010301d05044200ca038540107051600c08002c48176103850300c03039010a48090b82d400c1070f65000781107503822004916000030041400040d12001c090150126000103d60712a089100d082c0e0007103028550641244a01180d041d10460b40c0c080c0072b181c8041c1c181000700c101c12290103000300c4126001d42c0e100c8000010000f42d49000d000905103500c0311709224842104002019000d030348001c05007c010504040d000010700509080003004001410092050544802c0c1d01507031030f0015141207002c2030a190403080d066014500605100020414281144140e92000c8030030f0b031800026920318400402c00030403144814000c03004580e01410081d0340d10082c0d040010304078a00289008030301c0c0c0244042c40000391710901103d4000c881403070440e0842d140c040c1840000d115145c01750424940015050700310b140d4503c814060b85026407000c210 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 707379100 1250 707377850 707377873
    0xa02060c0a02030a030b130c020d0e010521070c12020109051c08070c03090b040602060415061a07050304051809010f020c070b0d02040509010611070801020403080307051e03011205 79
    0xc080c020880d205015030000c0c0200e0003020b03c66404842665001000082d6402031058500b040300c120340c07030040040e00015000147c06400c41c141c400d10000a192aa161042d004805031202c40702c0304103070400b9000701c40860452071143c206600a140c000703080c5200e0404816000e4020209004211058060045184012900000164207904058840409554542c0000c42c0d111003014005c07028440104404036918000318040c0000d030070f2030f80017803149050038180300015881c101d03000e4583c1c5041c101e0a003ca40100811080c110710341c10581c0381c1f0390545280450031070080e90001608220101301803d00a80080031040c029400799000b0440c8802d41e00740c01c001d330301c83c9903d240c5403940022000c025503003000e0000c1000700082000142810748400028403e82400c0c0c0c4030710006004010f029029480500800c001080d8840007145041c0c80d550b106a02c6000040070304003880341c080b03402422992184c895900300d81c1120401550781d030312035810702d40401c0425029504c0c0d1207031022004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 707380350 1250 707379100 707379121
    0x160c05030109030509120a080c1b030c0604180b04050f0f07020f061617070504060f08010e070e04020c1f0f050903071704081b09070e0d02040c03200a0206 68
    0x40042d9015074a1502e00104141402031441c1451000c40203071040341280e40100302040042d0100b0040d41d00503100840e003801c0004481c0c61124047c1c0d20a800a1004640c02c1d500c01d0102e408590038a21030341e007c01c8078004101c2c004c01c8007131800741e0003500b404208070b94440c203540030030300c560350074183c0d81c400d40c0310445d049a03209030150030b40c030481e4021404a031003804078074014001900c540c0b074191a8040c44d87c200400d8010709032014004603401090a0101d00d41080c0c0b4984000402e180c81d00c1c003507151500c0000c1040001e0601001d01070540540365098449804076aa0200390000b03c401040d91281c41c03101d04031003907103181580340c6083d00100c01d9480900941380110b0001c8019402c000d1180c40d00c00701a644030340c80c3d8012010400c00003814040c00d01c00186040800920a02c85001c00070910051940080c009030400245480750030482d40e6003030310f84003003d030140d40005005004010940081c46208510003440f40c42c030024140e80c800080040400e0003071903090b41d41c5500c44020340f8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 707381600 1250 707380350 707380361
    0x608070e0904080904110d060312020f0607120603051b09060402070218060102030c0a050303070906030203010b0a0f18120203100b010503040b22080a020c0108090c0108040f0206160c050301 83
    0x29510007025808140415480400703440c50880050001900144d134aa00070344503032101c40808034031900e0b82410000d108503803a6201a10415002400a11107440806030302c4510042020741400414058030705e0030fa20603807108020316482411110041c1c01101506100d01540b039a0f54810030341c0c000065000e090500a81d00d4143d8058800c941790f4040f06001d0030074860042c18181180300c207205d000e510364802c0116644c5140a400030715940e0a085030001c2851038107401c84014180108010881a00110704a8070202194500704107804001c1c030040741c5241100740c1c82e00104000140c04141503001110b00c00340301e0f200301c0855802060205a65083d50502c1c1c00041c0403403804d200160118440e11320080e4400028103140b5500c4100b1400101400c41c80001600c00040101f04542016010800c0401c22082400c2201e503600e82210410f0b6507002400c407960400c095100440e040040c00701b04680d02580c0146090303242d080007100d040b40100d204c034060340c0d403140c039140c00981c505040c03149 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 707382850 1250 707381600 707381627
    0xc060d3c09060908030f220f0305071a1005120c0a1802161406150f0d1509080903070e040b040b06030a0222200711031e030301060807 59
    0x5003540003400e448260300400d50600160782043d240e03a542c000040c03000c402540310b84000f00c1001c4079030906a40852503200d8030140c0380c804d500102c0541000c41c0c1781d142c81c070042d075900d8940b6580d07500e5075140014980004120088500d6181410f001d6503a10448890b0309076242545c0582c900400004072a030382d40c845481054100800134014004588400704000c0350100c6a60058905110320309192400d281d1090191059103d0744040b09002d0020301c4016000480c0740e071040007407600c0703200040380c0c1c540301c024480c82402c800c0302403400c21800100743d484455038048100040602800c020049a000c40c40c003610074042e4100100e030722244000164003644c1c01500c4c981c4c2c2c0341c4e226540d00c05114400751800f83c0c1032095118401c01030b681d003030403031146543c0d41050b01d9215502649810598000d15100c4168241a04640110410450035141d00c039803c0651000407140e03540c040783c00e0010384001c5c600302d0090610001034002d0008011b6040702c241d5a20900e1565500b04100c4103004090003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 707384100 1250 707382850 707382941
    0x4050d111f09051e100b0d05060c0c24010303030c0503090a030c0212030a0908011134050607030501030308060a140108040204060f030606031208090703140c060d 71
    0x110200380303450340d01c89100b0a00c40c0048584404aa88079152804000181180e441c0d1280c42010a080980e0203480d81e44070041d100350b140c0d0041c60f41d810341c4440d0014483c6400003404a00315884220802c5a0582c0170b41d880b0900c3c10314207003403691810060090105601090410701405543c5220b0800c491140c00c8140180594000740d40e8100c0301d5281b0002c0c2aa40500340d01281c0b50300b14001d10080001c45036545640c00c015250040742400d40741d50032090360403070200340311070b0558001038280184600c0700d0608104500d41600c98640e00f05202a202030401c1c4621300c200603059401d50300c280d0580e4080d4985540683c1c4800411008500600452803003c00090300550194090f4020030742080c8014404a00e55803544a19245801c883d442501c1c002e13180d800c204240007204a030b04225240c5072601400c02c1c908210781f10b54401e2184401058845036070184034600700c040c81034001c5030704000c10459072012102d000e032019024001040c0f130b08109a07900700400d210008070782003d0068645 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 707385350 1250 707384100 707384143
    0x70e010c030810030b0c03040c0503010b1005130801052719030518030d0e0a1401052703061504051f180b10080723040504051e04050d11 60
    0x150700711401a406031070084400c900c9040800059440034400b40b10740c84080740702d9100d05e42070030508059501c5038003440c080d92500410041940320500001800b00060604a9440c0030854819401890941c010040d951a060034415202c0b000c1962804211001c24a1004941c01c10005a1600b0759100d00d200c80410000031280024042d1024200c2c040400000d002c10f629030802090800c8151982c400001d000e0014a2407549001c2103e040941a11302502c00741d5400e001c00644188181184000307170140c01845140b041941c510210225800078090312a5402c200c00260703a02c0c1c510702e092921036410100041c2003c900001e000d04502000d100902800e89406070070108a80c0c05084583d103543ca80c003d0050585940c121601540405e40c1c601e0118030740041c004000781d0400c0c283c2c069001c000d0004c0f615844880007501c00780d4508a800051070b88440700705c60302d13601000683e13661401c0070380c0401090000100d800c069000702030b192030505070030315500c854450711580302c40d0000301c4506 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 707386600 1250 707385350 707385353
    0x2a0102030412120b091b22080d1b0f0507031502042417060102071a1206010507050d0503060d0209090a0309080111040306091b1403190506070e0a090f02030a05070e010c 74
    0x152001441070446080f02c40c0b810f40e07c0189900402c048001c0d107030030180c0d1179500300800c00003080500b6003d0820328000c440c9180071410502400701c1158043c002d400f1818100051282c24404000115841100201141e074070b5101d40c40650804d118541403221400100085005001c0c1c418030000c1c4242d4515a0b00e9207082c02e00c000c480c00c00b910890440c8104a40440da403220004440d06c3c680c0006883c5488203560b540c0c598000d207000300300d030381082002d01601000034000070b1024000c82035030a1107030f102e03901d40011401e42690100046d40c44910780041c03004403200881d6020b0604d0082d910b6000090312207032a035003039591000c0d00c0c0403a0041000100302045460740541d60543c4181d414000b2144000700c0419105d20581003582680d525014140c41480d04001c0683c080018002202c5208102d85819858060042c40981405a10701c0107174042c0d5140580c00707014000e800002c000c81c0412580c440c0082d00100c90214040f41340c0350100c0c0b0031030300800300703a1441c3c1e80c142d4039010680e206 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 707387850 1250 707386600 707386621
    0x1020c0405042427050d0f180314010605013006050910140a0b22051201090c050603010f050d060b030102070b090d0908032a0102030412120b09 63
    0x10025a01a0040042c1c1010000f07808003021420040364000b01d0780e080b80344c801c05003580c0b00c5450343c0c0420405000c603000280000c644601c2e13811442c03c2003d40808107107001d81c0c0c08054400401d40301c442040002c000c02c00410048499640c50500070044a0303240d40044d15171440c1d08000c0100c3e2079000101100c845d0284003030084a40108070003182e000d0342e071000308020580503a14a030580c02440028040303101c40c5249034030041402c80fa1485418500788503030b0410b1240c4021203d41040d8652070300465004018100000c001c050b00b42d9121100c1285518003c10740100101d0f40d9610014001170300d2716040080d0f0b81070321540420038240b140340ca01007100300749040408841c0c0688410715044181d40c2840a000120300403d0101c41c5443e08550031810714120030110300520140170000d002402c000029115200c800240e43c1d40690494003195070450708920480c00e042d07000100304800c000b4041d144a030b507a81e007a2510380c0158100c440384000d1350855000e0a402820003000201d40040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 707389100 1250 707387850 707387861
    0x507090f1e08011805060a061211190b131410260103060b0a05180708070e0409060204050a15050f070314120f0903070512030402030f03040e0603070e010501020c04 72
    0x203901d02118010769241241400d551214240404280e034504a00f42401400c0c0401540825880006c00c9001e080142000300c60100c00c1003c4d04103844501e807051641c0740c60411041089420b40c99950040c4e0b80c803c920b80310307172040c08c08800000070703290009414401c2001d461801e940084c651035940b100700f42d01b100c01c5200c0c404e1400c034002c00250034064546040c0070641c042c40c041d070300c0404c202c3c031a40d050064010541d80110b001e442c01c552005030340f002e1b20710215000302c601c3c542104a501e030b50008984c066019110b80d5030040c504203850040000c0d41d4000c0c02114016a05c070320b0056a00c64a1610f007520a4003008003007503080000481d8151884014881d003886810410200c05040503070b1001c503003090048241011000042c82809441040da541d4051040310045103400141e6650340d481e04c40e41c0300c0100c564480400850304560341404044d107808104000c5a4560b40c1d03030b5a21001d813140c00d8079064003034000c0001c08603c402b114240301e4142c50040e0014040b0076404c109000c0100f4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 707390350 1250 707389100 707389139
    0x60c231c090803031614071b06090e1b04180b04050615040303080c0d020d0b0411030c0a030209030f010c1d060a090b160501050108011d01021306050307020102160b0103060507090f 79
    0x7540d0030910f400d518040103089482e004580300072035024071000c0e0044508c440e402200900c080b1309800c02a0080c40c0c209280e21801502d0041d11030144000410707014004c64111104010014440ca05141481e500040b8419011603003844642c50700001e00c0b021103403a28117510aa8420001400403034060b500d000d40010301c0741c07940f070320307090003200c1c60812600030904600c00d440d12650004250b241c14040e4403810000641410310310b08040700803000701c0c82821088400d0503000b04216140741d800388182e1544100340d2000340000e400e4040c1c020826101d600880180c10b1031801c01d0002c90a00006440c00f003802034485160580c05c0c44110340d5a500410011010890401200000120203004050013420604008079495000d06211701d040e403000030f10424260300c113115000c0040041c60007002213030070038104a585c030b0b10f80907412400780c400d0302c140303060760b040d800f4002c8200009090014104d034080c0034100f00704c0d16001421100300f102449070540700b01c0c1d061028000e01068031076849028 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 707391600 1250 707390350 707390357
    0x1c0f08070c020a0902031e15040f0b1306061101020c07060c150c0206010602010e2407051b060103140102090f060a030608100e01060b0a0504060c231c0908030316 71
    0x600c072a4001510031031960400080300360080300344030510904c01751280d8409811081e000300340c64081000c4080c0b01c1d00c1000756100b40e03215072848034441026484000507400140c0300c00300103624811984050b007503510540c4000f4803011580302d070880040c800d82d500b8981d00b8010b00390722884d141e0100c40b035801c065019600d10801d41446040030400d4460302d4035402003074024040d5036140280281c2150500b8224a051340c200308111018122880040417080804000d403022a8031127400c202ca050141d1403080b440402e800c4018410343c5000110b190407240300e2004484e4007584184640d09038003808441941000c8a01303829101c0d0302e003d001402482c0014680000c400383d8403c0250b02c0c10a000e0608007038580d07560301d280b0f00d80380e007030207102c0151088890780c0313107000c0d00c844006280784201d12a00b0200418102c1c0041040740d0f07180000c00100c03032200a0342c50512880030083e00c1d008510340348540021b4102d41c801542e030107800c100086403003510156040d40e8400364107d0340c1180303400041040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 707392850 1250 707391600 707391617
    0x19080318030d1a100503010902030c130603090501180b06010c11100c021203130e0705070b01060305100f080a0609020301090611120a140601210203070509031c0f0807 73
    0x201004102400010780c0c0344030007140203d80e62022121003048092914024610700040c0064590828101ca045411082c0d0050703880d56014140a03443c0130719207140400703810801000500a078182c00c02e103442801074000300103020411103d0341c603410084000078540c01c00c030750024059600842420304008d00441d40b0658a503480c0c0300048200d4a41c1d0307410004140300c40e128005605003000d0304201c241400d4004c514006440401013444c01307561003400400700001e0001015030b4400d00c160381500b903000008428950b128180500034213822610300480c07144000001603c40d02100e104011640e0b000050075081083e0380b0b5500142140c030354140e070150340350b140f0700300051005c1c40354441d0303171941c5039420340c580990105040c13000002400c0b08407c20b003007004110900180c0c401150b0001f409003018031404528940c00b070f10450380b50558558142c4044204422690080c0041a99481c200d0a5a07030220321401c15543c8107180261600009100442c3e50190030700802000e034000740d02d410310400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 707394100 1250 707392850 707392891
    0xf0301091413120e1f1413030f082208011a0603150103060f08150a200702010c0b0a0f0e0703080406030b1206090d0828020a0e04050108030a11190803 66
    0x15891108408200500342041d80813042031b0f203c1c0c44035010f40042d517101d5260074035403001e030078404a1074000503224442a851a5003000090806c0303c800c004400d95500034038660100322100e0040c1ca1203400015420044142071880020b40d102900344030080045045442d091429880804800799081c10315030703910340200d00c0c44074005807040240302e1075005214402c1c554660504a00010b00a201810b0600e1124044110140d041003484800c0f005040d44801c240e0004070769230800f14401514411600e018054250038940203c1050064541c003440b01900411645075928400c1c0700c064941760b0140405d0101d94461740248008180080440402201422040342803100580d03c424055008210303210302c00e608404056400840c030618500f250440741c16904145030508542400d003980058410000385c01130302c100d0361840c2c0150003008250703181c545450b40c030f610003030800b40860082100e040740c141001030301a5290041d013220203203880d01940e4100301500090024a182d0040014406 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 707395350 1250 707394100 707394109
    0x7031506050301060f1514090108060f060a08040507120503040b0a05040803030702071e0e190e0d0e040501150f1b1e0204050105062505070503030f0301091413120e 72
    0x40682454140c0725011894103103070001d0400701307001b120188040c5410b80b8003039084050a542413290b0a0030100c03400c1e564040000c2480c410308000e25485840842e8000990303500c0070f48144200d00c5403007212126a00d130b11000f90560766004005040754010802440000701c0840941100c07801401e24038205034803a20100c0c11608103c54101c0168440102082500c0d0101c86a550b001c942503c2280040c1c203002c03194111031401441070500c64000d0805840b6250039610030f050105116007a10b280b07050072040109005070441149100300d0400c0008075101800003000801e550013510303445520380c60548281d800221200e0a1040c003000384058002003038521112440c026100141405a07100c0c41c030402c4202c0304181c00c058041c40c3c05110b044040080c0390a94000c140740381d29a40000b010a2400034503003003558100e15054000031902c1d41400f400f0b000514182e4040300c1e81031007070b142d0030b00b42d011005504482c07200f841c1c1051502c40d8045210840c52030306101603440e005000094000104 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 707396600 1250 707395350 707395361
    0x1d06030f070311241314092703040801060e0c0408061303050403050607200c150c070306020f07032303161e050405030d03140408030c1917160207031506050301 70
    0x2400c0110000300301c42c41c46039289505006d8a120955800c20600320300110380b140740d0040034811038440c2100c07480c64858a6004119030300f00c0a40880f0f80d6542c0b0b404e403081c0a009680b1400030300d41d150401003600c4000b0395041d9000e5481c0704000b01202d0396100704110006e06882000d8003840f408110100220b002441201c0c40386a25880701d0b030a85000b20310607519607502c28003018054004401100803130307030b803410744c610141c000f4100039840344082c0b01924204011366000070542440029401001000480034155490090701e41d120f501172204c0c00d001800b60600c1c904074020f0b108000181c000010325504058540c003510744241074a041c82c0c0320366640c011b0350485e00040f8030082010402c6180c10040550260786138542806600340200c1d031071541c01c2001d01300811800c0c000c000600c070103d085003a2140d82c2d107020f01400604441c10006004090408100f01c6c0c60742c1480b000034002c0b07000c00c16036146080346600404002d0b2642c3c44103043d840c40a50a1000340d6150500001c440d43c0c01d010b40c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 707397850 1250 707396600 707396659
    0x30a060c20011d06070e10121b090519050d0c0302041d070807052b1506050906010309020906010f09051302030916051302070602090a1d06030f070311 66
    0x420006100f101100d4482c02c60501082c0e50012040105043e4424041c1d040c03000e003034600260400807998151b03400318a0b401c05190301031800250040100682900300d0005040762100028070740c942d0140600e0013145860081d10048515040182e404d0003403001d154a4060072003101e40945aa0000f4281c0f25200322245181d01d03580f5000342c00300014848080109548c07001856110714103800304001c1065400e100d90410b1051108c0f6942610030102498000d500144600100307800c81001002409640100c81c041c04c3d800002540c194060720410054640080290ba90f65607160f004403607001c140c0c40300c1000c1100d180000112230300c40d6180c000e481982000c1c050303228a02034080a18100340c0030800000c2c610810b50402c000e865403440c54010f41c081e1107025a48405505041c00a88640381148cd0011060040080c00300011140c12004610100f030101e00c0740c43d00c00c01c06a4a0149840014581d080321400f00001503080340c4401e0001e0002e041210b00038400c85d00381c0c0205954201 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 707399100 1250 707397850 707397853
    0x10605030402061c02120c09010207061107080d0f02070902130308090d140c01080f0708010b031e0c07050d090e0a020705191a010f06020607110c03010f0b0f0105030105030a060c20 79
    0x4000401001e0018680d521511500c507072800c5c2000072300000d50f1680544920814014110b415610951062003040042d00028046903889450020700801c10b42041c00c551006025401010804c107010340201d6240e01d03980e80c240c0394414119100c2c100300d0707400501035650059890011200080548025071030b10502d800241c03001807100000075260300002040141d02c0400c90b010419041c0c0c05ca414141540c94030741d00640c0f6a07032503811000c1841c44140782c2444940c0c40a08011b200301440e070003001054070420076a558230f1310544065405110500903d840110b612000a1001321a640607240e403500a40031110603001f41d20b036054807942c43c01c0c3d05071000b54a0050810030b00a031245020f0062000d455080ca10a1030510004d441c0e84029000c8410421000c40d10b12101c082000541443c64005008114200141828000410741640e409004c1c0300304d0b507812406503000304d058904803003024001d402620308596440707000388100e0340b0840c203000850540802508485250102c542007020 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 707400350 1250 707399100 707399107
    0x31c0926100f0b03031c05132018060a06030e0a0206040f090b031902091e07080910090519050114040b01030c2c0601050d0c0801140d0803010605030402061c02 70
    0x100b20406072540e9025036400b0f54804c01c1a0110b603034250220360307041e01d2090000903441d01e030341c24409130b00707200380f070001e44504000404079210f00341e0f8020781342400c042241c4548a0b43c1c0510105040303903100f02c42069210b48a8402002028000c0c3c0244082c80f03092070a40c3d0030180c0d5075000a60a80180d0412480b40e40e0f00d003000d101402140c07050301035624084000b4245c4548032091244031a8600600a0051007042c1c0480c400003182802c0118003604205051b001d4541400c0040c25942c0803030303662070507100346250307190380031014450b202c01c29410501600c0c10030a01000201f1070860010200d41c25983e41e04440b02907240010082d014070710441000e04a540744d17003000060030b5401d400c104034003030300b40e49403602d2a1550345060a81b1319040502c04916502c19006036902c1c0038070100b1000c49420011545e54080d44080c0e0b982c1a81c2d200c02900d0f14040f42d030b01c10300c00810a5a80300401c510340400051281c00e0080003d90390281c4020030982c80c1c51410540d41e08034007010388d503c00e46180c010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 707401600 1250 707400350 707400371
    0xe0102040806100911030c2b0c030c0908070e0c0d02030c0d0b0411160201210903080c0906040611010b0a090b0102060f0f070c2f031c092610 62
    0x160106801044c401005210042c08490f2284461101602c24034041c0300002e40d42504c0e0030f0780c2c210074440c2013116040380c050459a1072108082c0400c01d6111000030300d40302e100c4101a004500c130790180c0e908207008281403820012898440348019240f64540c10051008900d048502d00086102d40801105180c4900c1d000c41600d0980342050035403440b550400e080080b142041505880049001c1240300303902c0c02280c001a120601280c1045141d007524245000311003000340c011001007846642c81c2019a50f47e004580f0300d038050520b80c01e600010400040003140d03c40c030b0a001c01e00715104000aa070034081400180c00140036402284195210080315407a90f80500c1055800b00070520710894600d80700c0c1d00d400501c00300520b000705206500d140b2600740401c00d49039210b40d854440c08454843c41050300594101c0c442c60541c0d1017482510150b42c0c40211a0f46503000c000b019449540c03c203402c1c10a8501e8501d868102e4940800300a15401b001c1c010412080103890110b000026500824 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 707402850 1250 707401600 707401621
    0x9031e0e01050f0d18050f1207120c061104080c010503060906012303040c090e0604030927020c03030a0507021f050c120414191a100807061d042c010e0102040806 71
    0xd003507d100140c1c2100910f00da6440e860b00441e81c40d5644a810402204140d0b00155a0160801d4024115034a000c1d0060004846071000304191003801c4203d0f10890a644c00444803880111100398102001c1d00c04292194041d0700380d00340c0c05c0c10010302d219003403500052110301a00115003e4ac2e01080455003000f4100c11407241480c0304180c4005425189466140a4003210a5200d403520840105010440b20b40340c144038209000104d00c070a540c0c0b04d080350200744c1e80e50400d545000c03000b480c10b00428005800052a48040d00311088101040e01900c041840100001004d8500c940340401c84081030f8407807c28454800d0780b10b451104902c1010112161422140500f1a024095491408004101d208040c4030490709590160394440c2d80b070141c2e58a06c003941d544a040d082c4222000820926040100e240c079a81800c08001003e440a0041005899011003e2410b500d40020045044d02103c0813446224000200220f80c440c1078105e580e089900940c06010603401210a00c100b040c0c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 707404100 1250 707402850 707402863
    0x9010204031a04030e151c020f0a26060d06051504050c0d152909060a050301080c1504140120010c110f0d051c0f09031e0e01050f0d1805 60
    0x800e03520324028420000280c40386205e2448108001485004047c4601d45d5a404441030007190440c1d050322071420440182509540300074000605400d1701c88010a0110019441e2040030010090100718400352a0f134401040040c01070b2801940e03130387d00079966840e18060f17103000d13140e0b03003c80031358441200a0b500220707078030303540d40c08000305070700d0010030580100c0d41054900d80302418400d05101405040e00e1568072414010980150000c513840101d41e80040141d81298800025140700b01d000c1010080d866540c0c2e18410700c1c0301c01c14001448100c803013a0b046071031030506041034015040444013100480700001c02c2d4400302c1c6c1d100e0aa4140b5164041401038021034488000c0069084403030205c7d44903026090386500f04200400d1072a4203c5d1001500009400e819008200b014103200b0741002401036440140c01040703007000800502800340d40c0041c0c0d00d0340c5039030340c001010811400446e072580c004a4513100840041c040c49902ea40c840c0315842030880610495920b0340b00398601a4140300d03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 707405350 1250 707404100 707404127
    0x708070f150b090601030b0a030203150708010f0302100302070206120a02210c0301091e0c03272a0b04080a020103110a020a1502070b090106030204060915030b09010204031a0403 78
    0xd00b0140600d20a8541d0707841550001c409003000304038210072001003091540d590f403001e5854070409059519200c10554500c0c01283c148e42c840f400c42c6c2c0c0700c030b20b01c403964000c5100094010010301082c062491290380a0401584010000e910b03102c3d40c51003507882c2d0348061300c1d00084154005400c9810448201c030034216090341001041d4140742c0b0b0300d4603541a000500c01d9a4020740c5541c0d0300000c00c10710f42402130015031140c008005071401020006e0080203480080914602c0a104d45044041400a1803210582c80070008240045000808252403000030750700c55030038441c0c50041451100d880282c8050031540d401018490050700004003503070310700c640b90440f03030303404004c4901c49e2a804a03200000f030782c000c541d00c400706c0d11400e40c0354001c0c455904054031100720401031000b480d13030640290040f24004c6030180001a11525900101d501c0d82c1c1000c1d01e00407a808041001a4034040c40352b0f8049a5200014106036a0ba2110328441e1003a075a10b00170700300300d40c04020800d0340100c800d03801e06 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 707406600 1250 707405350 707405393
    0xe0102010605100c1e05120c2e0e0309060705060907060504030b01060309031701091d0105160815090c12090a030c021e120307060f020a08060d080708070f 68
    0x310f25416000e05a240210009045485504003c101da00000403e0900903170303100d801c45e891040032069030001500000d1410640f4003506900300908006012134003500011060b02070040c40303500080e10001c0c4091003044200b40410f2001c1400c680c1c405010382849402000078082c14907208040d9400d1030000d412003018007070284028000300b03e091214034155021402c000900c1245803d0585000e220f992044610040344c0d0004151081207070003200c42070f15090615036104c0228101e6600b0784104441362200ca4044034801e070341c801d102d00e4003650031107000485510f120b880e1502007446020201d070420043c6000084100054092169696110044e08085c04a20b03540b581c0c010010403a000b0040c0c4500740c44001101d41c5540e4000d100c0206a00400c891400c49043d208251a0f8002d4001074501c60b20300400c400c004026402100d0950009654038501903880c0703402c10481d007d80c09002d458458081c494800051102c500030030005000303800307117032007080a49802442d40f4141c1c040819407 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 707407850 1250 707406600 707406619
    0x110d120612080702060f130b120a2f0f03040b010e0c090a271415030703020f240a020313060c0f171c050601200c09250e0102010605 58
    0x814052001d46041c80c3d41100c400340c0d1b4041c90f28010810f0b00841021141c3e0080e403c500140700c0412030028100c111030007550b001c00d6640c1125050465590f44451603100354010045960708100f909100c200a00c540c0321241031409500303d144c1c190f0412038044400080c400b005110245a4010342c503400780404803c507140074100030201c0c40425403440b1b055440403220641c2261105411601c0701080300708881081030521024414800b04403e844480340001e00018000040c1030100b04801504d0300a001c0b640c2c149500010701110604010b0f00307a02c4c81480c120005101408500105a0b00d00260b00441c1c681901d40c03039010120615501130018030038040b4027640020460720b45205030903000f038082841451461909a00f03171060141080050b060305804014558440e444517000b0031080e40c903820711001428404000a4801d104040385501100180f00300b0701e050340c1c0c83c5500c148001e140f2940c040d4101c1124224401c45401c600c00b2400008101145590900c01c403001460b007282c040c0030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 707409100 1250 707407850 707407853
    0x170f070b130902130918060507030b0906060a0201090b090c0f0a0305060601200d050409060504050603030301090f1d1027021201090f2018070807110d120612 69
    0x1031100d481030044403070300801e405101c840d03c0074441005210183e001d0081240039003205d0000c101c0501c6c125820340c50320020641540c803e10510b42070310030203000254941c441c00204030980d00300398009011592100b0b80d00740010645100c0c075025010b20320080125502a4040001528544180300c0c011001c0380010070100354000395154002d10b00707007001000050708100011203002101d00e800403d00c100c00c40700000c954000001c1c0100c606490040101c20b4a031000c00c420707100c00b40c072100d52650051005014400d115801001e0350070501a0000d1030811001460503080b408a030a404140c10050031941d41c0038a9000e000750705004070444445808422100f190204200e24019004038800a81c2c035200c403600350300000107142c2007007042440542c0c5203003002302081c0c150070440548001840040032800e144006602c0b00d034404048064a513104081261003001c01000d1808000c110034010119074006c0c46100280c20305a42c0320030080148010000a603065036204404a6040c2000c40c0c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 707410350 1250 707409100 707409127
    0x1b0301090f0204092f010305400b0411010e030610060c03020312010909021305091b0402091503061c0b0126070b0a1101050403090302090a06170f070b 66
    0x3101d54103e03000900003020b400d121000106010000c4420840088040d0410440100c08060680709907401e01956a4201080502c200100c0d94a261491401e0000c6240074104400b00503048040a040940c0c01003034580c4055000203480c165418003e0a50710221541c1c0240c000300521001d0f0001c05580c2880c1200590303400e42845040c0070400b60103086001c151003441107514003100c1c0c00c2c12440a5840c3c00d4594000c00200700c0807072160300c0c0c0f140b060400e48443d00a03540f0825209020b001107040210740409049040c0701701a0380980d081000d2040c681e0f402d40c00f550a051045202c50301ca15000051003603d030409007418105451110340100003400840b01f485c191900809400c2015034010780480c1940c8503401e61040078002d814010070040314260261041c11541c4d99421003000e24046018200c580079a130280010742e840d803041c0051705041c02c01c1138020f540010001680d5590f0907420841091241401825030001c10950110342803c00c83c2c98054156900c1140ca40303854040001c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 707411600 1250 707410350 707410373
    0x9140103030e030c0d05150f04110103150306050406060314010612020607050708060c1908090a1103030c070b070c0504050705120a0b18040323070f02031603051b030109 74
    0x4042000078030300d4400b240c40c24485070800c01000340c0071010213032103882c0c411388031150703450076020001c05a03000554a048002c1401c0c012074024092406102c076880044003e0101119040c40700070041100000085081c880e840c4034601800001803280c1c00c61504550201c141100c103c0720780e062450601221094481405e0b0325a070407184103a54009074030f0b20030b0800344141d00000503405550204001c488140009210980c843c8002016801d4200c3c4c1c01d0383c42d14801d64a1000035401101000000350400307842d201a1500201181d05000340d0f107000d01d00d84540f613040304010f24400300e044001c114a0f0550600070703140850301401103180c40071001b030840c01001000c0303e40200f00c9000c074010001d00d5000203544040500071210b00b12110480740b01c00c02d015a0201c00203900b048401200141004007800d804000c401041e1030708440740c40d100210741d0b10003c160303414000c40700c0524007d01d2a075442c0c4000d40c0b10300080c0615403100f00a00d5094000e07840054066410310307920400084200300103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 707412850 1250 707411600 707411603
    0xc12031d040204060e130e1221040c0b0c0109061d0c030105161d043314011101060509011706010e040c03020405090309030d120b031c03200f1309140103 67
    0x1a1031030702211480c07030400350858400480490240342960340d510346200005005271076200c84914070130003418116034644d02c021a001b5008007030b0710000340051072188000b414100440d40000c200c1124a4941a013126012182109030705c000c1e103100480c8000c184071440004608030002c01c5540780c40101d40d0352120001c1311a20400071000d40003545e0007158420140c0e2108054010031101e0340e0a900404508112180d0250b94002051646c0045401d041e020003540c1000403054a202010001546c802c1140462040d081d52610004211900c82003a00c5008019001e4140c60702103e88250f0b90034000d041e0081120010000100008500c1c02d90a034002c4035419540013a884e42e500380706900b180104491254035010310f400030940389512103609280f04000e11010005071160301c0070165204c0e1210401d056502031188a20502070096201c0300010507d4402d00709403446003125080b035a4440c1700e144a590743d0201d91030140187d04401c840182400042c01c1110f0000225030b2031254005110 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 707414100 1250 707412850 707412859
    0x2706060306030304090615120c0c0b0c16051510080c0613260d020c01021f060503060a020d061505070b0907050d05010225021c0c12031d040204060e 65
    0x401e04544041080754024a03010350108140e9072121005489001c0404002c40003803000310810011071001d00c51041001300b6038032106030a45140daa590a4002c00401d0020301380000d0120481c0c07000104070030344104c0d01c2007028154070a0b0f4608000c980b048054060842d4108030710041c801c006000401e080074150840b1025180c074006030421a40d006a80c102d1801c110443c0c10700c01c0000549078481003500c140d50244d86005c84030560881c1e0310746c604210103006a2008254840c10040d01031405480341c20342c00089130860711400401c1c646042900c035045c0312035001951301e464020b0b42c03084101410511003144030312402610000c2607405001005019885c0c903d000c100a401c040203090300034003016210079040f11407410b0144c001c2d0000c0303100d2144000200790404410b03005540b100d040a034024080039403030101c0f501d612140c101d05402240c071244c4568022400100101c911003a281c0700340e41c3c109000c42100d811145000b00700011301c0c003c5005110603c8110780001d843d01e80c0c40010f8a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 707415350 1250 707414100 707414107
    0xe0d0215070305100e0c0d0c2f0d050906070b090a03020601080a08040303080a0f0c0504030302150c1b0c03060f070f0c1205090d1208060102251502010912030b270606 73
    0x1110b0700240c4500d56104070300c7c03460100103004454010766100c03500c12100d40420380084024080685100400a901007143c00c5000c810460794000e07006401e0059025040500748405503848050341c140a4924108a502520300c01c800c041e410031425024103c000050411042c4a940700c0f0310900035400b00a0610141900040c004400c0d9882000300c4519404144410000c58001400e60b038081d004c20b600500a05090780e505070b40010400b8050444082194644065940945400c5030360985200c0e0720f028400440c501c0d076400700002402007c2d004c40500d503030708200c0b40103010b031040c0003030f0282444500807071035000ca00c2e02c10b90302c000d031513980c14019900c01781600010b0b91031070521001058001131906210f6181d03480780d501c502c24002a021182c81d94007110180100d640102070042c01862661002c3c0807010090441c50040240c80c000428400707440d5035502c03000e140c0280c4c0381d0002543d0700b00080ca20f140c0840340700e200c150706d8402c0d0064001d10312100000c0c018004c0c8450301414000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 707416600 1250 707415350 707415361
    0x314011205061302040f1109030d1805040b0111120405040b010305090c1309020a03080c07060903050a1106071505040605160813110909010e0c060c0d0804060e0d0215070305100e 78
    0x85d002a90181806c0c0c3c0e0403c00d2160b40e641540d650f0300300000041c0a4441c08181c01030307040c041d00d240c2c008000741b400c40d079078140d24040400020f00506424a4100110310b51071000609080014880c3c0d6001c243d00e5948840c100801c0c80111001841e81034105800c06041c41a091800b117002039490100703880403020284242c415101030104100001d402c4011034100100344140c0801904c961a060800e9492041d0f40c3c05040f2240601804003420315000f481001d070004060b81350040c059000509043d04003c4103445035500c5000100c8190200b84d00d64040000b048807902c01c05034814100c8030003071030300da02180004001003001020351101d110243c10640034070096078003843c200b841c000d00d101810b261520009018000c0c0c04d1080100d03102d561807941c0310386071200694401440c0203009048040c6a51000c489a400183c025a1265994030503011080d500b40050000c001040c1c008119600042540700e220300c83c0107111108162810062044000e40301c50740310212004240e5040c0d0a40b00c5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 707417850 1250 707416600 707416609
    0x51e0903030c0615030a12032a020c1219060908090910150504060c0b1915030b0604060b03060607030e0406060c110103060e01051219030314011205061302 68
    0x19400140e905110108074019000c00001e5054030800380c0d8040302995004c080289540ca00e802100101030201c440f0708156100e05ca0740c880781810391483c0c41800003500315180c0350903882203001c6900043c2c1142004e404181042605180c00325001c030005d20308150144408413a02d5403031785000b4441d9888140b0308040c041e40006680707551800070300e0201c860601243e0580030048500c00c581e15a030030f990310101464001c00991301210602e899600c1900480d584090f003040c00103180c0729021280c000c5080c0b120581e441103204110b90401d4404517142182011070071030300001d22440c402c40c2407200c240201d0712054181c90304410261811a19542e4a00e400d5a0018000e95901c4c2c2141c502000082c416038041034040c0800c0c01039041c6264844000011000e450140c003c0449070100740004000a00301040802018088074040c5c560100308040c01940300446808241c000035210b4108203424410700032800c1c01440c05d0405403001c0c9076260b071a00d80790007001b411403001f2000a1408025502da = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 707419100 1250 707417850 707417857
    0x1208010503060a1107350306061c0e0706090807080610090207020d0b090c01080105010c02031e10060e0f0c070c0306050c090612090d0f0903110d050709020a170106051e 74
    0x2440005a180007070311140d407800780c0c6c000c0c00e151444007003000318400503102141d0440c0d00a200c0508443d1404131340c5640218401040c82200c03a400303603504d90010f03e102c01032014201900721640d40541852030a4561444c00030903410804058201d5001e100300303104a80401421030b060f42e0780c05038a610160001a5000f10705080180440408008019444402107104421860240ca0350506a603c2d6001102c106040010094041e4403600c84a0721b0410505003185500405204480041d00500341c56800e80d4001da004820b1440340c0323010301518426a208207944001c642c10180c1c201740c2951202a4a03400c1c42c840500120355580214580510784000c80302c110a001e0021a903079062039100c0542d1682c202d4071480359015001140b050719100b1079160801075030306c1c3e584010072811070302c40484240408030b1059020740c0c45140c00b070029100303001c00401403698101c0141c59a00031880a0140c1e4065071030780c0c01d00508540180141c5800c8030544850518002810080e50000a1024403911 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 707420350 1250 707419100 707419103
    0x40b0a03021201150b0904050705040b1b21030f0f04050303040b07140c0a03030c08010503030a08090a1a011706160f090315020403020a05030a0302030703110304031a041208010503060a1107 83
    0x210110000c90341d40150001003d641e138003a0b1f020866030b41c0b2000d0468403070103940115014240c0c20800c1c00d840810f40c03a50380f05940038203000da83d42c56207a807400b84100040707680400e901d141d01204200e0510700c4168010340c802c0c1032400b003510b0361401c2d550f850344900c40104014805841c11001c46c0311940301d07858420039040c0701982c40e503840c915040070603640c251a000440009003400c40030200c00d40314003407990403140c0141c02103042c400681d40c1030790075540092154401384117142510000c1070319080c045940d50000c1c0400300300380d414031182444445a10300c1c06031455001205200e01c0d401c401000600f443d00615006880303600e801c41c00c81e481d84440c0c0c0081c0000c034070b203640105440c0c02c40d4000e004032403084a0040503a5911420b158845000c044007070b000d03030010721070140440e010310a0303544110702c9001aa407900c1d8885c1d940c1c0c05c1e002c4140d804503010f40c084000300020040390704608505001c880c10030781e01c42d615000020703039a0440200720700086500c0705020161314001d10706482025 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 707421600 1250 707420350 707420381
    0x3031404030908010e011505360105150f16050a05061005040c030603050727090602070312201c0f02030601090f0b07061104050904060b030c040b0a03021201 69
    0xd0516050050100d0380034000c2210a500c0c1c596040580c0c82d051003821034001190409008603443d000422aa60742101e10707640410348402c0e00078075086010f0a10003a00300c0c1550440308154108020310004143e040802405903408110340b00000b85081d050303804036450800341080b206000e141290030141c01c10002001c1c0e100d0701c0107106007100084c0d001d0050b24010b850420041c106014220107070707502880042c0c900e801c42d24090047d1100700040d0200d105c000795a411080fa42d40128000712145240d0a40b03003694041201020164880b05509a0b100d07401c1c001e124000c52140b01d20030045002102060f85d580004100580c144100c41c00d00226100c1c1c14101700023420001041d0281d0f00484a5070b0000c1c000d4100880c402d03516101d0441500c480100850801e0110b03503c5100522000040440c0703080c003030000050f075550310500c2505c030318405c080100b04030000500349031411031051090384c492404c140092085880b4a500c801c00c6a4040b11840c880900e101e868600418a215402440 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 707422850 1250 707421600 707421641
    0x403080123031911010f091403070513050405060601030501150c140102040f1503021201090e0a0f11040e010c020a0602030606070c0f080607050a0f0f1404060c051209030a0f0303 78
    0x90b40030a001d40342441c02045807407005101e55004607040da5144400c0c1011a07e032020520101110440c4165000310280844000a841d81d0000d01500c0d203030080d2210300d645440c1080b081007014018650000400c2c20144140e505000b0340ca01001e080301e1030300c0c081004c044140c03014840c0015075900522441002103559984641c3c01350b224040b03a00802800100e05216924001d10038402c695070080c0c0c010390b00009034203100c80440034003401603800000303115550f41300c1c0c082082d1031074101121384550b41c0c1030010859141030001b500c036a000650100c0e45048840c1c2d00d8160040388410a550703202c000140e50b5a1443e0000c0d02e80e0141c1a0083c0c080b02540b1070118110440150035825107160348111041685e82c01c0040b60644511020040042d069000d006042c0d030090012000000b11800c0408040c900700c03986000a4201c0d6200c03000041d44070340b001c814082c0074007140c035110307aa03054640c2c030b00041600425a00c030806d440080166100034002002d140c801d0703010b501004080e00107500d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 707424100 1250 707422850 707422873
    0xe011823031203130b10030b190510080c0112090f08071502070c0b090117100f060311040b1b0d08071106090c04020f0d0207081206030303040308012303 67
    0xe03440e4400c00354a000e0302ca15007510462502d11001d03644110000f509070448112155a40c607010b850140624480710f051140100001d07103180e850038072581024602140d4000030001d030205580c03016047c900c0e11518403809224440012401d07049110080c00e000f01c07104910b5000800901c54254080c002c0001d03200307844100070010000700a61401020b08403082e01202c69640128419030400034198405c2540030806d000804000d407603400014109814680c0c4d0118481d85e13039080464030707250012002401130001030510400e27200582001e02d002c000ca180e00c42164040e0380300d18001e2100900d0302160105840180b942e85007038040c1e45500b920648000034402070302c2c910040d501c9a003c0344500030082900f220000e9018405c05a950080c0080ca043c841400025441b040d12561444420061040041d05600041926901c0b61640341d030381f0900d180d8401d1a44002500a40c07180e001041030002007a403018a1605483c1d035801d500c4c1036070b090300c00204115144001115018001c0b00043e21 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 707425350 1250 707424100 707424149
    0xd030b0a0b16030f110c0d060b041b021903200703020a030b04020f040212134115012c0403051806162306010f0303110a02010e0118 58
    0x800083c402d071107038402c40c148500141d5200c81c012144610076400004281d900d4030700038101360011401803400051000502e00483c060360302c40f00c48100414218103156051581c10040903580b40c15644d81c10000401642e03000384040540700c1b069140361204010f100d4a52818055980211b6004014003038456491910010924003120240e104101c000401c0d8420b05003070003110f168a0f840d0003107076002d5845080300d0525000c01c042c10f4952440f16140884420403a540036a032002c0c0361040c08000f0140000350b00002d0300034080042e05600a001d02841d0307140722401980c1546c0b4850b41d50810003620302e44550042016814548216a403038003407205042d04400189200e243e14100c40680c3d26055080c010540720301100e8812075502c80f502c1b0400300d805100d00c0c006200d1415016802c0c400501484c0349498000e80290103012007207a010030400d030b0410308106d05c0001c0140988020041900042c0501010114150620605080d450f80311030b601170301070001e0b02519412100025080740a1b8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 707426600 1250 707425350 707425387
    0x1d010207050d1806120c170c0408010506030f06010302120f33040c09150f0605190e100c030516030306061704150b03071203050d1d0d030b0a0b 63
    0x303003c03030361001081100b81100d6140c10306441082d00c0304075080580c560b02800902440c001141007005110200301000002101d00b80281810346c0c2a94a0ba0306260765142140e501504841c465400401480900c00020030301d141180d0301220588005051140101e0030f1041084010000c1e01800810240ca04074444128200d02c1c00d5646d64100541480020310081c40255406451204c81c100200490384c1d49030807070304808904032a020300c6241c0d00e801110b1101c80c0d98001802140c8042031030740c141c241e601a6a90117642c00d00d441d85015603144007003a041112110f0007010020f0701c0d4802000e040c0903004039000304c2d00d25141c2ca8192100e81c24002d00038003a80c0102c4001803c40360a108034070590107040303406035070040d00040c88981c070090038500403c0e540c0c0303045406d80a5100001051012140034004c2980a0b8407003503560024401140d040359217426209580c032081c1046240c08101c00618080840398a09001450a82000000c0e0140240398400603042c20300083c0c003021003100b09100d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 707427850 1250 707426600 707426623
    0xc09080a060b2b33020906130801060e061e01050a0314090c120f0c060c1c0804150c020c0f012001090c080a02061e0409060308090f010806030c041d01020705 69
    0x201c3e03411307841840b44c40015060382c0024910440110640ca8050a56004002c0400d0013810300d441c0c220810f4540070840481e40c000b0080b44d55543d0304205018040d04041e504c00021103200c242446010a5042e188120141e05810000003040b2000c15038002d50059130f842000510305a0649000c0e28150382e24840b116015002c0c2c00580c49100007468000382c40c3c603148030340e0400380004109040c1841301e1900145001025446030005c1235a5454140c0f61503040341005980302101490242004255980c07800e480300d0895291003805246e02c0d41c00b240f05400c20f0307000c4a4103002410b050004840000c0b507140d984050b07104000302c440262105511034091144111001111030741d642041d19140c0c6e1071400040d400a40402030035044043c0100090f090b544981c45a03428030f5202d820400440c0c035507400c1203413540d8000915144918000410303200318402440c2480c03031b0b8940180426158440841e040b03000e1512603410f1825515161914010030501e42c00031915a8114203109658892030b620 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 707429100 1250 707427850 707427863
    0x240c0c010e0307060e0a09110c1b0a06030905010b060a03022508031305010f0c03061e0b18030a0b07051b0c03030307050d1805030d0c09080a060b2b 65
    0x8524950141c031078403000d030000a0250454a2400105076411413545c03030680d80c00b00398140c2c0400c1185952141c8450300945603038640e200d019200106160410510160b041029a40340d01c00030f0ba070307440d4400b00030b81d21940b07000b084074a02440c01d180503045c080d0040d5440007000ca01c3e0302200307070305501a02c0250a606141d09800c0d50000b80800860001352001d040040b003000012441c801080940141505c540000500120111100c0c42100c0c600840440006c2e01d4032030400c0901444810000000340821070001c0e050700d06840220503200b40519a0761030f43c10f49805c0046581c0a10001d0b070000e4202c0b078030341d07891b203000c000041181d403200e65008180c0304094010500071800113600c00c40120003500840ca903485e80d4109172015000314544010300d54503809141446030900c3c070b00e1042c252040c0010358643c008049000281c1d08407c80d01410403032045410040030100080008217187c11035000078004d0700205c041444048201c503e05009800d0342c900700310700218400d03035031041070140b06e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 707430350 1250 707429100 707429113
    0x2a190302030307140c03070212030403050106140a0b0c0d030b061c020c0d02030703020604110a05032406046e060321041502070906150f0806240c 64
    0x8000c013a14060700449041c503600520488005080c2580d0b250101d00105003124200365a956445013500c0d020b80003d4418540001000d07c20706003130300920041c01100d0385940c100999146407540c0c5042009003001010385400c0b022916440340b900312405000c224402808845c0031040682c0030354005080c0000038032548424140c10792010007902c4083d507050340a49916240c1d9100d02c01200780b280504d540c4803100301400141075a0400402e00e84580800703400b00d02400700e0b40000392070b500040c0040d0042d4204a10302071410074444d5118515a1020003040200d8005e036201c0801131040107408125100e1003145007180704103003682081c00341c4a2018035000c5d01902c0600000d42c40141e840036059484142054144802c01e0b00b0040f00030045645542420342c7d4040c3d9008004c140b81800d40940c2003000c0c1070007880b6850069501801d18549040d4036481420001001c110005040c88100072500e404210995117403502000350040003c9200b04400510003806c6040d0b0054a1005c0c6511901 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 707431600 1250 707430350 707430377
    0xa17010e1903090b0904060e01140a060816030e010b06161e231203191407050a05160c14041a0901180f0e0a15022a190302030307 57
    0xc141c54203030aa4035950710400f452502e107000c0203a803c04100d09901c59260070300030420710301008001e4000c01d00c0d040c00400c900803c4007030020031401c030b80200040003411000c1040100703202462400000491600145095034150b109004150031034400b81d01020001e032034014181c410f88186c0c0000c0c0a14180b00c501a011041420503e40401000740714100e11089a054004607250307490081d00e405c01602c2c003414418195104580c000c40b5111f8918081e05540c80c1e0740b142c4c610800582e001c5482401140d414070940140182c010340ba0803104208001481901c079909114021080c10703800702800b24442e46510040c0c0d070380707002d0f400300502442c54420941800000503803c03003c010300142115070300e40d0802c5d4901c000d010890500c040102e07125000c020440505119510114452034040c0501c5021440d140c540741e032503800e102505500501074415005541140b280d007105081e0f044000240501c18032a00b00121320855826840200015105054010005521500040d0348000396000903 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 707432850 1250 707431600 707431633
    0x14070b010e040c080303070c030507050a02030a0b16020c0312130e010303030f0507020d1706060919030b09240720210c190c080d0c11010c030e0f0a17010e 68
    0x81f81c81000141d850b8070340340d0200c3c3c01030780244002030081054480c02941900407900c0e00f60054001c03200e01e45d00d1070030009060151b01c50040c116400d0b2019060000701040040e54501038800c0c000403a0300009180c00787c00042448000003400c1024030350080c0d60396410082c0c000c01c1d0307004040c1c8080d828040090802403012420300404e03491500d8141c1da480c028071490035403501c01000c464001d0802c2020a640b075075002c024842c06008400004841d60443c039100100b040c001d0210b00199000000c0400743c1c0041c1800c40f0010340c07030340203560401e940f640c008488016603042040c2d00c801041c01c800085100c04558100d01d900e055070035800fa1000c008d980e403094415141040101d801c00903000710070005542c85440385034054487d0440f6240c94401c85824000c03252807010208008012010400c0780341d40300202070040034280141d0905844e20701400804441c0305591240c00551000c04c0d46035110221b1074090445180d507110020038003000d1600800c500050b45003a4800d07415400f445403034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 707434100 1250 707432850 707432857
    0xd1b02060709050405010501020616053c160b04150f05100e160e0f190f060c11130f1803020f0303091c02010603060f02181f14070b010e040c0803 64
    0xc189d0041410b59640d1185940c0d4001c0100a0b1080000420a450822517005e054590503000e2195140240b4020882c810300140141500481000140441d580d800c4401c07099041680d081342c000701c0d0b02d649038582604114054020a20001e1a004a184001b1340c194001803240900c601211040c42d140c6130f1040d070041c821200d1000d000364078008030014a02c60110088990000303440014035884d803038001031154602e616002038030703480e4601c02c01c090342d00e0804000007404107040403280c1d50110340f00d4580914040c0d0302a40621406c200b400f000e03010b0b55101482c0f245070300d5800c000c113880f02c804ea44a000c0c02440203800610805184807400c01011080300c0c0220350f80801010841e6000c0d160100000344070440e101076550f5507500001143d4039000c0c1e41d108805454005940b0500e00191422050b0b00300d80580c0108500c0488100eaa070fa06144d4400210b16030030240080910342108003040e1007001c400805460201000041108064220368000c1e8880c010f00c1c0802d41c0c40340c00042c0d580c003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 707435350 1250 707434100 707434109
    0xc04050103080a030e1906200f040302060913060b0a020c031501060c080403080a0e0a0b0c060406020904060302150d11030f0f0a090501020c0c0301110405030c060d1b0206070905040501 81
    0x9030402107105041d00950111201020071710966503204080200c00d130850f50f060034191280b075280d900c80d00e00883c0401e511078404040c1c0e8401801c1244425000d0414011808002d008000000c0ca0408603518000390054504d2984414001e0a807520001c4031a9003100d0800c4000d4401d0a07424004c074640880d21144d80c4210103046c80e0725030729242084440403005035064406460400011001c034140764024a801c1d1403584803520078407425824040c00c2c14403640010235012003480003010307600010a00d00c3d040380d0040c078007507140c0b002600020001c00c02903000075400514120510001c5950f84007a050b4150b00e1401000300d20308039405d54065110071564800c2201409000466030700a000f01d4075001070007024009100f0000b50780c0d103401c99118041c2c48443e503004001c201c119250074042c41344110f01c441039543c109807604020035a6182300c82ea90b40d1007890003040b10f05407001c0c16845011041c404903280304c0c7c07404078a40081c0d1221010b84901d030001d0021100803466003098002c1074103e0303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 707436600 1250 707435350 707435363
    0x6040c0f09021e070c0e0718050d020105030403110f01060306201e0705010216030305040c0b04081b0402090a0605070b0a110306060d1d0c180c04060f0e100503090c04050103 76
    0x8003443c00d08040561011000b25420501c548010a8603070680c600144540c04988844158031004051090100340c4ca611051061080f1124440140d03480030507290426454100070318072488146c1c006041c1441c0580d00354280d803902100105129883d0002c2104100b280414154840c809aa11089200303440100000f148401d212074400908170006011890007200018104591103c0503810708103441d1064000079141e100744410f02c10403200110040500c08411480d0500e4242c1983e2902c00081008803005414528524240ca594049542d1884002c00314103030182c40d03400c090311903004200e0603207610000704006090804544180d0281e030446601031802d5940700800c1141552240c820b0690341522a8a00408400030401440c088021030002d0040c0c0913446041c851001c00b01d01303540d004016050203120a00c0c001d0004c440a40c0c030b1a14240b100300c110200250344130070346142c0c0075030030555140a01e4080c0d94480084d5000b001540160743c0014101010803080d41c2c801e01014008 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 707437850 1250 707436600 707436637
    0x40606050708030c071709040b0d05071203020f160f06020c0d0602070206120103082101031707031812120c02010f0e180a0c09051f0c0602040806040c0f0902 69
    0xb02d045080950350203142c07014030310b00d0405a40c3e182039003558502d050305c0700d0700000b00720100240b070280102c2101e2001641c1d076103800f41c01d43c3c4550b60386090a200b1044d8a1006a43c09018988240306446680c98450201c80c9044020800100c03c480759101381c0004144c1540081003d610118015005105c010b10302c503200c003400d4898900a60000d00c0032070380b100303080040c000340e00c00314541c190086000700c10281c1c4581d080b50954030380301151642000c0d8607140c0c82c01400000c518000404402c01410003054440c5054601542c500b081040c8005400f48648000138014504a0941e01c03414440ea065515003090707000295800c0b17200140c0203001c60141c103107107404648114540749800a0003800c3c035040d81160740c1d00c403221201c140e40b02c3d054203846002030031a15400032000001440300740e4060704039591100014420402c42d022807000c12285209540c01d000c4186c058401400d010b01c150b65140c1002c0c82c220502d50054441c02c0c0c5410018640000e411000e442079034091040100d55160 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 707439100 1250 707437850 707437853
    0x15010303050310090e010603120504030506150612090609100e03030f07090902070501090b0609010e010b0a05130b03060910081908300a050105010c080304020114160605060406060507 80
    0x1100e0700000d04560041c83d0351000007031600081d01540030702050000000034643c2c1907050060004111040303482c140b040030081080002e500103441369200d00f81401c0040c403846100300140617881030304d082c4a2015011000c1c000401d02c08030b07030075005038003010803160044942801c81050340d100410a440c2ca030401e200050203020342024865000e812031404819003502e4940d03040c126005213100743c035903a548600c03180801401038030060f0030850844415100c0e43c50140c02200c194014050b19a00c00000700700140c20601a0054480301e20b034030f090000040c4d854907140d810030381084070903034451400680460090208c1c1c0c400d01d01660440342c0513080300c900a48903d03440c6000050110b80f1140308021002031040c987c212a900740400c013040211428044075154000c00018280d0510036180000400090380c100d08101c62181d40309030040c0e1242e95500050320b40380a8404034840c40d402c00600040f074080c0580d80140103604c80c0c1d004110380c0d1900c80912007107a806002d9240130a038200410700 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 707440350 1250 707439100 707439107
    0x9040e0f0d031820040614010806040e0706050703030e06010e0405060604050603060c070309030507090501051009050f01210c0e0109060c1703041704080a0629060306010c1a0403020f15010303 84
    0x80e501000300c3d19844c450400800441c044403060390001e843c1e00001c3c6d01c258155a0b01580c410b8200c9400c50341070040e1000d0b60710154480b0082c0c4160740034070200080000c100340c007136081100343d01d450006461303980d0f80d64041142010070131178040b59940a1400065954030b030078860503000d040b000c1c00a0031680e80b44903401e403e65114010039818400350340000000a9810010407014020314035010409500d01024801c044074405101024400e40e03000c2800140c03142e100c889203da0b024640000880d0b10140d4040109000030920f00300c441c00c059600501582040754400c80540a98403150011b80d20002124070300845030009102c031600180044d11003030800c0c040c1d50028010072964030b1070a01703039445040d00c0e4456848108140c00281014060204510900100340c00903045003158220b03807280e8280d06004190705c640701b0440880410300c1b0342d200310003070490103611112541e0380039148100204031402c1210304500611402403a2940748002082d0020342495280300307002c0ca039080d0b68003603 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 707441600 1250 707440350 707440373
    0x130612050411100e030304080d02060622020f071b0320130c030b0316060206011a0a030c03020903011e0b0303190e180106200f03090405090309040e0f0d0318 69
    0xf04000782500703c07810f256003d0006100800c00c0b07100426982d20581d501a003800002050144614030003918205603885c44210180c0c201c3c14110010f81e1004604456495801198400380c4220501c4105248808598901009682c0074884880b8020f6a01c08981c00b44019a0003141d04006545a1425481d01d650040101100e850030049030040f07414011038a4a80510101031a25405075804c20031590140074181c050300001d58141504a020980192244a04035a03001015510811b012040348268152440540020024003a22494803070b2210350340c41003d040c20705649000091402441c0010407207440c008421141d0100d031010060981d60400c1d80e11000d50040d881c5103842d03c8800c50801d00a0180c43d954490b030040441d4012808665180707106c1c40300140e441001d01c0e00c4805400400e036460180c0440d404250b55641400142c194080e9038225504281071640d0031024410216160031841c11401c00c40788403854101c0c040301501c41c2d50240d08030040e407864602e07020950403800e5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 707442850 1250 707441600 707441629
    0x905100302060a051801090608010b0702010c060c031a100c02061e042d0e1b0f04090b18010e040b041a071d0a0b040e06030a08130612050411 62
    0x6518640d4075008544503500c01480074000a80000b00e030400c0c0001140741000f221420f1130a2280c090030f01601401201c018014140c1490300490b02004580c428802045c030b159110030705102d641524030016000d805602c0c814500e03043c1c128a0245241454494165403407981e40d100d80e461846a024010325900440c03c03000d610b010042510b6002c2002c800910003003e0440c00c0d07070304078082e042d6081c00451000710b9120580702210401c000f0f04015024550b0000d20040d1a0003583c0b1320100f0100b8140b140c0c401003941302c44086000182c070049680034000e1020140c07002201c40d0040e41c030f40400341d2170902410081040304808100403e12004a06900500c1140000010b03018001c90180e47d100450b1640c0000e04100345040350707180807100c4c000b8228400d85410380a2801e20415008900490041d0790060550348002784407950304104050b4001c0c5c100000955a803680012910500038074064030000c100550b00e0340b158403801c0d2140728803c2c0d801032040044000712500304019a606c0301d44 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 707444100 1250 707442850 707442871
    0xe06071103032e0b19030e0102090f040203090c041b170c0304110a0e13020f06121311190e0c0a02030a030c0201061814090f1e03190807080903130905 66
    0x8082134903082c2e0f00084c030800345584c629480c2c400160900a064508007008400c1a9006000d050125100c0441451401c0f00071600541c0301c3da100019140b501308281c2c84c4a031700505116071340400e07644c110485005038806550b241c0ca02150015494001c04040c0d6218204140800c00100441d03189580c401c02c000001301850300e83c03030303484c43e4400030600250780c0400c12020380008082145801c51900115a0b410354a9074184440d01d820160001d5001b026800c4101d40001070404110b00c500000c800039038001d0029009507499030324942600c000380155072068004a002c41c24100f900f00558100001d82da009624141350544110060301c50140501e0641d03481c0e51f80409d010903003804408008114000004d403c0e5001000314040b460042c10a07a01d1340c01c1500543e800b8500411031902c140240380941c1200b489503031001f4610310407540328481684420b01800e1601d41d01120107400b40200381e8441082e9107850002540f0b0740314031644400c00c8060010700300044a000d411040c1c0c403040c0c109 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 707445350 1250 707444100 707444191
    0x7030309080a021f051b070c081f05010807030b240a06050a1e0512040302150c07020909070b0a0311250209010b070c050409150e0607110303 62
    0x1941d441d1a508540c0c042c0015800480340d01030704030310750182001544030035403082c003003410f0a4098901084800035042d4010b100059030809004200003441c0040107604101c4038030b024600002c2218822809500c002c450410000003420000000c00a0a50f0f405c01c02c03050385510b030604001c0302820000000c207030840c3c8441c0c3d0109190b5410000000410960310f81b01c1d81c980c0c1040340200a0072071000817190110002c0c00c1072802d554081d0a40702210402511110151680d00302a8a048007040000d003e010300c801c2002814002d10780541645071084d26601b140384c441e5491582c07505081d001d5600044402e01006c61070900c01d80150701c40078032051505103800d141c0c00e140c00040000290080c44090101c4084d4110705050140e103004040305a502810700c44039503079001481c00c103032240900c902d40355003141d814031008109280f080a00500200410b1300b00042e05600c0e248200c4e032003000300b0604101e018600c1804002c40c0d100fa00180c000404850700e0b006840c6c81900006101d210810b03004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 707446600 1250 707445350 707445353
    0x4080d030e0a02030105090d0201061d0105060a1b080918090c09130507091d0303090d0c06020405040f0b03010b06131502070b07110a0f120323070317070309051207030309 75
    0x70f20078140500d10050190231040f203174810190944680b41e120002c10703401030600303200d018100c210b8141981c4c0e00300c9645940d034005060448603242c41d01940c2c2c00c0d01208500740010401104001c1c0309840d0300345c0c1c903400302d44030b40102003010030002c5030700f41307a10f07040800003031803600d01200510303800f921402198480809680303401317241845682010204035900e6000c52440341c000c0c240480e0300d20301c460040d451441d00641c0a902c480d090840c80040c098100481d404014030b98041c0d901070480a0010031101c8900a00c7c01c002d0610507030f40034025460560101c40c941040c4003164000612480700090703082c901000003005000c0c41c64480300718081c851000c602880043c0042501e140205000004070780d028013048a1a04d00360700550f07002010000c00c003c6500c6130744a030300c03019415040400342d00311401e96421080c40025401001701100258540400d03401c91004804000768004207405640c405400340c04480c0c0c450b2000e0500e40c040c1d4400d102d40d040900050020501c80d280c00305558589 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 707447850 1250 707446600 707446603
    0x30708030c010e01051003020d03140d020705030a030e070f0512030c0d0914010f0c030f031104080d02150903030c0f0f0d0501031a070912030e030706032004080d030e0a0203 76
    0x200c0c0c4001840e5116440d42e12051801d0054541080000e0108400ca07841c650000b02c5420101c50000c05014403c40403004c041d5101d413360301c1c2c001102400f5551800c0320720b001901d9030300c010a90b1002c20f20b0704080e02d00c5000c00141200641c3e449a00003c0e484c2d007041c0411055a08042000c5814803040041c0b45904c00217000c001000c24050b02c54920041c00d0214180311f50f803180070801e0400045181e81c1201c10750102c0c6410301d49408d41000b500540088200310007810440031004070032000003e00003620480001c4100341c02c3d207a9420345490320309003040d80110032019501018554001e00100b2030490303015006021414155011034038160595100c10215003100214108059540004005100e00c2e500d00815144000c41e03420210f02d0042005400c8085a003d859400c451001030101014010303618801030940007411a442c4690340d030b9000300603080101601c20f0868801507100307064207400341580c0039a0000c038040d2004040b50b60040b001015201826a454403c070112640944c40 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 707449100 1250 707447850 707447857
    0x30a0204090c0503100c120c030b090726040f11031f020a0e18011e03060e030c0f0f0327040504050c010f111c030e070e071b0f020d0203070803 63
    0x4159407640b0860726020030107084c1480c0c0d20400314103a050000080369a648002141c01d0729401c6007001a2012074081c04a00410003099a0f54000e00c400090015041c0c0010014450f1007a400b2195141030b0580d40302d00c1c440c40f09540007840c0719400645040011040003401900d030b03001904072030340c0384080740342450030b030f8070010381c51030143c0e8005000c0301800d41c003965140d0707440d00030307900c003090b02010810380800c0a0051040f01d45203040e2000402402c1c0d42d003042180119003041e4140040386a078010f141d2294060344e00c400251103040c4140155080c040b582c41c1861424402440c14111400c1801c2101400c071221040030048180f4440804c0c1d49a115080c0154014402440b0840100c4c0015181d40381102d04507083c000000d080701c1d0b0900b4000b454036042d540710340440d80c80b00f40007502030307000d40410303608108030740940d01c0042041c0d00340c095664450301e41d540c2e0380501e8150580380100b030800c00303030b402400c1c3d10f175050072400140c1000e10300946001e00c0074086178070103541c601d0060706540 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 707450350 1250 707449100 707449103
    0xc0210030b130228051201050922032102030130060c0207090c030903181a0c0a02090103290708010902090a0b0d020a1103130509071107030309031416050f030a020409 73
    0x2040460442e00c40825246d1070741c09480d0a880c1c588103030408c001500c038250700c94417007040c03110310f690200002c251089404001140344c461ba03d09024046d000548041d400c24041d40103121110810342c80300440743c03d811980e00c08400100030070101d5a4231410b002c0e00c040c1d071409003544280c07034001a8101c0240300d80308210150b95000103c0100e41c0c500140900701c055a21400041801e100380b1186007a50f01d14240c2a01524401e40d841e086006c0c22800e001740450040c0d4030000ca14000400c0c080160b000304c40b001d640e91034065070f1050072805402200001e41d124000144010014000800158010440e800c030042c400d9a103580d441c1e20208070f0b648543c658460094011501b64403442d040100c0e09400400c1501550500303007072114031a07855a59210702403113031415201141d0701500034030310001034100702001d9420b04c40e104e0401078811343c02448110703110b001654101100d1080482c80c108100356045038401e881e880c0504101c0047c4902d500c840c0e0501130061818016651442150082c3c0d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 707451600 1250 707450350 707450357
    0xd1a1005060d0614190b0a02070308040b071a150108071e11010f0207020f0607031106013309030318211a070207121505070c0210030b130228 62
    0x2642007280009811803a850300314010700340324000c03076200040d441d507240131b50b5400d04000d600c0d03078400d5000700c1c0340408640c03001c0d205440014000c51004d0960000b4a0403c1c0100050410f18140f4000454015000c540704005100c602d142c50381190b2003200103070b0b040082032809003c001c100b0450031030003410010903a070111715002d0003000b0421080c0100d03c03104800480171420040240c011400601d112605030340f10340070002c4c40b00b04040c0103030341801c0d400d000c0000311050380d038440414207068500b000c03018a0b865410501c081500c2040020b088440c1e0701035981036074581ca560ba0588188842c49800c12004465410100300103400014100d10403001c0b10803594003142c80e04082c0d038002180340c20b892841c41428200149580c000800300103c1e803c1c090390108510280c1400225110813a404600250512007800100c50b032050702e00a186000300c88039605610304640507003c940c170f0181c5490708082c980b202100e0314060355000d08440698068400c10100c0901003c494a004012107940130 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 707452850 1250 707451600 707451611
    0x915020a0b1b041404110403061a06070f02010c060f09050705120a2d0206030a02030421020a150902090c030a061a220302060f04140d1a1005060d 64
    0x611072268001c0c1e03003140404820711110701c00b440b45410548598000d007110040507000d005059242d03030b4440c6243d010410b0500e030703da6499203405806400c0310381c0e40d040091101e4a481c001c5242c10700c21541d8295010250420f0740b505940159540700c12481700380e9916948446100d03d40c036803401000070503032060300034002d5241088208950110003125500043e80540ca0700d40009140c58183c500b41d415164181e1103146030b03944045104952210700035003140001c401d20415240c1c03070300918004c41c414080c51b103c409920800d840000120900303280141d010311100d5001c923440c0d588010380e50fa000e0401260128098000c01c0c00c3c104156004c03440701d00300208010030b0034914070032400039202c200c16070081c00c44880d0070841c46004400c1c080003c0454403404903251004021800001d5030301410ba5a01c44a6002c001c0150350030a10030310311581c0500e140f034070083c03814031004040302d984952031001000580d020030500c658014080a112a00c00d800841c0d242c0d554809420304a400c003a01094 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 707454100 1250 707452850 707452853
    0xd09031e1704182715020d270203120a1e0203030420100e040e070621020c030403080313050105010312030e0604030909270501060509010501020a150c0915020a 70
    0x1940b8048159044510f810103a00c400140c10413001c510340004901441028610300303210325072002050141402c1c9100003901142c0b010b0b2600215106403508203800082000e003000d00c2c00c107100c4608000d50503044000a001c0503030884000d070035424404d292035022104030480090340c82c20a11048800341e8800b100308020441217040d0340401603040502002501078034000b18016031038841c40c0405002d10100c45601c02c1d1200e500144220041804407400d0940d0b41c8c0000c0c2003100180c2c80f0341200c40100008147d00905802200c041c08440d0000b03501d854a076441d011200d40001d8515110740d0035540110b80811824080d69018601401842c1c4070a003a0f002e014003290300c402250b640035000f0700104000700e0b401101400840304202c90104a1404544580e40315200030f580800420b000003000e0818484154080700541d50182d8281302141d80307400043ea0303504a68800100200001c5a0b000e10a880d03d4010030413a40090170f144000544802a40d5200711580b10b2200040c0d011a11850 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 707455350 1250 707454100 707454119
    0x70221041a030a05180a03030218030a0f02010807030c08150a030803010602060708010e04031d01030e0a150e0303270106030b07030f05060114120627180d09031e1704 73
    0x1900141810102103c0044042910346c07241409580501810f80c04a1580200c801c05500d642078030340300174281c070403018251a010001d08d4410a041c0d0004056a00191100340244980e01e001482c507110032107142ea4400095124940f001c3c04030b40c00c010420340000004e41d8240183d8081c06864001c3c01c840e11701008010400343c0141d21a600d140400f006001c0032a4001d20045a032040401c081800600b0700300042e4040c00b007001c48001c1502c5056030385018800b18a142200307400d0b07010414000004041c000603a40d0100756030035003440d1180c9005010f400c4a00203001c40e9942804004a012030b07a039100c4010a40003200c104c004261100380b40e003002400d41c811335038880f809092040c2c0a01141c83e10300401c5c00b03a9070448410000084c04210560f50780e0200301c109102d10740040a440701d1041048a960f1402c0c1c2c1c104403111002c600ad00c0b41d100d004180703803200340c6c10b9039200d1201d24075546800c04084101000009207054035903003100441d03400b07041c80581035a00e0b50401e5030b0328901500035 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 707456600 1250 707455350 707455361
    0x20d030503190b13021303050f010204081c1b050f01020307031e06080c0d050307080301062708121809070e0f010903110409020a0902030a0504020a0e070221041a030a 73
    0x2510b000d86803030342c110a56a10001003c01a5030b81d15030040c2c650481c2d03c03191240143c40c1c1c00280c13241c07080c01410311003510150018000e840c51041544d1103840c0c12015401702000312102040403030110084c00c5d5400311012004580c1501610440e040f8044101c099800c80c0c1c01070310074a000136203520800c4075039200c000e41042a4044000d080020a2a00641c02c0c1c48524107074032507114040201d440c00a2210130016514030a40080711183c2c0d80d6035509002d0000c42100346e0200640d02d40c00c58054103e0700c007444100407100e4072406440342c00c410003100c014591006510301c01140b400e2000000c02d07152400d0041c85a84503880b01002901d2078401c00181601459405040203900d54003030002071030118502907281b4080d60302149124403440050799001d5560003e55003103201204102c07104000750001c81c0038500a44400c83c4503a203640161039107100440350311001d60b0207a280072100002c2c40345000a102690500c05d070420303440f070718088800d82e4400b00804c506c2c070000c1b040c80f030300d1032140c42203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 707457850 1250 707456600 707456641
    0x2071e11121f020a2c0a08030f070807020a0e07020604030306211214121e1608070908030c010510060201064401020a08071407020f0d020d030503 64
    0x140454103441c1207034160700c242841d07240b0a064001c0313040300e0324500800107921110b490020b0318000a13041d192845101d01d501e03240501c40d8400000002d0485008000c42c0c05250015058520f4080180c95500c456030000310120381041030340c04005000f4403420606400341006034054102404c1500b801820b40349160041640e20310514100d08402290107007071509503510820100041c402d458050302d01c004100040e480010b0001462045150b090705218481c0e4460f42c10000f001d05880d00c61004cc0208480b1600607401c8103c00360b12540c01445543c0e03000340e1a242c2043c049446850040c02e540089110a51981d194018040b09a044405850140005100030440c0030316109014034208100540071a0f03e000007520b0440d2081c0802a003080310720403070320303000c4c1e014a540c03c3d0f507000b07510036101c44c0d0004807420085a4203901c00c44040805146848410307060460340e408200c14030641080341540708480050350801030319107150390003505002e51603203516460b24614006a2000c000c02 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 707459100 1250 707457850 707457853
    0xc0108011508040501020d060e0405010e030301050105030402061b03180f0f0d0201120624020616081603020403061d070b1c050601021e030a18050904030302071e1112 73
    0x601c0082030400400c0900c440a103410980c0341c8407420702034024811600803101090402d840070a880314110710700b82c001c82c0310302c00030070600c80100000d5031240030070f000e41380c0050010000315025180070740c00340148401b4404806180d906015003d491a0b224880001c00b11480e10054062843e015404003a10300c0d081e20340141090074080010034010744e03594001e05009500600041c0f002050348003001906009100d060f100c2c08889a5548d0050b210200c00014401d440006405044066801d004070005480d104e001d61903066005c00b0002175032000c01d040550900000010603c2d90141030348901c01c4401640c20254003500042c01c101da507130050f038422502081900c5d046800300c4240060449074950000c0c0035110803004030709003000c03580c040001101c0c006a4804085000c00201050f0392503441d205042c16402da44450b8440091140b180d1221003800050b000c00c0c0282c000b00b460030b200e05007081040203d038032001c052585000c0c003942c9189050ba581e0680e41007001602c1480c2000b5130 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 707460350 1250 707459100 707459117
    0x6060e0609060405121c0215010603020a0e100302130902070c06110a15110a020709060609140409020319060b0301180b04030f09050301060e09190314031009020705010b030c01 77
    0x20301054041c4594803455000e103880100d681d540917004c0c018469041070361728000c041095070242c029030320049401c80301c608003a00400003800c14041d108861103001d907621400d2401e9404005c02c426140c0700389009040c10340801052440d00f01c4c05015102402c07800342c0042c0c9608440c2003241c251030b0640c000700e051285a002402d01a007002420124456000c2102c1406000141c00303000030b08180700301c402013030b1f1011800104091300495448203031124400104034590741ca00c02151a4000c3d403090b006550841c950210302410a0b4208004207400581152054445d0001d4a0702d1007035181c1d000c4d20142d42d1101c2d412003e280a00400103940404691101a00025101e0245043c0301400040a11842018984865010344040c1d0010b1030014020000642d80c0d0705424034075881120010041e000d0301d41002d000c2e240c400200d440303039a0156251243c14035071981241e02c5d80e01c080d000c551610708c8808000b80c0c44032035000400b00d0610036400442c0d142d00d03600a042c0782c11010f0300b04134144038000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 707461600 1250 707460350 707460367
    0x150203010b041223010b010806010305070e040213050901030309080d0c030905060304150e07140a06082206060902071e0b0a11091809070b0a080708060f0901080106060e06 75
    0x1005a40a0301c0c1000812035240c44a0f1406243c44d0103441c141858502c28040c520ba24203c0650013103501e01003c1e260344100380d699500440481d501102c0600c08034181d000d82c00380b103090650180400e8400a60340d06c6882c0c0c1c0354000954000d900340d208500251400c0c901b1f00080d5010300040500810307a0400040c03142c5c0c0e80c3c0d03020b8100b410602405002350004400681406514103455a408004150421034010085106a2076042c940a00514003181409020301803d021b00541700322502661045001d803071f0400d91500200710980c420ba4000700c0031500c5030104115200d00b80091840380340040e99502a0b140030f0b600301c1d41101a40c440e140d141c01e04500802d025440d401d901c206900c100040070b114003040d882560151b20100381e0402074441d070810010b41d2000308540111f100504950343e00e80e4a0018400c039201e1400e004000564100c08503408500421540b03800a00062038114042500c1020891a40007640402d005039182c1c00704201d401d800072560820410155800e0b072614124 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 707462850 1250 707461600 707461619
    0x11130b0c0604200907080108070e010e2a030f071706030d050d110f07030314040f022e02100c09060e0904021503100618150e031f020715020301 63
    0x900203080d126500320078003d03c0c0c01c180a92120401d005000c00c0f801e05014500928840c8240035480d1b551007000c1c80440e4041a4601c0305048034081f140111550741e800e5030800620660318030080285003c048100c052401e080081c52284813503c00a0701d0902d080326006100381030b411844c0d0b041d014258140030013524049184088400c06041aa9641c00c1c869840f500a046028039a454144085014502d000a200042c903a06019a0702400b031503000554022180d14159030081c0a0b00443c1c541c1c41c0141403500c0b8601303a0200101c0320392418100c088440c00c04200304000d290040c0c0041c01107040414052050005020b0545030000406082c4100a00b00a4411410b14494242c605c0004d0440d50703003180c1c1250001a440c10070340c03213050585c0040d804007464054400400c00b00c05d420075400d5503103625103040310180c1d00e91512240765580203480c5140c49015454260142c01c0c0413070720030740d460142074088001660300141d48800c0350820192061510540d6404c2038010001082000712 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 707464100 1250 707462850 707462863
    0x10050d0b040e1e28051501050915030c091e10080d120603080a1e08041205181c110d050d1808070303030c120b0303030c070309030611130b0c 62
    0x6a1180c03403030091410f0300b603552030b03d08103406515001c0003ca205150b05a00e40d0026800300d403155040717503000c5c004c1e089071818a4009005031900183c030b00e0005104082400356034545c0da64082c007a241c03084202c1c40170030010001101e000da40a500d4035408098041040b02d80c1c0e501c07448800265218908002c1c40f183c0b034981c0c04010b0010054076840c20140070010b80d00010086900c542c038aa50b9000c081c00c040c1400d040150710007090014026070350480d40c0109000742c4140d40c40035045c2403031070030420155805c1d0040c21405480c501e80c0c450110450312644920091007c0d16000b4200504842c0342a180702c82d40c501c1610f0194241103050800280c000840d03041c00744190030100b110f1050f455400c500f8668030781c881880c078491150b000081c0754259001400030b0019588110403c0090030091081e0303520601a40c4e0940d00400010b000004a440034003061803007441c09a0301156a51074610079218101104214030100154030610403600c4c1580d40000e0401c10314182c20500c00c00d60340d90701c600 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 707465350 1250 707464100 707464123
    0x90d261b0f031603090b04060c050609071a03090a0b0108070824070305070507060f141501090513021c0501060f0801150c060e1605030c0a030f0f050a0210050d0b040e 73
    0x19500070b950f00406014030612005443e0552141c1e03102e80d618100200000c0035514155142d00803c40416500d502c04602e14041c2c44001e0007541102c21300c0051082c03907500040841c1e0003401110040380c0000c26000c0d0080c02010300700018442103081404050030040341c5919003110b00360542800c41121080d0a44071790007522070800013902d035282c56066995200c3c4400003021a4508140041080019030002d0881c0031504900c003420366400c5100c40c22034464002a5003c13031506001008a45010250440c503040f0762800503051007c4035000500042d04e00c51340411140d00e0b4001032128542c407804400041c2c01a140c070394520b51415a8075030320700300c102190784108401c20000600f48540741e04940910501202107031107404000c5220840590140501c500c24018030f04c003001036140c120a45800c0c1c81d00001140e1031a907035691000e000400252007119140545185400036950341c1210b113441050540b0350a941d10800040381d411103d0094020b44211301d0a0000c50a05c800020b0951035074 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 707466600 1250 707465350 707465377
    0x7050f0708030a0c1b03080a0503100e010308071101030e150627130302010b0a080c0a15020c01050705010b180106140307080a0b01090312020706090e0705090d261b0f03 74
    0x17460306200107902c143c40c1e030030240c10362000182d071960b903942c4030006501c0744072018039442c0c1041c0c0703036400d4400b450703400c1c030000c1c111080c11b1201038046580401020748540301414006403134000741a009042c03001c40500340c0c0320000c02c513042000718102000041410324444881526098410070740c54440e00c0050724401c40030210031246c03400c15000750300400c03081500030b080341c80306551034000994420040203000c1c01001807070800184242000610400b00d59260041c000394001d403001164a500410000d031019900c448024409032184005008603080f00210b81301c0325818441c0142c00907004007000481038508104025145902c142081e8000e044100d000c07940401e1170300129a298425003029140605106001c640e40d81c00290140860f800303a01d8028003d03991b14003d200340942150464041801003204d807a03203113840002c03884101d105002c4a1110441035070f8440c119040d283c411200480005259040c0309504540d0a07819103c2a006181c1c10003072070103007910781c010070b01d011420 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 707467850 1250 707466600 707466623
    0x504020a0b0d0b13091a250c0f0305030108060702030c030301060e13050a0519091a0c0d0c0e01120e0c090c0d0207150516050405091503010207050f0708030a0c 70
    0xb0107801da00a0341a100c401802d650303210441c8000f2034010301190740102c600003001c00e082d21004041946240c894906140164600f44c2041c9190496408040b8002d00f00a8803180300c000091a4107803c1d000240640e645503104d60610f10028034145c0d0290010003554018019441c0182001041382c1c191a8030b86000c0424482d0700740807882c0ca13000070480410641c2000100215441c9a43c440303032088488509000424034a5807028080f03030589200900300040d00600c0b400405041c205054101480d2244289031080346000380c0b0403243c40b120400d001981c0558084c1f02d941c0d0041b40b1202000e2132840c00c11094007020130301991190b181000c40d00030341c00c0380c00155040d41003c0c155a0280c28091f000c0d55104101c1c078101e40a441d03c0c44121509924040204104e0841260f1201011140e61206480e2600b45410040e0300d200040001c8441c000700c650754031558a0078000780280078403900091581d68504005a8107014058200e4440303940305000a01c000742c1c0c400311900405402a00d400d00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 707469100 1250 707467850 707467867
    0x240305060103031209060e0a020f300a020a0909170406080a0e190c051201021306050304051c0e030d080c07111c0c140d02150c0109020312040e0a0504020a0b 69
    0x107085c25601c0544020315161220020002c00304240c200c00d4804ca030840e208004000c2007103401903042000c01c130100f40b1030048419206840038000c040d04025030807954450007542c005107509149800110040b81c6495481080200400b2000c40160400b98100e081500300480108241c10090030010442d40780c980740100c440c01131089030302e8a42000c0031060710001c0360174441c4480d01d55201c0e850040300c0c0702c00031010501c011300c290384c84009010400c1903e6441c02504a900340c2002e03000342c4560040c00400d550480130220705802031855170f190502c40481120070141024490000c0c181441810340403c000100c8110854101e580d000540042c184921004a0b02101040c8205103030300d00c1d40c01d4240148000850305030200c40d40c03251040801c51004050080788041004001d402000c02d0f04940400c40028024081280103a800050340d80d96a8002030301e07008081d901030170341040002d01809400b540103041a41321030094024800f5050540c04103204840070700c208589881701261154 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 707470350 1250 707469100 707469137
    0xf04180c140d0320010606090e0a020a021c03110a0e030c240a11061026070b0c0a06060e070314040206090d081e040501080105010e011d0402070b0a24030506010303 72
    0x1000500000c000c206c841e48407a0058159203080c000e4086c0c6049207400681040790728000c840280d1440c1c3d01078440b11031002540301c03c901076544401c00340760b22075401a4038069646c018080c1101c41c0c2c2c0d200c01e44007640b0024075050030021800c0c0c1e8001c41c4001c4503c4000034403000981c4048095240d61a038400d0194000c072828808502c94141e50f020304000d100c40b403441512070000b5030308201c20f000205c800449001d00d48002d1400c1c00b5400c0e404c049420010480c1d40b1018191072025072042d15501c0c03c01d5030b500d80407107003140c0014681c15103d400380600300e50300d1b11030040c046180032200d242c182001d4001a90718010f01820a100b2580d0b070320000304118080094818450018009452840c1154012041600070307010300d5000036900000082e01d90300c80c0c00c55005011042c1c6408030030780a03480340da40c400a120300600e03421580030001880080c0c0f02d0382015100d0380d18500c0c0000d114884580c91a40304080104180402004071001d001140010642a04495141c2032801d051114481c121 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 707471600 1250 707470350 707470397
    0x601030908040e0105030c0307030b07050d09080705151003050c06180a080a060f021204030e1c0804030519021003051003151509050903180f04180c140d03 68
    0x145504004100010071075514100f4506880d0210f0a6407080e240031414140d03039402d00d02c0007a1030b06145401003002d05008500924504080c0400030a48480d540c8a0040c154441c040444042d4026800700c0308080d1501e1426421000c41105210420b10710346a03540da1b800c2c10760401c0d11a0350700103407482c68481d981160922030fa030054120b4815035a1101d1203030b00c03001030100035603026040c89440110000d0b184200c4074200c070342484c80912915191802c0340c4280c4138144550b040a03070350900b0481d80501020046126100d141590fa4941c210b1401c1c45c100950a001403c413000480b4404005990b10a658240105980341c000b80c2ca80e500850015503c88580c07010300003101030100c0e1038040c0e00a4121440e4240008607440d400780da64101c14003220070484994095070021b010680c004035004040180300c41e03009001c04200f00c44940003800f03c80400907048014011040c642080010b0103ca01c0020001680c41c80c101100300c0000c1224299042001020003901c02c0400d04070a0364121079 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 707472850 1250 707471600 707471603
    0x30e2a040b030601081c05030601080f13050330010e06120c040c0c0506061504090c0212190801090c120518060c0306010311030603030a030c02250603060e150906010309 74
    0x3c4980c5565201109030312100c0030050f21400034101d05100072114004c0d0202c03030141d1810ba4400c034180d964180719408850000c0c2450400b24020405000855010405004a41425008156141020300510a0352400c1090180034007000b04010425078401048042d4451010740313203d01e016000300c0181c3d04182030055003680c02482d181c40c50040b42e5004221054542c0706600311412922070b00100a138120b4404955100200f04000500041d441d541001040740c0a6004503202c0715800343c0c541180340c221291b1500008840802086c100380c0c0310501c2c2e401058070072020003820148020080000c400590f10460761b64442e804a85407081c080038600c0705200d05001da840307074280400b56900f258820796113140003e04080002d81d07491001011240942d10003401140f6048c0c0001003034000d050326801620550041380c08580103441480101c1244200101209100900340303a4050101e90040d04031801e10800f1100b08100c540c0a90928511070808032010300301c640e50080120050042d1450 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 707474100 1250 707472850 707472853
    0x31104050f060c0a0308010f05060313060e072705010f08070605090a1d04060e01020906030a15050306180d030515041a04020708070215030702100b0d0602040b0a030e2a040b03 77
    0x1507013420f040e80010928141c400040d036006000c1d654000300002070100b07440100500d01c2c1c4034003e00000d20103610441d007041024094503010381c1c0d14842d68202400c01e45002c1910041c2c081c820308072200078862907015060b4030403074601c1181813241365980d03210603020360b105110b80050000e500d99510b40450307000304001e02000258411951609080d00b10555046941505007030304c461140c1410b0003910340782d40000c0c01c3e076402c5940303602e00c000242c000d400c24568001f500c0c01020525072001c0c804d40d48603003d20b5000240060790030303507098a041d03918106407040500d42014422003529264200c0c9255400f140d010130b14610010b4038041c1c59055401d82c6038030070b1000401e0400c000d0640090900c0030700880744001c2c54406000a200c861004035900da00603040002c0038113500310140e00503a415440170700285912500b641e02c0788101d80c026000000d2185001c680a003029900d80030748101d140851018022668443c56200031481094455041048448010000342d0f1110b074084024410000c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 707475350 1250 707474100 707474113
    0x182205150702160602030c0d1211070b1e01150c050708010c0309050c09010303051209071503050a0b0f0102120903010f090b010e0a060b0a0305060303190e010f031104050f060c 77
    0x1010b59164507058000c180d200d4030743c000044a50020050301d003604150000f4045545050500302d4450543c481130815035039880c502d01c0418415800178061581c42842d07524000e0804510900c2c054442c50348003021603601c04010b200c1100000e150034041c002c10304121244070781c985480e60801403242c001034420741ca0030321190b840c0c07581904181c4e0141e000e50256210580d4203c14004050401d000240c040f4208100b03052b500885c2c0504c050380000510300780c482458640f0301e12804581c500910741c3c000390b119000d000c00062584140c0300189011518030140b10403120010b52143e503005e5420403103a0020070041001d4400307401100e03151403000c0d010031519040385000803880000707000d010061280d820002d4260146842500b00b034640050356a814140f050748102d001d010000c0c1542d8060009000150000950056042006410f0f4071a000c0034443c51000419010040c20003400f0181060540111416048100c40a440040c2c850468820f11080030a0482c440c0e9028245540301c2c01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 707476600 1250 707475350 707475361
    0x80f1204050c011202030126150a060e0109050613050a140c1801050c03120a060e0406090b0c0f190c140c03060a091218050a031118220515 61
    0x2140702c0700214404d0700c0e0845500da941d801441280400d00448000340210040710b09034070f016600000c2c0c25483c1c641210003400b00e09000742290310040c1c4a0700d08a40c0c075041c0034404684006445409402c0d091010400303840d1804c0090340d103540302c2c0c00401c1002d070b440b00030410f000410381129030340ca82084030092607800e24079003070b0000b98040390008034210f007842d4414030250701c038004482d58100290011410410101c42c160705601c009006943c45030740e200b01c0004c1c0e45444115a51143d4000c00b0300050107101414150702c049002000340e103024400f084012148903101041d240c00128180346110800341100301680d40840000001c1c1200500d04c6525075122070000705000703d20360640030790f182d5407101d03070448094542d140d20003003004918040f00c0d034409110f10300341448070700720b015500e100903034a1010070040c201070b410644912001c00c00c501110f00700303100c110850f4100e2001040d0546420403501201074040c4101703203401100b4251940c24850200600440c140f43d4070307640300b05030809 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 707477850 1250 707476600 707476603
    0x7030f0e0301270507050a0302030304090c12050103060f06050a0b160611031008010c0c0c0612060504110909010b030c03040807030309060218100c030e1504080708061f12080f120405 80
    0x18420100c80d548911500486c450800300d01e40b80c01c0300d502400560a050404a40300080c0c0400e0860008010000300081101c10590203464000d50040d803002540c403d6448112041d5000d0390000c600074885400e080004800d10011600050352032446600e1580c01440c0c00c0019242c03407010540e10070b6003c0140f0007109075820b00b8004450201e0001c012082000b0307801e6035010b0442e240034001d0303801c0036410820203010f10b05881103900700800020f00f0780d8540000604481c054030720003002c0407000c9422540350502d40c0035180500b03080031205096180940002003284030082c0300804c03009011400d5810140603400514641382c1c0100103540b220f2982d0b007c05010303150882c0152041d805100c0c0801524010b9450086854042c0e0325040e8004d002414016107214414110010400811002406941c00c0c4028400740c13240602412103818070307103001c0c03603154240300707000040900a81041007240300300e13107038501084d038030007122603e610340d80c2c1c4141c1e000d008041440784000385070002c000c1000710 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 707479100 1250 707477850 707477921
    0x5010c080f0a1b030b0f0d0302010203090d0923010c0807050115090b09010e07020c032a1c0204051321030507020f3a03060602011107030f0e0301 64
    0x140c1105101c000c0d40c4a4039414181e80344441d40c03145194003003004180440c440e400c444000440039024001c00a640c0d000f003a001c040c0100d040d00180d5021060012941c001c0c06203040d00745680c5000da8202c0d0034007040004081c0709d880300e00c0c9110007a03581784403142d0007460803074142d9802603100e40d03c0d55800d0a00ca4003905965100302d00241d502c140c0401d581035203105a8140040140c84c0000d16828171807856580c0302c0c090806429031140003908280d685e0304110698050480100e4180d41050101c1c091070610f40c520b9603188540c07115601103550044103000c090049804441c0860f03030f40c41d00d0281d86c10303103440050080c4c40c41e40700300510402e035426600c1d030881800c40b40d03030100100d5907806c5040f612240324181d1290303950000402402030024040c002c400080c02910f40700040800031100d40d5004860000180200b5180c071010810300d9020f2280040340800030a40b149041041e680c003d00300d02d12140e128050144510b60384d100c5032000d60100c2c5c03541c11025010307a000747d0303c0c0300758071401c40 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 707480350 1250 707479100 707479111
    0x304260f0c0306010609120605061513090b030303061014040f0801050720070e0414010c0206010e07031a01110a080a090509090708070e1305071409070305060f040f020705010c08 78
    0x85030f0030001900901c5120350f142114019902100b0042c4560348020182401911241c0d204120140c4200068181001003501c4070f01600c000c2402d52408100c2e074250350000144030f00c80c2e00103008000b80f41e110344a40c004003c019250822003007041120b1540180104d400c5070035044d220080c0440c02c041d0542c850b40c001c05050701d88122811440b940000c02d40c2c84000341c020070381c105d46420408000390350b2440390410b216181c40d01c0070185030602d890840b000c5030703441401640101c00401c60000c1c51119260000340a28040c80901114150241c0d51301c21100f200d41008101c00f1041460002803080042556100c21195607407194048003e02c215030a00881e48100c4900d408200c901e00300148903802c6031070840203880400d2a059510441c401e00610040702400c1011400c00003813010300240b0050720402030b100029055900a120550174010618020315240c0070901c60580d0302d031801184900401c0358045840410304803008040c0c01503410041880d2309080300b85031016001201a4400d5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 707481600 1250 707480350 707480353
    0x40e06040c051801030f090f140f030703080c0c0610090c05071106090607150f0f090201022e050108030d0c02060f01050411120708040201020f0a050304260f0c03 71
    0x54648804020444010300040300c0071607000c00c000b2083d0010944a909129014100000c05081001d4140b09030303445e4000c201ca0702500a406c01d07080114502070020008150380081070000c540408190b0b07284981d0034058140481040040d4003004982e085030b403040a103905544440c02c2550b201c84140340a402844045410451100da0092040003130b22081500b100c0303a211040c05040a112441e4001010036400c03100400c0060701246009000c1d03a0003082c002800a010f02c202a64076080341c2d25140019081d5003040440d0700544e0380010799540c0c80301e02a08241c10b01024400d50000344403010319a510b942d003400f00005003e000030015016141c180310051098141520003283c0380c1c001120081d0500700c80c1c0e40140003d003881c7c0c1c489215580d0b4403803c0c0c0c1c0740ca070901e6502c80a0038001c0b9041d100045083d0200421540d05005c10280d10500d80d00030040a201561055107900030b600841051440d50110f20f040010a1540240301078840011b03502d038403180040a50721040080c0481d4001d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 707482850 1250 707481600 707481629
    0x315210708071502070b031024120e0d08090c1e10052a03071e020a0f0f03061e061d07050a0f0c03021c0903050f03041a07051f0204 58
    0x1285040a403441c0fa1015030140c10741c80c0c02e190310311129810242110010724084107020410b01c08081684050030403e6916030080341c040b1100404004840e902c0110f810b00781f504056121130001650300425205007841d8100790f07540030440b441c00d1800d41085500481040342d03089003484027105480911020f85070a901001401020f40f0984140005051030550504007841104803008a45134003903143c2090380d103086e889031030740701000c8543c0c01058203c400708081c8100314502021080000c0c03011459025403035160650b10111a1503500c400307882c003600c4402840314014003016030050350801180070031801d03850346c14071541c5518400800350815416004a080c090050080c2c607070040007682d0381203001d882d108044aa01a804008800350302c1801040d1015080c0100c0d000d0344c08a855586c050104d26500b4520700d0701c1141518400607810811040c4101402c0c0180b05941d240d285185e160b40c1c03070b000e14010789403170320000e0f194004400703811011750b864480d43c0062041b680e0a5048092 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 707484100 1250 707482850 707482859
    0x3030b0301090b070c0309050a03030809010c1706011223041a04050d11100e0115060801140f1203030901020306090601030b0d0b1806010305070501180605031521070807 74
    0x7282e900c0580901a880d09000081d20030f80310b0003904c001c852003440c02c130001070b40c0c45010842003c3c50f0341049000c01c840c07204000c08240d00744030301d00d40042e443c904540030740c11031269030f0408840900f8a604010000341550365420300740c0c2089165490f141c0084514110305207680074403910a450880b4820300044030070700700e005040304450023181c2010213400c03120300940040d00c1c807403c0c081902c0054000c2501c0824404c0c0544140c1c0c6d0300380120310001c281e00c015280a41d4040f03209401450601c0300c110b00602125408000c6a1b41c403181c1600c0e450102c8810a0000d03450b545101d035007a4540c8000810400c100c035041d000385000f540c06458044540d210000190705690540b030442c0c3c0c00280e20711240000c2090341420365041000c01c07040944a1801030341c05410a10240c00aa81541c4000c804101a507840541c19582d0701c450700285241038101030000300f092001400c403c41c90401241803420627684d0310000c983c800588410026171203600b480640e11080a4400c80882c0d0148690004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 707485350 1250 707484100 707484103
    0x60e0304050307030b1b180103051b070c0f08010207030e1011241602030a0e0109081203251b030302090a060806130b0f090a060807030f0b09030a0504180b0603100303030b03 76
    0x781171900ca4a07e680200510800440040000600c0d102e942c0c3c25105642940d0318440000b48101c40c090800008510300703000040c1195003a43d44038461581c810401000401c0d0300c508000ca289004680c401514a042070040b02d10043c800c070723001c40c24003407868149202d2885940f400314513840c81542c400c090341d0b412200d180c100041e18404026800c00c21007032950318440c1c0d41d02c110398001410100c010584992003a4a003101e00078240008070000000d022160310164600d2103442c0c8800721200001e455640300130702c0304801c6900030104108164a0004240c042d40580d4021840a07202c1071825989210080c85244180c03012030007a080045683d510380c07110b000e6148050303c042c10400323001100f04103004000f4001405140d44c140d035103002003201c800602000c1c0007140112440003542d281810003c40070171004c2c1514655500c00c00801d00020340240a0b141220054854203d00e0344080c107406001d45001c0001e5640604000100031013034071124441c9069a01070741c0c040181580c0d160070b15 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 707486600 1250 707485350 707485357
    0x20405010903060513080a020705181003121116030210020d020c06250302030307020f0c03060105092e09060e1003062c102403060e0304050307030b1b 66
    0x90001d05803180c1403012806581003980c01a0700318450318548102c40d15102142d4100c2c0d9000c01c016085a54200103510317010300c4800e0250a4500400b14504000036054000107182c4401090340766000b4801c8900c0d801940c50160f09011141650f2100410799144031a8440a0204a20402240059207052803000030211040005c58000307064101d240400c018041d0041680f40c0e0921740c04060203c404240c0003c3d45801910a800554580c24a6a006030424400d000054181d0303014484800c11907070700281c0715046503800c1d101c42e1400c2c4c450801d000464085142000c840e40c1c565a4031806141981186074112202500100a02034035048014a507981c02d43d100c0c04240c80d01c50b030a20106a56600c5880f41107500307a4020340100440c40c801c103c241d40300c01c20b42419000300900703031116900c500510304c160b10200c3c4c150101e90129050f03060700103030a000141900c2d43d141100c0315203071810000c903005000e0003021903001640d00e103452656920201c4005800c03020415505400044a0003503 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 707487850 1250 707486600 707486609
    0x14090708093c1b060f040503010f0903030b10050a050a0c0b1303121404171213020913050d030b0316171207030512070c0f0506150f06090904080c030c030d0f0204 71
    0x3c1d0320303803c0001000c102c80c41e0410031101c120700104202c009002e075400d229842c00b458440707102281d8080300703040c0a0200c66143c040c190203403004880b0f503051580c0c01001c41d180750000c2c1c204261290003c03070040f102880c006e00d0040c0451000c8080c8619a14100154409107100341d80f000314118034074500300151107036110030210070707034040f404640054103d03e1740100301001360080ca810003550482c0e60050600c291640042d20303000351084070a5042904407907502401c0000390566002c410740d1403135500c1c408200280209940e881603c1a907a40502090b034a440f4428680401c41341c81c0c1d8041d40807241869105100d81c0300f5401208480c2c4041004d4a203411b415071104e03030a10000310f510f501c08820080c00c100402c0f07035601812000030320b840c01c0820a5800340004181d01d02e0003012603c10b0701700e2402810f1007800503408180c1c50750b40c0c0c1411114620b005850b003040540351450006220700540c0301000c042c2c00003241c0c0100304a070003c0a00b42c8040071141c148819400c00c5d070070700202d03c607a018 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 707489100 1250 707487850 707487883
    0x22080307120302041a0c03071a04030e0f1806210c03061005090c0c0304120c0509090a080301090f0e0105042901180b010e040c0e010914090708093c 65
    0x4017511100c209406841c68075018001d40f4504506543d0349c1d00580c0380408160301c130740b11071030500040c10350015141c030081c00140c0e103411018224000051004602c0741e144009224031000049140e107a080c1c0d90581100303400503442c01d403103c0d0200e00751142e400c034402900078410000082d0048003034101c0c0108540020b4103c8809440c0c01006128560001c8540241d500c4100070002c0c295003090100c4248900644200f00c8190801d420010041d8025110807166406002010040303800c0d802141c1c1162600000015041100c05040300600031221000805e03511305000c11043c17042c820701d00540400504500d152580542011140c085421300401820164074010710401c100aa0721100c50804c050400341c44c1d404100c0005404e5659403903503140055016415079107256045612403000e486290f0401d14074148043c0440d144060091a100411110401080080c40144440b4652aa45404136250100c1d140c80c80300c0078018040c07101d50085245040b050341c0c1000421460b04210380b019 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 707490350 1250 707489100 707489129
    0x1d040f0213200f0702102d0f02011427030403060f050108030c06040b06220c1b05150705040e0108070302270720030a0201140a0b152208030712030204 66
    0x1000d00a420010389020f01c11f101c0c07000841c4202d2598690f0b07000e016404042803890101e083c1b80002c2111b24030341d09480c156810100d0004000c54107012042c1c0c02040d02c0201a9021164044c0981380e080d8095202e031280800207021041c8422604118640241d40d4000c1c0038691707030f44080302d07a030344244034180c441500f01001140000d4074400d00c00c1c7c1c008500401e0300c2c4910001a03030310b0401020448544100d242c0e02c00d200d410b0f0980003104405d4403500706118407011029511a20345402c01c45101480079001e9034001800b07a40141e091300d000e400300300c01001013980c51303030714141e03448049001c1a88194007031b545040450100791407100307824842c0c0c00f400142d40c072003c100b5a810f480200034078981b0390304600342805080041010b001919195400031410401051a01070030300005002c100107142041c92480e5551103503403522690511000740307950703100d2100c0200100840186448000060800e200203400c1d4000000351000601600c100c0010b68030164054040380310354030032030100c031740d600 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 707491600 1250 707490350 707490353
    0xf2106170d02190512040b070b01290318031303061b09090c0306030b150108101511011806062c01090c0e03030a09080f010203011d040f0213200f07 65
    0x20782c4811641881441103a000341c40c0c141740c0920b1031704145c100042c26880841c1d2501409440710f071850040403610300b2081307800300750070303071064182006d040003d42040f00101095503441303800c2040c0c0405100c1c1054036160441d1500e904204590361006071015414450540f2105d4a46a00310034451003d0300c550301024901040c45029005044a6205255642c240007001c11000d1200920070300d040440001e40a20880c00540420805000c420200c11104020700805510307001c40d5801c800a801c28141034040102500d014141d1072a8011a846c9080d0a480412844ad042036080d00c00d03080c035116103ca200420112200580780c03121003811044001005240407550081c11a50510328200c2030004817040840e19503448041c1c0740e00096504bc8003002294000c0c01005207030444030b0001c0d49154500030096402164418010004019003400b1600704040d01ca48500d15035405404074050324141c8050300000c011440d24002550341209815040c90403540480709011075201c00542040010f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 707492850 1250 707491600 707491633
    0x1090614011202090a0308091c0f08090a030f0c0e070815040b03030403080309070e0601020a03020d03051909030e0a060c030206010e040f050712020301110306030a02010f2106170d02 80
    0x41919840c107069003003040b000c0607105c00da0384070080d602400c403c1e82d030b40540030f003408000c1801041401d001c0c00c9503600c1e01d000580520618501e69004450707183c0390710b0b038000090381844040d030000700040102070b00d070810000c181149000304d408038900f4410943c1e03244002d4030508402c40d5007010503100d41141b102c0520305584240681c12003d000c0700c2c02c1c00d0b00d95a0703c26042e441500c1c40080d584c8080c008015104405510f140d002000b0f1000d4032001d030305950003039a900c01056031007040c95280d00028000001c1c0300c460204042071b0620130300c2000d80c0d030b05001d03002e0720701c0f05c2c1040e0050001e1480420030ac0d001d614081485540f50340101410b030b19010303424009041c05002140c800440a4681001c50020490744d000b921240c84c603405004201c0c0b040600311405180605a004400d204101255502060704061150203081c00c41002d20400c008468680406401c065a81840602514030340000e40c4500c1c1a2054541041780100b103042d13205075600000030200b00103900a1100e0500d0804 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 707494100 1250 707492850 707492867
    0x603030c020d2310060603060302090103171e0a02150c0d02030c040506070308090709090b010611151503070512070501050f040509070c061a031902010c06050903040e0109061401 78
    0x6202c100f8220744040e26003032081c50025480c42c3c0ca81c0d202c8000c015220b0304034070581d00201414182000980c0c07842c0d0205050350130501c00070b0b0003403820540800c050f0051900f20f44001945010b21801c21480c0c61040b801c68208004000051186a000c810121010755070b03540145003540540f400c013480321b00c0c000060360008192000d241418400018280c0782d5002501c0010700ca515201c0c1c032440c180c1c481c10700d000001d43c0481c5000f41014024800b00d907d007810ba5040d02c00b1890148a92170304502c100d40741c81803c1060445044070001000010201c12a00c04512001203050f190316030f40d80c00402c1080c03030015204480c540c00806040141e507010300700a050550304400c0d05030410340c0e40c6001440c408001c442850200d003503904c910040102ca44614444ac200e00400100e00300b91840c08281e850514096181e15243d660006806586c064a10b002040340d200c1020300c1180b610070301240d281d400c02d104051004003034000114030036115004010503512000c8203c00c004cac800d8401100c0624 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 707495350 1250 707494100 707494103
    0x906140c0f0705010b0a0b04170102041430010b031e03090d03091203092408010b0a09030803090d0201140708060f0103060b13031203020f18030f2407030603030c020d 73
    0x650b14240c0007000e1b1506145000144002c8034030b00e0710b0342e240c105001001c03800002d0b45000c692040006200008014149031040340c801d031441a00003c0300d440042d4068800303500a209002c913050400350044054000001d644e00c16030a03102e045203a124a60344803041451419043d810501a0041e0340c00c12000c0200c2c81402032030200200359640719403584043c1541d01c26400184160000c0c40080d2141c810a0b840c140038139101094100d615100a00038001802040c15102d000501408200e104240388000780d600040c0880e42da00b00344241503514180705001c00095424501485030107211440080c1c4201307416221007200e640c0b04002c000852540404e17050515545001c08070308140d101018000c601c0e030340a07030214901d0840c1000c000801014103000b0806004002684500c1d112000740c03007a549034030410010103104000001cac10646c840f00880030f41d21442d00702805003810100035100c0b444124001507440e4484540403010744e0700382d010103400b00d54040458001410079108403800b09 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 707496600 1250 707495350 707495353
    0xa090207050c09151503070c060b030705040c03020903190b070f120c030c0e0306070f110715050301090e0a020604060f12050705070c0918140109020901090906140c0f0705 75
    0x10742d048000071111030042d070390244c0c18416001416880c5c10700000e4030b17141e003842c0e942860852901a00081a0701c4003040c0050459842d20222406902c007040800c0250600420511511541482c0100250441650b0034883d100e903400720045841449400106960032104242295680030416540c4152411985081046107556004025414825240d840100f0b0340c0102d985144081300600381040704a0091203500304a0038400c91036000f80740b0007103000880c2840c00c45c03551030642860034034640b035000721a40c01e083c0c00712212481c0c0c484000d605072004108100450046040714030b0f5101c0000c074000f034000408101c207100300340c061441025840707468500044854034901091007a102c00392518008070b4800b088100c10000340d1044d04010b0404c103182000509100b60680e1345038403031044040c03c1d0900703126081c6842c078001c0d0442043d294002c0e0500da02960368210707190080002c404191900e502c0c4c805000c1e044c0b200d9042041c01660340703606082c05c1c04884014582035070302510040700d0f103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 707497850 1250 707496600 707496613
    0xb070807081c14190c090302040509060702100207020d0201120b0307030302010c140c1b01050c15040c060203031612141302040b01020708030a0309030e040e0a020f030a020a09020705 80
    0x54104005100e4071919182c4100103115030340d191000d40d002003042c0100c0080c603008001005800742003d500b100700c540408106800c1da001c058a2891050304081d41040c28141040814440001d4450140c0b09980c01c4801e440c0d61050294201e0180d40c05c000d40c0007405564100243d845100e9032410091034060000b0416440340009181144980c000c40150351180c40c0000075641040140c0c08514401030b4003031811041407140742d103c10342c0c04600b1010b6814400d21000c0c503441041901e203a03e40450842c2d11031542c40120014100b4100c500b147d00490300300c0042030403803010056034019003c5024074103560796180c005a400190f40300300c0007261030382c41541d0300310300c0c0500c00c1c1940075401200e908200f000c0103006000665004010740c0d8159031051408003d00f4000004035000c03050b6070f290005d010802c41c58226250204086000c1d80241000c0c0105110740010900b003183d18801c4403a99201141041410b031141d200d464082d601c0180b160041000c50750b41e4000b022402e1050042e00c90 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 707499100 1250 707497850 707497853
    0xb060c010207030201051911041505070b0129040617090c0418140106050a030b04020109170d0f0807050901030207080705072408010e1909151e0b03070b070807 70
    0x2282c201c81c078150010703034442c0c061101d4125108131001c598002c000042c06a00110b040c1c01610744602d00ca400d06d11402c155660800600c16001c1e82c49a5030310142c030030b0320755a44034582401e84480f100800d0a451451000303030440c00710390301100d040b18542d4881800c82c104a0746e40e5103801d84024010001405582e4500585948906c1000e4030407814904001c800c0e12207092020b40007805100c64809689054804d00007a542c03150004201d036808800c0c00303069555440100d401c036000da0700c090b48990b65400d00c03032011140420b00841940c86a92074110403240d81070b044401140980303501010585c01c0048182651081d0010a0300c00e006030303050392500c502d83e62010300c0c010850b800b50030049240759444250507284050541134150501c0c01c10015410600005401400580f5096043c03500000900342e040f59904603240503904110310f036150701d602c404030b60f0184c2040c00c0c4040d02c004152076075405180d4203108501c0380500c0034006100140c10040340c048a60f1180005482c0b183e014000b000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 707500350 1250 707499100 707499103
    0x1703010602010606140c07150c080d020a0e1f0522080303060a170303060603040f051c02010e010621080d0608070906080d0e150f070602040e060102070609090b060c 72
    0x600910303403580000f400501c0c01c900204208001c94950001140411001c0c1d9001000916001680c807616040855004015021b54031500c0041004052000109030b020103044c03550302402d5020340079180c2c0c3c400740518108010300781d02070101410baa0280d5908480038144503002030b200c609076068181c03100b403c85000e41244201c040c0d200300701680c40003007000014180010300300d0090410390304480c4150000d1040584a00008140e240a03841c044006030910a28007d0320b401641c2142c1a03907182244040b54080c80e0004044d50070141d0300b4041075507034403601403055400b104e81b00004030000035a4003500300e085500c9210140c0b50110306004100d240181881a00000d213080401000d000780303400d9a0a059629a62291140350800310090b0042504a42c2d9011171000465101e103191400c0f151035150743c0100480304116280c0424100c007041100d90082040c0c803c050802c9035690b80300401281c0d16205070240f00002155040200705079401034028880104004202c40d0030101d188500b503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 707501600 1250 707500350 707500357
    0x609040608070f1a0901050a12230916090b010e030d05040303020d03060803030720160e06060a050a0509030c220b0f0a05091012120f0c020a050d17 65
    0x4007541d00205010041d40b0004100315008014820b2005154051311070420518015a0324441c10b0050000e03450103064802c2c8a00e852082c02c100c010022400003010781101d0110050182d0600c01c03402010456110740040c101c8000790f00d0b0880c05148a00b424281e00180204805060510408820f00d5038203907018000f201c0100166620740e52250f00c1c5040091400710581c0c48402410710700f01c02448080404812680c1c80085820602404103481d40380c2940f01c0d240141442e04ca004e400390780ba204540450040c0f044484251030380000d6100c4108024640c0304003040c0402280080005944c9540100050f05104800a054030250548040401e011405800c015600c2c1c0740c810005017214107040c4200502c01d4800d50349802d0002101010030680d0000e40200c0344289032040c001840c0440d0751000b0400f800340650340001d9201f003480c0c1811180e17121210000402d08041c0555502c500c100351070521250010410940c440c0381106000940c4901c030002d4510030107004c2c201c1031142908006 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 707502850 1250 707501600 707501609
    0xb131a0a110c0a0318090e0f1c0f051b030f091306050a121103100b0414010803030106050d0608012a02010203040305030a0228090f0e01080d03240b03040c170a0305030606090406 78
    0x50624040b02c2002e890400c40411038050200021903541c0700c0c0c1d5644200881680c1e8540d06149a93320780c420142803d04e81031006020540c4800510341c449011010003800b9900004d4800740104842804040292080ca01802c0e400c910420001c10050703801c0e20500900358044d0300039100c0300a029020a0802102081061a0325140c219881c441d041510808611504414034039046505240045403244010301c505001c001001c5006242020342e0361200e0000d11800c80200500781d8498165003a2541c0c2040034205001d58000c0f0319030706401802224880c6a00d55a06480e503130703c03900200002d400c2020303554001d804440c030343e01100150700840d421002d425203640d01401d10f1300442c00c0e40c40c0800e401c2528141243c5004014450000455244101003801c0101c0d040c4882000c009034043e11506048903400c60000003d00d1002d042c0c0114029406030500b414829103d49103901040742285828a459100031a0b55002c0391052001d540c10460003070207249010705500000e400c0c0d9400b03420 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 707504100 1250 707502850 707502853
    0x1c0501050c180319020114121503060106090f0b070f0203011e06120b0f090a0c0603020703090f080c10050417070510030c0c0b131a0a110c0a0318090e 66
    0xa40100d500c01c20121034610304003c400030101010701001d1140241030064000341407103240d40751800801c403a40f054074005488000242c0382460320030101c21118800d4003080c0d02a020b07100c00403a86d52300c00c1440c0429201506151151985008603006196000740426030340003e142c131107000140d40a000d08040d51405a0304044203014203034181003120070f540d005408412491000c82d0004c1c00305610641e00102c0300c40d08502c6543c80307a5269081410b24900181409000100030a2650301070380544902030181da07900c2036194860f41c002a00502e90300889115600400c200c172110b20f0422040706000c01b10313107084c5003410b80d580c001c911307004140241e141441e00000814401801c1c5031b046001c50300b0051805001000712904050054207000d800600500b50000c0020080c03500c4540c102075043d0b011040c4442440b8400c0124440c0409456082c1030604142a10038003078482e01c107840c501480c1c1c40240c0070100c80743d82c06407400400c90307135500c0c64508103100000304c0d40034608c20403411109070300 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 707505350 1250 707504100 707504107
    0xc0a022406040e19020f040207140607110706050d0c09090f1410032a03051c0f0c020907050c0a0c030602040302130203190e010915230906061c0501050c 67
    0x7801c100c281c800402e454030f00707540020910020075888810304000a0340544252120055080104019103d640340c042c000244c21080144074003400510300b40704e04582d0350f40403032019014400070344628580c454180054000d0080081d0009540c0c81010120b41074104400010390341c11541040e05c0f00450441c46a035a01c0c5442c0c80814203606107168042c560404080303006045d6a10b185550008800c0e80c000e0394846a04072414000d4019010003031900300048403c1d40c480d51a400504100c3c684810002911200c96810050701035100303002c2c180c0e8001c022038600d075a0b4010444041d0018401107000e48500f103003c9010401c0660600d019501849000d640e480c00c500522011546c04001c400c4e02d544100300300011104950004900540e0082000c581e0000045640b030160400c1c10b030262001000810700040020298802d01c0750401c0a401d06c003080c0a00c4519081c118000c642e05015030700401d0015915140c1701c0107034a4001066195400052102d44455003143c600721200e101600000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 707506600 1250 707505350 707505361
    0x5030c0709020408060109020c07121b0909020102061f0e0c0301140114070204050a020912060108191a061f120b040612060b01050409020c06041e05060c0a0224 70
    0x14004400501007048041d03251501e442461a034a03c014414449129800710300c003040c0c150207000403c0242103040060b043c07041c4070304241141203014030000d024054007000000d13a100c5140916094242c058001d800307640d460114414032550b4601d40014464000c400c045820691070700854040e041390101c084d102d6040c00d488048810740d0140e200c1c14004c0c2c40c0c4a400c040043d8408640040b54196030100380ca0b1650f403c85800b9003d604d450940c03107081c410144a640c007000400324101d401020458506450003480818094074101c00035003407032105101c01da0501e0200342e2242e08840b003d0800322004c2000300550001504201d4120002411316002c07031a421a580204602d54501311070030010b00d403403e070001c1e18010141d000146400d8131050100b01c641e000d0010b071801000d64880965607216006145a00c0e0002200c0883d00750403080310b9a80020035a00240010580c40801441e0b03644a40300c400c6450f803c2107104800714894170710540c04c608416000d0800a10b008040f87e002800d00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 707507850 1250 707506600 707506603
    0x141204091a0315070c0501201305011d0d021c03021b03060106210e0f0a0204180f080f07021008150d05101e050c041a09060304031d0d05030c 62
    0x142200d1107070748000d040c010030742e03a0072a41d1134100c90f40d4102407410f0300440c40c2060141000c1c0b840002e5144050501400b008501d04c0240501140704140c40c410301d03121401074455101c1c00d941d50305110b03000c00c05400d01d8185442075020303031800204010300e82e010030607008001000000c004c400682148030300c90000540d210000c3c032550f1044000d8401581460310080140d242e44c0904000b040350b400c3d802804400301d5025a20919182c000e503803007030107000c11590780c0b8504117204900445c58a00c1d4000c0300004c0f802110140ca6000c0c080152804854541d15031503080000c00a082c528200001001a511401000703004070041d01d40180a02c1d00d24048800840c82a60039070054114112000c0051310200742c0907061061070340700140031403004403400d40588001404511052500017800b51028111004d00212803421101444091406140564a0140403a156080300d42440482d0000c0e000754000c280304155001c0c104801c0c95080c0c00110b044042d27803402c4e507417a00009040d0280450 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 707509100 1250 707507850 707507891
    0xe0609061f0312200307121b0c230102070b0904020a20061803310504141017102706060303031a09060f0102011b180e0f0414120409 58
    0x4d044040c600340f000c0c0e070b00d4999000b40c0a82d802e00030842d50070b00c035182580b025041005901d4001d810450b90035190070b072507010103200383d1110040d082241c412200641c030005000c1c2c10b950b02c080c0c9440c1800143c0e02400080d4211003032007005d00c0800289540448000302e03940e0244800c00009000c5410702440766000054129050078058004111a0741c1d00c40400605c49103024070304140f40140c00310488003600c40c070b2003600007960140c00c0c01e02010102050b402903070f000701c09203101485880e640360035400d403403c0d68020a1a00340c000b20000340201c2d90380d5000c140345418004140c011070070034003808503011031840d4003145d150307a90300340038403d0540c036110b0708030f41e541ca40f01e00c4d5800840103800907032410002400c540c407410000c405904964402e400441e1307a04070307840048041c40c00d40c08028104580700c04800541038200d081c001072018062865502803111b6040044654841d40c40300c0302100d0271883d00b101d00f8480c071403103600b403050034070300401c014502e4120018040d01004401c078258007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 707510350 1250 707509100 707509157
    0xc07030305160e0d0c090905161e171006061d0a1a1c090b190203010308030c070201090305060c2d0a18051809010e0609061f0312 57
    0x5040c0c80e041c40c03454200240c614220004c0380c201203212001e2500801017445a040916082d0509503640108000001d031800541d210030040351081b030f1180074041c045119012420303400d24840d1300410049000f903a194001c80c0003801914003207043c051007001070341c68031f0340b01d81c00090014072301d090001c0034444c10040241c0100d4071001241e00c2d00784158860100c890902401c03d00020b01c8032441c1820105500940e11003120a00000c071031801c1c1102403010441e001d4904081c0c00f4070003103180d07001e4421241669072041d1303601e017076840c0c141007800d0641001c5401c07414881c8003900403005ca40b00300891445000c0e524075007550f850514240342e9000500325003201c4003603520101c1c4084800d840c4191032051000d45004030b0914000303d40018099900d0b0b000769001020040304540322403611200e144a1007041c402400035000303e0107116541c55003180e0700b0070250021004160880c80b5101c5480d43c80000c1101041d040361261540300513aa02ca416200201e0300d4603000ea425003e5140441400c0b6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 707511600 1250 707510350 707510371
    0x60306010602031b0712140d0c03080112020117040c0f0501030b0a06030222180b1c030e03160f0807050a0f060318050f0d0905040c022508060c07030305 67
    0x1945001c00280d581d000d1071840810340d0084c0350310000c1c40c2504014500080400011200c0c983e00b107410071500f11021010000352a0040650a942590080742000c0507241c1c150b40e094002da10700620f140e1015495413040f0304200348500b00350000080310705000e010300e004801040a09103001441100c0e00001c0e40017a05050604640500e669a9841000220344142c280075940d041c00c0303910700040140107800d00c030124002701c03000300d0b0b500c080041442400260403c200a80412a01080880308820503d10b0b10782848001100010344130304404d4001410250883e0b0640b80b0003080c0c200c0031380307183c0c00002e8041c0310103904216090080000b60020041680c1d101415405c180000e41250054000d9209140c1c86001180b0102d54039407030081c4c000d401c501901e141c507802074191903d0f1030b9101c8030000000c2020310007140070b10b0b15200d22001e45240c0d070001d000e0a01410011124031201c01032840d6850101c1d02e00103030b420024402544511901409207655040928000d811a00080e002c2c2205 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 707512850 1250 707511600 707511613
    0x10c020f070e0a0914060604060f0b031603020c010c020c100504150806240d06090216170c01050108071e0e06120a1e2009160306150906080603 63
    0x5800c010a080c8242c91280b140d80110741d0b119640c0c00c01601c059000103107502c0d2080d4004006580c0890b42c039008590481b800c1c03111a40c0d407041d8840d555054055000501e60820101d94908803201c1c0704000c001c8942000741c2484044041d86003181d4211800c5000760304043c07403680783d92030104030401e0f0184890600500b0103051900042601c845602040c00388200301002c1200c40e40c0300d00c0c02c0e525210340500310942100c04c20024901c19049440040981410981c0105143e11907000359209500c40403e00c0c41000903a0b101c4500f0204407035041d960b0b2600c10050b410540c13100703005082c06011404002c0c44854074140700c01030201e001e5242c075100e0205285003071102400c21100070340c2101080351032140240000b02658244201d07010020f28a86294085c00c130a40c11a208512a25001e000d1070200d0003455550880011030300c00c0d6103039008020ba000201c004020a001d07100700b01c1c0c141760001e0041d0b06c078449034406041210742c2038081100300e0410041c10354417882d9075921a9064000c1c141 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 707514100 1250 707512850 707512873
    0x6170d0801050d08030412120c030e010c170a0f140a0507080a06030c0b0306010216060e1206060306060d23010b28060f03150f061e05030c03130605040b0603010c02 72
    0x811700001c0c1005010f40e88445003e00c2492182c802010541c15400080202c04515140a030051040842010f099403e054a03020050300581040240f0803815007000503070741e95000b0620080c1121655541002e0340c1c3ea823054500c107a0a40c8040c0309902da17040005070f90070001c40160003048011b18141c651400c191007400001c00c05c0300b480b82150222a94103840e62201d20042c1d0a185114003040f401c0c1000c00d4000802551058008a0345071080d10078000111405481c26210300046600d26095402040800c800e41000c000c1080003174065489042001c90626010411031007220140016a4541c01c2c031604900d04410007001003090040042c960310f2410130401d0340189030b0710444040c044c3d546a0808224000d810258080030b503408500e05240c0c840071103203181d00141c0590b800050504800c8401b40d0700c02e60386046c0d000450b4441604603035a58030318110320b90000b8500e41c4110301028050002034132900955001d0340c40b54042643d1464484c00303140c215602811160110350100b40a041e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 707515350 1250 707514100 707514113
    0xa0905150a0c020105090d06242702090d03090302131b110304050d0b040501061e1206180609021e0f060702030111070506091209010905100306170d0801050d 69
    0x161a0381e11400c0060000450b800160b50501070308140c241c00a01c041035140c10070804c1d43c414001c00c020069411400d594030015100c034188180140d544101c2208070403440000f54080301e0348080c03900c80015203058100c8011810b00c0c1b0450800310042403060f407045c004c40c030349212403100304200c240c01005020303009401201145c0541ca090320078401a90003402c80b40006100302c50151030054803caa20108615090788030100071202a02c25500c0d084002c030f00582d400002c0c81c081e41500d200c0e03040072420a070034071141c1d841a070021540c0329900c6091140035810160040c0d40d543c05240005074008040c010301103040540d41400791881c8407040c0d4400c1d29651654070220103001550003075103841072440402d00502000d07038000403c103004501c20042020010b00c46209281034000c1e07461400405580b649a4014450340303074086000031200b40501c0c2040301d064220019146408038090303998440b900408010000c0ca90103d03080011030590098104030040d00510303050381e88284000003525402c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 707516600 1250 707515350 707515357
    0x150c1201050f0420121f1a0c0d030903021509070911090603010b03310b0405010b0a0f05040b0901260f030f030a0c0c0f060b030a060207080a090515 65
    0x12840350601903a00851529544c0c00130013039881a0141c3c803000d6100d400c4100860308070b070118010130f1021030001410101020302c0441e13600a00305030080018280140214184101c081042030104107011004411070104100d98a002c05034a001400480c1030600a080030300c2040f0020301c100d00c020600089803c001904821144a4940015841c1681e42ca5503200c3c82003050301c0d544010040004206500784000840c0650083c01441c144201100d58041c000c0151074032012096500422040c04203140810311580b1034803d4000080384200c0c4000074180c2c90090700510188442c604051001d42080d1207044005102100c4540d15903141c0994a205030074500110642b2141d8013001a15048042200f140d0440440094a442d040000e00c4003c1e03a40003281e0622505051043e0060018018900a00070a07001140b000d001c42d603588442003e0310a4400300390309032058040c007401041c1c0c18405043e4092294441c3c42d41c46038841c43c02400c04007580c0190b807140c24000003550a41c3c8a08045 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 707517850 1250 707516600 707516609
    0x140703090512010605060409050105090115020303040b10030f0b1b1309090206040f0303030504021e010c230321092a01050f030109090203010606030c0203090103110403020d05150c1201 81
    0x441d0b02c540740c070000a4090445a0701031908030f00007140209110586810032816190152007a0702540e80c1c4050a41085501d0b103900e00258004002240104001c04080350780141860000c0d00f00d0f943e00e0b5902c410100a0300801d40f81071070314005028205501040d0841030f5580b15150030708122507000800483d030820b104204c03096940310070380411501c2d00801d840040105803080c000d40359503414050b0190104440c120b20841d54511000c070100030020352103986103810707910015902c1c5250380300d10407400300c50703505d80d0300d8101190188000c500c10801132400100c001c041444503070407070340d0007121124040c0203512507130090304202d00300e000e92035041608884091483c407020071126005807a0792050301c480b81c40043c0000300201e011612504150b42c03080c170a40080080c1a501c02d404c500310740d45c81c2d038034000681080046601d81c0d031207900136031005040009034600c0c05940360300144080b20b030b03480c0444032034025201d4000261110302209600c400381410340c40c54030801904504036440140103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 707519100 1250 707517850 707517859
    0x1905061e0d0b0708070f020601030f020105090d060e010207060b03060112030810080a03030b01020d08151002010b091302090c0903030f0c1905072c040b04030c0503040e06011407030905 81
    0x3000c03400c0d5540300c008800040d001540304080d801c0080c40200400d9007100e08070042100c94050103540741c40019014100c940001181c449440e00b40d00460349a8445046d10ba070099540c0c1100e804a880ca109515100803844001607664206103041c0e000c1e10044034043d44640c000000402901c82c48504601d080366052511503000c1e075824049000c080c03819085140d05224081034441010b405620a0207800381c03d03021640c6440f1071040407168508121540020745140c42c206030007030300f815071410040a00900002c207451400801103601c102048561101102041601c0700c194144074055a80048100011600c0c00902c0341c0480d659100f4081d21405143c4000f41115121805100d1300c550801c0c81d0580c0504004a400c0c90b85d40d52855004111010b004204400114003a2085480248036660749804603503440b03466405410000800990921014141590000b00f0520081002c1c080d40fa96190450525034001401412001c2c42c040014808000c0040400d81211402040301e2040303d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 707520350 1250 707519100 707519149
    0x705030a0503041a04050c09010b180f12010f05150d050c060307140a02010f0f1509051b16030306120b04110121241208090d020901060206190506 64
    0x83c4c003002c1c0280300e411a541c0d04d412042408100080400c41c900300580403a0040740c5030741c031032880d942680f04045c07444c1c12a824240341d030031881c00c002d400035002c4240200f444030541d4030b80000c0c0d402d603406948030011095a840803c1091600c4440100060009691510704081e0035980c10707560300401a1345620510b40400040c11a5114491700f001d030b2454481c0094943c803049001038040c082c4044441e2142d41000100d800382007862142c184804c40c13203000500c20070300c1c00c24907034000c2c01c018140010302a442450000051304100c024008200d1220032010310104a04008046440c0d6400500c4c00f110b903a40700e2000304860301007081e00550440b540c1c1800041400c01071f980000c007400303015401d0340e5048401ea0700c20116403040041c003c034200c3c01b2002c010400d00da0b1081000c00d0282c0300d640c03c000c9180001042a80c0090502e07032174050300b6030b90201c0c011740000d9980d0400764410001a80142c08000450030350f211582000300e80c485043c00741c3c1c108040014000300110242003041c0010700d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 707521600 1250 707520350 707520353
    0x201020d051c0903080906091c031e021b011b0801050415090e010b122103100306090b0105042f0a0219030e010206070206010b030601110309030d031a060705030a050304 74
    0x51441c0c1c103041d02950800c0000c00c00c14135002c0d1800d0000c45132440c8a0040320005003600c500419010402d0344458442d090b05001c804003500280034680c81160721010070441c44604461601c0202106d407801d884400442070122416400d446450183c060710042c00081049100d80100606043d6407080301e011074400300e001d0100718109819032205d4052070900081e800c0d000811b510030308035048140c07054001d0000e4aa402543e950181c003c614610b801d0f40e050a4402d8030104c007550b040029008080c000f666a91100f00507217007500810b8075000220001002185441e1140c40c05001003555919000c00f0986100c0708500f0782c0b00c2c1e104021550008401406a20a110311988821403495101450354036003802406c100070800c0c068090701c16071000c04d12685c0001071140c12034244801052450b6541c0004450000082e50111158030040c04a01d161f940c0c1400244a4482e00e40d500003002d1850b040524804610003c0f003a01441c410412440400c00102c1280c1c905035190030845c0c1d81c1d4545 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 707522850 1250 707521600 707521627
    0x17150112080c15220b041b0e0c18040506031209010c021207080d051c0b011403090c09161e050c0d090602010b010305071b020114120a0c08040201020d05 67
    0x150b0001c002240a034030f403022041200104268041d90b00e0104000e8511115001c000100b050040301034002c0740807030001b40000716041d1148401060001003120311654a214184201c0c1003611220701528020403c500d1010b442c4030040407030001103805101da8184040407076101e06115103210f194020000c0c41c0f68159000303080900b90680e014000c80a541100001c00d51505080c3c0204882c50203008644042244902e05031140301c21858120109464520702c110300602c0d40c10030321030620004900a60114607000040d62154682e2000342291030340368010080d801034018130030075280480c0103081007025480184206103c0001080094554030031070251520301500000c00118480d12011180c181d0b44900d00b2411503110350024841050032074010b40507100100c0354074001a0b03c0001c90740c50018124049443d0380d0040c10002c1c65680d010380b00f005a0751081011703414401d0040c00744000b85032288100314406031a494100721504166000075168080e007200350003000408100043e10044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 707524100 1250 707522850 707522857
    0x306060c060504140f16050406030c090e0a120806030114011508060f1012061a0d020d140a09030e06040806012606011d24190f0f1715011208 62
    0x1c1d000c0315180000f0420035030340c501902c5002c401d050301444000a623070070a0700a030800c0e243d008120302042410111240020072034031010135a944a213080110124401e003c1201c41c105a99803682061710b000014036080daa000780d581281580140010001c0c03002d500e4054074011202d180195058461200040742d0204808030968499000c0d4000720540e80c118998151015581405011855407a4400300f4002809600840b5040c402c200c18042070f200340c0d00800020000c0030000429000315007810054000c01c94180050700d07581c10300c00c800d041d0000d40304540003000700e030910302e42410809210380781c4c801840356540151850502c40c00010400c15a0440542d00000311003080da592011040c121484140c096020442d070004074610079002c020101c842262a40c240842007941d00510003072041c00564000c030716400150200e64410300c94558030041201c100c03120180b0307003462884008090081410784039640070101608200485481c164111071f9681100d00417142c282c20050414803 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 707525350 1250 707524100 707524133
    0x8252111060c040e1f06030b040f0e010509190206071106040b13060e100e1e040f050a0b03031201050f0d2f0a03020306010302061605100e06070306060c060504 70
    0x24440401c8038100388040540110b500011440865440d004448600d41c02e20505c07401045459150a10015001c2e401c4004242400b07400000e0300030104011808454102c1e450000c5030751148140203090704108181c03800f00d40304c1c41340714261030590303030005040e40f042d044002e100b0019507010f20b1265035107505035001403034050010341e07944480780a000041001c600640000c102c1388400141c0a042803c1e0314601920591505080b1083d000208603204070002c4c4c50f000d0300180c44003851125200c0c0d005a071396106400e40081018140000c2d007a059a00d0300030045d002c0c0d402840010404125101c5090464500780e81d01a035482285000c01d0000404660281c000c0c1080d90219a121859450410083c0b40c4261080e15008040e010044050060b01c0041e40c9944010014009440c141c8001e00c0d80306041903075040c9942955541c00c1c100b50b540c8518216865940d404a502c000741401616480107807440d0810009051110241688245142c094040c1d9580c078009410031a42640628041 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 707526600 1250 707525350 707525353
    0x51c09060e15091801091b0c061a1302040e010e09030412021807020c090108011109090a0f060f14030c1c020d0b1302010314131415010308252111 64
    0x1c600f04c00da0394080c20080c420100300d1031a140540e48100304800302e84114581690b40e00d45419940d46810001c0e10321000c0109134100d007a144d49000e0b59807086075512094541ca000760325a4a4050750f107081820503801074000040da00300b00b0840520200450301910b0300400c00403118010ba0000c64455104405032032012081003052003180c071303000114012100403c5030301d40e16580c2c0701c0d0cc80a007a540740c40790360000120144001d028a140086003643d200c009000005800c90440450009803140c546c441070140c0c100420a1041c0c0003e00c4c5050341c625001e8005221044686012400030380307c0b186c4e50480c4108101d2500215514600102d105a8001801c480c0e1410500d016088819140c02c080703012034500309078454030306941007103e4410b55480030000040b590585401003508580c050300521400340140c50780d820043e5240ba03601079800f0b01c082e56240c071880400042d102c0b01152960003008015200000050002c0311040425203c94010103136180c0e104070150780c003c5241c40180701c0ba = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 707527850 1250 707526600 707526619
    0x6022113030b1914060f150301090203010f1208030a02030619060816030905070302010e0d060c03091106070f110609060408012301140103110f07051c09060e1509 71
    0x14044030b80000d50083c0f001c11407008800b40d11034034510032940215500d03144103c4c00c60000d8010300e4010750702040000302401d02da211488070001c903039407980241c01c40500d03941d0100050241c2041c50250801038107103e141400301a42c6619601c4041c00010b005504164002000550584400303000c0440c1c0d07011246070320012911040c5c05010854126040d18003209007850b051030040c03107809034011040d0001c000d080500e042d5001156007045000481c0c2d00841000c02c0b03080010b6462103100400151035800003003181c80342c980007503946070346c515091081c102802240082400611b00b003c40d6503120415404210740180070904d20300035000c8c5641d0020380030400207036161040d0425010010011305c5d200e255240c40c24018004e082c203002e40392601402c6a0b0041e4154000d5001e040b030421103030046410070750ba54044041641c440507045030b1603045408a00d080940b98043d0140480302801d210024908240d8010580c0130f0982030710303208010825240d1203031601882213036010100035000d00003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 707529100 1250 707527850 707527853
    0x521070807030c060f0605060904090302030f0408070e06102f010c02010902040608010c08071815020c180912070804090603080715061805090c060c07140a0602211303 73
    0x82d0303249000709513106424104c1c5010700702d209220382402e40740000c18440c01d20b031361a000d11000b000c481c4822001c1d80320030411010082a088050002411040b00074680c444c2482290040042e018001364010a01c102c000503800707401c49240e142d0b8020b01c203140120580d03600c50390a02d13401e070311b00c800d1195407030728414138081e941c1074211980d4940282da081c02a1581c0d851003600304c8100d103084000042000f03000c5003103144110300c0000ea10042d40581120240c55861014080b41d900c1058400f50740961307441c6003a820028001e03103c258010f13044407094900882101d40f0360001c4c00c01c05440c007100041c49810012140b0a40b006070640c00320410000d0f48902d082a0154401003043c1c540ba1100d8002c0c13291800240501401d803000d451354101180c101d07500c002c014060180c4040b20714007800f45030950f1500e50101401d0350082442c0180744480c80c182c448208900d1160055004280e46a070501000e900010545010622003144404100c1070100960450041c80310300e0320a2200e1040010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 707530350 1250 707529100 707529107
    0x702070b0a09140a1202060d0603170702040506040c08010b07030201021e0406110604021c11042903240907080a060f0605100815010318120f020307052107080703 71
    0x900b5140544503110303003c149401000070206603845000c07120603c42d10190010b0401e000131b0034110f6103101010a0642d201d6481e0412410300000d8581c0c200e030041340800545c0343c503006282d080312081da02000707100c1d101c000082c519103050198900080001402208251007503040342d80f0f102c6c040c05e039841c981d0410584e00f10710b46e005100b1381e000240f0050324196182c0c00031030070600640d070017071071040035031b03089202052224000c800c19503032800f0001051445846070b0080d404040f18000000010200d40b944550300700303420b04a0f0f40d00a41c0316940310055002a15a2a581c90060012000481c0e1701c1410240c502441a0000c1009001e840805000c10038980c00c074120f4469100700a100c0c3d03584640038061103901c07410440000030300c03440108904030781a45003110b40d1035040c5070100d205c541e00482185454900c0004582c01031121548000d8075a00010002e03060b01d0701d1000d9860486c554236680c0c1d03610498140c00ea1701a071010901c100312907007241110142d541c08401580c442d901401c014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 707531600 1250 707530350 707530367
    0x100509010c08011d154c0c0803090f0f1c030e030912030409021b0d0306030317130b0108010507090f06090b130e090d02010f02031005090702070b0a 65
    0x20001c110108000305008070f4118a044c10703600141406005030356850344501c030340c40180003456000714540d60f4800c40300f01046460194600d228000b03003541c0010382c0b03200c3e14001c2c1441890084d0503003201400303407060303200d4203642a454109090036241e07260440a05c0c00d0041d5180a0171003442041d40c0b001340c00f8001704800c4031014440d41d04c2c1181c1d08040a040d000d4450b20008002e080d0420009414140380c2030f815030408189060803242481d844d00074141c101d80c1700000c0e14018200f06282c1b600c19000402c562540d60352149030a10000e850350303070041c08130068440d803046400f0321980000e82e0200451032482030180c1200d1070342c03001d51303650101c03a00030401510b42d980002c9200700c003c154500d400c0070800484a10303070f441c010300900e008407654540c0c00041100d20213412515000684441d1203070703502d0148800e440504016034170141c001e801c68055880c81e103281c1e4010b00805c079071095002d1074182140d00035110210661395010080781451000e4001d06000c000c0030405c0b000681c0d000550 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 707532850 1250 707531600 707531621
    0xf0c0816090b06070210080405011e0b03070b180d0512040905250f0c14010603081b1203150f130213352e0c11060c0c10050901 56
    0xc002c0c4118032014480203200350070020350002c2040d80403030311582c441e04c0603036403083c060400018581c1500c40d90041107142907044c0240691110814802c614050007808002c10030300885c140b82507104003c0003600c0c2c1d10802298401c2ea11018140c040c0130080c81861460080c80b2119642c4075120140200100825140d0904010314901c0001c10225070310f0a4101030341044e00c0b480710b41a080501117079402d5500d103013190000c0d07110900503107402c0309019450113140b04031a415126400d2f04105070004083c18801040382d40901d14070211030488030704994204042e9030003000301030f80341800f007504030500142454100804401240b1150307143e80c060a81907043c80c0c0c05141d25903840580b03201c41c0d00c880f08400381a640c0c0750f14200520941c0481c000f1308034000320a0300c0c0401c3e061074030508403007140400600c034441c401c084641400140d1003003c09062071400c142071080c04201182e69942001000b48280c034000042020f4488030420007407100c002c1e07000d000d004514000003054013a1003070402 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 707534100 1250 707532850 707532869
    0x206120906041e05071e0306060e071412040809041103040c0e06010509062d04080102031005040606210b0409050318040209181b0f09031011070f0c0816 67
    0xd0030528240f145402815030400d009100c1c0500705102600c18141c0840f00b02d00055032240c00100080da1409000003d1202c8000d011007440c04000140454419070300291a51008000da00203204003072029540003504000a503446500c0100894001c00112070400c0b041c0340c000c01008200b000405600083d5440c02003d05850b46a40d001907810707024444035241d21880c140842e03290b4101e010400144043d6080407020352140401c81140213a0164000c44402d940000401c41d20080b40200c0d00003d107015a003c00189260107030061020401d4013514901c50031000402c001d2030f9054000080e0f600000340304005070390081c94107aa503a803044041d10040b002031004010507103891300c255580030402034620144489034260000c0182c0c8001c1c201c1107000c600d12648059030394050701818001c241d0010303407665030011400b00341c074002e0101035000c0b1417810052074840f024082d4040ea020300e60300004c0300c20500d81911f8031a81d282465040b41040d0300c15005814120030b00d11407210115100200c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 707535350 1250 707534100 707534123
    0xf04060c0305070207031709040221150d06020a022b120b010504050d050a050a03050c01140105010f030b01051b01151a0403110f0915010e0901180207020612090604 72
    0x44080e070a40d1401c564503009600b1140c01000407030001d881c401c07500c000c4640170614000d0400c0029080340c001140c00c40c904030709120714080c6d8008040c03c6940003180c02d14600e034041e8401c0000381c2c0034005000000c1ca459000300d002511107008102a00441021003200c40b159004035400741411510300414070b0000e454910581d00110681c41400c00c07a4078181c5d078161070b003030510060204a43c903c0c4000c0f2060700c100200c1d04045041840b800c803c2d14441e130350306a034502d0410103280c00d644010244580e8a00b06500402241c0c0e007280110710000034a003804509290f0107001a41d03603000c0c0600c152180710700045181007015041d44074070511100d00711108021502c070402c0c885107038030002202107080741c01c100910100e281c05000c1520b07204d00414001c8010041e801040e81c2200544d841c4a101c02002c0900340550303000790f0100003a01d02038958800b590300d42151850102c84803010056510343c0080d54000350344071038003100c29000b90400500450f06010307803603940e1388100721010364405580384e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 707536600 1250 707535350 707535371
    0xc030c0237050a120f0b01030609020a0b0306090613090c030f05010e0f0c010806040b180f070e01080a1d0604084b040f0b0c0c031504110a0e0f0406 65
    0x250010410b80d60060081d03441103040040c161042603441c9000d50b04106401c242d9000550001402c6028510801003c203945000380305001c00e500c002c0d00b00c850303500018009c104150326207100565009408480700044c064034007401100520000802402d031900d042404801e00207043c05003040e0b640300c8e02c0200100e80f000c0c00d034591282d5a9800f4404550815490b4229561050401e81d0300040c000700001800d02954000803521a1814900c0382012441010041c40e01503592030715030300c00b01710f0401a9020440d140000c000c480000d100581c0c541c0d44102c2c100d94401c181103800048940101250742c0d509150030100060b0b040b200c0404882038070210411240c03205410901c26024030f9008051441c01003000381141811094100500c0742c0c0e00b40f00002d00c500b207061502c0020b10b84054610340d50321030180c0c25070410400b003004600a0b8004180044c40614002006601580200319130920288000000d48070400030380c007551603002101700f404a085d1030b83e041240140d04c00d500422980c1b0300d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 707537850 1250 707536600 707536699
    0x41121010e0402011209030306050418050c091e0c04030204090b01090b0a3501020414040612021f0e030105181006080c01030c0c0b0f061309020a060c030c02 69
    0x84070000d0000300b0481480500b910183c021b8a03c6521908000c40d21a0300e4002040c11a03603c000c09001c40304c403501455061200500c603040d02c0d140f05440081031440c0101e02c1c6100740c41c0c0125a118a4600000010280c0703000300c0568000c2c0d54014414026034a16090100c3c060000380505002c1c03a00d000048191890460b075aa41102c0380c045088421049500c1e140144560211301d882e0b041c2e01910180c81d041500f8401000075143c0390728403082c50a600000d00084034503c0d0003405100c01d00b5815a4050303980d42c0d00311011000480e60030800c08803858001c8542d00c0d407506200b50550b0800d0248060242910340025200b44102c0445400000d0314104400780c80c40e40c4541b107942c4d008404003803000d5100380c101c90503088207420421180c03a4540e503000d40000c021180d010711048003070705001c81c3c0d02c1d00740040c400c0c5e0303d40700310140100e06583d00003404000103807080e1818032421007150410076000340e00f000c940a40040464030401e4007042204060f0322940c40f078807852000c448005550340107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 707539100 1250 707537850 707537879
    0x20a0311130612081b0a030207090b040b0303160c1a070605060d0c060e0111060a020306012729031e10060915090e2517130204112101 59
    0x2c003c030120b009035541d4803404100c0d4400c0c13907500e01c0b09a03089180410408100040c0c624a88a58024102980352515120403501c800c8a001d20843c10110f0281203941c0c00001e50364449a141c040c3c07412a015403070004103549107036000b42c08000310200e6a10000306004040c0501134000c078000c0c085540e0f00001c10001881041d002000482d080da02884003500c0303040d280400c00411b041401500041c01c1c07900740b03410b10480b800c14180360004104103155a00180d03000488541d40ca02c518481d040703800d2049024042c6c09240035420082c1c4030818004040c801a020110300e9110066490800c915241035070070034100d40c40b00c1d00b09075902003025180d994480c1c3c0708070350751a030302c0d4200c050174000020300c170044000d800b20030403c885201146168000717840601900740600c0c1c3c0c11b0041402d0540e0b4440c0d5440e841c455041c00b051039984c4465402c40c14016910001c0c44085024580c010300c0010024181c00e07242403031100d40131405843c041c8240e600c1940201d034486035503c10b40e989001c4d0f86070203207 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 707540350 1250 707539100 707539109
    0x50a0605090d14190804080d1806030c0201021b0a0308010b0c0a020103110903060f07022a190b0310091a01170c090d030e0111010507050306010e0d020a03111306 71
    0x80c1900080080360b05000000003001d401c00c140c4284e4422803002648851613154266134034900020b04003d4100d040002400032a05810700030f82c00340c0258041555001c1d1885607409164446c1150a0307214800c2d0304540d94542801c101e0000c4001035880b03140e44522a400403404948824008106c608c1c070101524034580c1e50038010001644c00e90b0045016015000000828110030300c06900d103a80c045c00064852030f4041100a014900490024603022841103000c504541440120100268441c0201c500840680d2140030300e859581c2c02c24210441c650003a0b601d140c020040c4402e9882d0031401d04111151603c1c2480310307101000c0000c010b2412206414041840d507004022180c0166072202d9000d041c0005023400c040c0d88a01144060020b110120700003032410160319219a0841000582c102400b00200a1851b00c0480a4083d21000d045103060004555181c0c0c42c5686100390842d940390f0203408519869500d10b480b1661801d0800000d01c640c3c003c1030382083c0600d4500c43c080445 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 707541600 1250 707540350 707540359
    0x106081f0b13030f050303040b1602030403060903200627060601031503050a0b16050a02150603031b070311060a05030a110403210206010819021e090907050a060509 72
    0x186010450125540200c5002c0c400918003403000000c03e00d9080b10600c1e843c00389018650b2440c182c50300e90302e40e140c010700326802c1c1d000070714403481855800002c1d10b064a03400351000416948908003a68a1a0303540e580799965100ba00b101d80340c41e64041411809601c0c000202072140704041c0d40da20b0b41032a801c0c15805540d101c840020380310b40c4260402003103129000070010040c0d4803511601c0c1480400311041e100c400b008400c2c01002c0c03c0c2074031400e51140941c541a82051490751009440d490405403c01c402880000480c0503681d060048a40e081c1003008402c0c13060640d000070719201c945920054238480e02001800000f42000c00464a0071840b543d0f48520350740c2e8800d1540020701041d850002e03107400c00e01000c00091030586138881480f21594805521542410000385807540503081202540c000d44111101c00001c031060100ca183d0407a00e001d0348410201500f010154540341681d406070209003030084401010a201007510710680708000180d1721014103482c54070421100b240c00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 707542850 1250 707541600 707541661
    0x42910080c030601030207080705150708011836020f03070e0c070f0f0b0411040e07030b060409060603121d0105030a0c0c0203011104050405060f1c050f030a0305010608 74
    0x415807010015980881e050500600f484110b84900d10241c01004c81250789602006060160044941e00640e108007207107020b505039814000c01c82c8074041c103e4882d56040341c03a1041e0721030f030390000c42c2c1007800410f0800340c1c02d21011410304803c0004002c0001603010300520140c0c0320381401d010940d0381c181e40070841c20221a88400c0110200e60340540740545200321941c00d044000380c0c2101d452760340300340200c104072034a00313250900000c0340820b16444d900c11482d000e00941d401d440469284122500061224410f55030716001c00c000e0903264400910b240d14160011040245680718000214215500c800040400510b40b001009035400098007041041c000941d4681d01500980c0e55541245030100c444115680440d00b1b448505541d006902e4000c9014807640c01c0c940305481d4441012101c940f441482071340800c0800b441610092038a080740d0b41d450061007000c0210511383d04001045a03a100034080c2c00400130002070241c000061182000718140c2d21405031010a00300141810680c3e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 707544100 1250 707542850 707542861
    0xa080d09031b020105190519091503060e010911040302120715030501051f0c05060a0c030b031203040803090a0b04030f1101090512030702101a040c180e0c070204291008 74
    0x202c6e940b50069404100c0c04100d00525451380300d030f051020305a00d8039103090b8241896605d031030700c81910b950f42e4105403030701c513041062269016a650450b03510040004002d0341c131200c021102d10858001a411000d943c03903103050b81c0e0000544600700c644030a5020480320034050110300340c44080c414251301c0050703c1d07c11440d500c2d609200103110441420149400c9001d0303660f607410305008549040d2010345d200d85487e500d642501949000c0b0008a000d84039010500c1481348850202400103440c82c0750210014200c80030410504016540205000c02d443c603151034014280e00164000d00c4c0002c520b50b00440c4204014090120b00742d901030702030550740d01555514141c2c0d4000a01550462088080701d8511072124420342c80c40b0b640c0030700b4406400355403405000c16a05105180310801081c10455440700810002071803d42d001e01c1e01e0800300362140e20740302c041d40c00351040107584540303003103203100181060104580102190341c4c01e00440421503420440b0190003682c0600202d4000030000d103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 707545350 1250 707544100 707544127
    0x1a0706020a030b03061806070302122a1c06090b01020307060504081e03011e0602060703020a0c06060b070b072303060a0f0b0403110901260a080d09031b020105 70
    0x1e5201c80c41c603002810301c40c2c28000900c1e2901c02c0c0d581002011030b030701030f1215606051181c0390740011075040540c80d1219502d12102c011600400d000010380b402800350201800d000080c170307220007031070000f07503107400402018514201d44140c152490750f02d441000030b01074503980203410a00d00705801440c1802c01702d40301d40740942801001152800400c100500040c2459210601c00608814045480398108090600d5111015030849005021400100f00041d40058400e41c0481d0307929001d604d034101d44606031840c1441850082809041880c00304003c400c42d4040c256041c080c0d021b0b44203070346901c503081c2c880e480ba24004900800390401000e1050482da030003540c0090380905286c0b05640d40d2071418500140030340002e43c0d0114001004c109000c80c540c2c1501d2443c40403141861594509101b002c85c0c03440042200500d52440f11903048c1640c8240400c3c00b10035081130020b681d0301d580225880050000130800c901050086501006480e10b4135800030391594180c40c4c1328541a00e0030300c4113 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 707546600 1250 707545350 707545357
    0x70e01080a02010c030c150606051b060f0402010c320d030522021f0f0f02010b061e1c060503010c020a0b040212120d02031e090a060e10020f12011a070602 68
    0x4c0d6052280c00071035042d035450b2423003608010856079581c15100c0743c14010a001ca85240c10038221186c0c8554140000c00c04001040303a0071171f60901700810080712034074010458140f18004600b4602c2160380c461806502e486050f5102005103040e42c9582c00c2e246019000c0354001c0c0c6050729010030031450f012300f80360031200e013110781400241152002c1d049078214030020124800d1400001f610000010300003500000c0788807204403240002c0c40400d0f8031001150484c010341c070400d0542007184103018000341e01c0710100d50583c00c0144011005c52283c281030b070042d10240c41068084e6207009000e4401520110302c10140650180c1c10505544550302000740380d0f10342e00c8805030b036030103000072813100101c2c0381e03005000040007008056200e1030f004006144c047c4154140741d8055602c1c00402c412a000420450f048907801800080c144001ca0201440d1501d00740f40d0f03485175840000c0742c1c0f00d0460802d01801e4600c05480e040c150726a00c030f503411740d07140f080703055184105a01400400c00080c900d4014 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 707547850 1250 707546600 707546603
    0x4051c020102070b010801021b03121302040f0c020a140f0c0d02030102090a0306061d01060516170a0305010f06030b01020a03050313150b0103110f0a200609070e01080a02010c030c 79
    0x2500f007680760f48441d940c00900b03a0200c0030580d40010711300f071444a00340400c40b281101030041d40c2402d9580380b02c1c040c00c00000f0498141203200b81082c108541e6507510103003602036020f004003c041f401c000042d60316020740506a511010100c640c42e2801e00004040981c507410f00042c10701c040552003031046541c0fa0b0082268103540910144c030382900e03180e207801e0003103000d140c000c98058508010780300031689826051081201420040c05107035002411941d801ca0420442113861b582400e00c0c058942400060303580c1e81400040d0040c41e6030f45900300c84d069072810300081c00792543e00c800039400ca5040c006c203030380560020704d210004240150003a551041160001c41841d01541e55142c05580c0000d40d003d2030a540d0704200207581d6418402c86003c62840000c0e58a0400041c49030310842c00350600601c1005100c50900d0120000c4400d50314401c0442c208485050411035007240d141c0342c0c14011040c0400344180006060a0001030740c046064040e1070b41130880700316403812200ea20030400c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 707549100 1250 707547850 707547853
    0x61005010e0d0501050f1609140d0203070f0b0c011508060f180106180e070303090909080408010c03020a110a03050f1b0a20090105130b010c08030f070801050904051c02 74
    0x1000c003c03480a0080b07038440c10003c81442000c0c03030710511241d00c0034100b598400420081c6071040c803254811540c2e82070302e00001c031280b20400d040362002074944002030300081306845c1c03442000100c10039483c001d00880e10800b0f0090003e400c40165441d02580c00384100c441c10b5215202040c104070044102d150016100141c02c810b81e91100300d4142550310951100301c0c134001003c1b0b0003a11400b24419600d003500d80a0292164900e1a140244510103601860b500719507204050307030802020f5004c640040844500904c4000c0068030040c00130341060a601000c90050720710005221004143c000000d0b5041c0c98083c1042d030040b4000180e600800b26000c00d50740300c0d104140d070300e450400aa1003014071856812580e200f2900034205000090b01039180144000401844556034400c0030281ca02c0140384001020b80484004880c040341e1450b000c2c020460010070302c0a0701400042d4284a4132668440d50032690f41c640504c400c500048a0103400c41e0041855000005207040c1c045039202150310 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 707550350 1250 707549100 707549119
    0x120e011104050603180609160b09010915170c0c01050603031c051003020315190204031707030504031a0601080c09030a060504110402040806011e080706030f0f050903070311061005010e 81
    0x1039031500f06c0c26146508154800280207030101d015299400c050680c1c0c108140c1011882400607240e1445802040079407410910f020f40418840c00d05040d03041c000c44240200743c00e1440354030b0203591102c41c0b206825428240021868140007007102c00c0c035400310b0301950600c00404078801c010315002e0704240900b0b1240c840000560342c00c0042440641d841010003003141030054044452a0900d00b0700e950707180c01804100003180721020300c114511b4105000903541c11039480c08903420320864000500103c0c45980044420700f01c040c0c4a0703c01d0500b0780300c0300056141c900700e2100340d00950140b103502d680314807040300000321075030001504184201510007003858008001411713a08280c10080d8143d2042004000516040800000329502d992140c008103003841d5050741c960041303019503402d043d22401240300e1080580d00024036004103103810440303400d016010680721762010344190700044022825141c1d1030000f0a006014051581226206500d064010340b400301014803401da20100e181c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 707551600 1250 707550350 707550391
    0x6030709020c15010e07050706021809190501210212070e1f0b0708220306090609030315050901060c05010b0a0e0f091c0e061603120e011104050603 65
    0x500180428104240c0906000c1c40001228401040140d1040501e0170611060040c801d030414100d03201e00c0d03041040503a80d04041086940c843c511005440d4000402d0360820821080c60109261481028101072000e640d031410301c203541840a551641c1b2101741209102c005146c00100781118a8203001039507031842c0e03229006d902c1c4d02c41c1180c106100015500032070005410300d4584802030704500c5011400e0000c5601d07200c041d4002e084c020711200e4405554204001c4010880000459100b04180300c0c015551403c10050008400124042428061903040e1107817181241003c0d58400745c806030b4660310f000821500406100025120755585520b02d49040d180e003e0b0003005840003102980c5142051041031f40141001411101c881d0001c00c0140340031040d00030040c450b0040c601d42201002d03081c0c0c00180c0148201000100180c030310380220810517400030101c425030347c2034180030000a42d400903080e0903207480350b0000d040c8040c100010b120500c1d100d005150804000c0321582c0c0c60711440c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 707552850 1250 707551600 707551619
    0x405120f06010b03010f1a0a0507050a0b04241a040c0e0415082a011d041e05060d1505131e02190303170a1b09050a090605060a08060307 60
    0x2030b080f007441c0501c00030041c000c80ca059400140202041402850084224450724045015219104041013000600b040921008000c0b0710400c50700700d424103d0030704052500e0111003242581c92081d2120419803003071465403030300c103004d801809056200717840c581641c10071001b0540c614a80c0e0500c03003411900c61294646104008008031720b0052a6012410101c00c2483c0050b1a1032628400326440075580280d04440c240e50002c00003030921036403ca41c40450114844148010180c200f8900b20b0300c3c0f048101903a0500c4030005003151b082010f81c45007000d014114403582409054000d9100490484065a60101c3d5000080c029a8590340394030341d540014002548402010070031309003513130005514081c0c0746000d01000a581700e1011034607540d0702070a1003107078001030082d129244d80058200c6440750020614840141c1085080800f0a18040c01c03034540380c007400b8092207480e140442d1950f590320400051700c4004101c1030134244603900888980000400d441d4150048504c0020340c0c1c6030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 707553956 1106 707552850 707552863
    0x6040c0c080a02071208180901121103010207080703050c12070f0f020f0301240e0103110d030e030616030f1e11120405070e070201110405120f 63
    0x91444260308100044e40501000c080345c01c000c1040003402d60062084c128031440e9440442110b409200842c00c090141c0340186201e071031600c02041079805d42868180b0300034000f52804070990794221040d000700307a04902107800450f2518510109000c24a144078420000e00e003452959190044211680103018140b00300d8034440e0320554030b42000303840300c0042c00350003807103035483c200490400d45490001c0304040e1100078101042410352000b4140c1280c3d00006004540b180d502c0c00c01c80b07910400d00c0214188038941c541c200581d1420703c540c0d440b94840040400451644a60180961303032010315095100349000c0030031405844011490f001e82c0180c2c1c1c00003031000d90100d040c2c1894419449141401801601080100a000a81002500c0c5001c25500a80d19403880aa00380e800e9840f2003078504ac803d01080c4900d091503c1c00880d4207030000203c0d80e04403075000c100d50500a = true := by decide +kernel

theorem cover : BRFrame.Cov 707374100 707553956 := by
  have h0 := BRFrame.cov_init 707374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 707374100 ≤ n) (h2 : n < 707553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
