-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1259
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:02:24.936013+00:00
-- url     : https://prove2.me/submissions/ea5abcf4-d659-42fc-9753-22302b55e523

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 226258992 ≤ n < 226438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 226260242 1250 226258992 226258997
    0xe030714030a051b071d010e07030902030c04020906090418020306010f03261303120e04050f060f011701180507050c0a02040c0311120f07050703020d050a09030506131104020a 77
    0xd1006012004050f0051000c84e541e052081c4c2d00081825415000758040a503207102440d00250724200360910040c0c80203100104044c109141c04005032030014502c205920115030151b00e5004440c040381160066001d103a80c06424109642c00211126924042d014002d5003540c0c0a0f80c1c0f030f15a403402606c10392000038000984c0c1e5000317854138042400030301a402009094545080702e0300304503603c0c074090390b0020380d00d41c48e038503060880854100390172a040309019502807103c0d1420308901002118000c0550303010318484c0c0f0035103005a105d00025152010744030000090b9503160410907800c1c001d00498070000310710f8100880d141074014010b46241082d1200140740a0519a00b4400a03044280c0204c0c249511001c4c171141c00304980001e0600413811000340c40b020f24100312180010600a4685002d0000c01c0007a00b0101c0ea01040020320364401d410071643d50307080340303000f01c80749105580040c05901400c030a2148005500138909080c50184078450000e00e52102080228491a02c05001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 226261492 1250 226260242 226260247
    0x9010f0503040b0609192d06060504090b0d080301030b06130506030a030f2a1a0402060a0806130c03020c0c03070f0501080406140910150617090f010e030714030a05 72
    0x13020b19100e001942d021200d41c200e01c4950300f0f1509440c0030b96141c501c0d03130120880d000300030800f41c400894001415007048041441158030342940909144103034081e01c504140c0340ca407105c01c2500d4102c0344040055000c0912941c0c0d607903038100780c940b4070300a032011403240440950200f1181907500525016044c020081c1c00c8042c555a01a00e8000841c2140d40900c03030b054050340740246801d410800a41c1c9031503d4440c01d00d8207480c0481d80d0346880600103150603903401c28080583c44d4007050307400d90707021800c040c0806d842d03600000b041e050a858581c02c1d500c1c14100911b11469054000d4400d4200301000c8a10244a0f2410942c81e114180201d100c105070400042040b50b2054034810b4010b03004540003d082a003844040218082c222002c034150740c0940b01384860b0640034820312030320b4540500b540c000241084d10041c440c941c4c9103850606440c5a0300851813185080c0b014000180124008010303650070b002c01c4c640c503134010030000d0380c04048042d5040b6064201004032400042d080d5039003803 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 226262742 1250 226261492 226261501
    0x21207080414130f0b010e0d030207050d080702060d09110307060e01120f0501030b06101b03031a030703110f04180f0c08060f0a06060c02010c0b1e0a0209010f0503040b 74
    0x100e40b44544092aa0003061024031500c603040f144158840e08000030700c003007a0000104005440002c046404c14000d046036040c003000b01e503000c600b000507140304589248510011381040819800780b00b001a603c2140000c0030205489540e10491031588100d00340c2d000300420034109170316407460740f02d030b0000700d180588118999840790b2100e402c03440417407500040c501400c00d40b520868030240c0080700c031040f4240612440f40340411900724004c003d03107030084205802c01c140502d200c010090090a0603221959560042c3d40c1d0070381580c1c142c80140803100901e17900e0410381101020809028052454292120002d0905009182c00000881448803100102d42c2e2201d008a080031381c180c50b02411203002066040052041a002d000010307842c0301d090410241280495180307a2218081c080c07410b211100617608a407003001c0c41a080071102030182e951904543d03015030711001d1010410130302c030200203645915901401c0c1e2110b0030381e214208040c8500081d900c5120a41700908600c01200008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 226263992 1250 226262742 226262759
    0x6071d0d060f020412080c0c090403090308070c24031a060301050d020301110307020102190e24041703070c3002040b1815151803010204030212030a0212070804 70
    0x180c007452010040113103015a21107544444100000c8115170300100021054042c0b00100410413100f10121541007503030502d07503405440b41c642c0e8840100301c40740c04141e00c801d0180d031050031801003481440740040a01d02c2c017040581618840c0e540004a480d20031070201030301c1091041445008050300da203140d64242000c000d855030003044200c0c1e01d503480b14100600024980003a5010751499000540c880700040c10801c4450100e41940b020443c0800d00d0600340d80c1c0e440902c102e644517101300380310100c031700494410452180e030700301c00b11f811035030341e200c1c5480e403400801042454050a0904021616804120404401c2e0407074181101c4070b480d10f241c80c1c2800d400321101560320042000500d20301070800b290300100303110b4030001345000c3d11081180840c07401640c090018401c0340c0746c40a0a00140b1440611700800c1b500660780b01e1003440f010071603142541150042d580040940c110f620380d0341c0310b041c1e483d4000c0c844031700140241c3d07030b603008001900001e0351911603120032000e0410703041c075199 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 226265242 1250 226263992 226264001
    0xf010605042607030812010e0a020f120a0b0405182119110a0c03021008090d030e0106120b0907090203071d061b0615030c090109090f1406071d0d06 65
    0x80c50b8603018001d000800240c01e24001c1402540b00031488029625141d0301010598004000014840c0104880119601980d00300c885000c903c6030200013a44440080800a20351441e9913900507280000307000580005154802482503810211003021402c1140701e51600d1031050602510310b000d12029141c540180703ca41015a850b1901c1c14842e040c4039001031400242c0355042d6404641a102401581001021003030900700c0c03411b042d00d59003003010000b55100d03089a0314030201551032003c01c22150007900b24070001c200c0440c08001c10101410301d09600d000039600c02e480b521030703020300040c0c4400750700a480c492425910792640b160342c40d940540d0000d901402c0c4552042081110422010000002c00610301242006122500c1e04895000450f200003403558400d80c004122208541c0d00c403a900c3e419a010904045243c1c0380034035040c141c2c00785a40e0000c02c050030000811070707001c50000f60b0034445d1490356100038411000c90b0384d914243d062400c0c0c1e81e0b0000300e140358010208196820 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 226266492 1250 226265242 226265309
    0x909072f060624040f05010f050c2a03010e0d110f030403330c0e03030403230a0803090d02011d06070807050913050a0506120604031d040e01050f01060504 68
    0x100d9501d1010b040350f9180664807503042040394192a6000344144c0d40d1000580e034840755941011032034080e906800c6580c90801803581c581c2541d400600c0c80001c0e25200c00f000c04400090024040f6a1030003000c161540801d400400018407001d140d50000900002c0c5503079085101c0380a1840c0c9800e585403125051090000b09050b03050032843c0710403000d121010100088000040090b0101d12440e0040021801c6641140301e075005100031f0000c54180e0640032074040c21050311080a5200d07604860400003400303400381401c80e02104121043c60046406403d54049034020441d8420000c0c040c3c03042e11103101703442c41c503a0100e000100010300400a60f80c021031541882801c00c2203180015100292030740b03848102c161260140151a4801d004980c6c021100b15200c1c409403a000307890365a0380c800140040c04010984500070004408a10a2011600f0241091128608140115000c0c160aa6804050140e074600000c2c0589c824402e860540e0b1003030b010300f2034074071099040714000d02c52103c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 226267742 1250 226266492 226266529
    0x902090c04060c1e0c03080306090c030601050f0913020714010c020102160b07170a0e150c09010c17030406050708150a090c1803050d1b0809090a020909072f0606 71
    0x42200300818408061700000f5841703410700c640d0301c1c03420324148201c0c1c140c068400301d0b03101d800f4824046140e130407105454100d5940040d1544454010740080c00f41c540b0b110684007154030019400e418045113040d2480540340000003482070b040800b2089080b44180c2e000f51346002d0301558180009444851101d40198035490700b80c0044044a542481c40390040d1034000d0004d030340b41c988a802c40000d102a000c1c0400400c0902298980315021143d0f502c81c941050f41000b50f2040b0b03d00420507008034441e01c00136803014144e04c07460140390590040c0b5040e1602000f040254000819198680b05210748802e0301815040c4094609020500070345a01c041c04420b1200a0780c1410341c5020040512004500403001070900284110300030b400c0040185c204042101c00c4e122060100e110340b412101400c40c1034400b468a0303500c0c64a000b000780211490654400d030000c0500086075070040c091603038000c03900316004400a06003250382c800c0405c011342c0329180c1c101d800040c7c000e1a00303003104001480e420 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 226268992 1250 226267742 226267793
    0x706030b030a02041b022a04051b0703020106140603130816140d080708100614040b0703020a031d0901090c020f03040314070509040515060303040503100902090c04060c 74
    0x1030f80010240e503420501450014800c040002c61a03030b04020001c0c40c421003240c1c104d00c20380418000c4041a60312410580036544580220f840c1c1d52007001605504000385580300d8950304c05145c0203020b416648940604681180090035880c41e0103800c407402a50182c40402c2040f01943d146841500400c40481c10080e0386040c2c00086255038160203900d217860000341c0031050280f04081c01140f0054685d50820254070704000b5000c8041201c94165070072400c001c00a00221702c6004003500c00d0741c20400d0380840104201007095000589070400c14465110080c1d401c4400d00e024201c0e1100b01c2e0b0455000410710010407031030405a110b00e60500c0d442c03064031200e404024003e465a4030031780c000c90300d003a0805041c8411440c1030107102d02402040381c2003001e508164a40a0380c51058100c845007204d0100041019964200102d40040c0301c05820780c1c04d03000360481c0b54401440002803c1e80903000c030100081c0c1c1141044200d8090f5049520f40000344100742e11080031b1052011204440000e06 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 226270242 1250 226268992 226269013
    0x102120703030906060f08030322020d0303051b0f0708031b190801080c015c01020a02070e0a06051801150804120e0109030b010807031407080706030b03 67
    0x120040c84054001c0e14041031100040c90500d049643e254030056403200700707201c1404031b510b0104c105c0b07421040384c0d9000100604500030180380d2401419000707600001582d03107a020035405801152140e0701c40305142d00210701b0130140d4000361046180412200804000f07007000954403101031031304400210200c4c0c451030381c1c20849415950080f000c108406d440c2c07484403441d8a0b4010b0740b0b0b6014024000107060419010800609950b100724000079902c5404149501c0c003074101d600f4045000818424482d034000402c1081c10501c50202142640d800f20f10701e81e556181e01402100e00c507c88a41c02408814a44000600340c0d44000d00b0012405494800015196490206c2c009040c420061500c2c0d440d403402c1c01d06250340300130808100620040720300308400315628610b0f0400c00296070410b50841032041004a41a11240e00014850200c10340089488a40000c0610a4a01c0b851000b003002140070340950369407541c0c1c800c1c00440d80c814641031007564400d40180c9452240035084904000b032 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 226271492 1250 226270242 226270273
    0x2060f0603250e0408040807060c11060d0e01091101090f0308030a0b1c05030315011707050a02030d09050c0102060709031520160c09020717031003140a02030615010e0409020102 78
    0x1365411350f548075005c90280101e200500078100105000c2c2820381030b0000680d80c030040900503542061140c00c1c00300e01e5448012990308502c42a003c200004c121455917403030115180d0580950103030004a420001080048030081490b080e80d4001400c02e013107944040c4840f0191841c031500b1a0410000050007440e03100d44180c0c950002d2164000d1600d0b0710308aa4811101c120310380e50340d4100088403080042d9802c81499081c0c100d080341c90704c15969128103501341e00d10711807075000c1500180750019980600c031000ca0340c1e00100b4800d90a8510310740341c0340011506a485e03804094030580d0001c0c40100300c8441a84076a492441e440c0118914000c00d22580c40244c00c0402500280c46000c00404208115040c0c0c10380500f101000440c02c1c4029a280c00d6034101e10100010620701f000804594400c5801d846080150b82c8030003c01c110741c1d10400c07819100d1070300c008100c1c080c1c8102d2001c6840b5500f040c94a4141001c180d5480c4040c000c403800304406080340c500d060b415806a510488910784 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 226272742 1250 226271492 226271519
    0x206070c0b070524011413061a041409091905100504080307020601050301151a070807050321060904030f090e070f12090b0103170c07030b0702060f060325 68
    0x80c00303900a808512144c03c100c90003000704401c1040c20401d028014440032001404110a220043d201c808425803884000740c0180596001944001000d60541c1c42e072550303403001402542c5805402510395804107003441804101581e80b07500300d8001082c81c4d0201503081102c950110700078003c94a03180c1d2408001805c071101901d00b076a41a01c000108094189c04119250060000760004c000350795881c1c01184808046000748184a1032186d604882d404404003034030f03615034100c00044e948000d030f403901c1a540d50000719230352030039000d0141096840c42c180300c6444c46200b0107007100720155216641210400300700140710050164140010031000783d5028018410002500d480312595004400a0002c01e001328903807038400d01b040c06440002d107178031016504607036105001e10440801e02004003050b004980c0f011000c0d104140c4000107000c0d03400d81c194020319984d000e0300d0960302c0754001e42d900c20030100d5405415500c40c0040032840356180da020b4101d0040d00c0002400a9110310b00d540046 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 226273992 1250 226272742 226272757
    0x3090b0705070b10080d030e0c1309050d0905030c0d030507060507030608071e210b070c0b0906060f09100f03050703021009060906030f02070b0711010c0c0b040206070c0b 75
    0x500045841c400f041024a070300c1350400c1605071020102441c04038059980c108491088040684032034022000110030000320170a810000e245c901c002810700c4442d0b00074061001b042d40d1500c60b0f180c07241507241c05171130b02d00280c48001d801390842c074500d4814006020b454007400c0341045000c00c2104041b818910a840c01149556808228540b400c401c151034400e06411550103e450310000102e58100355048400312101d400f1035032070700405031400c160030038141d8402410560402042050080e44440000700c4a40318610038000c5440328490242d444004a55403500a603890342413009071710303019845650204407100c0002126840d07005480890326568030072181d55200c07400034011851f1642036400c0001346483d08101e07003458040020000a0144141d809166039100101c59100359030f011940720503000900320790709080600e401844064956540801546009808501e162040081c0074911350091100046504c0b20307001c111040d80700302c20807914074070141000030358804101d0141854 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 226275242 1250 226273992 226273997
    0x2040b0a0b071b090c021e120f0306090c09180c0c0a050606130903080f04151802030f010e030a11031317060906060603040326010909020406050411041503090b07 71
    0xc5103d1200280005031150b0041c40880f82410909180307641c1c0007961690301a13440c460040600e032400903503420000408000030005c240054028085016a001580983d1381500c2c8207025a0341c0c80c8060409001d4940c03c40d511500c64414544194250511aa000070301c0505903403612842018407850090b00100407105500031034104000c501d040540180c442c450f402042c8100802c44e50010440c003801440c040c43c1e8100f58000c00c00b402144102e0401030148120200b07d665030b06c4021105000b44410128032030310501600061000301801544603415140e0000c60405e40e0216003540c200c0b00c40e5285d00c50701c2c4028000114140003060104005085070307c00d544101c0c40b0284036500b48000144200855804001480100d44405c800c99502640502c0c0c44074680b6001511015924142c4001048a07001500041521711003607225540c0b0310701c01c0f07d0410115555a0078481a16004030105010007030a020800c000c0200c0d02030103112400620300010281c0c002d690302c0c42054416100d0780b00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 226276492 1250 226275242 226275263
    0x10c020c0a0e0112020919090c05210304141201020f1201120b1302010c02040c0816020601230d05030a0509040509010e060403051b250b0a020a02040b0a0b07 69
    0x15039040888800002e00740141144140c0c0d81000810312810080c620004d000d84040320001c0c0090f22407030005028401d0315801800400701c513050440000c0c0d401e025182c4515114800011002d020140081d101c0013000c025508151410703040700f00c45030404030140c1e003124540118000030803084c4010301c4400364010b90151103410b0361404010090303058000c08090600e07410740201064494142c3d503480541500e4007079010b155440100c0316840101e1000350014100790b443d841d0660882d991300d20070020714a105204905020040780c0c1c0d030000703104603883d41c09420070488111082d904a921042806400ea40005003590343c0e19156601c000b00140000b2401300b8414600c0c41c003401125042210640244440850911020f4560001034001000c0c881d0004400c0e05a903942101c4008900302c0348191030b03003c203000500c0803041c881003003212591a08000301080c0c0034450310581c0c00c2140785900410011400b507085c080103048541c681c5038420040440003440c4081c007401050000e1148540c2c40 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 226277742 1250 226276492 226276513
    0x130204020d05090c10120b0d20013207030203040305030301080f0114070e1201150e0613091707030207180e010e06130b1b0f030115080106140c0f010c02 67
    0x1030800b4401300129100c2d2200d8010a40016400a400d11850100c40000500030f4950070005c0e0900c02c0f9000d00812503e41d615032010304c0b805140742030030b081d103080e2560700c40d6540b01c080802c000707040002e030700b1403040f8122103110482c40d00c0c40180c0b1042d4460700407a45000d85036254945550026442214558083c0b01070f0b03070a402c8280130742002c8210050000c075a60500c04009804800044002c9000b03810180c6c58044c1044250003080941d8030014002d5074040c5c07a08980400321000310740d507501501030901c441c0c0d42d20b2214400c844001e43c10401060107210910454046a0b115080036002c511032070030041943c416811090300300102200c800101d41128000003401e43e91150785a052035003080c0200201a41011488511241d115080c0203566075800d8a144120088604810f003884000c500100404800030085040e00d019509848500101510407514402c09000b1030000420380110103600001141c06000110300c500c0a40b00490841c004041c2100c003a080ca11005900c19141c52 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 226278992 1250 226277742 226277761
    0xd0503060f030a120e04090c090207030207051507020909061b030a200306010f2a0204090f0804030b091207020103180f030201020a090602030c150915040c0608220605130204020d05 79
    0x801c408003a06c0c2401580c126450700e0060781ca042c03084000043d000a092030401d4400c0c42241c1c06400700030700c14242d5036455a1180150f030840701c8202c1c061050b0f8808252201d20002d410f920032181490804c14540081401d03a5081d0006401c05030010307111020311108807806000020a58403000b40ea035100c2c582500010000890500841e05120389010590b071810300c05044419401c0c0800200503820365280702240003041000000760400040e11024010480c43c10b000780304507405a0350001454594655003038a46820002c01225003130100300c0c070b40046d40203070003040e0b031644a02a90100a2100e44403104100e020990880040c0d43c00541940c030641c0200c980c00181116200560400c420440c10540d500141501d1642040b190400280200400c0094002c030910088210400303080174500161304000e00c0c0194000304008a0015501c4069420741d12040980741d403445514000700d88038403009103c0902030707542800d454a503100c007589940c0020a4801c0e880d03080000e1520308443c14 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 226280242 1250 226278992 226279007
    0x30103150c0807200f012906040e060f040e030d0b0907020106050105030a0e21040303090e070c02041104210209010501020609030f0a1b03020d030c03020301080d0503060f030a12 78
    0x24020b100319441400f80141e48040304080c42540300401c403040c1e882e08900145410b2400c42ca01d9035030b42c2041c0501480c4014841c100b2010f0410001201d11820070341d0401101d03008601481800921107000160a8a020940745046100107000022034201107071a55086138048000801082e40b500150038840c10072024082d8010f201c1e200820a450030440000c086100240001c0e22458599070442c044c2c0c80140080f5220101c1240080c6208850f65903503050303504588402da02103004440001404020860b60f03d10400091340c4400d44c03030f4110b5082000074065440f008032100790502011440110b4060703214100082d159454075202d00510400c40700400580105045402020034072040200c000140e079801c01103c45440d0711054001402c0b01d4520b019111880783c880303c03d102005168011525400c814076960781031018004050050f4240d12081c0324201385076011090f80c03900581b01c0c07009036402260080403006280940e000103494928500f070242c40d0f00c90040525800f00c0e0308006e1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 226281492 1250 226280242 226280261
    0x30f24020a050403020d41031e0a11012c010902300604140d110304060c020307121b08010c05040e1302090916050105040311041107060203010315 64
    0x10035890222011002010b83c0140d00c0024050000d405040c020060704c4040c5450b0a402070303d01000140c1407a40d0328490054603c1c103003000840404a82e145541d020003214094403003d01101c01081011500110a50240741e005003003001c1e03600060813845081c02020842500c0015001a80c0400e48003400600070015489090743e251242402c01600d070211a0203841050700149086d9840d00038200506510780d580042a81c0281c50412041081d24003291101d85143c1c41140c00c4002c444005a90940c044512504143d0050100300802e80c40340c00a00314845c0b015041d54541a540c00e001d21004c1c258000803181d8020001c2015014172072021850300415500000b0301a501c924480504075201c2c46c0181407402c00c0260000c0d03407600c0d484170300714402503002d0055a42403070008661615554842c1c2d4440c1e64080107000000c0d81c8d817190b03040e9400d494200c0d15500c0d036501c00001300001840850b445a41e180c1c024000d500c00304005101460083d80101d003409480e55001017120700b114401d60 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 226282742 1250 226281492 226281563
    0x122707050d060902150408061005040e060a020315040f0b030606191203030e0604030c02040501050a0f090e01090203030a030b010206060603040b06150903010204060201090b0f09060f0c04030f 84
    0x18010030099072031644010300590803003000500702d1058004500c860030035586481c048400001d000a01e40fa0001c0c507640300d5510303111010780e042e44a5080109850070301080c40c150754840c401180d10000c9913401580c110460070f0000448416880c01720341030310f158680d030701121542c92260b14603601b0144481544041c080380c50b8401c1c03620111600e03074070950314004e103c0c08509034000e410825003ea80142012914a8215901440e00b4a401418808824000c0703000d1404d12000240d80d04100c0c0c40d07001503407000c0c0200f000403814404482c0080401e06c0480710b4564035800d103080540ca013840180104083d03503801042c50285d05001929003100a45164092002003041202003210664071540114044480700081a4502040c1e245402a1070f04103509d5440000c00040e426015808103011070710032a664181592100d100f41c22840e4200c5010046801a20000352400550464298050001c0c0807450519803a503c0f00380340aa42c08808550002d02000ca1940c42101c0810404603801100d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 226283992 1250 226282742 226282753
    0x4050f0601020a0609021804061505040501060210181b06020c030c0d0f0203072103030b15040614070503190219110112020708030c07030f0c051906021227 68
    0xc00001d580f440e459038040e00351550b5a00d04e0085584d440d52942000100464007900344c101400d104000703100c070441040b03d20395091400a510b0401e40030f403a04803805500030304900100c90000c01c002e4100344103103580741c90401410000055903d490403100d104801408403c050808002a19001103e41d04038841d511010b0b200b4910741d00c002d2a04d1009a00190001d0360101c281702191400002d80c0162290184294020102c42d01e54441c10101030300a07541400814290307030500c000c09655014030f21014800300020b0003e030b40580f2600002d602500e003810315002550312020300f5500200c3c0d0140f814408550550421a4108110071030252105c1100314031424075911280c1008507801054180032004c2d1400c2c41c48881a41510f80ca183c0207880d8640c3c9180c0312015900340da0080800b103002c22042c84c072045296114141441003030380d02100a259000c05441303041421050200111201902040f5180002c01001417403400380e04203004440d440c441c00b008540150002003031002c4d160b03220 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 226285242 1250 226283992 226284001
    0x2060c060f071b03050a020f0f010c0e1e0d02061e04150203121f0801020f092d0f04180c080c01141b03040b0307051e0306090f190e03030604050f 64
    0xa03611011003c50740344c10b02d160707258100403040c0d05000d280d4150404500481c280c1c0c2000b5141034100c0b040f03058035560780d01c040803c80410002004025104036500300c185c00b033400c0c06404e00c0040e80e54141c0c001000c4e1420001403044552001c090940144900c0c0c0300401c080108000915003440c040001f40003450904160f01111400c0417002006003260f031280384000100300404441441c098001c00009540d10000e0116030b40c00350f8000140c9500413585a00514249440f01c22683d40901d6030140c50603110a8030341c100107107a40140c04450380265580503c1d0814501903e44400c001d1241080f0b50410b8034203500380341404585100b503414032041103800c00d20203450000310340d0007807a1034902481140c1d102c12081e1844c042d94010601640002050080c00c85d0084043d002400c03241c03815190154401340061828081910803c2d080807103000850742040b44032480d141e110688410782480801e2841c80300c41a1980d1400030719554100001340085070400380580342d401002c2040703503c482e050 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 226286492 1250 226285242 226285277
    0x70f06140a060b090103150b0c03210c1602041104030b071d01022d0607090e010b1c05061f030608010b09130807050a0605070504061205010b0a120902060c060f07 71
    0x284d0040750b810195203d8028086000c0c1a284030050f119852041d0703122640408010b9607940810b070041c0f03506040c1c414941d140e410103600e4500c40c90038204a41c0c10b0902c0203050221032015030000703c0c3e1041c0c603031030340d4a82410b021000d00011030055151010a00b42020054002141c820320318002400030710600700c0d580d0b00004c80e03203a82055451a5400d08543c1902d0303941215034000c0c40c0c60707e07008007800e1001c03081c2e01c082094103942d402d0b45841c403d640e0303840d050445841483c0440160030b6403c0d02e0362291106030351211b80d01c40d4016081c6216021082000911014007407203010200c0e544100034440704100348111450384a05480035900c80c1059014812117401402c0300500084000441c0c0301040403d000a000e032a40c406814009030600070700c0504a500f05014900001e4550340c81d20300804403602415040b5280400c509140484c0381c070040380c8885440200d0541242c4035140c034401030300c07008010f100c41c0b08610094950b5040c49812400698805070400081041c84103040c1001c10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 226287742 1250 226286492 226286497
    0xc030f0507050f0705210901090b0a090312110a05030a02070b070b010b0f0c010905070e0f0403080606030a0902030a0506070905060c0705040c09030b07020f210403020d02010302070f06140a060b 85
    0x405590040e854107200d243c2289409500d08490786d00520110341c0d0002c80032000040c00040c44241c0b42e46504c15202c1000348a1070060501003c00900550b000308041340100880c0d0950b81040c0c6081d0701c0c007a00d080855841c105001108944503072000031a01d025943c10320661024100b401074091030291366403100403448506010710303980040000360400d16445004101c403d003054020091014400078140340b9110000c074071071110b02058490014940010843c43e1038451540342e21242007685a4070107001e16038000030590714603e0303900c040102c090303038040080c00351541c4110000c04103803401004c010600145a8030641c01074100b842511122100441c6510070346805480010b118042003400310344401c880d610141020111005000344164042032440b50241034038121000c1604e40d09040e4107540c00710f146801240410f03c014801440c098580082c2207005150141c00d0110070b4541265512040f48200c400c660f0322000f402e04542e4120019506c5421042d08200440c94103105440a1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 226288992 1250 226287742 226287757
    0x60d14150a090c300b0108210307080907050a03050705030c0f03060a02090a05090c122d09010204090c0801030c0801091a040c090c050d0f09030e0603070509040f0c030f050705 77
    0x519200c45151803110b226a98081d200e0741042c8003241c4d12181014218030364280120300b40c0f0b00031140c0b03443e010004540c1503408140c01a11540c61030343c8164007164012006080b4030316038018010002140d6070b462000c200a10b000b000036250140c504070401d49060310508140c1c0c094454080e072880d450703401150081c0d03c03042284003d44d03a8a101000500b2440c007a420141d80203950801b4881c036200400040d048407032800600380c080d074a0790306003207000c54840d010b82071411001c0000c010025642080068110054400141c14551114440700645090144c03040005610100400c10300040c3d402c071030010502d000080001c0105030b250102058600c1440c0340301e95070314601280030072102d03540303c800402c0c1c60741c2c2c00c100030700b0b164030000c00d1a4010340c1c2e008019400c10318070b0b43c02c4c00500e01c9001070a951503114182d450100000340100c6400041c1894140038080c007000341c43e0307100d0f0b0003500c12103400c0c4200024510501c41c009021525012107010b8401e149c00204001d05030050101c4034107 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 226290242 1250 226288992 226289009
    0x70503060f011503020720010f0801050907030903030e060103050d0807091505031806070806040b030f06060f0a030f080406030f05151320030103050d08070c0b060d14150a090c 77
    0x83e0540003400b90040e100d240030042c4120080100b410000580c00414900c00f007090703036480e92903503420070119101d01003030066a80c46683c0101042c5a18000ea03c0240d01da442801c001ca04a042d8034621810801e00b41c0c010354480d00103da01c100010f41c0070340207641c44441801c080014904090002c02c1e203031007a21040701400000000319080c402e02c1090924441c159008542c65840c00d2000140244e005031741c4107010310308200300140d492501094114801d400341d402494940e079544100100c1c801c1c00c05003076400400044005c0045868500c8003203880c1d01825000d651146001402400c40b20255003200300c1c3e914100c140302401c1d4800e06c00b1082c40720115216910080e5210105000740101101b44840201c0c030541e40d02c10b8440d0300007842c1240e01590a4945a50180c04181c0c1d104004070303a42400980c3d02c0b44030320001403003503080d60341140c809850200700b00840c0d40c3d0013032840314400c40e101a9070700081c0300b0713130445180298003988158410700900000e0b040e2b07034070890000045d0140224 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 226291492 1250 226290242 226290269
    0x603090a0f0312021804112811030c010b0108070f170403091d01170304030507060c080702100c0b071d040905010e0a200105090609040216050609030c070503060f01 72
    0x1803511480d0f4a89034990350701003c541c0c1c2c03da03480c03200c0400d01c1071902c9107008604040403200c0d801d039100155282001c83c2d030b0300c0d2045c2d0001017841500090481c04500144203509218003602c0c070081001c0c0401c2d5070140300001e00c3c10307c10f000141c8001c0303009201e0401c100310107407070715805980300800180c80070717040080052035142c52070140c411b15100c0d0000302c1c0c18529141c02c24148200045100c0c101c51203851109008188862036075100e12540c08042c1003640701d0380e402c0004520420090f00b5481c000c844240c01c0c071a8690015100888060442000038209450709044c0500e0b20103ca40080031420844180400e200200c1c00000c5500801c034441ca58820149051010a41004400521560607170b0300c1c000041c030385201101c1d81ca03044c0d5010240786207088001540150300711004c0241c01007040303040c01c40c003604000280d0b00c4044064040001d40c0d06040c005403003040f5090040995034051510303440028400703464103805600051099006100344010404484a8181580c0c3c01661010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 226292742 1250 226291492 226291523
    0x1902150306040b10030902121212130f0c05090f100b090a031a16020c0a0902091f031a030a02090610020f0a0b07090821032809060b0603090a 62
    0x1401480890b600c01d4000407041d10136101150b241d803040c143d481c801c13150340030f280c1e00350a08160755002c000703034400241000304080602e8003c032110385980000b0301c210500b41010346517552480551a100103d6600427445001c0c0520324004000d554401c8480c00c420442e071900c2050151022018072450400f0f070310029869000f07469100390f0102654005107210b40c10300703143d164040001000c44194008540d000314000a46101060840b0b400d00e008140d0350540c0d003400e00920003540510b040d0b0381d2000c1c1d4101b5014403402d20310007078010300280fa00c00207044580c914109021850b141d801600c607822046600e0016902c820f131546c3c022000b51103104441802a00c164900745a50380f1003807042c40b42480d03800c100f1418141d114414078840d5a02c0019580c0c4001d515a10940d81207034989a05c01d048125900b8403c1c0c41c051980a0750292005079041c07040941e048003e04484078850701c1030b44505804080c01200c2c052080d01c54011b5804501c0c2d17280040405440e2040d40000900d42522291800b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 226293992 1250 226292742 226292749
    0x601030c110316030305060909070e060103020c010c08060a090603051b0609091f0e090a2a14030d0c080d0507050d020a0c060e030306030a1b0b1303051902150306 71
    0x203034410752000307048998480440000110411868100300d001a06100000c1d501e82062480503008007400c800070a1031508150b01e0300c01950004240034100f59090160244454090140740803060b91510744000c03d041880030700035a042d045e04440041d0382880c40c1040050390008201100b0340100d82c91602021250001500500c0356512040d480450340041c46140ca10a5002a0850121940d9045180d94071200e825000400f10751804580d001007443e000403400300d0340d580c0c0c1d10600b02001501c00c2550340807118035a07007042c2c2207400060040075000a190404120f085c032200c0050510404161090b07441601d103215026120001035160004240414091815180220f12845007551501c1d04550020f01460709544140e80c02d03810300e02896184840403048a00491000e4090304804c6000d489a40100840c1003007c180c2d0741551400095401c0c054014040c2911106403660903a4a0b41c04c01502d80800e40030300b01c1e0b08920450898006a503081c0409045100090180d40c4035030340d82001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 226295242 1250 226293992 226294007
    0x10050c0a0c0c080f250302010e10030b03010e0309010815060306010f090f09090203010b01030618091707140d050406091215050411120a0803060d1b180e010b0102060601030c 76
    0x8000350720944d50841007070440415601c0e0803203400103408076801203c0e4240b1880341014480640070500000e0628002c0c2440300b0b84003850581030801040100744c0b040070a0031110954440c98594202248009566038060021074000ca01c1d002408450111080041d9440c4000b1740782d18103021280c044804ca80d1b000c1d80901c4014540114456621551800f0010282103840800c0b0320075464003084138a10b42c0284030302c00c165003203502090795402c42050303110020f004002c42500c05800c3c1000b0652520b0006000f0f00d80700d031142c40b052104075000400189803c075100382c40310070f0007030920080c44403a6004c04000c3c100d9030f803880450110200c03820300c4400880c503c03180c112074506010400090000701d401e5840036207000e949140c081f01c2003c44c0c0684a07421318000400c180782c20800f180702d6141000801c0181d41c0203085070640f03a01d0040307904e6420403a03503012080c00741552035010700d50b10381c5221303550061115000a206460004000070b4546600401080c149540e961854440c144078106 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 226296492 1250 226295242 226295249
    0x20c0d0e13050c070204060510090b03130b011701060515030c0d06090e0106060e0a030b1501050405030a060b0f01050a0804140304050a0803070b10050d03030e0316060c0210050c0a0c0c 81
    0x1003000750381800d010182407540008000e80c086c40c2829000542820320080303039030f8000c915640c0c48491074140f801c3c400b8aa130001c0c1075050f24183e844811001b040701c080c910b60091041c99502d0400032001307039126007034a90a6000138404c813041e070300134101421184100e0b50f0010804900603a52103810b0440c0004000c03d81004c02510f1800c0a080c49540c0c0560080003903943c140c41d00400d451404040005403206800000c1c840b010710404110f40f05d030701040c420341e80901410b150341026261400b2078500440d405003a01c09645852044215007404844515400001e2030f240d4603000c07500700090031008d0040c200030500d1200b5003100000000920a40e80030f000300034103141220359104107041d6241c0010009846d09031012001c614030030140312801040301d80162048d1182601034600f0341c01480e24001100e094001042085c500d601c0038000c1c20300091081c1e40000ba1494a41c400070328001c3c1da001c02011251820080c040701c01c41c520290b07200f640513481c00001c00d03109881d02c000c0120b4641d1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 226297742 1250 226296492 226296529
    0xc1d0609060f150c0106033f0e0d11100c0b0702060c09010e010320210402030703030810030b040f060b03010b1c020a0803030103051c0e0105030105010e0d0203060106110c0103020c0d0e 81
    0x48d00840c528400d8009a07071320002084000c14081c907003000350841c0a07496481d00d008220602c481402c6420040e58001c0c002d8041c0c1d0b030000c02a0b0b031200210364074121014080c00084c040410040410000811881d004420ba1004280601d0700300302034801c42c171501c0d123142c0c1400000c00304414581e01ca03812812541182443c0c042d20015500124559500004551451030741101884017520040440d51132041e44c00500a24159185031401c2da41054040c201001140348150017001182c0320030b0035640242c4c0311309031008044071242015800c4808450125110385d05040301c411380c0e44e80380007203256840003114080011800034030000301c0010241d400601d40d80800b0000006210b07000c030b6900d110004c110701074024512014001c4450b48420400d16010810600051085522511040c0d48109000e0419400d0340010b800180c50300070241e016034009050804180c0f1102c2c814801052059003e007415410600c1920f91691120178616001c020406046020500d0750780b549001c1d0b5070700c00004d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 226298992 1250 226297742 226297763
    0x1020301051c03050304021309060e0607020d03090203070e0c0409111e0715020a050d1b0f02060708010b13050d060e0705010c0b060d020d0b040605040201141c090c1d0609060f150c010603 82
    0x3140c50319100c4330211418000341c010305a107460454080d005000c04140d000700641903a9040a064060104000d000c241c80354506103c00300300070100b071040c0803a00800c200781c25215104400e020165190003664405807070300a0100e6400200101041000180c40383e10241e241c68910100329864066481c140c2180c03802c1000c0304102803100d0388035485900f100c0d40d0300324013007d0200050782d44e800156002400a18854010480301c286200074041035403049000c08042d981e1a000150314480024064035016681c0d01c00701d84c2c5c60001c200202c018102800e100c54140e6603602d6202a4080c010010341c0910034481e007440c110340d5194103001c14282e000c0924000780c00c2508020700144000c60f001c80c0460888c20b1003500540030401540c0c488400500b845081e0140e01c0c0e400c40c00b805442d50229140b0702140c40100e84424091084202c009208500c0403e500c0d00e002000903601c030180ca0680901c2101c00d10143c680c0324032100d54000d00000141560701c82100201c01d00402c2c0c554405420380400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 226300242 1250 226298992 226299011
    0x20102120f03010f080703050a06020a0315180605030c030714190e01080c19060e150d0b09160207031b050306010e0f1501231b01020301051c0305030402130906 70
    0x3488051816074103004d21810050b40c40d80ba100360342d6000703800060901c1d484181441d001800c03a0f001841d0517101498040342035158a207591640350110340203480039040c4480032044140040c400c0c0c1c4010721003100107007403802203100031903101c5686005054a41101c2030078010203460301c550555420140c100000c00107a5501c0554000756000e014a01c0a4010340402c51ba951030040320040c40d407147c0c4d03003102d00c0b0107107816015503600422040f55600450440c1d12405007110510190588c241c40580c04164044038108100003600018450b40060210614202c5d0140d40007130507600b600d0348442c0302c06400c800340c0140c6050b6a101e600203680362107400000f0400c500d50040940c003030f18851844543c3d83d1191018810400400c410440c0003821f00b00d241900d4140d0f82d48090300300d810300c02c4024a402c41c103103000414201c40c910701d407101d61b4000004001c139091041c0c030706107031b140f0307a4000c0001140b069400800d00d11000d04041d02c00c034200500c0500c00c01c2142d00040d80b06034400401c0000c1c1c0034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 226301492 1250 226300242 226300267
    0x231909060f05070b0c0a0e03150610110a0303110409290103090b061c020402070c14060c0c0d02040f0905100b0316030602070f02031f060b0a0807030902010212 70
    0x150003050001010780300044540ca00440a40b600740394001d16581c81950303080c80c0b082031a001006000c00304081d64001002644090103007070340c40008e003507a10425141290501c007000305d84e11001d9041104921001000c0b550208a02c010b0030b50500d000b18100b144008480c249000e02d400800c141e40c5002d5008541481501c0364003901840c804200042115400040d4100c4124400140209040340d0000d8503078904486080712031540d88820394400c0d000d58010404036041f496045600030805101400300808240182e000240f00300ea085290110880b08951a02540150f10b80510065214101195a01d801c0080050f0f600103042003605181c0c14165610202ca180420b007043c54240c000f5001e06010075511400068112404807461540e43c9030002035018034030648182004580c040c006070707010b001586050f041d001020600f07101e840707041d801b00c41d0719600c21248400200015501e654102c152142e21020fa4200040d10f12010300050303080946c002007500011400244500c015807 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 226302742 1250 226301492 226301507
    0x2030717030c0c0d03051c0f0f0207050c090702100905071a1206060412110607080a091806030309030201050d06030c06111902032d07060509010e030a02012319 70
    0x1a556030850714400540c60a005029004d00e00107070014204209040c03407003007a0741c2c0802c50307203d44100005c4c0d00300c4008074807012207140d000c05001c0c0d240c00048041c10302c00c007044050b01d078401c1224070011605040101a64690102e10300034030894035410700400b400300c14400d100080c15a141022007400c10035040c84829441000f0628403401034101150309414410709071010740700a01c020401c20b000316203c3c00c0385144842004d5601c084100401d0300020003c001600c9a044240c0311030228900b01074058020300c00d0b02855036851450000c0410120380e04c07512440480e502802c201d40e03110000d25121001d4450743d00003426202814200207a13841d40800464079100d281c5040e034841c3c20004000e4042214054070107549075105906440c3c201818004001000c0c3d9198a403c84803544c2601081c02c108299200d0004110040b8841c1d40d20b5810400040341410200c0140ca6042140c0c0c0c0043c000104542402081c080724801030204280d080d012503c01002058031074022404d230610041814 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 226303992 1250 226302742 226302757
    0x307030306080f0c090a0b0d050102040603020306031216030503041a072a0c15110a0501020d06090c09030303020d090203120d140c030109090f0209040b01050f030705010503130203071703 82
    0xd20400001c0d03011058003140301c8000341802400c0300039a41b00c908402d0040c20f0309030f820a501c118085614000035009200400080016840240e1203140c4001003500300390300d00b003600c0c01031001000862414680c1c1d08019002640c5800c0580d101e0315281044070864802031440c018104030301701401780494114074008902d0303548003044849600b900185415582ca0004000c188180765a030a009186017051403401c00c204500d00102081040c0d600e0b98500500c40700300380c2d620395001480d0a840c600900988000e814118800c1c400c16a01d40e00051008010b8803018041650203e82c4411401d5150400350382d00e90020101c44591001600c1598154000c503403400c80c081c0f4000100d508080c80e000c040340304602c4a12000d0440e0b1074080800f014050070b2000f111480407808034000180c2d02c400f0304900950140d4a041c050b98106400d0102000140022900c61741c40700f14200980d03030707004085030b80c0700c84070807005d403204e80c0184040b07480c00040390800c044000901403c03020008001000d172649 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 226305242 1250 226303992 226304009
    0x160f0c03110d03021c020f06070e040b0d0b06090a15090203010e07110712061e050901060e010521070b0c0604060f093201021303020109050402040506030f0c0405030307030306 77
    0x18002000440716042c000103015030020404116031400100d19202030007901d00603a0b402a803441001400c0182c201c40300f4010030020b148a840500f454800e0141c4c024083d01c0c2c03551211010f4642d10098100107000a1080c1c0d01c440c0020f8100341c007074120300d40755400600b46483c403548581d6020080d4000340142c4400300d5030280003800b031a1050104080301036a46010306502400e10407540e94903c8c0107c42036074000e0722189091000500e82c0801d0340d9141505800050713504142c44420709581c000c0d449206032a038140010f00560740c17500e00c071264202d003031030040c0c0451000c0c2c2080c5040109990111003d141d01003500b44500b0000325100e44a07030b204400070880340b01c4480c15030048640070035014240f100007107a42c0c506041c41180708406c0124165855007050841c01d00c0c00e007a64030501260703600c034203807031020400c5580080b0b0002c0a480e04450543c01c141c10300340800c0040c00000d01028039803400001241180003080c049901071b000c05800d0300e64400c03441c28003802900e464070034810b1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 226306492 1250 226305242 226305263
    0x216021005220b070b0c070c090b011206080c042d0b24030406051e1009060b04080a170c01050a0b130902010c03050307090f0305060702010c0203030403020c06160f0c03 74
    0x5600400100c00c2d4103a51000d50700c941000482c0c1c850300c0d10032000908140003102d0801c080000300c0d82c01904031004007003804020402004100005040c01008a1484c81550404d203007406110404a80a80358803c1904c0000340d54407008094000c0181c15512052003103481101803a030600c203030b000181c03c001c043d152103a00c004048403c00195a0240c82503a5409041c40480c0010b500c0390401038212800072140c020501c840002e09078800f20a071000f416400f06040c04106a4646010f008010540c213a592410245400c600e50f441c3c200d441801000a444512402c000b1507101d800c0d01d100c0442e00300200540e1800d001550001e00000b0032003403140c030300f5507407441030702e007a9024003100254180c2d140d291a10703039a601920300f0742002c1c05039018403d441034007084450460582c040258082c4000701002c3c2048503001c1e003180e04107650002150020820000801c0d00010b207080c104409a0301159540c12201000c001d640440500400c074040095682c400e2010304a803000031b072400b0320050030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 226307742 1250 226306492 226306537
    0xb03100515090c042d05030303070f02120a0c020f0303120f0709090506030a03230a12060e04020d0321020d020702040b06090f040e340b0301060801090216021005 71
    0x70800d0180380706604a00f0340641c1c100305501980801d441c101075000d0800c0000176106c01c000303411340e0001c5482d000040c05034160f9148040e8104103111103901410300141c41c0c03500150005001a001a201134001d512062081d10251810170444040303031040545160345040102005003510b030103903401800078504031000305005040c0d01c511405000300900405480c00f090f60141c4800140d80e400b49038404800c0703803d2101000d20030040c081c00649684000344a22010501e0301143c0d4290030a0901c07070110820400140c60311201840442d4160030705003000410100015640021030b42070301c160074000300309200400810f80240c8402442242e060211079402002d009003402003440551740a000c590343c1e8040c500305640079440d50070080094903008136844901404000426800d01034042c41001001c0f42d003824040d20002910400381700d03500e154544540104106c0060090001403680010043d101c3c1a84540340381c446640a00002800c40f00c454019140360070010001c0000e100308203852 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 226308992 1250 226307742 226307761
    0xa0803180d030507050d05041403040807060306150203030c1803160611010b0f100210140105130501121211070f08010c0302070c170a0602070b061e0906040b0310051509 74
    0x19403184c0000e603030700340c1030011a0031040061701e0040c3c8182d404601040d002c0794407403000e000400c080d155010040110a140c48001002c45065900541e071921008500c00c2c5220360101c2201c1d00510445d0910b5121061202d141c641110040740e41035140c030a44144102c2d81003800498000c88a4688860700140c151482181c280c4d00d9542540c0e5002462110040280c40d20314000d0b0440100c42c41100c00c21605520b1100480700f4200311aa865111800100040e00d03024007964a00324800c030b001d00440d45484400b441c038618104004000b99214585040c0d4948261407580702c0c0914a012071718503a545100165640a180c09850419420042c2c40006c5600074000c807039010754000103d000c400d2500704401c43e80100c0350f200000c2802840d0050005c01e42c140040c0410380e0040b10003940c0e0381002030400910422840c4603084201c02092190303002d035600100147d004005a81c00b0030700d46d5001000130704001803100c0d9900b071a1b16090600415640c20a800452002d0640b100c40482d01d40c000d81 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 226310242 1250 226308992 226309001
    0x11b03052212020a05010f0209041805070e0a090b0403030c0f0e060304021201060b031006170402011e030b0d080405091029041a090a0e060f09090a0803180d03 70
    0x41e01c0216040d50410780c0051500c0846004966592041e02d800340b003a13699103402d544d60220080703020703500459040306900c2e01d44aa00319034260070389100e4961100755034071038480f003c070b2083c006030390383d6000014041e800725084403400661151420306640f07041d15000e80100008000d640c000313907400b01d100202601601c2c0b000d1030404028220341c1541d45503800c200030503152101443c0300e035488001c00115220624065030056180481d00000542841c0e8010f01036281a210f02282e16820414000542d8000300418a20140b0200840c20300342500c0003a8054640312114036041042c80d0a21000d00400c00042d1041d9081164103a6450b01e1701c103000f0309a001180108100e55240814402400d00122181207200c1240c000701401c0c50341c0e800e070b01220b50804c84c0000e9100d083c000340f60301803442c28101e403001034043c41ea040d01c103504044010940550158120b240502c2604001c81c07500f0804000d410707074465008a076035580e03140c8402880c0c0040c0d40b024200700c05119030340742084550b000c0d014 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 226311492 1250 226310242 226310281
    0x90605070e091b2104140111090904030c03090506041d010902030403020606100201061d07030c0c11010c0c0e13020108090c1f0e0d0506090c03010612080304080c011b0305 75
    0x49114511107880e485550303014003131110640c2803250528440002e80c064180c4114021181c03200c9540e2000341c034500b540e44400c540d0f0002ca008112006580d0303101310f0040c0d086505031502821002e820700c3c0c150b400107a19004564070070380220340010381105080303c2980342c80300c4c0d685403190b6903610103103081640410360b0000d01503003024002488504000710706010b504404e1002042c401c0d981c41c0b030405862419030301e10310140c1c5008200180c80c0e805000303803121005a80b07400f1036605c81c00c7d1200e0070001c55505003c0d04018401c205041481840100040544040c00c0440c01504111120301c0480780b920f14100d020615030300000d95244c0c0040380904036184054110500114241d0581303800c0c41c00110510184a44801815a039444698440c0e030740364407a1008018504000b0170051410819100c014803da0601c0d0051003070b0603c00d80000010355110740c0d40c07526a11f440c90302260502170b03072068001079841d04500c141811074001d0311001404450702c08004d0f40d00c5904107800305294042 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 226312742 1250 226311492 226311511
    0x302060912120a02030310080d0909021309020c0106090c0503100909080705010207031211070201022505130c0f08091c03021309140a020703080a091104090605070e09 73
    0x34031000c0d4280107038103028000c20710058803281592885808102d07002001c4580041c2d1012041103030411a8401c00405407641100a100e00c4002000c000e000500c140122045030381c0100307405c030f15080c0d5444000b003e86503001c02503480c0c3c070301000c00d1802400e2601c00c1500741c0781440c515200c0709019400301e0b4024a4070b5070380b2907000c078148503090003d80b602e500700701d440040030070080300452400c3c030280c50302c80e10941d02c95442006071200c00c01500d006903003100401c1400c004083c0140e800080360701003404a0a12103200524484150540f20116070010740c2002e44070050303a0060525500c80914001951145544654200d400b15404001200da02125501400f0340d0484080500c0203051580454507000d440d0000c0c809075101903800c2503001c41d20440e206d418041c15100900c1e0f08a80c04954000c0850505001e514000c00b1650040c0c10b0918807580d803103600d4180072041c40f00c6c00180101070000d01080441e45420402004110f50440004160b407105100d14a0001c82c0c2c81c4c041c64144 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 226313992 1250 226312742 226312747
    0xd0c0203120a0c0c030c0c030f140607050301080d08040f05070f03120201051512100608030a0201180305030103030f0909060f150c020f010516060c0801180203160e0d0c08070602070b04030206 84
    0x50345e050328200075024094421304c540144c000000741360803032542c05051290440100c0d01d40c642010510b0101c0c050b03c1401400f90920041c0314625000400221224440c84c0524554446007404e0b6100c029000000c0c200340203041c40402c03a800030b07489031000c40b803250343c81e032824a40d00c01080307007210b00c10340f03403504c110420031030150b450314001c01c040e441800c01e003003520b84582c804143c810444005501555458101091502d0526020b100b02031139050101c1d81d540005a41e60780007005840b05000c020248030444100c0c4581c180310f4000080907020129081001039119000c482c0c0c80b140c240b01d0350b0001010890200100c500c64401e04000a074090101e0007030b21402c0c0015103e81c1c000701040002110310b1110f02000c1441801070902e43c0c001911500c110f5414410b10074024560b1002c0c0d104ca1034010420300ca10300e51034404c5181c010040f807078294080030071500018950841d01001030f00110312407201282c8400040f03030040c1142ea15130200c88595603a40c45000550285200284d4440e609 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 226315242 1250 226313992 226314017
    0x5100e07050304060911130b0a080307020a09020c19050312010602030a0914010309020a030b04050c06070b1302060c1b090711071e1215060e011401140d0c0203120a0c 73
    0x181c0045d46041c0c414442e150000a07400c0c04590030b81e5284660303001158444440e03036060300b0040300800180c400380018501e8454140c0124024410038450141c00310ba00040d200b140817000d11130721000804100c0342103082000350034204d070789810441d1140503180716100002040c41c00001200c54168140d12140003003441c200b044c0c114416007101c2c8a042c1500c0c1c0203800700694030310b202c1102440c81511104038905044c208989002501d1110314050142049440c02044402080325444090348550442c01252072010450501660b01922840d00c2050301c51004140c4a88801c1c80304002940d0282d41692034101c101c80c070300701d000455100d90b000407200b030001b82c040c907480d800713449425143e960080c2d9469442402e13100d0106d00644100200d0307010b00c50000c80e540994002804a100b00c0d00e00c950401140801e0301503001701e004c0c14441c02502240c6120f00ba8000d4411500d84038004000103903442001946030b500c209410405000032200285901d00c141c49160803c0480d90b0f0b4101c0030f040c0303 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 226316492 1250 226315242 226315253
    0x3031805010e220e030a081605040308070b040f0c0b09010e0301020a0504030f1e0b0702120414010815042306030105090d200102030c0d1d0303070315050306090105100e07050304 78
    0x140f05000c02040e9840d1400b0286a00c0c04000a10b6244c0c0c4503624083d0307900d4020302c8800400c90020085041060820041002c20304900a5816180c4c0050704405191100d00c2d280b56914000800140083c00304030700040c011042c600504120b94080e25100315401d544402c05080f4892640c8500c00715001784401d001054117090b4502c001480382c0c0c032880d00c243e485998503c0082c0c010208460b404e2500080060381a414020b6115442c1e41b0174005080906091048880f511150b25050400450f40001420400c00304661020450090f0041001400719100164070b10b040c4209010003048000c0070690605051281d640325981b0800609076103080942c0440d40540c40700768814007025094242000345c902071000b1070251280c103280550712981200c0c40c105941c0a0030400c00344100c3d42044030180c500100c03c581d406511494001840030050950001040d4541c11054040c4640310400c900700f20154880c5d8000c80710342805809456461304071410300b48085030084000365060012400103030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 226317742 1250 226316492 226316539
    0x50f04022202070203030f030105120601051f051c020408010c1805060901050c100501031406072a0b040b010e06030304080a032610030b07020c010504030f051603031805010e 76
    0x10307a1003901614003222500041d1441d000558440900785000004000c18a04031700c4c0304a030b214110703000c1c010b81d40c9040e001a40c0303101007100880c088c0040714000c02c000b80c480c2e42141d41445075065904028140100d090009411034020603540350303c0d040201e000c0303602409240004c8903034080c41f02d941078104014028660010f0320410705228050000042841c1d041c4140307150325411a500140c0340d8550309140a050115010341c12064100ca02403201c05a0300c01c01000c0742403800b186002403004403180e805020240900c4c00f4264040c010b003400200300c072008299040300c461398030480050302c5880405440380b01d02d02c1104c60940c4040309130b40003c3d0040d003000d02c20000050b14100720400540c5982007860080780c4030200d00b10311b147c1c2802000100d4000e16002010f07807005003421030314900040c00c01d205034000a000c003007a030740542302045820801900907012115100c80e8203a502c2c503000d881840303640d4801c00950050000440c080d44210010800c4a200422142c44805212242d40305d04 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 226318992 1250 226317742 226317799
    0x50d0c0f0519171810090f0b030f130206160201020304050d080d0b01031514041b0c030f02070f0303050904090813080c0108040209040b04062a03050108060c07020910081002090301050f0402 83
    0x84040100047c0c00124043e1039001000d140007116564540350340c000f100100000e10300f5915040c41008180580c440405a0781d1100500b40c0d0a00c0520300c03400140d1031030041d50f02c02d070f44c003212410207241002412005000c6070072103160f043c00741c0303e1404015029126400700346d85400c2481c0324200110007643c105030254440150000680681c0c41300440310a62096480d003000c107248000e0902055031010072641070034070500c040c04045060003165115082940700c094108038022a0340003040d9500d41c44010419403050b001a42d80508032460303d54030483c2c1c0306041d420f0043e142920b08550003601d0003072051f6401042541e565036070f581c41202c800005441a103c099031003240c92118900580c28501c51541201d0780c44403c14203c0d40101903030700503040700aa60700081c0034454203602c20303015031b40700c0359040f103482c1c00907030307890683e26100070a6034042c85040c4614464982c25800540c002d103000c2100354000c0c00a9500c0c14000c40109100303407402500810302e28010174a00034a4030400140 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 226320242 1250 226318992 226318997
    0x323120a18030c050618060a1e06080d080a0c0206070c030216060305060f1c060203060d06060308090109170706030e0309150d06080604050d0c0f0519171810 69
    0x3103105003407400040c015140c214041024a55000300b400001c001403075015030701d05d0046981401c101c0c103803a150b15001c1c1036002556101d24076840000700002201d075141940042c1003090541d500d00f40d41d9200042c059a0300480c06c0c0302c006ca155813181e80100300170f1100c3c5400030040742d21035020848509241070025000c60080c085101910f2403141c035850f004010302d40d00860f190404504006a510a05e01c1c2d01c4c3c882d1080740481000c1c0158105508202034000400503120351303c4070b010581c0e40d2801d1500400480c0351100100400244030080c00e000c4e102a03a42104040e02d5000c2c400d4260860380740d45405a001a00070042140700750040e00c0c980c1c40f40e405507801d1484c40000304404100f4504d95401014002c100c4405088661013003000400500c001050305080c00c0d210162140000a611000c00003030707803a070f401408440000301c038486070701200b190f001e4020444120051100725004480c00b0508500c0102000c643c2c02c151000031141a407402060000c02d0108189403c2d510080810f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 226321492 1250 226320242 226320251
    0x1505070209040c0b0309061f0e010531021c1a150c010f0501140d0305070305070804120305120f0720010b100203070312060b04150c120207030323120a 66
    0x198000241301039401202450000c4c01542440c0c0100301980c21003c11f4050014404501001101040c058150440e03100359140b55145907074410300e032205124840301c1004091945150b0400003202c1c2c3c02010b01d070080070809000c01a550070f001007643c0100071400040d0f10030045070790301031030b0002565289048801c1c1d03040c500303c544104036003511000c01118490a07a42d800402c014003034a04c0c5c0c4c5607500300031111005000010390b0041c1803802001700140800c130000c0340c007604110810085402603c40b51000900b454003a28008003c1c0d40400c1038052003d2072000031900ca118521606805028217840d510803810301ea00c110280084500d032035102d84d42d00e81e00307400000e407070781c200710030701c1c1c040950256580303810741d0401408032191298150b04044c5800d8003003003046110400e850aaa41d94030a203250112504001c681403502d09001814245020381b41c8004c2a40000d00340003141c1c826100c101c02c810703956902980040d1603c00840c44e106013000701010440114040c2c03948003010950019 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 226322742 1250 226321492 226321499
    0x12091a061809010b01080a0207170a1106010f1e060813020a0302040c09080d1803020d02010201140106090f080619150e01090c0305150307050909030d020f0904061505070209040c 78
    0x1202010a4402c804a42d640d07102007900d030b50b8403021131944440c05030410352030450203950f2000d9200d41514040d11507200440c0e040d05840c841c00a02592158030012160346584411b00d00c00008d900d4440c0d03510130034032142030843e00140b60300008204d80180c1c8603107010340d48511110790041d40d07100040f031788071441d1900840140c0c2c8910502c40300d00d035039940d0744c0c40003414a4805440c100c408450170382030044c0c68090b1041400b401d00d07a40c0035294144c4148040030700c548010703805824100101141c2f0504203001081c055845014141101c4254448410880d518442c050300d4040c00d840d035016151800031001c00802207074210444030b511100001222541c0d0308102d0038019000e800408403241c8482140072481d5260107296085040c24404505007000900041c5d910003042c030825000d01c040d0000510102001d0017903841d030312a031400666071640c04025401c503903880300748280d01c603600d88180442e0b100b05896250381101010380b942454002541c00304660039100920481d40c0320341181021 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 226323992 1250 226322742 226322779
    0x6040b06070f080306031e1b0604030501050f0615040810020304080418052a03061e0301020a1211070305030c07021c0b070f140d180c0308070312091a06 67
    0x70b1142c041c80319292242021004c150401c0b502d41ca038820100c11408880c0c1c4440c1e408203100240001c21018034403150080e0300880c038140240d81c0007500b95480c000c200610a4042840c140c0306850807101302d21440c0e0b505d00c0d10300b19401980039486440d03021600010724940c0329402190041d00a4a106062550701e105103520150105444000d041d1281e05000c1148480c480408031a141e191411490020507642000136000080515105243c01d561007900b072144420f0400344140041d00942d500c0802900c05070089081d102d000102c7e601d4207400c1a140b0b111030050b20300035503050f5100b61858507181034200058200f10300c01c2c4e03031020000304984030343c0f540741c001c222195120b00b424045524000101802400e5401641030070712042c140c0c0c41101c030f69004200c42880290840001d001064102c0380f41c0001ca1800c402424400805004000c1c0401800500400c511990300c0d001c0d0b59085c0320503034003518003260004146000038451540121402c0190561100c000f4003803a0060a04a610 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 226325242 1250 226323992 226324013
    0x615050409050a0218060901030e0f0d02120301080c21010c0306030b0f04110103020d090c0602061006020f030909130f151103090601030201030e031204030801181406040b0607 77
    0x5004654002410841c0141d03500619a2150001c081182800d480050f401040c20342c911040348510400a00540301f41c3c000c0d4400500c905402c000c86042400c200446039560140040b580094450310302d80d14410380204048905858100c8007828407000290240102c2c08203180c240c1802d080310840b24004c0c154240b003561884520380e03030302040040c40c0d400c10741c10b4860040c18468202e1300000070400030800244103200d06034070030710b40160740d081c3c12160311008203100c2c1c00042076080030280008540d640010b0084c042c1140c18403480702a039507136805981d02d0f100170b203869001c0e03041400761001c585001c0d500c1952208107095040f40304011075864460f0b002011808482c075144041c0c103c13080c9600c41c410103904401c405141b91460601405283d40c27424148002130405482d10381611900038203009840500c04e046414003283d0501d4600a40044009d0240f102400010070100070b9803011400341c0c480c0c60304900320000d00c54aa85c01444068003409031426003103c001c01c00c0e03000141401c0344 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 226326492 1250 226325242 226325279
    0x11032e03051c0e03030309060f060607080c0307060c02072711160c0605070f12020708060705030106020c06041d060f03070803090405100e0c0d14010e06010906030213051306 76
    0x1c0800744041c14500a440383d501d8801c5a070080d4014810800c2ca802d002803003d8001e120b18810100e9036680b000003403e50301c205400107203c1c10011820800d100c40000c00340c00381c0c0e84660780c00d001040403000700304c0c2e036041244600b09814015402d10003844e001415033300001c0c440b0180c041a800041c0031080c1d01e41d0304c80c50040c03000c500440740c400f0034030a4a50448000e04982e1a050745858501d40390031081030764850b005800140c1c418450a03009001304218801040244142d40d064039042c04003405a4100740b0404000d4000c000e00824107262040c00c4906486c0c4047c580440c261200000e4411080b006214503044003601c0740c840d1041d90200844401002e040b4020740d030719020141400103450002e803400c900752014480c144484100c0300e41c2c15500592640c403050b15442c5084044006c0c00d0502c0000b4082c142d080004620045030a501902c119401e0b2103007a076883d80c2d080100e08911a10101c0402c2c86a0380d0000c1c0103038a84041e004405003180980443c00315203580d0b41200004e140c0c1c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 226327742 1250 226326492 226326523
    0xd03050702040e010b241e04030b130b13050705091305010615050901120209190501030c0f050a0e2e11010603051b19031511032e0305 59
    0x98014110301d0140900001955483c00a1018504580219903101d0401091045d9080090a00000c0240100640b201d503102c0187e0f41034007202d580031004c0c003541b2a00040d00d1200f4102c0024907500702c042c80d1200781c260311001001050707071484506d5258185155040b0703460b00440d0000035990340d80b80380c018019690140400f411074098586139007147c009500020f03d40022110b4030b5080794200090303510050003030030041d00312200c1c41204e6000b0300c0b5090040d54065480380803d1400600c4810150503030304281c80811400c04208000d840003250300807103000080e001c0280405007031140000d01c1c01e0080142c07400c43c907240b00c049250070520000042981104841c056010b182e41d000541001e00740088001300080c0d410754840f5515814a91460303c080d0756440302c040ca8580b034920550f01c13101404a8021100c070784900d030800646a0008000355014103080c0030b90b182c19038000460303000e06071000c0c0602c40d40c091a035451501c01c1c00309080480c0e1140e0408004042107042c03200c0321010302c140 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 226328992 1250 226327742 226327747
    0x12130911130e16030504020d061d2d0c0a0306021305032505010f021b013b060906090d0501020f1603090b0301060e090603030918011a07120c0f020d0305 67
    0x100340d24581040e030f90450804141c1070105000150b1125650010f1b8960040f030b000c114040390740c0c24039500d21007840d04c0c05048d00c42c0780142c2d204038859a801e449010721110081101140c1380300090303500c0d400580190b902400042040000880388d13401480c10207030160a0902040c0e681000a0406501c880b00e8a861244040000c1403591055000c4000e004242000902c0e141401c00c02991f441881ca43c210700c2c04074480780da0795160301413a040f20f1110308088600d00070b8540540c41c80140d24110380700082d4106da5030583c40807860403009482003250040d02441c240007000c000c01219100da0441502d0795503007000482c00440a010050801070142660803014600603e4001c1568200764805400c001003400103001955200d4090203074200c04440da43c420352118400641035114007044258800c00071050b031840d070760f029002141202c0d543e0300e0303000004092482c9072056201d1610001c003050a90b0b5001030419000f0164498080d009042010a882850b8040307400895020030075404a60301 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 226330242 1250 226328992 226329001
    0xa0303030b0a0506030f0703090f0b071805062b02040e16080912070204090c08060916080c0603070f03110d0902040e011401180908030c090312130911130e 68
    0x82e4002001040256846880c5242500e000c4084010281c10801015100c100c060140594400300780d00030354011280d00594202214040c10700003058000500c6480d040000080c0c1d450010159107138084081c1440408072081ca54000e890302400c00022a002ea0a10010483c019041485407040040010f414054000100d01800b455401402c8542941c46070f100189180030000c00c0e2859590f05030b401007600b0308240b60a003001851600081400e00c00c09080201c0003000140c004030b48600410980951601c50038500e4445400000c1d041e00f00c5402c002050f2003502c10b60f40f400c03c0c10010714000a032029802d001a0156000070007001c8050b440780e0303140302503161901c140306034030312100000c21030001c0443c3c8400d0224014426407642c1c5609900c41b08ac01002d5800414a0030342c088a40c03a603901e003983d96036481d038000070359550080c0308201d00e4030b0303006403607800702ca0010710341d901c51410300c519109150001d443ca1103114558180f051018050200f040245000507060407420032905161 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 226331492 1250 226330242 226330249
    0x408070f03021507020d080c012405240301061b05010e0303010501091e050108090c03101b050f0f07021807020606040e01150b1803060405032206021f0b0a0303030b 72
    0x520843c6071504100200c010780d902900700620f02d92140642da180d40c4580e04050040001c01c00c10740c0050744141003452421030000d400d0701542c10469088280202c5003004030540842e80110b407540000410043c41914011100c41000c21100c40c0c01c1e0341502c1003582d4680c2903035500c0980801d036601c00300041c030840d80c00c202d00001411020380000080400c0180201c1c0140c2d8910a85042c81418004036138510010b224044941c0b1015007202d006001c2c01d4588001454942e08008031200d84003050221035101d04222110920a8034140741480d1000d0034a039800d90024004030381c4070714a244c40c0c80c01c1611980b40c240c410041500036007020f14041c13080c001900c400d00325229842e403403d4040003200c0140c032880e0081da98022000c50b101c5500a00c07010a00d140000041e0303051080f0b508000c200a000001042608000196103078801c6980c600c10768030303110b0f031300695001da00503c0d02e0b520240340c28110308544000751507012801c07490741d001103200a0410303001540002c0d141c900c000220f08 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 226332742 1250 226331492 226331509
    0x6060b040b07110907020d030c09050a080a050c030d0206220b07030c020706230306040f0501080601080c0f09010e19060605280e0607051018021003060b041a0408070f0302 75
    0x71001e88004515142c45d0200a4440d0031060030501415941d4401240803403203000300c2405000054544403240d62280c102c0d0307070303181e001c502d08895503c182805a8070506001c02d078280703107903e150010142a100d40710300b61400c111181030b08404210280c40c1501054100352890701600aa40f4001408d0303614100c0241480c00580056045c010401040d0040f02030002000d0000c580c84101a522900c6400c0000c0241420440a420705c0c0d00b081300105076040089452412030f050003040310030441300d1400307200d0b80720480040c69600038003400040001000e404071081d882060004041450102c0b81480c03011580310f600300000091001c11041e88400e103140403581c22044014241c2c00c000341c1d942000384000702140b000ca010341d40104140d0100b010402901507188101003090041420044035201d0505801d0411b074030460800c4403e8040d103001703214103000c1d50702d42000d2603e050705087d414003e00403088211490080104000501083c1c240021806031140c03030a41003c1d02e01c1c0d4010804e813070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 226333992 1250 226332742 226332773
    0x40201110c0105040b0a090b0f09100305040803010905040f0c0807290306120709090506070306050904030806010509010903020901080307121806030c0302090d0303060305010e0c130906060b040b07 86
    0x5500904101d00701d43e800c03005440444403c00e10455841c09080d070304071900760890380500e003144c01c0490310b078035450203900203059500e03015078403c808884140803c0f070030b5400585019103048001c00060008900c030343c000550090162503007100c50305085e91400081c0f42140e00140f00c80d0841141407181140500c000c034031608003400e1011070350903028035034403d07840b01816151180002408001ca080c0007448120001c20300c03a4820041c990041c1407180d2107280449160001a14242021406150003046a401140c150703644a203640d98500c01945c1c19400b070400c43e8188203100800200585c1c07074181283c0a04a000081e50f2121014039041c80d024944107a03941c1405100c030320702451403c0f044500811100030f4a000700c1c0903046100250001c1c481c07010100e8102440c0410b1500f03040c3c2540000048900c50802040000d04fd0464a9210030780e020300c49901c0244160380036000e5840da0031050045006500004a003980e4500024842c1c4c002e900540b0783e6040030401381c080c440c0400714900c1c0f2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 226335242 1250 226333992 226334027
    0x706050105012c09070c0515071814010e060f0c010209030607030e1b0103021306020f0f2409100501060c0c05040b130509120a02010b150412020d14010c08040201 71
    0x400100300c0c40200800b008243c6014450340400a4540c901c10410000219009010342d6000800c00c0d40c1003e10080031240c0c2c1002c2000c541c82103d1030000602502c080740c20035101c00080640d01720044804000a421281e0311007004c1c0490718554211000504a2072649000143d0300c10301c1000340f60400c03200420540c1414903200c4042229600807540c002c40d101c40c10080e450320304030400181c0c004e004100850442c01e0348020045131254001400e2000e030202c15044440182d8609046d80d5aa545041820380300840320000b203441103003000943e41c003c00058240d42140c2c82d00310000c02250701c264060400954115080002e000d000c01306003000c1c08083d60140440552880440c1204c0000d1440300182540d907400500c10a6090050303244808140c0f02c1150b6449005400038080c003c2d01203004d110300d84d0381c034100d40308000ba00c04072030803166501c00018400c1c0d6981c00b001080346880c0d0041e42c2e1400344021350080e0310000c0c400e42d064814540c58080242c00d040c000100102e5091210040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 226336492 1250 226335242 226335287
    0x11070f0807031e0f14060612120708040e07020706080a02090a0e070509280803031306020a110d030501030606050303070213020903120706050a14010b040b090f06070605010501 77
    0x102200200710403055941004000400010101581c402115250750150911072004240c404001403465014201079885c02111303a26100d60040000f0b124500c42003140300c1d807100f100d0a080000c0c4002130450280075451040c103041c0d0b1815075422400c001c450540043e04080310600c621a00444071070b4120303c1c454000c5040600101c04110b568945004002502e9000c2001590461081c41101d49003100031300742044419000d412849503030709640c8124480c0a8195002c10294400400d0307900c0fa4040200c2c44402403110703144c000c000c2d4070a0200d2010850380c101100c4d0034100802c8080221212030390001100e40c0365051000490b59030350030040c4a50010025200503980340c0401c4400401d207801c005944010100001b898002c4d0904000300418001c2450818404c13030341d0210307104048000e401e03c0710072000040302420400034060483d62800c140030a110b4455520301411241c3d2024041001c1c440210001404981080c201110301689a000520003542e204000c0180101e0039000c020 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 226337742 1250 226336492 226336499
    0x30f03060907180308090a0b0a020f060703090b0408030a060f1e0f030803062107080303090601060207030f06020c030d02070f0624140d0b090609010e0319030506010c02060a11070f 79
    0x140e083d40502c4054090500800d60142c00e41d034440741c1c4070050403420b88180c0d5509980c01c020751640d41d07944c80003c1ca03020b40400102ca4602034042d00800075405074100c8290b41d10390780c8100141d08080c007502140d940d210b10205119030342150700d00c0540f095650202c664900e480011004101d2034003d40302040c0c0140c002c000041c0d0040170360f0382002d8221030014040000c00c80d1021100310305100c02c02c1511131450002030301503000c401140100841401d940150b81c071044244e994850070300c4020240140c0100b6000031030b0117540a05061079440c8181c0f860101500b41c07003010380e003003050300f0303a546088550402c04000c014031510503c03c070bd9501c1c10648124404004203031540a00c6120904001c1141201c0580c0d2100e0820740410b82c0002a40240e05143d14850f82d240130480f401c0c1442d610340129a00214800015070f11508501030300064048101c0c40201d000e00805003280b4148041c0c3d0344000300603600c02000d45406001c59a40c05c1c03281c040c03000003504c0c203a01a071000c0d0b07030100a950f050 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 226338992 1250 226337742 226337777
    0x5070305061609060807021002040f0501030f0917070809150d05090105070e1c0c03030507050d110309040b03011508300a0c0201020a08030405071503050609070305090a05030f03060907 81
    0x20f104840350707410004440c0d99852800d900f002244070400d095548006000325000c100c2a0700c12084d00c90a990400c800d02000340560704440f4010006040005090701d880c0340350081c5002048075510490003036042c280c0040200b03900d0803421320f40d401d00c035002144143e4055128031680390301c0380b42c40e80248000d0600c02000f40c02042c68158150180d20850380e50034205080182da422881d501040a0599968a04000b0420b82001c003048890740501c810b100002449800760b1248420590051031414080d40100320041100c407111039050754075002d10b800c121909803041c00040c4035280240241c00041500700154410003824000580801100c0b01c58400140c420781d83c250f040343c00d00c51000c81b0140010307481c0c468885001055160300004000401801095000803100f4400c0c03120227402c604e02c41030742915000c4440740d40000e030040000d2126842500a1030308280c034202510050303421604d07402d045500001400004040001c01d100c0281015031100c0d50001423031600f0480700c00c003440071 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 226340242 1250 226338992 226339007
    0x60806100801050114040314070305161d06040e010e0d030c0906021c0203040f15030b09070815060d020f1305090403050d0c03060909050c041415060d11030103050703050616 76
    0x1c2d14100b00c0c806400c04425170b05c1401302c5016607002041040c400c82c00700280c0c0c0c3d458026010458a50040d000803070350400c100201c00c02038900451007000350003940e45212080c50300041160340e02c03e03164486c11301454005e100fa0402d01304000081e103401c40e854003015050322000d0700361004224103c6020401c1960210768450200400024980300300d030030704803c03841e40c029078200903c5030080316400180c049010545281c02c018940f810b000b5510000c08010402c00101c0c6d01078046840c0e040050a001c0c1c1034070018503800d00c0242050b04000c0d040ca03440b0100e810032150500f404000150700340720849640c0507900200340403140c101c05031409580040c2103004900388130110075110154450664080d4000d08090201ca041c10001d51986040096969040748566070055240c145d540190b086020b800502ca048220900107114805d0b80a0000e980d11000381c20409030786d1145030201044800300110b00850161004240c102e046040031800c0ca58050500c032200507140e010500040c0d008082c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 226341492 1250 226340242 226340249
    0x6150d0236070e011125090606051206060a02010603150e0c0301060501021c09030f03031a03070305071806091401060f020303130609110d0c060e061c0213080105070801060806100801 80
    0x240100c0a0b0601902c0d64a4609000c00078008035040200c2c401034500b1000c51801207411f1420b0921503a9543c140541e01441070b07006d1074140384400c00c0020500d04040d8014400e40d107491000142090703480e25462a80c0181044440c0d0242c0c958110b070302505070400a03c00301140441c000c0140d5864000043d40d520784000c1d11203d140c410301c0744c4041c0b45020b440c08000540d0040b0304206200e96a240060081c001c0c00303202072a18103220083e8040f0b00380000c400040d640c0c0b043c001c00b003003400c0c0401400701040006080c150b0503221413000c100c0455a02824071a10010210802194184040130f00b050700fa108107030b41154018400c001a8031070701141c000003e03800c8400040c4401e81803e10040220100c041950060361060210781041071021205080303c41c540e0300e070700c1d074031030302008110a600c1594844000040784c0501c0d0060b0311256801014852404441e52140710b80d141d1149007505c0044030a000440c0000004011150308203614942c0120201d520741d100020b40800600101010f00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 226342742 1250 226341492 226341497
    0x16090203060f031b630c0d0609060305010b030c060a080a11090306100314070501081816030317060d0f060e2404110306040506150d0236070e01 63
    0x6015080d4240407001001d101200e40e81c4440360800350170141c0303e046600c3c40c2c054095000d03143e08042c6141c0d40c000d01240c01580948000d400c0d160070541810507008510408440790f83c48100041400440c464500218400c80021814400c090b08040c20300250641036030050b0420403100d00c006a1100c01c03590300005034140000c00b1a4019100009d6008100b4404d8042c41100309001c280d070400b03010f040071030307205003040000003046164031a02c5a0051148601160712100450441c01488425641d01008330782120013580194215094072078032741c1d20079804218000d0001150030410700c0d010380d00850944028540407007944d40e598103600d50700303009440706940d004000b45c4000c0901050340150905141c0e04070240c0842880c540b01002507508440752513308d49003484600b000700710244695044005880550703500e9001010300c0304d2000500c0d0f44960000351110050f51061680c03941c51413480c81030001c1602c0b09030150358200c069181100300c1442d490070003100a6003d40c3c2103084103405e2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 226343992 1250 226342742 226342759
    0x111206070504090c022e05180a02090a0b0907090e0603010501051f020a021509030106050f1c1a010303110c010e03060601050a03060503030703030905100612120216090203060f031b 79
    0x3e10106e00f041481c203040c514148010000320120090302c01200140c413038441c3d041010b51202c09007620464100590350909030401c502c0f8201619150400580c01030000401240e921420b40000e1004002102d8940c0800c07140d04091040c1361403a25004e51201080c3c0080003113506220004001980a000030307010f0420454040020b00d00c2481105c5120b64007426403904045542a40b5085800000044e0700035071900d030001800d85081043c1410196010f0006010102011840c000444003d030080c0e60482d0503402101041013200640f42c000c6000741e6448881d107905012840c184426158101e0400c0032002103003c0d507580100d107280d04803a090030310f1650ba031001001500500f202e588a03d50501000c121001415010b82110316003520a006807040344200d00c0c0e0407412141180104030141d081100b02c0c030f00140c181801d249454090340100c41c44020180c0040f840d8240e030340c0102541c59004018003045041ca00c4041c0130042040b00070b08000c548015441c41c10562526600c2c0c420f020380c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 226345242 1250 226343992 226344011
    0x5280c03121101060311040b0604030c03060c050403140c100c1709030f0102040b070b0f0405030306061b0a0318090204141c080f041d040201020c01080405030d0911120607050409 78
    0x2da590100120708500c000d00480d030f03580c00c0c030020b14914410041c0c000c0f4184551000640b5045003268203403540441240044d41c25074940310020150000c2803424024108800b00200d207110f01c402c40080c0c0103c00901c000c00d095014040304079010350340c08081c007400c0303400b800001320600806854001c402000d20b49490b00500000e1034480c0c21070700d86005501c001000b04d068024800105045402181641c8041e100c481544003408400c03900a06a504180046100b80c80e10000401d5900080e1752040e02d03000c0009141410b0249880b0100c02013440c00309440b00c0d4420306d2510030003d080d01c40702141410301c1c0003800304000400d090b000d4411080f00360391209e101c3c0fa54120706c04003500a41c2890311a5504410880700798014094400000742c00d411000000181a050324416076043e40500301022180e001581d21400c00f40048074140000c0c401d11141d105d40e032040d220b1a42c0200703945e110403180710b01404447c0d8607141200d01903070440010008000d402000b02d8045488064002544568 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 226346492 1250 226345242 226345247
    0x305070b072001020714030901090303050705030f030a020703080f101412070b0a03060503190308040f0b07022401050a03020108100b040b0309100b090a0b040212010305280c0312 78
    0x80001c5542c104401c080d003038074004150b010303144041c401d10000d041c02c8403c0b48001d40d680110120b540c001007510006100082c4100040c01d0b2440c80ba0f4100c84c184640c1611801994000302c9041c0e140540c0400c18005160380014116041007080141400c1c0d03042218802e0035000c1c2c0c2c3d000340304044248040036481521440007401031400704000781d404041c0c440a1110050740b1030151400061709120002c00c0619001c184071000300c4030207071190500400c80e513098a842c00010016200003400c0450340b400300f0628103842d841809039901a003101002a008070403000c44488121404914a50040c0007503211190310b4030560760242094002c5036911410101400240d405c41c01200601280c00115106040080c60150031003500707461080300d804c80c8100490754201051940130700600c0109940d000f040e8400491000050000340c5400b86030581c17810f200d2001c4c0e00840309540b0440600c25503c090418507101c4036401210054060302c60b8481c11114034450001a004402030105525041d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 226347742 1250 226346492 226346507
    0x6040b13021207110c0a061d04060b130e060d14100207050a1103060f16030e190c0f080a390e010603110d0b03030421061104030305070b07 61
    0x680d040380c15595a000e00001d41800181510b03542c010801514201410080106650403030040103032104039014039007182202e08200380c108081034808542c41c0151143c5440c0250ba0241040e0350280303175030340c00074900000e80b040241d002001a1070a00d050010595074a07400a06203500011914290300364100b09900b802482500881007030310006014042220101ea502c410f54003900c0e03054840c980803004c0c581c03150012140b500c000502000001c8404a00c042440c02083c1c45240001c0d625004d80c10035898030342030885410164140c9602c0302c0030440d00440c80300140541d01e00900c00c19241c01c814507607a515980c070003000d421048240d030030701e1851801402d40c0c1c980304810b036440c0ca5543e401242c11900301401149200740200300003082c0240240145000600003810305032400360b00c40001c6001f0038201c1622507050000300000030704001031030b24031800c0e024030346020103146900780b41042c00c450801807c400c0040007440100b001c42d03040800c1d281d115420415888032507503170b20f1040f0b8160 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 226348992 1250 226347742 226347769
    0x5070f02060a021e0f060f0403020a12020c13061a07020a030605070315090e12030709121412210f041b09060602030d06051537260f06040b 61
    0x413003908201c1c01301000058003c03400056942030b02c0b601d490701d04440b9080b210444002e00503030b01c07100f031190000d544603c0c8121049101c3c030555200c000d0318030000310780050454083e00350b00d40300c0c40244001080c095400343c1403284d402d661450030082d54085000d5200b03034031010b841e080c0d8031400201d2142c06070708000c158080a06503001040d448425032802480d000411400502c641e0117900365207031b045400c490041d00301c3d466440071246061141100e01a200000700ea4004000300b59842038003003008030481003a0000d2800b0348030051411400c1d00181d4110300c20f0007031300241303007840900310341c1d1207085400035008040e0301c2480c00246050f040c80c12040d480400c500c0e2030000d00040341c0754048082d02801d61000301c20f0190565640070051104948546510041410007140810307140c0d014480728021000d2071401221116480c1c22040d26944990400c045001100c1e449031504480350310b403140c0c004545100003c0d08112110443d0f030301000300010f00581c5d850302808001c3c2e40e00c5280c00c090 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 226350242 1250 226348992 226349023
    0x308180106030507030f1e0c050409020f06030a0501060f020a1101032d020405040e03120a02090109090e0304030b07021c030b010c15090203010506030307081c180302070e0705070f02060a02 83
    0x202c3c5d40d02c0c0b4101030400f45070341003580c4140a20310001656111a6075030010300e0f4102540844017402d110800c8000c1c480d242040340d04c031313070418100f80d0580c0b14200a180300311815000024150b141c00d402401c1c0742c0d071400b221400c64000e00404c50004200c0d40082d03200441c00c0c82e00060007040c11b1034101550402d030260010300c0070200b01c0310320700b0350f9560014416110180e605016800356005075176564007520700a103090492a170000340800302103034003178198098140b415408541d5a18054400c5852130303000c88440e5000010107100307020360170070440d8200340319200510a00d00c030044245040f41c4904448810075488103002c0c00580c0c4504103203201d032900a07060150704000041c05a0007003880c06402c074029400c00002428034a008815140c001e9002a466450480e20b40d041c0c03014210450300c402030030f60b500c900710f840d54103240140054540c841c1e001000c0d0281000254070070048014000c20070001c00b000400d00107000380c0321520800d58141c0d001a01c5500100f0168180302415040240303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 226351492 1250 226350242 226350253
    0xc0c0503071506090b010c0204020918010e06090c07020f100915020609071205030304141f14063c030f0d030c0e090408130512071a0703081801060305 66
    0x602900c82c603801040c14695008010300c41d6070b03414103001d6031400e141316800b140c01004194054149a0020035031041700920308100140100130041500314280c009126600700c8008010b02800d02113626a00b01e034801480703074106841940081c100e00100c004c068045c80e030881c04803602d80e001c0ca071268054650f0086061058040180007035807403004446c04c907000d20030608002003403030310304406458403500140a949580d485440344150076a04980f0b5440341c0c41404642d041500589102e0180040080f5021800b2031743c0c51a2194051401b5043c9132085c844903200080c031400b541d5941200061640ca030080d8050484503405a218910300d116415000b11107400f40e61240119520058650342e031001c00000102038000c962071812065800c0e0050300c0c0c0c00108000c07656100c003034602c90a841050102e0561140041103650080f1410729443d40d010140c1840074141201901d03a40072841d003501030808030b80e074070002c259820150070900c038a1400900008244400e400c02c2d0f02560b0400304559 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 226352742 1250 226351492 226351507
    0x30c08040c120f150e19030e1009030506010b0324060a0c020d050d020601080610050d021c1205030115021212060a03080415080a020903070306020f071502071101050c0601090c0c0503 80
    0x1070182c564143c412105d4011914802c0c48500c61034000c0780825050307500c200c14510700b05c0c1806140301e2028010f10074031155200c0080021001c1110034040c14042d0b06042e101d0070640c04d15940c80c036003141c0d41c10300714464052216141d160325040d18402c3c040ca103040d0b00308c00500c0c00818076400480001a016016400005c8141500050000d04960a0504035816980e81e0282c2850150030390090f1584201d01402000240c0345c40448101071500480c4281d0220309950346010001c1031091145022a0000c401084480052100701c2014601c030b00252000e60382141101c1060300c181070725009840054804148651107058501020b19030004d031349652152213140305505a40386070020000a20100d000030794540030b5000b42d0700701c000058002c10f003050559541030040e410990958030210010300c900000724550740000094444041d40040e5140d007030341440f410504402903624144842044156a060b0000031154110b440100000680d5119450100d0703400381c08480c068160b00c404580b02 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 226353992 1250 226352742 226352783
    0x60901080a0b060f070605070e1e010f03060803031003060e0c0d083010121509080d06060c020306130f140c0402070305131e0b0310091407030c08040c120f 68
    0x9028603623684039800a401c5a00412502854801088000307241c81201d200036940a1240b00840140c01e04010440350b48650341140366400c110740c14580c42c0d001040400c240862803140e8110b044184024044882e138420204181c6240c40e88014010100003070014140400441c0a4054680350b56461440d40c100c0f04090000800545a07481c107400321010000f0019060700c2d080c1e0072164403025001d54014200c20b048020540704200380d6990b0301c04c100007501002944603082c060310958031242040ba000d40181032801000425901040e0f00d48050b40d03012901072001030b88241c0c0d00000c010b800394030791076020b42060303050002c05402c5400400c01404254021014290310a00743d0401026290384503241c4501c0820300f540220540c0c12020103211668015008641c0b00d0060503200780c0c0540d03114003920481d1a01c1c610051010205002d00124650601400d4000c103242c0c540486141404c1e21000c80c1050103201e1058042c2d20511840c00304504c40702000300d042c0c1c02a00740d050402c420b9511 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 226355242 1250 226353992 226354001
    0x1a0f041a0318031903050403030b04050106050c070807140607110301063002060d09030e100203071509030e040b0d350c06070309140115060905060901080a0b060f0706 73
    0x41d29090140b44040362040c01c40001030314080d0701100e003118000e500d41c15041d002070001400607010103417112194081d0703407100d006060090085903280c0366503c1c50401c119003406d01031382100d00e0903081200100a050751040000682e807004440340c40da10519407410322620042d010444e5015400c142002070004000300c0d0403880c0404910000101003002c8907408006455014000d500035000d10a002c00c4410035070000310350307c4c032904203000044100b90000711400c1e2008070389801030b400011070b8002c11038000041c51098503440c2c030920100e00e899801900c0518801ca03642e0040c2d80c0d4050701060b0390380b0010000c0319540c110454030407849420654021074001c1003051604203100a112041040b120b00842c3d41c03030b501d06805043c1c9512091011005040599000d440901e0403228803143c1080078400d5481a042d8800344844449c50f000b00680000190340c415489000240f20720103050341c0046020341e01c52030881d00000d504032440005143c45c0100054090380d101c01140328410002d076580f0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 226356492 1250 226355242 226355251
    0x7050d08061302161b0b0705010903270b0d020d09230c0f060c070503031c050f091e1c08010504060906080a080304030e060309160e011a0f041a03 64
    0x7040380102c1035a80d4050240c0c071901e840d15151880107030400c000314040c1071010f43d81c078800d40c140d040115030311440c0a0464100d0304082d44d0995440980d242090740140d603100001000c400e1135003100740c80b9001e81407650385c58414841200c4000840c5540d070155641200c0040900031000c112190590500680050380d02e100406041d00220b0721181c0501d000614410342d940003804e000c0c0450340003060021a1b00064601da1951003000b0340880c55075001c3c800f510381d035031042100803585040c4501400c281e03080944066032200713054041c82404c84002c22005288078451300c0340b24000d0010300c40c0d01e1a00d6042c51404524030304511404031200e9100382080c0c100c5000301d80502c0701c542c440450340102c0b01c0c544030381c2000c0c3e4007003c0d408001880580145501c14020304000d0401c003491804502140d100300c170300d159190400c9502d200101310740034407000604514130b07282d8855810318101c051384185c001c145680300310000c0303841035a203c85403007140c0151110241c0040154109000d01c0d03615007054a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 226357742 1250 226356492 226356499
    0x4170c090a0209031902040b090718140105030c0a142703030a0e13020f040b030a1803020d1d031507080c0f0901030c110715111c0e0607050d0806 64
    0x40c046460140c080c001d03030b400100c008028040001090182560403d44100c08a800c2511035a0403202503803002d040e035109204a4503603489058130341302118030320810350b00959041d08002c5130344c5540d80d074040c00380d83d8004c81c0544081d9032000c4003e800e89498144d580c1406801c28001030100e40522040c001c0c041071184d5142c1641c0d007581810405880740180d041440c0016000f44840e02d80c0d14144000b5010402da1120040c07a00e2007260120303c90741e21035007000f281d80c98000240514850b03180302e0590040c40000c141000100d607650b000b034030352005280d000d041002400198201038000301c9581050940107045841070003aa002c07444441801304c3e070b603c0c0030030010800288500305603c00c4440030310715100c03240e141c07a0402d8015001410000b040104002d500e050180705858104081d10290a10300078503220b003a686540100141c1a00c050f141c52500541000e0782c0e06c00620700c11000100d69070504440e01e80c8036001154147c00350540240491141d8041064802c3d000a160360142c0f0064 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 226358992 1250 226357742 226357759
    0x50102090a0e010302091f0f0f1503020702011e050409050906060102120a0f0f050403050a0b0f07090b0d0209060c060a061805040308151c0305030a06092304060204170c 74
    0x809602da982c4109100103904420200c00040314005d43c0c0034203024801004400c1c00b407054035000340040d00b46e0150054103518110a41c2408001c2d8034504150b041d401d5403800b5440d1080340da000801000110f00100c00384920046070b48042e900a40c00c1e40c6c00341180403000c00061a2849401e5507500e130903140e0602600490051050300d440000440d100040691100d022110491104440c2a1245c50b01e410800106000200010300c090280d48626809640c4142c11814011641c8060359030181098050005c001d0b010480941c01100743c82d0701000c590b0b0016121100600800c0301c43c412121084014010301d420400c1814240e03200e035069685561141907840441e0040004440b81950b02402140380b02c5d0019814102c0e925602010030000b5080141c50580d030041c00003041603c0b6400c4000c14000720070403100c0101ca100e20001000400700900c0800036a9010000c2d8910000000c0d03c07104032040007409001d42a0100c030001c028013003004a400b0f03010741000340c03200306075410795110ba03016 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 226360242 1250 226358992 226358999
    0x20703031401060804030c030f2f0f032502061b100b010c0b0402092802041418040b1506030a02071e0c0b0a0212030c19050a0203030c091903050102090a 67
    0x100130041c0f2890341900c030214569507980341940c08100300403004007000741e085d0074601004445003d60381e02c580100d900440c085400e40b10641400700740f407140e02d044c0c0d1060284600b201041c01c2c400e00c00c1040150700c44404121400418001d11960522140308400c80e000f80c1c12012001440041c3c0310321101d0100000e4500c1c200441d050030b80200007415070610180414090b1800d48001ca8007c00c01d42541d180101c41001811000c0d650740001d50b90080d80420100041c6501c800c140e042030400712809180c40c00c0800c4241007a43d005400034082882250002d07155501520000414950080000c0c1e20b030300c0c002e130060b001303540b083c0401c880b10484a5592480050801c0036031288070b612405490705103052000310384068000c1c03501c5204603c03a0b41d030b18a07440da22100c020b5004924550403240d41c1c5110503a082c9a05600f906030900b0804100312a102e403d40c0401030342d0700315905c00b2030281d40307460710400910900e0800d000c680000d20040000410814150300400c0d2207941542c030000f246a8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 226361492 1250 226360242 226360247
    0xa0c031803020607080c030d090606050f01020f0703140a1b05130b0f060918040c031703011404050403030e060f1005060c120a1701140a09060510030b04060902070303140106 76
    0x50300e100007900400b0911002c00020201c070060100610031130222402d1004000c4034400740c0d0114a0160313041c5542d030800340518101050b58064854080c00180759005a032070700c40d07942d2282480003038041e561410b4117074008442440a65075245e00140d00580400b14004041c0b03c80d240ca1041c24818007141d40711140e408083e026020146200030b02c1e401500c1c00140501c8025803107086120344c481c601c600c0303e421009450481600071402000700580c0c00342503103000c1c01c144280c00c404d162482014001040407413902e250000c441e10041d100869546c44501d000d60140c000fa884906d0745004100801c400e1000e5400741c03901c08c0c01c160ae20b10209550352420310045201da0381c004015030300080008508207140c0e200605c580c180360300d030003c95001c0c1400c04450140b03080e004038409038541100c011041c0342034600000a0106410b00304001850b000c0080d10070300c06800308505154603403c03140440e0752907600031401410b1160055681c0c4040e8a802030003000100b400381c848005c1d0030000701c3c69a1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 226362742 1250 226361492 226361537
    0x27210903020315040618050f0d0201152c010618060e010504051903020406030507060201050c1603080402031515130b0904031407051207031d0a090c0905060a0c03 71
    0x980142c094005041002040b41d4900c02c010404e4402d1902c941e00c81491890040010b90325038000c1000d007000e6020b15125071700b011714265944c41160f040070111883c03c0c80e109207803001c0711642483c0c01e030304c170242543d661060f02030701500f848040d0030000000f88003500040c8642103480383c1e90303101003c2526410182e40c0361800b00e101d0350000d02c0c1407009001c181049072a2046980064031205035440d0340c1d44c00142528116001100c058106201c2001429024000c1c940c0021aa48045041a5015406900407540e5100c0541008000c83c085025520280001400007202980042140c90081003144d014000d603e4064011824018043c0c4075603854403c0292491004110203e5134030760b5102142c201045100b1000070030700c00c005000004004014500008482c002601d450315100d09015000c6541d004424510b0346030050070381381d0b90342c40f0643d40c01614456100080d40307004891003140c00108a420640d04110001040b1070101d4020074402a51846960344030038007010781c4c2c040403120 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 226363992 1250 226362742 226362749
    0x15040b01060e220e0c030a03091a070b270d03050603100509060703020c0313030f0201080901020a020601052106150901060f0c030e060f0a090e07090506030604272109 73
    0x9902090300c03c201e8125007002034041501030440f0004444040040d08150b4020800c8012406c0494100540140003d103100b00030303c2c022605040110940341e00e81d102d5070050070081e24110301d0030040c030703c800003c0240d141d8030078100c1141e403c0c0d810114050000c203001d40300c20b4800e204030085500c1c0509280603007886903e2020140a0b01e03140c181c1c09078040c0d0040d4984e091035000921480034002d2800c024031004500078450803030404500d000141800354040e1005010b070340108981901c46400003103d0341110b60603500929002014814151b40c010031110805103030180405210100c2c40300582d0016510041b0b915150690b66000d040d2031740728920300072001240c81500d00c20b001c2401038020702005d840107841d041c40d2280304c401100f501e6111000c240c5c0490942c520a02140803040078041c2d00c8001d9041c490042c50400000401da400002d0aa51007242c5038001d80c0d048445100d00041c4810709501103450f0a0b2140c608449190700c00742c40e801d1008101e200b40294588280c590100b00c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 226365242 1250 226363992 226364029
    0x180f030f1603050408060408040f0603090206180f0a0306060302040506040606022814010903020106061b060b040f050c0307030c031e020307020c060c07030c0e0402010801120515040b01060e 83
    0x141140440741e444100c541000603024010284400100b51100f8443d240c4128131402d6031542e60b13410101c441a1107034440e040039040500d0400088016180c000c1150900041004803500003c0003000207201c87c42284402034000c880340000000f005840c1d0007000589100320350503c11555410140804c5903107074803c4100680c0103a1000c0000d40c04607a11140108000c4480c800c07000c1c85490b401948001c8000d59503c5a641d070210f8003d159080c45040040d080034070340070300300f694840b40d04041d803011460060410303503542c030900304656907513802140d4112040d2000c1c01545005c1c14620301a40040700c410340840d04000c13031032044c0f9200384207030080e009081012900c992560003100d00250001004501944180c03102004203565410140c200b0740d002a006260041c154908507000e000294003c0c40e80000310b40030302c40141e800501d11815503890b641c8041e0310300c43c1410600e103050018180c44100d08940d8040c08140611844028107951650300d0340202c5e0b224071004c0c403501d90100d582c2c0089 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 226366492 1250 226365242 226365247
    0x31009021e060313080c03030103030816170601180e070507020a090204030f0b06040209042406020303010e010b1e04061701060503090c060a0320030103110d08070206070303060e180f030f 82
    0x80d940c0d107868514100c40c0945c603030764100142c0c0b420341850b50b4000e800607004104010f0401c0443c0c0d18215804150710702a00c0c4c81236808045840080304014060303c2c55050244d40c0d40e0003503105100c03c0924005281038010300c0018140184003900b1540454002d81c0a404507410100d2049404c1c000c42d41100d034482103010003142a0380303c20307031017000140101d035105808019604c0b4590343c1e8001d0300a200040d00c010072005042180b06509041c030381e403043c0d0941d0800d03c01000202c03028418681104c41e1100c00907038400090116040e819403488180b603460501080101e8502c0d440214154098861008041d1503600da543c107548a01080f2009440742e030000340c60f448181800d9015004202903030a0218500700c0b0701070700f00006040841c68001c0040080b00400c2840303500041c9400500b000e554a00d0700341100e4860780164071412101074000d0000280c42800c062180d0b00500040018495104a46c10308400103080d08080c1c280440c0d45120358185924800c44c040100c034109410000c2891 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 226367742 1250 226366492 226366501
    0x2010503040609120e030c03150408031f090504020301110c0c01140c0106141e031515090408070b07020c061b0114040f0309080a03090603020d0b031009021e0603 71
    0x115a940024002c46125449001d4440001c5a031006400c24111503219119204501414145000200c00141d842517100f0a80600c0040400352241c5d045500a03122a60781c0d564188145100500d04048a0b141004d08000042410803640110701452086001313208001c500880b0030034500a03412120b05d16081400040c5140d03000e107180b03100035929800305500303022490081e00c1c00c5500c2c590101540c040e1440c0300881d6480e200021182c2e0440085980ba0014030920110750382d4030070241c10306d840c10701800100b01003440c2107002d40e540c86030003442c00000345414904105075401403a41200d0641040c40401c1e22035001061304c1c054414043c0c14203050020075021060703012240d05c600c0d04903560324046000d20750b4100d103800348514014003c07074029000c4c80c90024135a000c540d002681a41058a000c0c0010b580b2000c0704040f1912481c0150711500303130004c11001415140302599041c4911003101c46400f0240d048154058001c40b0b041c1440c4a159101d055000c007051a0103a00c00710400004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 226368992 1250 226367742 226367747
    0x30506040c05090c220b041805060d030f0c0501020d0c200609100c0306030503030a1508070605030c0c010e060907080729030714030c0702100509010e100203090310150f030506040201 80
    0x1500e01014040c141680c0799146c1c000e0003a64000d030007040100341a110440c614201030b0054a410000560b2403580015490710000e04c03e05c031190403542041080c102d14010301c0401d4041d0b900b156a42e040130040c00b1003405001d8400000100ea001a100c03c00c0800005c1e07110201e900361245c40ba4a000d005aa400e4001902c018005002c840c001d040c2e8601011002c92030400c05075204030084500040d8003040103510340740c0095103a1103002d0a5022180034452103078410283d0ba0003449615145480340118150b15003d0000394190568900c603000401c200e11a0000d02401120125000e4401c0142ca507010442c0a2035030782a410310b00c0d80f08070950021400d588004640c000007510f09a03145a8070880107203061750040d1802c501e000c80c041951000c2d4500b000c1c44402460081c204140b401010f40c0000e045a00c24004c030f81e1055014800318064140240700b00e9881940c01001c0d02d060355089211078000349102001d807240541c1044010608030505c5045d1025260004024645607440c2e5004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 226370242 1250 226368992 226369027
    0x60a0902041d0901090308060f031e011505090106090513180b10080c0105190e0603150103050105043b0f01020424120e0304090e030702241606110301030506040c05090c 74
    0x1654061044bc1512100d01d120181c2c1001c442c0c43c00000800d61210a01c10301180c031210f5044144070360040300041200c5500148050700b11201584d400f034241914204110080c07c10700508081080c090071100100080b81100501c5000d241c0380007464a521003088a0f543c4008044a60220f0420003c070740f11407070a042265504081c070300c1c14041408102000c07840c503420941e8443e40c2002c01c4c9403441c030250b81601a05000d8007080d5020010109240210341100e80c00a000030f0181e12443c42031003e9040001d140e01c0c0c2d0214640880f26448484d14626000394020300c524a496035201e0309008195010002140114032203a444410f00c102c1031440c0c50040c0182050f0805503c0304020020b00c10400d0f02400c0790410401015548580301801401030a078031138205120032203407505281080524003c1580c0c2c1c039050203413845107124803a25142008022455080110003400700c0000104400003c1c0c084c0701e1803140203d014070039a50070178850459070607101603264840a000d0b004000f0351041c3c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 226371492 1250 226370242 226370269
    0x5010501021911120a0308010b131205010f0612060b03060f070f1119060f0e100b0a030b090c010f1103031803070b01030b0702010b2403060a0902041d090109030806 72
    0xc0895148103003c00103011074140c02500d04160045420f034018150403e251500400798940501d10b0000707005260401c0380da59019805403000c0d0300d40c03180144002503000b00d007083c40c0d880c3d0800c0350315100d9003030a00b05e03044000b04827549420202c22450310300380442c005008001c00305c500072158444540c25502580700003107800c00c10a40d19142c18546408105111024585240b50000d030720f080d09000003943d64200308400024288920303d04403140001d2203c40499a5031400a854480940004e10030300031903002800c1032420206001c114400031410b4245120240c03102180400c2100c0305031413081d5441079a000c01c2e00b003032000902c200c01e2011001c00e00d94601c0c095902d044010394442d09015002c0c1c00964a031500c0f401000704e22502441215960fa100715404064180215414119512030078500e0900b040048045051361316111803c5011304030101041d51504e403540002c007140301684522100c4004c2c10701c0801c0c80c560040c031501c8103c98155542d142259992000e11411502918 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 226372742 1250 226371492 226371503
    0x190207080f070b2d0706020d0b09060d030531090c0f0c1b1e050102120903120a1b0311060109060503150403022a10031521020d08070303050a050105010219 68
    0x6244190300c4d00b0180c001c14010340b10312001a00c038003041380300c2c408403101c021405008031018000c1c8040740d6200c5425081d540d5040c9865907582806030590907a03002e1028400d40c0d0885c1050316200d07007140c5400c1c4801524820714040140b440090340803990a0900103401010074420442580400d400e40c42002220450000240185a989520071808207803035421100491749444240311669051010020b00c06a131a109030512020030000b0b0f0f01c0b1080c402160300040400504d00c2c1d0401e01401100c14108200140c405500c1528200504500e11509030340344180a803100100e007009481c410032007901c4010700103150105507584940c00f202c1e0054030950540c414501503801c52021007a241d254100d04096030a003481542c4240098540c09005400501d030034001c24128203101a60001c0450b40035080d1104158045888407101102008001c0d4001d42844041e0303040c46403a0000f0308440d4880d030f504100a50381d030512002255000c1c02100d006800003400d018850b1078410100010a0291 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 226373992 1250 226372742 226372807
    0x11d250b07120513121202120a0c0f0227060d08040e0a0b040e0102120a05070f0804030e0a0b12090a0506061311030a061e03051f02190207080f070b 65
    0x5404c00020403545038000076004a000e04400200824115035061701003540c002000c9000044070a0125401000d4120042017a407101100034030003c00140c1003800e4003c0c000811119010f0210003103406901c00e4800081285800b0840e58108281c40348107854120300384c182001d0418a010314020005068010103d80711a01102c040da5103114881ccc1c0c20081000042ea110030f01d01c2c181c22030b00402410810701c2c9280c40104103046e50000c00700c854a06851400341d40d10f517034510b401e4031602d0001ca4035a8100d0070508000c900410344074001c140ca0001030380e8401850740c0342c00b403266586080840042190b0040f00105050381401c030706052404c442c07001c0110390000c901654070f410b03820071102c0c0d1580340d0b241c40d070070000c0d405071a2944400034000c14194014030b0454a407030f9540d100703140403c1039000c070361403044100342559816109001c40c1c00b160030402548401e0025a1110240100c02c0e150092411006a0540010700001110b125015136030401009070741da0000c03501604046401505103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 226375242 1250 226373992 226374007
    0xc030c0305120106050408070605030402330a03020909010e1303030209030c1302040905010b0f031b0903010c030b010f020a0b0609061801030501021210030320011d250b071205 77
    0x4000b02c441c080e190941d10070703450b00c0c40c0066403441c11145601080900c00304006101c0542c4504a54001d02c8041624004405e0b2103041e0185a51001d03e0035410329a40200750401341030f9150300100f0340c4c0c1e40e0460b010422641c860b0814040c00d00b069803007c50f004140d20282001074042c1d00948011140101540d07600d540300c10115401403c034408400c0b1050340010144800e45040c4101c5002d0007541d91400c1c10300c01c2040504646d444040c0c40109c450000c0007030703c3c0400b080c2404449480002600074405000d602d84050040c200341c44070035002c21143c4528401e103d10026202d118960041440c4007551116014441e4846000d0a180c0e040088405080083c460904502c1d00862040d0b00040c1d982d600c0640340500a40094510350500c2d01a020030004a50302c62803001150000c4141c10142c064042200c0340180305806181c44030b020740d803125a0320034070041803841e2000301e1540304d14100c9601241c1d04031140224002d81c03401a505120040104410764001c0622000a05180e8680f0030f0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 226376492 1250 226375242 226375267
    0xb1905093007081c110312100b0c0303060108010e0603250305061e060d080409052a0d14040506010b070602040e0c07060b030c0307090e0c060a080f1302010c030c0305 73
    0x181c1e803c0b40c1040e41c0810b190341c00c01d03000c0c01094049428140350078900c2008007a07280307440340b01c0e481a007455840c1301400304603120401c206920080041d150119501d2a00c000c110781c4941045404502050071040001a50074041c0f0342280714000043c003411040c60703c3c0f5582d4100d102000d0700da040c0206001c1d0084009142001120701454202c100034014010300b5800f40441e07840244010302440f20071b0b0000d00001c1e10360080c0c03810f886941a01203019541d1200c14940e00a0104070410000d0407400c0003504030041c80001c0202182801c000d10044508509040311880252001002544141d00400015408101804030944149400741c6016511981c0301c404500c29505614080b42c005800c0b01004403501c20030040d22426005080b00d030702c80c040000d444003045d2040030901c40c1c44401c1510820000e00c5085402e00c0000d040907162881400001d11502e41106e0b20b01052542c3c2010612802605440f4103005905a40e0041c0e41c0032641d030111245101544224180704062140444581 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 226377742 1250 226376492 226376503
    0xb160b040606150203040f060e0102030c1e0d09030b06060a0c06020414131a06090109050310060905010f0f03111309050a06050a060807090903090b03010b19050930 72
    0xa0081c400411103030306002051802252412590003594401c102c204450110410018100c0304142804050310805c640140c1c294800c144003e9190f0082607004440100c0c00901c025802030700000b00c407042c103000c4000703980c1c04160780000390a0108410004a5500e4403d00901001c1708074600315104107403503601c0710103a03000342e00038000c42a0075020040440c10920b00c0300c00c480c0341094080c48901904000001c02c4031010403907034000d020020b0030b8031580c0d00030000301c0000c08000e0221640040c51121001c010483c500540345494201000013807440c2c09540e1403401d8458842c10302c06401e19581c2c80d001800c1320208000c3c1c10040321103c806044202c3c1c483d8010141c080d41c0a80301e000310034548082203c2c401000441e41178034226080c804840000f581f04140c501c1d2040c0003880c6002824252004a440d0744449100040000089001e0001001901100008141e010803030300000d08203a0f21402091038440e0061a0804583c0040c54a07402034000014002d411962682c11a09020f0510 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 226378992 1250 226377742 226377751
    0x40e0a140108070503060f060f0108150307030602042d060e180a02180109060c0b0604020705030c0f0f030a0e0d02150a0c0201080108070308040e0405150106030f0c08040206040b160b 80
    0x140c00580c3c1c100441d04091107820f5000040c40f600d207989151410015100e030000c405414100510a4000341070381034456941c150480700141200c821030740d28036107100654004e0280904040601e103841c40404102505102c08038081d07104004410f08041c41124100c04020019611802407d51000302c80c29500c0d49500600a019000d40d0b250f00541c809051521650401410048048010010ba81d031204400c201c0c1580058400c14a44501001030064026007134090074501002401041d44000010703501048a404000d48842c2060010083d8a900881e0060750100c3d4428041100c2845c00120103091948010002401ca4000d1507a042e0b1a410050345580070840d0070701d10070150740e00401058018828070b801000c3c07290440d5a0001c1601551161040d140d1250340130a04000017401081420714001107609a03c0da51280024054401003000e68803032031402c55021300c075901c5850120f206603006404207250503c0d200e8002c285c1d03841104115401a0484124000541d0000006000d03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 226380242 1250 226378992 226379009
    0xe1b190501091e0b07140c0a030206040909152d050702031605010e0703121b02030c101707080a14070c1709031002090307050d1509140f0f010c03020f040e0a1401 71
    0x1c0c40014030a81c9001f2804454a2155211050400c0142d07203140c1280d00761010a9404102000c446c03812246400380c10000b100b4050800c1c07441c1c1c1e00320f4403110141c0c1d00c0c0441602400c80c0c041520104100311007054403800016001040f110a018144c03130b085c1e030b180074858800081d000c0007000c170650800d280b980041b1180d800c0842401c04d00d50b0701c24140004442138940b42d00a0481c01e5000940d00d92400c10031b18010501400c21a840c1c40c000d0078a60000001c0d42c2048500f880d001c81e0092925408903940c82c4802d1a1030030b240f4104440c018468415110b585520319200003507103d5002c042132021010904020401c00c0c03401c2620180805000e500c881e207800350725418090201810208544c03c402d00903001054020041481502c3d0342c6442110098000750951082c20000c01100800c0131130400c034480d44004400103400014201005a0804020044080519011026407080404000a454080c08148103140c0703045900c81d0481c00c03458001030000044440c4005d41c4000b607001030321 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 226381492 1250 226380242 226380263
    0x17060906060424020105181f020702090702010f05070302070f11030102040803040e1608040f0b061527010e0102070317042607080703030c0f05010e1b190501091e0b07 73
    0x3c03040d0240201c98000c0491400e12150b49103400300c0c1d41c0e0742e83c1c055404094148021800ea01c1c0c1e40384507811500402d8000d800b0b590985411a4003a028188021540103201d01e08000100418801d01c01e9800e0300ba0b001c001c52600c40002d444010031804000e40e02a45035608000c0080d000c04100700800c02071640e40001d16640c94425540b148116403002c01d1000e1285035020000055002118035884079404034150f1180e4070b4650106401c000030825400b00d8550000d00c1c0542c0003d540d0701e260700c030404103d242c1407450014004440d00d10300c051449015901046061000030300e0020704403e04011010354608141d9604001603a0201e0203a0002001002020001080a0500c4160007811102008104240c074554005004107003008002e08004000e403035070802c0200a400810303007501c1450881e01c80505642c000d03100d242c0d402e03645610030001d4000068400c94420303101c40803500d05840708085140f420000f00c480154014040b403402d044214081108901c3e48060f000b01401125610b5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 226382742 1250 226381492 226381559
    0x2120313051608120c070305060f04060b100504050d0203010902100801060f05030907062010060f06020622050a1205211501050c010204030c0308030601080106170609060604 76
    0x141800314610300301d060a000342506103c640300028580a005040c8058640e60303081c03103c515410604140c0006225000e11802c0c0200c011038080c0540c041c0b8003070070040004000c44801c20212500f800607080104009010410145c500509405a0740380050000310b4000000d60026a036600d031110b10f00c010550010050041540c480203401900216042c01481d50504809941d690b50082c0304030003c006505560b0850341e114654284072080945003294108002d0072102c00c05024117000b042100c1ca001c0c1310002d082071000031072a028515000c0400c2c50354400100d500399041081c602a101ca100301101031002583d0100a07070070341041030b500c19403140000d041c0c1c4001d07904640400c02742c00c95020b00780b01541e03505400d29090881e00b400e10f607a6038034105400d1406030240303034406000c5040e8035100109100984004500c0b45000b681d40e20302c0e980e00c0d0304090703445000070f1209148040c04030000030000c0c10b049200d9a08030b90001c0c200c07400d007580e40400f0074009130007810381400fa548031100d15 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 226383992 1250 226382742 226382753
    0x903063603070b090609060430080a0b03010209010801050d0f05030403120e0103060302011b050723040e01111818182806110c01090b161e050304020102120313 70
    0xc1e070004c0b000301c090b020f1800c01c4008180c0d2000e01410140c80103846050150400c030700b20007441508256015095250800e40d60050300720740d401ca40b0b640c2c0303075421301c9400da04615043c404c0342d19081e016124041c45074200414000141d6040000715a0f100307140031201c01040382000030700b00075403195032121101d2940c0c00b0014104000440ca050615041c10b405000503a003201602c8981c50b040025500c4404007400d100b49801400c0d44088800c400a0310341d6a110412000700e150416401c0d03609204040f501c49030079088488990520401003020b100304024010074901510f490400240014020700038070065100045054428038241a0f20034046040440144000003a885e0307c0424034000c0c0c2c01100070300800b40340e03190300140841c1d61406030f069102c2c2c00c081a00d1441a80c4402013048005900d09180719000c15030320400207500380ca0341030311802d03c660204520051059024040c1d240d60203420b031075a410103007080341036008400003012005031000c050340c4581e03520310304a03180e0049428072 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 226385242 1250 226383992 226384013
    0x3220c030314031005060a0e1c050f030301151202071a0a050604061a0a0309050304030506090715020a060b060913050105100305060f100c060203100e0705090306360307 74
    0x360015820306100f00f0210b035480d11828011034006844050b80c1e03105907101220507500e000c810681c0010271222550002da9504684915540301e5002c6642007469510210341d240403d00c101c4008400301800981c1d01d512404580c60710300000f50001d17007403040036a01c039401300c003028441c51219120b0038100f003101100c501826402000640c2c042103402d05007140094a4456403900303c07840d0340c00048002c5e81ca4400c0d8050b010440c1c01c04240d80d2160341300e18003a071325003806484640384c1e88151440070401900c008907298480015800900e010011590340d03201404000200d56445241071020180646a24002503121610003000042c0c0f58180810040281170500070001050b01d8102002116181c10848500c10740782203505a03643e201c40042142e52102104c3d00509150000c42132001251000c4408d506454140c003000446654100d0100da031405015810750349648902e02250908200a04c0f000c0b545803a214061fa8084812a018100d0400507514096035800054114140000c0045 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 226386492 1250 226385242 226385267
    0xe0310050c070c0b070c05090613050406021206100f032703030b010906020a020906040e0c0d2603190f1b05090f0d05150a02070629090c0d0203220c0303 67
    0x71441c0c10110162034000003a4801d0041f28041e1800c8004602da9070f0343c0e2014505082d00c0d5080030700c2540317403500e4064003075080f145034501403080100100b091482c060012003141103d075541d0040d0180140811009844091030440d500740880003104a002c10041c4c103001454000d490105d09240c0d00c00004001f40340592000c0110340242d61500c00607500d42d0304490f0020802c44002c0340010a0786c03000d80c10144014800c0d0741c00784030281603404002e080340c402c2d51a00300314203150030601c1502507103c280780301c21540c92051141120384e20350300400b075074000110100921000a200441c0815422011709903108000100e000490590003601e451862024010420740b4402e6003440725030740d425034070040d0803e142070346005240051441640f56054075201904094240105080511840301801e01d0782e49200c1442d81c60f140801d00d84c107120100764021988a400d2034903100b05402c200f802508041c2545940003407003018048444412105501800d000c0c80031302d950140347d4900a490700004d8034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 226387742 1250 226386492 226386509
    0x91b0e18030a020d21140415020a1b03200307060e010902150a05220504180302210c030304050d11010c09050103090204090605241e010e0310050c070c 66
    0x200301000507901185142140c130b000d0405031a444400100c1c0d422440d00550302e40d001e00d20302020a46680c008000d2240154080c01580d243c42c041d0214404c2a07200b40c0d024440441c00040c0f501c1481040f41148145090003450107032000c9040c68007031000e402400030f08007455800410200c0c00d120350740c0724a540f64424600208889042c0f42d01140e2039045040352041da400d0f004c115160320720b010314200c550401e200d40071003040c1c60180c0c02900f404190741c05141e0095107400110250410b101202c0104070380c068000b000340100c8880080c1c44c1c0c101100030510310502c18000c030300c2c440e03400700301440c05244030b03a000d40310240062100030300c201c540311150395540c1e06142410143c00d8103c8a641c0590b803080c44c0100304817495001113405410491001094a460a001c004030780c5401b81e00031601294611402007102c1503541004118400c0441440314100d60300c841c8112580954044610840045c00b034801c0c0c082c00680070300c12035030100c60181c002d040020300344003000000c184450280c441e04 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 226388992 1250 226387742 226387747
    0x8010203090f070f09020a2a110607031d0d21020118080307140f0a0c111e06090301230103030f0804031b03120c0c020906040203040b0a091b0e1803 65
    0x881100c00501c0da0344608582c0d16070000c3d0385540c45101d025152079005102040329400c1a08c800c0e40b00a40c00e035004140d41a0000c880c40030481e140c00c2080b900019015580c4580f8011002c40c4c05040c881e040e041c9503030103080810454001400c0c0d40c00a00740085c1d5100b1541240350001d00642580e80240d2450721320765009202500150800c400d403038100a89142c000c0c2000d0b01119401014811211819405180400d103034902640c800e106510b00e51145140160b0003840d0310600c98541034022010035407000d803c0322154181004000380042e40b000030008917404030ba9212440760312070320440c03000d20b0310a207000510500d600407020501245071840c03c0546454640c40c020269110841d00e401c2c0742c10741003076440c149442800d00c0440d02002c0034040041070000c07540078000400601c0704900401e203010001b61315281510980c1d20031034101d0790100c0140e8a11002100a01d803e0508031004203c441c1500550032080f41c454000d80300007002c2000a0a140c488459206080076207019150f204 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 226390242 1250 226388992 226388999
    0xf0902030702060708130f051006090b0303040603110717040311060a09120c03200f041407140715020301050915012003040b030c0a1e0e060306040207050708010203090f07 75
    0x3072001d0f0f104c40c40d0f00c2c00d050544c88213100012014009400909210343d00c101c84d800380304000c641007100e0044900c0402c040ea13541e000740d40a4911500c1c62a80c180c109020401809001e90051038810014500b81c9180810503600e101c05c403400707100b140c26080b45c007040a00030003c000390b404601d180b080f01c0241c100b551400d4020b01c03854260048008112043c0c14000c1005400012400610b911006c580c00c1c1d68800120030031007a840d16000f500c0707070610792043d040e9801c1074070071100445152000200a540c500200340d41c02c840305452164407090403c000780c04201081a54000d080100d40b000d43d032940341c041040100315000e06a00d280c00c007407040022807a83c01501c5071000018881800440051108640741103001d41e51261702508030010070003c00c8aa403c0041c506010651a21013500126052482081c080803d030a404140c0450f001410391034030401075688220002c1c400f600e400c0c556562113042600729442050319a40110a01500f80c03400e2041c0e1038804400c4006040d4070f0b00c4d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 226391492 1250 226390242 226390247
    0x4051801030c0308070f0b04080d14010e0103080a23070204050f1e0615030f0103141f020714030712110a030e040e0705031b04060e190e0f0114010f09020307 69
    0x1035034031000341303491070009082007004070b041d851307210164000f55026005d00d400c1c185074806500100d0700700681d40c40c0070018045904481d1000e4140d0b0719000d152081e91313086941d00c0c00307554400d1000c1d1051010078400c81440c0e0156010800325050700309a100d446511038418401600c40141002c9500d00204081043c80c80b00500400400b10003000a42c0142c0c0b20400422120300d5410012032001100000b000b8981c41907200c01c0e81224420364140e00c009848011094450722000f4a091060380c08041c03540603103040e60003402103540950420b0203030304a80d8400c1891503000500c211010508061400000780c0c00203020858030150380003604101344503036002068407140e210092f00c125039034969042988170401426028200181c01c8880c2a01000e101d0500040f0000c1e00c0c1d4815030a00034049004074001106900400070040b41c104e80c11a03042e00540604200203840035144035004101604410034015041200088492001954101540f040c59043c903500401d180074010414442120b9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 226392742 1250 226391492 226391513
    0x5040510030c0e04090501050f010e04030801060c080405061209010617100515030d11010f020a0f0e131503020415050609150c0102040b190807080c0d0b0303040b0405180103 76
    0x245280009842c050040c080c0c4040d101c407240c02e81c02c2131424000b84e0402c07105501c49030040030006e488040741d0ba61140140c40da6042281c004001448070401001128000c158543c3c040740704510090030241c684001c1512030f0040f00429034000c0c20107060001110082c400c440151480c5070013000301c4c5a11203503d03542c4400c0b05140b150311954510010349100c035812601c04142d04010180c0300c9052900c400180520000541c48629502c0e02203038004143c4607208131040e5111507150202c419526240c00e640c0300380519280f07a0015182c9030401400582c6208641a040c051160b5079410303070a5005020850f40f040d8134004090104210602c44c65032000103a0384c50f18004c58000c1200c0b1f0312045e5480250241c40b21000710342d8000304020954241040240c00d9500700c4202826459602070030499895609030740342408145d5540208545004e00b200400d684001224041200f48000010920390381c01980400d010000c081414042450300041c1c5800c002e007021103a04155045480307800d180d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 226393992 1250 226392742 226392769
    0x120403021e1e060c010c0201230906010509072006100b1216020a080d0c11010506150306011701080601051f050f1c021605070501020a031d030f07090c0f050405 70
    0x1d251682d0080742e5640386400c4500c4880c0a800070701001c0a0001c029000c1c1c889074807044202c0c2c0e55080c00342444024041003030310408008004190ba0303441c2105000745640c010b05024100108501c00b51801a200c0700a801040302010081150b07180ac2c4000d6140076100d50490741e0941010051006d1801b8050070b001d410650075400d0301c3c80c1240e4007606914021840070300501c0d0180c0414020800305042c4c0c00020080c9041e11070480d1040314190450880c4e070104c0300554851142c242c0c1c0f203500030b0781902441c2d05c40c006061070030780304050b820051000c0700b0991007125103a000700010300c050b05040e8182d59010518030b26044410400b02d0020f00580102459590440e502040111714140703801d6850609030329024086603101c0300981c0614403000b0800301035a19104041001485510002d8407000c4103800d5900c1d4562498092009105120301a40c910381c0f40c400d125504826120520250000b84000b4000280a017000c40780980340074442c060311014040140000c01c80e03919003002e05940d1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 226395242 1250 226393992 226394029
    0x6110a05071e0f030302060f070e061903150f0515030103020a0e0703150b0a02010b010f021b0d050706081806010b0912010e060106050702010210230c0c120403021e 72
    0x50040781030b44212200964444584192065000002d05030041441c90081e00703880c0c4004a02d540303011094490401c00100c9a030040d408000780e0000c5400c0141c4050280706501e80410000300c01c2c0d01d10300381401c20790090781c251030307500340300708043d01c1c20f0b00f84036400c02d60500b500b030709540c515000281080090b01c6030040a1a400303001401e0148a940010000c8917080350400150b0380b03449010308142c00920228000d50f2030429084040d40c060110141601e440d503000745903010642c3c0108003954842c0309001c0d045010380e41540c00044090105401402e40d0b80c0d5520741c68a0402800220031580340d031549035903045040144166102482224012002038419000c0c203071102e50070754010005010000e090340210000400d003280d1000041460034000d81c22510f81c01220181201200e10b1307891010003140032038480340b110501d0754410342d500054030000c640c140788000074160b04025500e0003034241088005414000c514003480e074103c0103400a0890004800e4070b80c0400c0401201c1c81c0380602 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 226396492 1250 226395242 226395269
    0x80309030f130302010f091401050c0a0204020a020102030f0a02040510050c0a051b0103060603140612030c12030a230604020c0a080409020c010507020d050f210f0106110a0507 77
    0x1404081002110490390003100a0341c0d440a074001d00201051881c0412400940c0d0050380c400c0d814800c84044080c2c50a041050b8244100240192540d60040c4111035243c051680c0810143c2d9652029141c1d1001d0703500003599a10b00503074510041c1d00018049800644180814042503c4075803451641d5282410996076500d2070f10900303840c0610501000f0030910500c848080e06a240f0800d5000c1e400003a24184a05c5468002c00d0b42030701c4880b9612901d01000100041c61440e04070480804040c03081c054074a403090540900c1c2c105200008124a040c000105018507415244244011400d0030a440c01c4880c4001405030440ea0003d0001807081d40c000c00c8403001ca880c1441200461076114500603070703503903540070780401940100200c01025440d010003c2c020070b00109400882000700e58403d40752000c501644590341c0c0000d8042c0c02d80d00002c0500311544100001010b0140205041315241c6602d00311005100c945c83e07003041105600300024150009200045900031b6440701983e801 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 226397742 1250 226396492 226396501
    0xc0203040303080c03100b031005090a1422080307050a02070501080c090409021c03020c0f010306030c0e0a14090c03060115091404091b09050603060601080406020d0609020a0f1704050a0803 83
    0x2010000076003141038511f000005000d8800d0b2001e80c0711040b26415241005d5070b94801d5a4181180d001001103a12043c15a00043c0d0042a00c486000d0b400890380065400b0700045d15441c5440d04200c0b2403c01042c0c00181100186404010b5903000340400d18194450345015180343c0309a000d50440c0502132a1500d140b401103507103110744501c4240034028403103800310320360500941d60126858603a0081704592003403180b6520900170300040d280c11905020b00146020b4000f00c10800c018491003a5a40d04c000010303805880d8203603113016441e400700408000b1084010107080803c1a40650301c1da1850000f00c03080c0a070018903010440304282641c4205180c0303580418003900c101ea00040c8808004407040c00c904502c085e100c01070b105198030400940c0e07200418540c1e10700c002c0d112580481d20039000100040c1c95a002485180c400800104105a84072102406d03071b044126808042210304c00c2107078103076501249001881d440f02c42d882c50702d81015150303a511444a85009043c0d4a070000004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 226398992 1250 226397742 226397761
    0x6061e01031d0609010b1207060c0803100305060117011505030706050a0201140a0e15040b04110f0a0303020d02150c04090b21011a09160305071205010b0405040c0203040303080c03 79
    0xb084000c0d410401e4403403615080440e94000c02d0000e0f65107100d14106d210400000360009001c03400d03540d00361100f0002040d41c3d101d074491904000c01c0d0303c01d081100000400058030034000180284107101c503607012040c04084050079907151600c00358403440807503c10801c613640041c040044139400d0a040d50b4501801c0320480c05403440c030040030703c60260340f41445100202a80b00c0c8010154541c2aa21903042d0010049400d810507213007d0000c900403804600401c840000c00c51801c1401000c5c0e2103813001800210f07048600303543c001c0d00581c010034000c40059405000f03980b0071018280d6845543d103404041120035000b513000e0b040354583ccc5c2e989024680c2d1580c03440001c01c0303200c1810300c01645141d540c64901034600e04007034281c20010340348014440e090058480b401440d450301c84040121106000b1001000b0041c036000c100038842d00d19041042a41c0b080e41c3c00b07440e00c4000c66a980f803d20041c40203450b404403440e41150300c10002080402d91004400d0b03040b03079000c41d540b541c940310895903 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 226400242 1250 226398992 226399031
    0x9070f02070b1902010b01050c0a0222050702060405010b0a0f2913090f0603020d020405040c12030503151207060f260f0c04050f0402071707050d0206061e0103 70
    0x240d600760780006140078421502080000010811350003400b079295a480115805e0180b0b034030b00315103039201c2c0103107400615100480351121250740402c82072100c10a4484010340f141591007001580046041c003081c40020701075200c49003000c4d2200400e641c40c10b0100d440444e850311401c07a840703020441e809010317449080c8180280007124180ca17201c04650b442080c503104503106290403a850140c0207404c0c10309500030034003240d0700204065024010f0b602030201130701d4018001c440c0310140100200321200340a04003e40c2078042e55407181c50746413881817280760303802a07040030303204180400c451140da5000040c3c400c2aa02c072032401d0042e0203c569015200d1001080015005400620700504076407601c5a0f054030821101d4080c60a80c0c4943d640c02c0b040744154004c1c660400c10441d400300c0700d03040c103070020544584140c152504600b0303c00c6449a40fa00100b008036080d80101c2a10080103904100f660740000044035a0340c44080085100d100c5080d40c07480482c181921401d4604102440001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 226401492 1250 226400242 226400249
    0xe01140402070812010b040603140106080415060e1003020918300409050405010c080907090b010c06050a05011503110d090f020307060207060906020c0a0618080d020705040f0b09070f0207 82
    0x1105403139035850b4103103034500d07402078010140001d14041d1382207001100c0403c500d04036045030700c80341e506e070b1501e0f291034980041640c20000e1141c0c44020004038007101d00e040b02c0c8500d0380005030048160441c41001a5004050a00100c092200e541107054031004280c04010010f42c0f0382003000c580d08019503844000141e080e5183c00c14020400003060411600030522542c8100000c00c0f008507070311801d842c100350950705422250b220305d41c14000d1544960021000207414102848000e586541e80d009403a401c41d900d2840e00e480701c00410540b0708028009508020a007424081c02d004228541e4007405009501040e964560340310f0410b002602521084050300030301503411707641e102d041c0a5a551081d119420001c1c2c807a8600141c150b1000c69050380c0e4100c0145071020f03080c900b840807210b0140d510b000d200508007000d070000d41c0310002c00620072403003016000350007035524290030003003100d203500c03a00c820850603c0b0000940743c1c2c4128a003680310000b800e01c032840e000d000c04100d103409029007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 226402742 1250 226401492 226401517
    0x5010804170705010b0a080109050d0f0201020d05090109020108010510050909151305010e070e09240d0c0e070903050307140c182208030a0f110a080403090e011404020708 75
    0x2507031200f40041900302c81200501910850380003583c0b0700c00345013203c51451000d0456003110741184090f91045a041d08001c2c01032002509003101c40265100b00e85042c1c0f451044c0d1382d9280301c10b6046503009028140108802c071204842d8000034200680315124100368240f08100000c0004d90032420003c06042d25000606000120b4550f004154002c003001c0c020015a111914002030304030740315004405127a2340182c2030f903041da00e446d032030b10301c07500038030044100c003003141030220041500c440f400e244400d4080c007140e100c1c0760300c0c1c200920740c40340c4050441e1040105c44001880841c400004403000c295009885000c60400464a181042c10040c01264003070800020401c1a0484400c1c080c05180036401e09050401303c600c910100c1c070030320f20004108141c2440040d211350401d50103a600401c2041f0007081410582d0003986da203510003c0d014020035003400512051607804100c0b4005008027070707598291035040166071741c242e00e00ca925031446250002103500030444541c046e110700612a1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 226403992 1250 226402742 226402747
    0x1b0103020f070b0603150c0f1e300115080702250911030708040f031101090303020307030e012a030b04091a0903070f0b070519020616090b03010501080417 68
    0x1442c143e01d2009040d40c1c3c66201b44100000280d885030b0440c0902d01800c13501c07103e146003010401c1188010b0b008030441c40340c03410703614540c032048242e1203005024504104920800c0310310380030b8907820300c0c0701284894a4070b40c1c1c240005105404145420540c40c0ca030505100f01d880d40c5811089140100c11200d414681e640384003844d01200c00742d0500c000344d944552007480000740c01203044a69000c00c454600c001007038900860080344140301e8503020746d03000e460300080d0000f0700a5620b007510138901048000a900004011001ea03140c81a00341307141a0342c00074041c40c400e100d014029241036a04d1015080015902e6900c114000d910810b1742070f0024100b03022401c4e0b0b0742130004404605001c004116508000025003a500c04812030b0708665102c0d50f9012000f0154903500c2c0c0c0b810000301002c0511004106204a480129040f00740039541903004001e980741800c2001ea00081407100c00d0309010030000c0c01d1010440010949066403428680f480940d40e070350601c0f601e805010000f5422070f0000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 226405242 1250 226403992 226404007
    0xb0409030e0a05010512010509100911090f030a170c030c0f0a030f082202060903062505040609120c1a0403020a1a03040605040606080f07050a06050307021b0103020f 73
    0x1101201001c11012102c2d0982d5558032801515244580180080d0140c41000144150b1070601c0e0540c0d040054551305108403926024800300300c403055126821442c4001c501031600c3d103003c0e002001c5034103080c2c014104002c8950784003c1e0361007090b00c41d00807030710003c40d11925401c0104252914681000c0031135072000041005592030f0302c250038090f4001034015220806090113402030038010541c0d0800114600c4454011860000121030304a80c801c4007046500d003643e40c100403041c060348040072144d10b440318404040100c090005041010310109100070807125130001c110b2422620101c24100c000d264070f18020024500642140d07201403c40907c541d510800c4201a2064078400e680c1c403609240c5840c0302c507030200808007200c58030020400c0064001281600000e800038030800e00411074a03120540c0904003034109900ca02c543c1d00c454010410f510b03007840180010030150411a10750700f04204002e4643d501c1c1741c00100d18055401140c4c3c5107900c0b03603045610010342c0b6212240c85526 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 226406492 1250 226405242 226405247
    0xa0309240f11030106090e090118080c06060f010c06150902030103050d08150901090b120601121b0f06050f0c06071110060503060612070801020f0c1606140d0b040903 73
    0x1010340459421440c003540010000d0a100c201c3c3c0c161455030700c44000782841c00300354005910780108140070b25522420103c103254684014660030354030408800761030b0302117150005c0c03402800501c000d100d4008040385d42c07040c5e60003501d00101ca9421010206440d10007894140e800d41c5190b000d00f604038400000002401170100741c8001d82915030391241841d031180703080500c2d20b0110382109503100ca039030801084a2503595022402030302014001404c81c2c0281c001d40c1d410600240d0000100d070710460171006c10021041c85080b40c607100074600704000d5062a22040b42201310b805500d06011000448800c003042c000f05840f8080d21000454030540f902c1003004001ca07010b4150b903181e40c03207902c822809020381c0d0f0080c001516000b03030003045250f9549040010301120007055507042d0142100100e10180d007800180420800e114250740c2c0c0d664640e10003440e2a441c0d03003400d0f04001c000882440b84550100c41d010a10400d1090320b51104001c0014000401c4004900760b07201e442c01d03090303108054 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 226407742 1250 226406492 226406501
    0x120203070302100f1e0f1d030a0b070e060f040e45030a0f180b161e0f030e130911040509151305030403020d0f061b02030a030924 57
    0xd1303055883c0d0658966006452002c040000d04510214646504283d05503200b0040801c01d0f4442220312200c0810040100e0f0803c881c1c910f05860540803c0200423440760043c069952075103060b11103074074000d12042c003501c041c003607070050034000100000030901c040c0307403040d0112010801b901c141c00c4c0752484102d010300c802d42d41e5480d4007198100280c103108000c00401500e51703108454958851000d4603110489412910946090314100181c0d0040760700d40040003c0c0c1040a60013080a2030b8002c2400c2140e4101c01c40340c4010065070400d48030310000b504fd40c001011690381400e107400c8212129001031227004501c6002d8a180f840c0c155150284800f840c03910001150903141081303286ca402207400e899121100d40362900c6201300000c030303243c5001c11501841240c021015241010744a034006041190103403001c0d15401101c5000b00d040c008240b251000f008202e1040000c0060f0f076642c0039440740500329a030001c0c5680c4032900414800182005044c651134080a07000b0041c110140f00001c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 226408992 1250 226407742 226407767
    0x801052a0a0e060417010501060c02180714122502070e04030509060c0a03031b170417040e100e01050a060507060615051305151207030e1903081308030112020307030210 74
    0x150301f401c000140043c06411450b60b0580c02500040810351244c03100700c60050f004d06418100040000c20301458801d6102508096070201c42c0031b401c03800d009a181212085000c00d540c58280c1041c5001c0308683c00007500c004594000070000072694540c14203a80c54010a44201e801c140005070b5401225004140b04904610a450401854403003000594045581591000100302880c00e40b860340e00c1c504040a611a20440e1007c00e04590046100300b0303038010b030303020308088801b0009018080b2140351400d80609030341c226408041d0b140800203400300d03505102d04e03010701100142007001d0092941290000c1d2a0490140c034040d2480003000348030740e00c46000300b10214440040420b0782c1c6454840322100300380e610382c40d500344034480841c030131031210242c40302c024959a03515800500c0d005002400225442085100c00211a42000780418030010211030f40707010420104800950440c3c182c9041d6100020401501045032021a2800b541da401c081c0d401084034008078030707850740940301500f41c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 226410242 1250 226408992 226409039
    0x40501020d080103050c01030e0309031b0306092409100606020c1201020f19021c0207051e030d030c0e130207020319030c020907170708010801052a0a0e0604 69
    0x41c0c04a41d00c040b03602001c20b00004009030417071080070101e90721030380180400019180541e890f0440c00030000e45002021100c3d0309205400b2a806031441c5010301a2507401000c5101a03d4017003314068100659040d9400d0142a001000421660b82c01044000034846540c00300308842a110b5401a58550010050300d1059803203540304260184103000740d074202e103001100d040c108180560601038110210009404600c15072803003042a481a4080c00c41c4554960060040b45090a0600c010011003800100c42c50352480c01d01c5240b518000b43d03a204690701860001000c81004504603000385882d00304542c0302c550441180d403001240c2d402007803080c0c401c0f0102c9007040301d8194604c0502102800150218144240000150a0800665501400616084031840501025a003107054103461040c00241c0040042c080c0417030911401e0340286064042d10780d188195079142d080690585465a0400b0011480760822401071a90040540000b081c103138542e46c0312035210146a000c0c0000c12403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 226411492 1250 226410242 226410253
    0x14010503011808121f030303020c0c0f010f12060b042301080408030106080a02040f090e060109050105060f0f2a06060a06080109090201120c031409030f071518060204050102 76
    0x1102144071940340c1c0d105622400c02ca0900c44c100f08010182003000700318484002c1c084a02040b00400f0580d0f0002540c480c1c1c50043c1c999011081e414940f03050240d041d40100001d9842c1c1080345e801040d02031810b55149002c280d442405400c26010708140c8d440110b84d20004100414030043c0110030841c1c41c1500b2a0341103507180d0f03000c011074218600b81c4002d881e141c8104018800755100e94661030f070007400b0100c054a0720fa074600b0380e19100f400b15405030480ca6503914055208010500000c1d004042c050381c280440e50604001450034460a2180c1014000c001078200d40711482409540d050b84600400e43c80e407032061001126054005172031021540640c800240052400c001d0350421307030310255514126a0708010308000109100780080e13040c004c81c007000c035050360345900034a032074a07140340e8000c500000720008041030b842e005080f00c4071580051158003d85000113042d541c01c95000514108841c1d62140100024035902420700c09000e0110403410030310080350020300c225a000e03421100c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 226412742 1250 226411492 226411511
    0x60c1f09030f120908030708041b0e06060a0c060501080303060a06080f0109020c0f06070e03011a030a080703090b030f0106080a05090705042d0e06070c03091a0403061401050301 78
    0x20440d848003000401040c560045458290700c00c0459244a0030310300800100520261203540f4a44c00859811000070348550410003000600314204810710042c10183d40f2a5007490310055191600505d19070041002040000400344100d00122645030071207010011540c403412207646a52089034224004c900c0050000340d030300d10a0389800e01c580208008107005900b0400020040d502c01ca14003015489036035110b0248000511001e80101459202d01300344e242e0643c1414292454407001c01c03203295084454142d240c40c003003a01c0342a95880348100e5503c040034a404c0d00c006a07990000c017180b400220400a0003100d04c40254140c86490700c2e54070842c0c2e03a01d00c214060310340c102d8291a083d0081d2100308014141074000c0d00c840ea84400030f00c14000c81c1050341c200c40d201649807441503191580b00c40c8212102c188230058019110340f8010380c442042d0b807405814583c40d0f20549424412450350700200c40100e40540c2c0155a1009062102506020080341c0d020000e0143c1c61080d407070310300c4a6 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 226413992 1250 226412742 226412803
    0x6030a02070f0f2108070f0c140c12210f0418021c0b0609121e010207021311030c0c070306020f0315030d140c010204050402071b0e01050a0b09030a02060c 68
    0x101d1034944c42e551802c003692041c2d8200e8005070185032440901a0040d400b0703000600380c0c1e4484082c1c00080005103c1d5030740b02d41c200701001c600c00c0e0f40fa664a41095840b0b4001d00d42030300010421202c207501c05540c1d0b11810300b61220b14403903540225412115035030b15000d2400d40703800500003541c0c011203828204620170a96001c64055415240e840501003100c0d20440c01c00c00242602c0d04645401c0d540110b0360004d061400c6658044605116540003c12600b1842c0c003840e500d0b01210440c9003081194101c1c9907904080c88007514074403100c03c010645000124042150b0000355a1142c020b540380d10400500c1070154001783c601085125207503900002c00e080014210691101c00d9840c0394a05501c0042900b00b940b0a00c2404003c1d5001c2001046545560009108643c850720081c806251100004840d070030762500b040d002408450010055541e403400507405031461000001d5a40e1002c40002c3d2511000b542e009420520100301080100c801103454150780129440504103e5000c0c0040b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 226415242 1250 226413992 226414043
    0xf08010e0610121b0f0207080f0303011a090402070807050d030e0319020f2b03020702100f020a0204050a051506090619051b160506070f0206030a02070f0f 68
    0x1650800102d282c400d109074400e805a1400040181c800203134104004000b1032030112446124002c0b0360b41000c0241550b6040000700018a0b01101401d4030410140c58148c0300e00c81031003042c0403c1140c100d4104180d204c0d034115100c00c480108119a034030400d1806107a29040000140c03a94050710190440b41d074040c1c0207915030314000d040a545041d840c95003154005541302c940500b103100c4c4c3c1c0c6d420401303400104030452013240b481c0414802c800d41d81c1c9a120b0740751440d2600350200740c018080000140c0300c05001170102c5013241048400d818000c80c00328580404200c0195000f4249805d000c1c6c01c21a80c0d11090041f261024424003007a5507030144a51031143c401c800d03400400c2001605511500b001092030080d40d540f804d98900403098403c426400c0600d104401990080220522140e50b55400c4000420080e00e200382042056100c4c400046403800c80a40642400000241060101c1d41218080c0d540132100c1460055281822511942d0110089034018002c074461409008203142 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 226416492 1250 226415242 226415251
    0x307120c120623190306060e060420030402010804060f0507031406010302070804050607020103020c1f1a01050d0507030e0102040f050a050406180e0c0913030e01050301081911030d0f08010e 83
    0x10f40b1000c90103c0050191003104100e132a141d0303e48809003c00002c1180c01104020300c041211480c4a0410000b040100c4040e9a003113035101d0001117455074019080d03816a9809902420501038658550030880b001e420456081c680840c582010010550381503840b4048002604106003450380d90840150128820b00d00050300c040320502c02004585001c0e17004142e03040c8180340c05404d040d003038101c1301c2c81d22200c030390300140000c5c07011401032015600e440f034205424219800d40d08002d1008001038160310581001c407051a8550000030451802900440e400c5d59080008542c2c0f0342d031380d48505c22003040502505101e011403010010355890b040c0104800e540096502141410070b1124085c0240a5200d2800c00c90060903680112a9500c690861049040055440c0340041c28500242409000e402d01070520006100500c030f10303280041e0396900790442da400c0380101da41a044c414060401c5c01d42d800d525206000e0300b2600d21340d01c051400e114407c1d035102ea005c0c90362a0b0b2400361902e1000c64 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 226417742 1250 226416492 226416539
    0x3030e16031707021903060506090402090406020703090305030c03040f0504060602250906030c03051009030e0f060906131e080a060b12010903021b03010902150307120c1206 76
    0x24401c0c00460701c00c00200c100840d00a0400303107405100d601080710032622100100d01d000c0750060410610000340030b6a90300020480d60405c3c540340c26400513034001d5000d04044c101541c04034421003050300608581c00510f4128044036100d80c4980307282e50b6641e0190003407030f102100202e000a228101030181100382c95041d0040d0841c203c40ca00d28080008500003100c21084c07010070000358441d0b40d8031401001e14010805100803e0450811074a8070460206c480150b82c03501c2054030100e079210302c3c400c0c5488412500826840b00d02000904a4006c00c010f443c2c1c031500c0003444d0074000c01c59a841c602140c7c10a440600e80b00402880800c1e8010144502d0605810404160340040d44a500c4010b20141c0184503000c01451044000d0840d01d100c0c40441c00344c1c1c00704e88000a10030b17036004110038111085000780411011f03a40407607042ca68108d03100d4505440800455040780c0202ca010006140594041000c1c15021000420034194520f015070441c0c9404030100e00b814068149103000c04546 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 226418992 1250 226417742 226417783
    0x504020306040303151502030a0f0503070c17070503030a020306120708070605030601030f0e010905210403080904091a01030314031e0a1b09031b0302011e020c0a030f03030e 76
    0x5031810b50140001c2c44210409443c1ca03178020034603201c0e000e04035054064590095481d54076001e000f42c10b011403418114140300c410300801007881d50064030030a0440c1d1044000800c1303c404502d45050740140c690050280c0008000c00440411640c060340c4076001c1110180a00303014000c159441d210755004000c4160400034041c82083d010344001d680140c0185400507440c0035034074001c0200c950f80c500d26110b42e511410034205010041007556a450300319a800d000001060410a10794400e6100c010040c04011800c1d0415a5807070380800f1440e90080301082c60080041002d42c08440240811000f084401d112248204105010740380705172100d4030314820340d0710445102514054000d0100140c50313201c55000740c80442003c0221807803103272521a91f11090461520b03903070909410240e004110b050440800140c1ea00080300c1010b00c00d11020b0720404200b44c08200d0502682e8500d0300d4020200480010410400e820080b081c0740c003c0e5020008460000101d54498030929505104d58000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 226420242 1250 226418992 226419001
    0x5040606020a080a0905100203070c060504060905120709110309010c0206040c030f020a030c060e040e03070f02100302070803040b0603100b0307150504030c1419050105070f06020909010e070f030504020306 90
    0x83d0010040300b40141006003110f035a980020310504041400c200c0160030201d04003080040c035402c8940904640c3c01c0890400d424908001c2c01d1120510800d8420000880e41d1070007404c0911540000d0f0407d00e00500059902c00081585030340162501c40d0103602e44003c80c540700c0c4c408a80c040c001c1c0d50065100c50590300e542c50352811a0f000101c20382e403003508031500000241802c00000c008103025200c0310002100c00c2c080000f10f88140c002002943c20420044002a04480c51030324119270445005003203509002046000b80252070004018035800001d01003400710b1503103180d01c0f42d18102d007260082e1459503c0c041c140d406261505030164004001030140640d81009005822000d241184c20300d40e0326202c05a85102e10740c08040390402e2218143c190b4240098541a03100d1040882460701e840d0a0000380b4500c44d03460098594070fa1040d0103000c0144071307011102840700041c2a00b500d542c5410b07440d42101011f0740c000000c181948442d40343c1d05c2c0a07010b42d5218980080143c41c00350755 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 226421492 1250 226420242 226420253
    0xd240b01082d04080d0507030f1503051509030f04231f1209060f0902030f0601080d08061201050702070e13030801030b041b0e07030c050903100f0e0706050c0705040606020a 76
    0xd0004c0318940300030702a900828142d44551803048031784d40d0740458070b00300400400085030b000030084002946800e00910100344002161a00403003006101110341e41c500c0350540c00c500a00c4c000303080280000400060710070401d136000301d44040d5a2000c2003103d4124041000c0710000f80400e04070030855100d403860302805085568070b926002c00c0c01003620060350351000100c1c2d500c1d01c071607041290340c0c00b000e00a604041154460307201c1250b0041501d5410b08075620f80e03480b10042108100040c00340019002d84804c0744091b500c42d4503000030b0100e402c2400d030194840b00c0318000ea002c100044000039403101004051500c1d52034250700e80c45240c0c1d003162520380f500326004005440740c20002403100414001e40c0c820358010071041d11503128604280d5001420348001d0300300d86080002c03d03c00a52030b56004201b00401d04401c4000291881c6a041c0100141040c07070381c0c601c22401426070020301a90000010b00412146800390b668140e11a0100000c072102802032a00682c0102c8402c40040c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 226422742 1250 226421492 226421581
    0xc0a06090804090906060311060a020601140102100e010f0e1209130b09040818031605061309020313210203040611030936070e0d240b0108 61
    0x14080c0380450b1516880d40f07180e40584045210841e80166188020400e0060076010403200b07140480c0c00c0c42c98481d18000080da2450706014084489103a81e140001c180c0c000c00407082da601c024a422300c07643c818800030600920070a10a0000340342418131a040c540380200e801c1c3c5505d0214215142050301da80180000380421602590600f42c0c0c0b400002c1444d0750341c490080c402c2e4450040d04d0740d100300001ca401c0090460310503841c041d034009074006014403181403d51054480c1501c1498480c1810700c000300481c0095440101c1e1144004103125166801541d9402c40ea4090245078207840e900b4120003c4240349200403070010f07002400305005440c81004003403858146001203034100929200010b25100c40d40900030304809050100600d88004122012100039560382e20720b10381c0c0b03041d00022b0600034400400070300c07500c00c4200800405c031038a000f00050102c0640d0b8280c198506460400003006660200c90100b6509000109607904562180100c052040e0b203251190303520351410300022 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 226423992 1250 226422742 226422761
    0x5040809101826070f03051e0a021309020d0c05030706052503020a0b0c030f0a05070c030e0d05060108160f0f140105040914041205070203030909070315030803040303050c0c0a06 78
    0x141183d0a0344180311504100443c00303410075240c08060700d855484c20615020310547c0c1c5a0f0b03e50203540743c48644a2000c00d01811243c2c050316032401141541082800820621000961000c9854500e00500010140d64400d6440590454180c3da851754415581801045d01c000100c0802000d419084c401081c415000c151003801160700c1e0346600e5590403503090381243c0c5c062032150040100007200207031404084d00004800000c20060402110081c0204080803000d001e108400d104980141c64260341241c072150130105880d961f5071640002074503504002d8100400a00001010500309480b03c2d901d02150200c80d00214214036098404892000b40342105045c0b100c180310028850815006a5040d01480131445055150500e80200d10042c414104820000144502d0005890000850780210000c54003a0806c0e580c00d0f03c00c6010f003240c0a0202c070340f8614000300008101c40070000e517015a120b42c034148496510305143c40001d00a21030100300b140d00c040005004201301d03a0109804 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 226425242 1250 226423992 226424039
    0x9040b030703080a03150f15080414030f0714070f140d0b0106020a021503010b0f030919030c142b020f0f0c030f010b090f0910050408091018 62
    0x3950b9a464106040c0c01051410001c44c2c0c4680110560801c0183e54070090545030a00c04411401c2070980c0320900000b6420300c040c0407500d004a020700c84134600000d5201c1c03036082140c0d03540d05440e205540076000b016080b1038000b004068280450b002084003000d559100200c48180d6146c03001c20452010b640c4002030f04902e18503c2d4401084855144031301034807280c3c00804040b0301d144188189a031b500d0a13204580c0000b44014444510b0103001c0b0b0f0808008040c0d4a512926115030090825007040051909800f2040e96403013055004810088018011202c40342e0f10281c00c0040c80e00c2d84c1121003103500c050740c146946682d02c3c29002e01460300ca212441140c2d090001c048a45141c5403032040e81103c25400300d8802507403494100003842408403140c0080c040c0808800218644c0c1d03401070001e80c143c2c0385881c005441060100024100e8180101c0107101a0409092568599001d079004a005440d0580c940d219580180090ba4248101c0c00841e40031a15110030384003041c2e0303000440c480 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 226426492 1250 226425242 226425253
    0x50d170a0c0b070e030606030604030518040204050a030f14010603020d03030e0109050706090906080f031b031204110f060c0606060c0a08071208061f032c0604061d0309040b03 77
    0x10500b0460b105125001503201e000345100d0307000805107000002401d2622070b170b0100d001c101c0020307803003c2a20120041d01250800800c40c103030000300a0302683d001950800c64850000081c041c41d03800c20b003091405051080751170701801d0341c46400d07100c444c000030303401009054000b40024825402000c60b4056400002510b1459503245403e01145500c074a002441c1540207000c0c00050303200c0c000081c00540000c10340e0b10a042941c40c0c0307901500d0385011700c3c3c140582c0c00f04a00e801c14030031160441d801104242032461b09142c03900c020990b1080b614090100d80e8814000d0707003000300844816400020040c9203903502c840c100051380c1c1c00002c021a05005500081c00042c032154040d0004500c9144030005005003403200405000c4001c00d031a109145042d90a00150260000311426505601e00400c0300d401041c103643e080060000c2c910745428840485908541021a215018904c544428041d4103920741020880c500c4c1300c0144803183d081000480541e2500340d00901051002501750382 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 226427742 1250 226426492 226426517
    0x30a17070809210d0201021303080307140a050309070e09060a090507050301141e0103150c030212090d02151018270c120f0803060409080f0c07050d170a 67
    0xa102003070f5082c248045490b2080f91006003081880b9081c40c09910f88002c40c01d1604c2c2007841c0c001307a1014400501407010002c04101c405102c1d01403141c281f140c8110660740c0b805220350041c4558803c580c803010718003914030045490780004036a203014500381c0c0010a083e807614414480240450102100c9520030b60100043e580c400307024205a0303607084031b2050701a10b030036a155021b503007005080706640e03c0d50400500c0028180c980c030401210128200240000513150150024852014400c1c001000c3c041004040e00c1d00041110403c1940d40c2030366001e0b0108024142d4680080d01c0c0e0458030000e00030140302c820040c1181804045941c0408604081c2070034403c03144c03411190040541d104080005014440742e003a2420040800c0180300b05d107a100764490420341c83d2100c5009100c1103000020842a81e155005000c1050b00048455034602110030000c03003980c400a40e20443c0e01606100048510780001c0083c0102c2d00f00da0400048030f1140e100c15515881061082c003484440b4000f02c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 226428992 1250 226427742 226427749
    0x306011806090512030a02031c020403060614030f07240201060e0a0213151715030d0305090129040203190f020703080610020703060519110d0506030a17070809 70
    0x44004118a48401d03039080d0038901441031644c0b860890000d40d0344108054144c2d580d000044540746055988502c841510700c01e5404081e2080c4d81c40a8030203400c001d004292030000141c00e841040088003150f1801104031065520384091344941000c11003600e03075103010540e000e40c80c240031151920000a5030354844120030a00482501c82034591070b800303d081c01402c1c85180003400035051a03c41d0340c01401204100400c440006520070029211a8022038a4070740c0c01d540d0340819100040584400c0c030500100280109811071704c900ca19030030040361110342d81140d6000c5080900c0c41504450b246540e000344406540060845004159500000072a2000900c60b03041405c915010159803802c050800501c030301c50240c10284174484881c0c50001c43c54000480c02c00f245d6201002081680d903860b540011401d1003407404138942c1c245400c450b40240c03030030020a0800b03003044c81004562540005e1643e1446800320051010942c02c0001c0c3c0b0040ca910080c02c2c0c02481a00014130301071005020 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 226430242 1250 226428992 226429037
    0xb04050f130b18011d07170304060309080408060412090f061e0e030f0102040e0c0f031801230103050d020a080318030d020a020102070b010e22050109020402030115080c03010b0a05030601 82
    0x140e0342c17440c10000b0480c04658092045400400000c5a8005500901005107490b0310a5105032018180da4805e80b200308004013081d80c00604028054480701e01c1c213170070304002210a0358004c0c03000903001d81021a042000c40c2000007030ba11156103100d800302002414a4039507040310043d20074028046084c400031350b0100700d68840a40000000750b04c40b031405050501606000e41a40c500c282d040c0600900009600c0c00c1d03c0d80281b490703c0940c8043c03e040c0e0301500510103c0300c0f6488107041c0301f4004400c104142c0400341228410000c07130769140380c251360898940100f00300c000c3c5020400c002148204812141c00c0c4c0914807900142c03031528090101803404c990289246102613500801c445081c00886d0600c07030700410880545030400d103400b0034074070742c40f642440341c80c049100a02c440400703100c4250b01c05e107030041d805070045541c3d58440d01210310351140c10014900186c030450006411a080c03400342c0e0b0403540a403c0e498240480701c0c0040d54544c10051000d8101300e403400c96000c104d81050382 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 226431492 1250 226430242 226430261
    0x1406091305010314010c020327191e140607021201060806010909030f0206100b0d020403020402041205060703020702060301060f110a060c020714030601050d020a03050607030b04050f130b1801 84
    0x8407030b401c50b000140030309440c081110380047d50400d00032296040f510490764a50705004c00c980c11012600c10001801c20400000050304508a2180104070480214082680035841450000c0798642c1d40440b8100c02a044000355000340003480303030f5001401c1100482685219060010540b1500d880885251a500b648210711840d241d11000041c10b801110035100b040041c400f500b80f92400a50032646040103110344400044001035420b405c070b40940c103890246a00030070035580d40b9a80d182c000c143d59442841910342d0f0180744085100d8a02034400c89840c5035006c1c0c0703030900750703032030500255031800c51884903106001d1822034207001d0000500014036424416038000410200058000f4a003104942140303500202c00c624100803580c00080550440700101c0324001015810710104000410070f034001050762050302c041c44042500743e000420681c40503182040075540c1c079800303d2a030013002d03101d030300c020719804100b00c010030b003000310301544400c5091007000c13000c40117610f203421900d1901 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 226432742 1250 226431492 226431503
    0x504050a02040c030b210c030a1b0605030f01030b04020a0b07140106050a0810020a21020909060109030b27070e040b060a0303140d0f0e01020a12050114060913050103 73
    0x4003011032a0070311544040d861149400c10145083d00c000c5402409240d0388110803510282c1685140c40003003040351001c1801a050310341d003400d80e1401c8441f40c61000c2116024410340e807004600a80b064040d13030301c540c05001c2e028103140d11f50b441e51b04100d0300c0a0810380c0c0144020601007503443c035000003403043c039201c0d0b996405d5900644c25070608560003034008034440d024000c1c0030049608002401b501e013050790031006a640c60f4040303098400d01c94031281c079502c001819010f480d100307840e680030b040c10b401c0c00e845100844c1c0d00e900046440c0000b6000040c400c0843c070340031541e0960b020b0164070b8818100300d603600c076603c076006107589407100030351201d250300614400700300422107041782d00c0d9040300341074035032136520b43c2180e40180181103140700300c005040e8003042c43d84400072580c01c045040c07401280304100021000d50310f94040d5005061000c04a01803c0841441c078030140b00c1c0504070744034880d10040301c200e18000c1042d1680300345650707540002002c0101101e01d2162003143e00941c03195 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 226433992 1250 226432742 226432753
    0x1305011403060702030c0c090627040c05040501062c2211031303081302041e1506050d2f03041202061608040201021e060105040f0b0f01051309050405 66
    0x284101841e02c04001c00c050300b1500140521404560001156924640215940304469072110003180da1010303048860000c9005a401e540717502000344488c1c03400b46006403066500962581e041c802500c00031310030701c4005034548000550702d084116a1466103c1d14040c0e1148100c184400070b03840099412035486428403889648a0800d00c62044030208801d02c1101c41c00d6184c100c41c000d015908511000e02400032460000f045100d504200c9010241d00030002c101050000c0c90b1030985005107074801480d0743c0740c22005c118200c40500e44a0844010782d46407480c0000104180c000761595180c040d900041c94404000c0b000344003e000c03100c1141c0c0040440d101d10741400c01e140994101400002950040d0092106070f090b008400c9a5000103410301007142c0d221880105c2c6001e030520f240d04801040e10440f20045140451954101c810132070b07050258111500c040801c407000345030144c0e40000150300d0740c8819401758014040d0308420882c4581001c2c1d680014005441c030841e812591034000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 226435242 1250 226433992 226434029
    0xa0b150304082b060801110306191212080906040f172802062802031b07050105010f05220e0115060206060411040303081503010f060b0c0d0201020c0307030c02130501 73
    0x5510541c0020003618000b401f01220100c07000040b41700241510740160030401c2210400c40500800400400004140c240e409100303041000e01160207581c0580001d694001150b8407100001c0c10328010f030740114900248200342c0d43c4803050003c81068040038071206000d5a0710124100510300c00d554130b0440c0313001043e480c6400090030100c005042c3c81076104403100c0190002040443e0b4001c44208080c016a2038485405024100c1c0b0030b0000e400584000040315001c015041d00054101d0700c94840050540da12042000407014903c60b0038051f01900102c1410025000d1b00442403050b012000010071902410a055040d4880e030822005640107406010580c00c2921034000586030503481181424259a4010090079020740f104c501e050307024401c0400d540d405e601483c280c50b071565080000c6517482e080c401c455082891610a6402a545205159401030003200c00401084010b1441c04403995000d50707040d0242501642c0010b00701c45c1c000982c4030030344074403406417900350040b01c8043c5a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 226436492 1250 226435242 226435327
    0x10b060d051503061303080402060d020301150f03020f121b070308010f060c030804080d0608160501030b090103030e100306350f06070309060f020403030809060a0b15030408 76
    0x20845642c5010307900c5041000801a40903030005081035140c606a4901d45075400051800c1c0a20450306000a200000018440000b414512161101c64480305140e80c030968041d0124010300701c0c10003803003004006c410404401c51003101d60002d51032140180c003035062088080076400a40d01140402c101e24014030060099600c1c1000410b1149018100b10360150b138003c0044401420003004941e01040d5103a15103000d40000300030340111011a0307004c031032803c071901c104455803103034601003481c1a40b5000142088490581a00d070540c8409024100840602c01440a85401402056620000070699034001064441807011005e140c0c0c900700d411078010040d1070310b003601450060340050115008440d001c64425841000c1e030074001010708490500c2006001130440c0c82d0706180c030018000c4101604801d00b01e003c0c2c04104112210399560007160406c40d440403c900c0d40c004001c00740d0f1039a4140460042d6401840340342c8a504029012142c01c80f200c030003040c0728044000300c040701c1210a4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 226437742 1250 226436492 226436521
    0xa09150f0b150c0a08030a0b0d050322032001050d0f090309050d050c010809030702060301081005060d0f02150c0f100e0304051f030207020603180118030e010c020102010b060d05 78
    0x203a10b100c00d54980000484000e545519421000b441803d003c80000e0350150a64041d804503100645101c15461241c03505603281d6005c009407014400003840c0704440840c6000151003a00d81c030a100c0700984020707243c1f031142c8440f540011410007034208000240c5000c0c43c0240c0c02e58a1b440200487d01030018600582040701c81d80180d809107400241800100c0d070001460b034460b800c01c0c28829459100c08000074114800c08802940002d0300100010ba001e400250300d10312085c4c042002c2005807608030401544a042e45000380c0700703061200c11800949840303a4030003420000320010501e46040300c3c6003a814401c0710080310400350010f40d001c7c40c0c0407603d401020080c920000155141c14200300004c1c103076903049001c0b0180005180b5210090f207009034102d07228540c0044c0080d44a143c103a041e80f03e040700303c01d54500c465090640200707564840b06524041d456154442c4880f00c1c21403001104c140c07100ba402a4115900d41ca4103904d81d80350b20000b031840e04940d80011985280c100000706074407 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 226438848 1106 226437742 226437769
    0x9071e0e04050109090c0915091b080702030a140310030605090a03030605030d0e0628020f0f0d021207050f010c090e070305040b0a09150f0b 62
    0x140c0040d50300d0a00c03542124180000d80e2594400ba0a49440d0709006011110007601449030032119000b4000003c40102c0340b10b89a6581c00441058500b40b083e0501b61040f40c016130b1028550010304143d01140d580019850310300c0e4890020040710072200a8000c01e00044089080000602c3e120b00085030061004d00003070402c03400c5161211011413048002c0780c80c00d103001401c0e060220700da0841250a40700ea080e405e0a002c14041568024200c072a8011a042200301860042da08401e07601416a4014510052000c603050310f4049114040030303c1d40e1002e42800e984a5001400c5582c42c425503440caa20b4a10f90710303140e45030594490748013010303500344008021826448201c0c00b040340c01c0f5031043d030180c0e250140154111003065401501e84010b4000042d01d0117001e400004045225440c10528118000c0c045012149c00d2000240e4403030303c400e07650246280060840c4081b = true := by decide +kernel

theorem cover : BRFrame.Cov 226258992 226438848 := by
  have h0 := BRFrame.cov_init 226258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 226258992 ≤ n) (h2 : n < 226438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
