-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1351
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:31:19.476582+00:00
-- url     : https://prove2.me/submissions/78a5cfa0-2f1f-4f70-911d-d55f63ef064c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 242805755 ≤ n < 242985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 242807005 1250 242805755 242805757
    0x82203091d15061e0c070e0907081f02040807032009150d060b043308070b18180a11030405070b1c0e06070305011403100f09050102280203 61
    0x242a40084061802001d11410888040e01d2001c4c0801c00c0d4801c1103e040c250300001d9080f5992a8034103500010041000c80c8549035910f800526800191010700c6c1040241c540b12450b109145030b400e62010850100c04509a0459004000c6001541c024603100c1c40c00c90030540350749001881038042d00400b00c40c3c80c6030600f855406080c854580010300304030784042c820b824403c950141c6403145e0300c130001001c54a860207814610708214400c203001050600000d40030030b030705ca020b0340d10042d03805400344002070001805034103070b400c05440c4a8a680c50400707a003416001c1c0700c401c3c1d80c1094840c40381d00115503600b41c05900802009005006100c06e1801e4801d19000440703010b00141c0c88a202000000384849c004d0518208046e05107070000c8090072610159001d0f000c06102c0c950006017008000c42c0c3c18455039003d0841c074080d2a140e200040c00090303940c4511104a400c199954203c1e006130740c03665201c07051311740e8007500a5445403115220401c88101e400c000121403420007030000c40c42c034130100c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 242808255 1250 242807005 242807011
    0x11106070309060b040b010c030f0917010e2406010e120d030b130b010e06030c040815040b0c09030a15020c100207141606030e07050a080c04060503160501082203091d 73
    0xb07550b0040422381c0c0c0c0c5046900c00704618414051000c0c05202050300b8040c903455840d800107440000ca80002102556032401c442040d0306040c0d0410190855101b0402903001600040c00f441c00070200d40c2294001044118080745c4591184a10a90070821a800d80c10682600400b10381012400e4010100d1505441811038240d002503003066881e4403030b00e040c401440d08140042403481c249522680e1031864100d800928401d40083d400c200010450042c054690100252140c0d03410801c940b07021a0381c0d031000700700040810300b5080c203452100b0600e50680d04014204000c4540d8020000c0f42c040c02035100c24000e0703400280131000b82c00468800140084000c8031072064000c100e1a02004400529203081981450700524400081da0340c4c2e1828010b01600030080078140d90b103030703d4081004543d5150301607406a00407240c48034144900380b6150741210b2080c24043c080e41d072010382103200c1c8510b0100460800550223801c0c014181d010302000d0a90311000c1d58480410b101c1c03800c11060350022 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 242809505 1250 242808255 242808257
    0xf17120612070609183905040f061b061b0e030111090d0611030103061406030615100221040f06050c060402040e01090506040602180109030f060902011106070309060b040b01 76
    0xa0004000d400225a070303030f803145c0c0c441c60300000e007076028414242410401e910302402243c03040e40e2200ca424400c8001200400c2903400e20300c2c986858001408110001486a034051001c0180d044e0384204640b21500c4d580b5600000030000111400416003044c001c04142c85c000400d0381100308050b0034140f155440344254400628181002e00b000c009044840701021a08103450b051041080d000070006180a14480c1c0b0000c1110a82280c82403210040140072074881d505ca50184052429682c1c0604c21041080d075902d64a002d044030260302d400c2150020708107000c001d41050005540540c080c0060f1018811808126a0384d21002c554a00500340118002e40203031010500503c0c0c503900008507221480004900d5421540380e082c18004216410b441a5400113400307a440304400c1100c0306551002d080600540707080d51180750b00300c0e858041c0200302d240d50348440e0065a00580c1480c65600480f01140d55a2414503001400380204207012613099007000420240d9103014080c010707242c241 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 242810755 1250 242809505 242809517
    0x1704060f0224061315170307120e0a0f0311100f0206011511010f15080a03020703110f030304030302150a0c02030d09030504090e1f020f04030f171206120706 69
    0x60042160002d440501165801480c0d80580050702d8154000c00c0d03803540ca09528018514038010440c0080b004070780c480d80040d0810040000010305082d13807030000521a240505100e041c0340b020940b00122600800008880380780e0010130000b07200290400c0b80010b94007080e6001d1804002c0e1100003881d0403540160b0410801400b07d00d1098403c0364004090386403411114150354007050843d5210302013000c0c82d548034113203030b030607034122000c51030003494510b0051420168645000303464000d14080101404001034071040c4564901d0645a00c1020040c140d998032540c82c540030355560f1000c0c0c03081404a685a000882c3c006503071081c40d8a841035a00503519110100001800500c8599002c40500c03900380004035038001d847c4101c02d01d07600c400008040801c11360500000300d00039000e480e209540100020700b4014185016181100d501801c2005164100c1c581282c1110088100015088021901515005046560500074501600c94000152040e4100c60b29103160740105d5001c980 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 242812005 1250 242810755 242810803
    0x307060b090f0f1f08010e0c10140c07030b010602100e0303060105030403030c121d0601080601060c0201050d02121312020d0f110f0a12090b04060c0204181704060f02 73
    0x3140001d0b1662044d070107041c1141c046914006000050a250032158040e1b5441002101c00724040241c9886d120040300d000d40505480e410040041801070201c080d8030602191000e91841e003004040c0141d81c0c08032201c2e1041da144c40c002980d03441c5001d02926000e0404804d40c2c0f00c418084126401004103039a050302e503580b95201500607020342c068120070040b010060101e150b080d842540d0300b08041c0b501c01c55011100040282c54400180c1040120790086401040a2504264071070b0425034282811502c03801d0402d9001d00078022600d514280740302c02800c00800300742c40782e601e81d90301d4810708403420740b450044022a40d42d01b0040d410404142080e5155503034138010035440d00c4500c1404c04507040c20030603071501e50a20f024404c040314148140d500d01d41c1c1c50340d04100220098842c000c44107080519007100184950b03008000079000d96030b541d041c0c09a6581c020b441941c01038124000f038190990810440150b640103106a200107280003a020032854400310f89403482c080e69905003451a0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 242813255 1250 242812005 242812021
    0x180f011a12060f10030c0f080609010302090c04030501060902040f0b0703080a0e0111190801050319030c2d0b0106092301020c12060103030f0e180c04170307060b090f 73
    0x107005040540d000c0314800c140c2006030b0720501c0350b005121141d5004105101103960107021054080e0303d81c2c081c0b0869004020381b0341c0b00c01124604603601210307003903031075181d4405155551203a41c0000d0301d42d5080c0310002c1a111000e400820071209100005c00700c60b6a2031016120900807840b00a0002e800304011170300b00c0c4619044100101088800011144048103007940c07039500020751088520704202902c807400e0b0b0810740301401040c0c158080c0c11000300010400e10220308000004060020700b92007102030141c0080450080541d8010042c41e8511011018407290215202110700d822170f00b00105900307102c1d410a50403210b61340d60700004001046550821070300100c081c541180320b19042c004050350f560100d007113207015140140803a035042d820002c1418102110141c14010360102d80304a94880710385182c180b544c0c1000121160301d82200d01441ca104642c48010094045010824440c00200040042d1481100100a03011041090107404c0008a4200c01d40c5c480c4200010000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 242814505 1250 242813255 242813287
    0x160e04090311070303030f110f120c070b090c0910050f0d050c09040b040605090a170d0e06070201060f080c060a08040501060302041a1c050d030905030702180f011a 72
    0x12501ca030400c8030403101001e00326450480960700c2540040d4860450a410450a22a1005075000c83c50500c2c50480f40940c0c10351144215a9441a006043c03030000740300b0540344081e030f1002c03588000301e0f21250500060007641d80f01501c003010721540b03c9101080740070582c03c11260449101a2000825101a804006503001c45d0801500c10307000300851901681d0b1001082441544100508007881c1001d080c2035003140c2c002007224085900c250410340104918040981500381501c80b016560002c0c00201e4000d020030091565462040ca42440b44298040d0410304c10349002d80c2003041078075550071466965010543c055070704114200302000c50f1505c1800d0031036002e401000046103243d80c95020408841d043e0440d8861000200000f64852801010b0500c1200500701140440c04080c0c603115184d216000c44034040c50368078601070301007082c1403042c1c41407260010022100022034000703c003807442c011180b420103100003000120340720091096034a4924608120a8100400e600e081001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 242815755 1250 242814505 242814521
    0xa0e0c1003020705030c06041403071703040206090301050108030a180b0304080309120304120f2c040e010f0b09070807020d08071413090b0d02031903110a0605060108160e04 76
    0x20035800700f00d140049401000209000101c0c880180f00600e01401c00a0662007040c3d00089250410003e40b400300b83e81910000b082001c514500d640ca03181c40c400100148103c00809800d5401c1400001d2144804405082032001940301c00a00031b00300d96294407041005e014608003071009001140100c0d048601550f844100ca0084610000f4040b4050406410885084515184845060150f9540400240010403081c00c21581505200140f090017081c90440f002010000090f000d405030380b40d0700031071354045c2c00030000c01400d0a101040000b816400e450f241c015880400440c4a8610541e0124400c6510f6405007001701c0ae1440301300c549040180101080114032440a0030b4610008001c069034901c2c1b0411140061410486000b07403445000c0b482e208000051900026890200d60021241454620200c00082e2490240d07491400d40c591805d8a105007001c110030050b80350300c9540258000d0f29424130940d039640c030407691b0003114842c0d0720006402c0d0741d01414a061171381211403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 242817005 1250 242815755 242815757
    0x3050f01090c08180f07080705011d0906010e03100c17070504210c030b010b07050d080c160c0306050118062705060d0b190501120302030a0518030d050309060a0e0c10 73
    0x1400f5417840c1080c0380b1349442ca030014a0107070000701040100d50f82100070f0300442d2464401c098200c0d6003010009040c0640103203c0740c14811407550f050f11a640c184440608102c1590040120701d4849400801d00d040700b4149105001c909004140e01030301450030740f0201c403082c04821150040c0d43d9115903c0201c061803c4481c410340400120024081c06c1c8143d019115290600742c84694a08045d07151464403511582800b1185050200340b0340032000700c3c1c4001c07500100352942c400c51441c013118400c0c03042d40302130009884d02c1d00120b030080300945140e82c0d0000340501031100c5078550001000d0f00b4410900003c000080b49904902c60380e058100991020707000b45198420341c540d8854160400007218410611540e56101c5c101108840c07141d6400742c80041d0300001c2030403403540c3c040d58900c00c400708041400801b0480000b069105290049884000350642d64000900c0d000588650000d4505a040e8011180007441120140c421410268103000041043d4103000e018024959440c4640340 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 242818255 1250 242817005 242817013
    0x100c0f020603010909030305062e2c030f031809060f04051501021b0d060b2103071203090c050103110d0911030601061e20010c03050f01090c0818 64
    0x800503985100146000300410341012460341d12a1800070102e4000401c4107101d54105c0004428000030304008000114241c0400c4241c00c2c074100080c0d80c1a91401e44411070300e240002200d0502181200e071481d41f1006404882d007140004080d50b0b101d001c3c4e4140e00c102440f507c01c8880b103e28152020716080301000d800400e28255000200d070944008031104500c000f28942400712a507410801c1080c0c0c0e4054540c500041070038370f40061940d140f201c00c050403e07911101850440d07500c200628a00f0215a00c40c100e8031010300b00343c9500d03504104401d442c500e0b1840010f108040c002d0059650306948503d80c124090705260042d402003110303076031260052406000b02d4022004500c110124103020300b11f4050a0111042010b1411605170031200c1001610544445003006425040a04071a14280f107042c509510401c11100c1400c2c244010582d802c0c40503038107501303405a02032070240744508c16034405a0780350044042a900c20611090000c1c1d207007400148400360b00c07c00b43c5045200d520030750b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 242819505 1250 242818255 242818283
    0x702040b01091d180f060402040902041b120b0103180605090c12010f0b0609060d180b0f09070801020901090506090d0204020703050c010b03210d060b180103060f05100c 74
    0x35a469210b0f9002020003501100700f8020382079014203c0f203240f80c1180c4018040c02648188203522494050320080c0110b80303821202c03085566a0700804500c160910255503c040003c1005145021201891840c50300d0440520000d500c02d002c0c0d035540b007244109005600202d0368640000345401804034010f4010010030400d01c0c0d550340b07681744a0040460001c40d006035030503802c0c0110b40401400728807480041001c4000d94890500361020a1300c00c15002903051041c84038404228643c20340140f9801045041005214100204501400c0c10302c04413581c0725180c1e1011800c0b44074501c542804200e0000381004146859001031100000240c01d40100b420b2940c08241a6007203580d007140072520100e075881c0101d000340302e11241030b01c044000300300b5a4000c1c040a411809440c18a403003680d070005448010a18940250703004241c240900359644024080d2180d441c2c1d240c101d003030b0019040800c00500c030700d01d0304000c03819100020041401074030001019100880800e008803900c0303042c603180d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 242820755 1250 242819505 242819519
    0x3180f0501110f090a050414040b090c13020c0d300603140a030f090513020702061207031b02030403050c1207030516031a150402030901090c1503110406050702040b0109 74
    0x280c20b2042c0490401030302c5800720420449003504035003100f1f010302e15000c0b650704542e43c0320082c25003194101c0c04459242e19000c40311824080d00f041c00c1500f202088409200e191aa03500501c03103500c950342641e030f0310184480101d03060745644100d008180c01400382da003580e00300203103c8260516182c1002482036943e0b030302d4241d400c1c4030054003842d03504602680303001d040d003004150203038503e14a013140d003150a050008413008450001c0501c000d601144190442d140c4a00721080d003081001c200406142c94100100036100c1c46039030303c82807500d100d0342c80300742030000040d642600d922101404514011906101c0c1c0001d409152010a125408000000c580705208410a0481001051000b1411030405131f8060304030500d2107940359204800c001102400c01c1e04094001012170f4056540c6d119125200d003d4039400c500942144c218070300008155844915803403914030340740c400348a0495600b041f00c00c9401184911008514100a1040140307000c3d80420341c0d00c041410090340c42511403c03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 242822005 1250 242820755 242820757
    0x60a020f060f0a0c0503250c060f0902120a0b010915030f06150f060f030507120e061501020a0f150f06060f020c120c060310091b0e0103180f050111 65
    0xd45460554201030600254840c2e6014504c4800c01a042c810700c1c506000481d14090301030100c038060500708074540c03040058840c032903070030710300750000c08c1801100d1603201c41c3d00090024800403881100c5c0c2c1100c00c8100100443e0340c0c0e4086400154407640b980c40c218140c0c020f0114285c180340c42102c101c50110005004100f0403820500a140020300340404c0c1d0b07180b00c610304443e080343c0700180c094801005055404100b03110350590760b280200300764030b44d514140d0750300c1c14600108000a0a080c0c080b402c050b00011050700c6540c80032810000da00b01c1400580e00c41414070800b40800b2440401303000420b0011044250a402d107101c0010300d00c2000c0c80d03c4040f9000c541001001502c01c0c1100c0c05d1103a07041024a80051040340c094151443e204c1d11240d031034982c403011030301519020000620211002165000501d1900402d200400e42c83d00da815140b48018200408503101d196101d44e2540f0900c14104205410b50043c00e2401d00c60700c0e08405151013401c00c40707896403140c01200080710040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 242823255 1250 242822005 242822011
    0xc020d080405060c0a030e09013501020f070b01050f0a05011b05010513260414010c051617010204080a0303050c0c070609090606020c0d1202160f03110f010c02060a020f06 75
    0x1c0034006141c900d19005020043d14444248101d414400502c0380708a0305650081c52000719103e6606032b100c00303102d111603100d008407880c225440800c00040340440c0100801c2d4442c450b4940c00c9180ea201c00030000d80b8912419038a400100e040c0052042d54083e04100ca500000344411452920301381d130710942940e0f821141a42e404000c2c00c0081c041140c80611801da00500820348180b0384c581c007050343c105015600c105100c5058803c0d0200440e40122040909079800100751400301c0c541d10307141c40705820329110f02c44001240b280c1030215204184269400c0c5c0b810740d00070300b40100c020786045000d0070b8041c000c400c80110400041d944804104403000003885e5a4079170704800c80c07802980b4400c83d80d49602502c2990854202d561241d84d960702d280c022540e2048020f00c10001c117a5080b03140c5084440d007080124841200450605400c0c1000c000b1248500c1061290503da1401e11490940c005861404598440360720070040c5000c0c0c01401c1c040e001441240c490a150000103880d0141c15 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 242824505 1250 242823255 242823277
    0xa0c0b0702180f040204150f0e010807060c0b07210c0215100e040f030306030b0c0d0b0402040324020d0207060b100212120405010204050405160206070f0c020d08040506 74
    0x1810300210705080754056003075040c0210307181c12854040550314030b0100c010b1000b0b205660719004031481541511141e000b90001c7e00d56008419292869488a0320080c06100c16600c50113100158451003000643d00865000c0425403554462a4081e601104801c0300c0f540c1c442c001c02c4211040c0c250320f215016070442c40da4014211440301075800090072602514001480c00e03c14400c4c03003200682400e0741d401a510804c805022034060400f14000c01c26178100500e1b1001000030300500e15010b4010b0041a48441803c0114880d050100b1003244200e100c01050006540c4861120544034524015074014189001d40b8000e11444e4810480e0700c4880e04454090b943e420710038903030601680310b04603800d0a00041c081202a9084034015008014040c4001402e4800003030400400390181e40060401400030303c4141020241c8400b1322880c000c8180c0140b05000004070040e205011081820145445001002581d50248410100550025659403600f00800980da864603801400040d500f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 242825755 1250 242824505 242824507
    0xb0a051302031603020f040302120309030f1605010c03080f06180a0207060b030102090108010b03090712030801030515010609050402070c0305070b0c0f030c1009050a120201061a040f05060a020a0c0b 87
    0x310400449511641c025007008045c411301515004c031443c0c00441d030a43c2d40442d8861a9042030840c041d14502c999010690103001c1c208124100203c0000c0d041c0c2900080110003440c00e448400440300102d8291005e40007034044008140c0405203451b00540140b00540341129800300651090103141c0203032519941d02d0390006400090007100c0c41052580f4000f10002e47c079210a950000380900c1c8107008011200c070000000c07400d240c500f085280000d140d2100070704004102418060240c3c6004d1105403210b01403042c4507040c04040d00b450506a460548170303000f03064102801d21000f03401c01c15045030540d0030010084040b41040000078020a1141d5119075500c2c0090211410040d04081e00704180d072003440003039031503540404c80c840b81c8150b0340400a4241140d00301940b41048858002c0d00301807100e0036011460303a06400040c10780c1c810582115510f10400905035603413003588642c80c01c0240c511820b01c8039140c001d00515500301688111441e0000580360f000d20001c0a03404800e103080 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 242827005 1250 242825755 242825761
    0x804060306120b0703051f08030a08070c03080c0a0903050f0105091903090501080402220e010c0c0f06090302031905041a0906070f020102030412030305040506012103030b0a05130203 80
    0xe4140200030282040d000c0d5000507125581c0c40d60300e040303c040c26500030b160303d03440010504007042e1a10f10802c482c0480703c101c4c95a9841e21641c595210f5044c0034009008030000a0420f0300801030164082c0e0301d907841301c2c9156910010000160805400401002001040000842c0e8204120045501100000a49800e0500c221480d04294001007100d42c2044400c40000c650002c280301c048440a0030040b503a035a40784005000e10302e00c110160b18413080702991607503003111580421540103000008204075540250156568031840318014010b04100e012100011459000300101a109004407800c100003680d51084903848001140c000071008102042108914101d6401ca910710740b291518080071403000c2079042c800d20380c0103031241001c01e08c60030440e4802c00480f00101000e9081200c0098035140040c0500002e50b000d50b4035104a50010403230400e08c0d2200780b2200091035009000c0c020310394050b00540701230307039030350b540040102c40018442d141c00110110101562000517646e00d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 242828255 1250 242827005 242827007
    0x100207080d0207033305010603050601091a07030e18040b09060a15140102120a0e120d020c0904050712080c0f06060609190b070b0403020f1203160c020d080406 70
    0x4440e03001c16108541c0041c40030808100541c040d51842d1141000141e402d9800382010b62030001c4103105480308601c2c2000019001c0c7e8581e100c1e5020710026610300c04c0c0d0581c1c5110385808040741d038880040002081215a0000740103c40447d80d20741e004c4d003401981448401a1082031004482c159244040031040180416050004940c440d414040c00c01c8040d14013841090800711078054030300580380e00e00d2000410b038002c020074a0b0038003006440541d1003112150007001210500c080c80d00405080c405020800c00102c1d2450f8400380c6940105115201c50040000d040c3c0d016205640d40d000310310000c21445c0011203141c1e40280904041a035070301007032011a140117002000000c843d00007c00340025030340c40f41c0444085036801c035200107001c0f100403e452203808540c0c0c088072211a001481004101c2803820541c400c50180d0280c9035a4260088a5034603402d000d420b03144881c208000003560103540c0d10b00c221100809161510181d0300590201c2e00c86c0c1d01d0020309840a13140818100809 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 242829505 1250 242828255 242828263
    0x1031116150c091505120c18010813022202070302010b0a05010e0108010b0d0b040501150215010f0e070302070609050a11032407050c0d03020901031103060607060b0f10020708 77
    0x41d5900c0c1c0c040100804080004181d001240200d144c40034940702e0406045108809580144024428484aa08100400003140e0703001e25070064454601c45d000342c0c2c0382c0d030007036180f50300c64031002000000c049055070800c1842d21901c0e8003501003c50080001c186424544003034001d69200e60000500c3c07883e00e9003041406030b5141d10007410000103900740c41680c1d900508040c1101c5034088080e460b283d03943c02c100c0180c100101d00d02d400070b1400000042c005407520540003000c0c13194013981e0215103100500d16640c0c0e0b007400741c0d10361050071482c104100f81d9948556944680d2510340141011500d40d592816284040b406071140d83c0401403e405010411888001c12041100204070b80c512500407288500181c09110400c000b0302070000701c01c140034204507401c14441d00107582a061241071701034020340000c2c01e85030001e41f5018101e80a21104c0044030f000ba100100424108201d0340d5648001d0150600030640100040d050300900c1c3d12a40818003151714590094891517040c81c014900d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 242830755 1250 242829505 242829533
    0x91e18110a0504060905040902010e210a08030a050703050f040f02040f23070f02100e0705030304260307031d041e090302060a0225080c0d030c080709051e01031116 72
    0x4198601590100180e0704241d5a40301c0c1030341073314650340c10003202c1d070700700d00322404400d020050380640c4100c0c07010006910000d5101c2c00c8990740c20415074032825030890440d20200c540d240e1002919002c18003251070041c5500d40c3c103100410103c3c1128180c2c1e1114261000c4c03528044c01c41c002c00301040c4280101001c03880e0700080e07034900821451042c600c020b64078180c016980581c507507140300e11354892a0500c40340004e0072000c3c08803541c0c5c40d5541c40d42151100c0260316581d0985168600d0300e400e500100c11150001d806544404034a00c01103082d2402180e045030b042d40c0550344071880445581d003109850482131480384005154101800e000c0d0800314010310201401e4410000e46088505405515104040401c2c181400c4021840c120100b48608041800c0724403507414000202070341034202010366003541c0d030741031400c3d05e42070700940700340d1118020f00351710100a0454202c4101c2c00c20010a074070505140124141c04980e581d191250f02c41e62301e1010130211050310314103000c00c14041400d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 242832005 1250 242830755 242830759
    0x30b030d1409131d061b0f030712151502061e04050316050318011110020d06030f060e070608010b03010501080601030e010e010c091e18110a0504060905 67
    0x19034440031500034407416121a0707541e103007100450000101c0d2518500c40482c2100600100302102003410f80c2c01d851092048003c20314450301c0d00056040002429068414010450b464140781403d82d4042c2603070070003030102c41004100c044030011b074400c80c054035461682c00c003060b5034000d040504403006d106035003c06d82d00b0b65000d0303401c0c88450803039050311101031584110789001c2502e961400361708500c1080c0a0720650725042c21a0002d103c0007200919403540074812074510328440b500192400c48520300401070b160401c10f608803020646400910503810b2504001074035503181d40d42c0c45003204001d04183c6059542c0d4207411301e05030b01082900050711960504100540c90030f2a0200c0070310050040e03c1c10810346d0b501007400c45c1d00030b80100000c0e4040500a001000807041014000c003820403d035030024030762010015804400396003110000c0541c010303408036541491000f05902c062000c07454034886d9114040c2c0740d2260301801030240380c10309079601c5035074620303200c0020454001500024 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 242833255 1250 242832005 242832013
    0x607110105090c010912030302070803070809070e090303240307170606030303060307060c020103141302040c0e010f080c1902070608090114151210090519030c02060309100c03020a030b03 82
    0x8081d130381e005540b000071030b070340b0300201e9030940841c0c40c0840103401951401412002d003c81405070007a00310a03101d100b10101002c681c11300d96a41c400c21582001900d6114030740d00108003145035041c144514841030f20720700e0250208942d041d40424a4003c45610600d0000c1c2095041e0701881018001c03150420b80440055045040001c002502c0301d585101c1d007814081d0b40c9201c4011039020b50442500340c542d0b0000f038a03252800042c2c41ca400b1403401c204030301c500d00d4041508034442c000c4000c8803d20388180d4500c0103488586a0554104001622802e01588284502c0082c107403a000c01e005170b000541d01802d981890880b000d41280300240c40f07034034664144046070041000c0d2400c41d6600c01c2c40b04c2d45880e551031b81807020400422103103640d070340c1030b01410348a23200150007500030015561080d821074141c640d020031a030150110f1503400030001002540100302528060001c2c2da00503003c081502d225038801e510920407211002c06640103c0e8001c107003060541e4051103683c01d0040107401070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 242834505 1250 242833255 242833273
    0x50d0b0406061e0e0604090606021510090908070210020c0915031c18151202030408030406330e010b07050d0809012711030a0519020d05060711010509 66
    0x54003500144101c20000030000c810356220520640c4c1c00d4201c07200c050596592180c0b140368100141c0a5400382c0c0006d4400c04151001e54040c204d5440d202c1e20b21308030b200c03d03414240913403030010f0520408140c80d074003400c0c4804000340e07560107004580c0686540003840641d2207030041c01064071000303200c4460010301c601d0388105610080744172591201d280d903002e000410008415070303504802c94091400fa00d606500460b42500702e0040d10380c480c0c12521180c48218048d0002cbd426031208550050001d0414402b05001031020740040134400001e111503400081c00c551800303103648000c040e1050004401000300059a08138a03481c0c00f43c107209940030b1510082d610303000d80c1c0b0703100e615046003005400b900042882e00d00b90700080d140b189690000256041110341c4a0500c07038604e0061303940180d01c00c0c111030740380b03400514640820f91043c06402c082919000340c0c040c642c0d0784001a070700202102421000a00103005c4284200250f031100581d1092404e812400c458005000c00710707950240d000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 242835755 1250 242834505 242834507
    0xf180a05100506181509060109030f0f0b1b090d020a0b160b0105060702060a08060111070b19090602100c0311030403111605010c020906150f0301090e0105010b2a030406050d0b040606 80
    0x2640001c0721050342c0c082c42c6c54032400012242151a230340047c01101251403288104020301c01a03011090096080c0d9201d5107030107041003500460840d0386052140300700a0180303241003024a09242c02c0c001401d90f4011580d43c1c815401650242c0d462a180c1310442c6411003c10002c030180345e014042c02c0d503505007088600d901194080c402c0031a50f405000a042c009200e83c1c2c46035480b2600c644400c01070355103142c1d41c6e43e03241c50540c00c0040c0e102540601003001400c0c1314071032410341040300e02950040c1780710404442d10b0401041c1b20041d00d81095150080344220006100045018030720076500c10b108032071610941c07410b1801480d554030400c2c050020402c0580c0c3e105200d191100d404486000680e1551000200d00240c0115110740d548000319440402c0c1d405070740598120340c1c1c09141403190104040030607080713420074020702214210a1203d91041041c036160700c07499034201c0e821003d0034111048480e18641140d404207000500004231621654030707a004031340380410300f40d80600c000c0d814000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 242837005 1250 242835755 242835781
    0x4080702120a0203010c02010605030708160303081506040e2205030a050d24060f050f04060e062b06080f0a0206070201020a0b07090303080108060f180a0510050618 72
    0x20080d20a12403015481030300300d4280b01e40c040041d4020001c0121200018010b4007030320b114031540780f2a0040e8800012001c00c0428024941d40c25090726020040c00d55070160f900d02d0000d0041c50f0260440c84200c035450b110a80248040c0c036030304c000c42425262070160f01c0f941c8100305010700703405065002c040001403c008142d91a03150141410380c0c4401c8034800c40001000e802d0001d08601001648180060206540490680b8003da8a854240681000550b043c0c8510783d6070740d040c0d0004000170042c0521a9411154045004040c030b4503210740d91030150680c1040c40c0040c0000c280611405100b540140305100045c41c0e4000904280d40410f04580c1c1c4030303540c400c07000c2c5c044e54000884104581c07080c0010510b980c0d00c1801900d09040c5110024131a0711035004c1100071894620020803007420015005100d1041c81007420840d5648003060603401120344544041445169880c100280d42807180c102210701000e00000d142c0b42c03800411041c1d1003441000c02e2030f032012000740304503c1402c00d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 242838255 1250 242837005 242837017
    0x3070c090f0c091415030a0c2006011a04050306090c012c060d02090306010308040302010815100c0203210715090201050406050f07060e010203040b09010b060a08040501141006020f01050408 83
    0x200035101301c0c00410085486a00d6a0b42c600c2000b200000070811480c0c0d1580c4101e4101e4a03e40d6246000c400d02c1c02c012054a082d10001412540001c004121062000c02100c40c03401051000030300b0280c1d1040401d02d0907000380c0f00c18009411003440c214040d42d000b624060f5000700c1107c280c0004440b54440b58001c0c01200416005200010703800c42c8805064040710080c180103000c0751002d60f541c0c24030300255005030104a00003400b003000701d40100a546200000114000d240034510406102c0070b4602c01c00c80c0100300d8050250306624031988101c4c4a02500b00f0b0b012120301d40d0f03610414a0588010900e114150003040d107032504042c0540d0303005055070143c5940d42050341e5201003268084200c1d0085c3c01d4002c0040f81401c072050369046064002e1409640300703802c4075885031a040c00e071500b601d840030f82d41030300b1800078802c040803240700f14803454129010304000185542408a840e0075001704031005400c0c0588041c2c2084032a034108041c045d030b100d41d140200315a05183c1d4500501784900f0f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 242839505 1250 242838255 242838269
    0x303091003020c0a0c060f021603080f0304030c0c060917070b0f070c090903030902040b0a0302010203031603021306080601080a0605030303060f04020d150807090204031a100803070c090f0c09 84
    0x810384010045040041101c040c2e00508400899503031007100030004203103803141c076006018420440c501e1427184208127050305e0f03001e201d090500400c0f4001e8440c41c0c0005109404014100003400b001c42d1001000d40701805040c1d8642215500748001c400c0c04400842d6194080d5008500801807000c542c400e03507000f8100c50304501c0e13503440c0c2403c14104045072a008500458a40400031082680640c00340b00514802c0d241403103114405e408120450b662b511000e400b6800c03c1000521801660800d0000b0100c2400e0050900e95502c941c00782c0d10310150052000301d0210030038400300d580c1010f8916404040d0b51000d10580d420200441c2d10382c00060682801032426500c0e000843d03441f601a50303070200b01f06030100600c10b0413080075580d0083c0e80c45100c00d540100040840c10a80c54000c45040e40c0d00b0a100740300340b48a48440001040b4000c00940016056a0022503006000c2c00200412405030030011161400e20200b02d080351003017680c00e001140303040b0103100c01e40d03040b00c4010304540c10 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 242840755 1250 242839505 242839507
    0x9010f0c05120306120a0510050c13080c030105061903030521090c01030f0905030708070804120b07090e130308040804050301020403081209032106060d05090c0f030309100302 77
    0x511058544800140c4000e045000385594507050440308809584142c508407040c03940a11030341003890b1201c0c00800041c1440d000180c910003154402e030481504980d903401aa868025502141801007420b40c0001d03156404ca0300042d4000c1ca000d01400e030b008042210b24420303a52036502c3e02906400c0e9403000900b0f20002040c040000c000328441c3c086040d801844c018601d1400348031407901c42c0904d40203076002c03d150040c00b089a04a0303114450304254404002c5203490ba141d02c0b20780058101d82e07801c42d0a1142003201007000c030188110200d64500c102c003010400d0400c284007500010268000201220f49441000000456541c2c141502a0182403030a40e80c0c581c0e00b480b40d00e41c4501d4211036055070000400100304071400009000c400c03c0c45c060100380d500d885041076128030603004a0044000d0881002005800e60744040d0741286000b0025490880244450420349000302c480b0320389900801704159090030480e09c814403a81049015514228100c400921031500c22555001050340c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 242842005 1250 242840755 242840777
    0x90f0106030b042d12031b020d08013c030c08060f010e0c0f07020f03070f03020316050f1203040914040b070305010e0c07140a0f210c030e04090b091c02060c0901 71
    0x100960101f441000540c90f4424034030300810300699500c1c5646024000900010000580f8140f04c0c6103203071540382c1c0c02d03282c41030b4980f511410708080805c40c3e82e1003192046007200000010b800320702e0a001001003501601241c500400c641240f00c005901120224089004110401c1c0001c000c5400d50401100109e88440c3d0784d001180401c40c15602c4941c040c4a6454041540c0e04d5104642d82103034400c5041f18824004004a2440143c8611076550000800c028030a8249028404420703820a00b03000c0302d040c50790b240d02070020f50706d11801d561550680349092006020700c8203143e40d44821582401c0c4615450040e0840491200918110602e01c1c04070304d034810003c03103484441c28003502e4000c03229140c0d41400c0c4a030026803121001c8580310481c10741807081c900c0204000100d58035540f90201c0054590320155024100b4402155005503580342d03000c0016401c408003400b80c500302008004001c00b00c41501240d00e1400740400070f550191081045d82061041264a841801c0c40c3c5002e52075 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 242843255 1250 242842005 242842007
    0x70606080d0504061e03140703020418022a0a05030d05101205211b0d021507020307080319020a020d0908010902090105060a170f06010e0d050303070305090f0106030b042d12 76
    0x11000c0300d0801656002031141555041c0c000c1c0c000d80701903055043344000d01c9982030b4102d00c00d00f9881610355601c40841c8842103ca2500c4441c0c2c000781e00c0544404030213030354881e03040d82e00400310050301523582c3d02813059241c00300e0a010050030851448030f01d220219203440da076401c3d020600d0f0382912031280807000e481d00e50b201a2101380c05542605003200d50070021003522016500d419000511480c92002c0312010300782007050048a09401440c070b03248158680f50840d51008001f07060007684800d140b001c03244503200520202c8042d5018010185618000405281480c0d100c2402c5038104035030301c0003507500d5624584c112041101d11903a10108507100760703141e20b0783e0070207080b01564200801940750311a5141c039118030001da8500b201024200204810808880c00c043c160303a00c20300009148a0081d400550024290f0085807001c040840d2083e080da060358000300c41440c03003041444100300809034440f007076103420440c11410080c2c809861f20584100d07040544840c5030150152091323 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 242844505 1250 242843255 242843261
    0x5030d090c0b12010314070b0316050733110a03020c1009030c140304060516110a0f0f0e06030a02011b02060d09020f0103110a0c0503040b070606080d0504061e03 71
    0x2080b9569031035403501d0095103080c0e502c070310900c03059602d9030701e040c002c41d003410b008280502929010075449086899000100045034815032000c02480020050b1802048481d48400c5d01c440c00c00310b2260615002c0c00508d540e01c40a4032080440314180010080f11070032010554004c000c0d0b03072600584680c3c04c42c4540d8039144616415810461600b05940103140e4001541031885009100081401044184056513442207101e030000140c800d00c002042c504c109101222080d005140d0a0108600c0303070006240b021044c0d00201010054101c10480c0d01d80021000c802051007890b103024030301d000d40101c1d445a0030054002c0c100007009401040e2104031400d05030960b500076003200d0300c0d940ca940c8810300505d10103505038828968805668003d620070301840701041140024642884d504030710644012180b00002c0385d4a00040c40041550000c0d500a082d0160140c400032a0542c40e09a40600b0603540030009000c2250420050000e250000700403d03001d40c0b40030301c000c0f8040e80c03010102c3c01 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 242845755 1250 242844505 242844509
    0x30d050f0d0507111c08010501080a020c07081c0e0306070c030915020c0a08031c0c030b18071106041a0a020405031b0306060406051c0f02090103061a090405030d090c 73
    0x10603103050240600e20f035029080c034110821341001c0b110b4084211003041520865003241d00c001071a070b403005200c594442c2d0403150300013014420160a00c0c0c080c4032200e08206054203c45174541c0b0044001220f1002c0081d0710290612500700341c41d0103004400030907103c50009040409115007100f031802090301c41c54090b402007a00d441c000081c80c01c0528001c1d01d50154204052103240c41c0c400c0850640c8001c8201c035064015200440c0c1000d01e040c0242d0040c220a4a1303a2050581d100d41c0001c180c0c903030207620074085000003608038803883c1003d0302801c030455041c8010b80b96031110f81000009140041e96044940030002000e027281c7ea001c48d107002034032954224680500400500306030402c0c0045070520386070021020754803a0340d690400d21044074090701c10142c0c013140e500c400c0c440000841100c0d407081805003002861100e603580200d000500c0a0780111a640d0f56000b00c4076a18651003401d00c4000000c948941c1c5604141d00c40f10f0752406802451041140d46861b21400c0000030100540 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 242847005 1250 242845755 242845777
    0x6090b07020f09041a28110d061403150705120411060408010e010c0503092806151a1606051504050702010b0a0503031e0d0e03030103061a010e030d050f 67
    0x840d151915011702c04490850085d2181d001c00008079000301d00481e9400c2d41186000802110303100381480b0714003e025000b141210304001049141300c4051580100070161840c250340d95801000c010a2505d0400250000918500460180309030268005c040300c9452011044882081d02c66042c40b4002994080d0555804000002d0004078518190010784115130008001c000d0b202c4c40c1281582c080c4021141003800b41c11103030043c8101003100f4a014461920441c920550045550324281216100b04205001a40d54070081200f1181607141c4007510a0003140b050400001050a65510220801c02000152076400050400302a180340782d10f084002003041c020390809040183c024805500705c40d00a83c401503011480e070a000003211900c40b010700340005c1480c0724a02e03031402c541141400121094951900a108607400c1018502079070207240700188401000c22590b00016074111003a040c00300600000c4440e80d80030070342d49115411405e00650365008164807080501c15910514 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 242848255 1250 242847005 242847019
    0x5010f050a0c11010c120f14010803040f0801060617060105070501090c0807080a020a0b1c0614042307030c050f0c0d022406010f0905060a081f06090b07020f 69
    0x8030030740e0250740008406000c81c0d20781d4036607207074282401e9080c1caa102030b4010108400010991074100b032640644008804064000340c111040c040b1045200c900780d001d003e05500114051122071074820081c0d0082000700b0007081175510701800544010b02111a1040050032039001540c207901503401c682c40c0a62040c0204030a210a10303010399040014041c11104c2e101d00c000104100e44000340040310140c00900c20740c0254135007015503136030303a203d2480f5020450150746160100702d2113004180140107a481ca01c44801e881406004c00c80e403a0307900240c0986c4800040074034064913120001d821950314070300400c0010580c5400d45152007003ea0b43c180d0400000b5800d154100d0100d60600b14040c0e59098074a4009080e172041a404001c0740c560010111a10214842d0741c0a541090040086400d00031070382c903600c3e0001112a00010400c4000c00c1940c401c00c980014a007410300340703280700c0c041d01001c254200640240a543c0e0f034007a81d101070302d000804805540d00c6081c1018460801002a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 242849505 1250 242848255 242848261
    0x40f14041a01050a0503060f040219030605160804080711061b0c12061e0603070905070f0206100b090d021302030106021b0d1106130f06050705071403061305010f05 72
    0x2402007030020140441c03001040002c507661500b012080c00319100103005007055204c0c02401d0005860140040fa40f003624100c50b9900d40c1e1000504000071b600404001505161041100e00c5025000e804201044031620802c4009804402950310854001820841c11a20b1030040745c0188200c1039030f1684c6420b10425a9941a0009110100d580054510149481384070303a05e0f0390b55070001c2e10318003c024035000c04c4503604020304422070351280c0000c1c01c0703441240d550509402141c13000d9552100060444c1c09100c0c10030380402c40a0b4124041800c0400414500150f460207070040000c101d115a40c5000c00d031065660f00316403851400380c2e80d0340866603543d40d00c0029586817510114217015000b54403038441c091400700320000d500c50f0806c0d440004070260200304840c3d82e0060b2100124034000410119802e00d010078036030050101d58440c160b44040606101c5e18014090740020a12060016070300d405407070215085420880d020283c1d05203810a1410501402c0544060702c2c1c0b062500c410 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 242850755 1250 242849505 242849513
    0x305100b0f1305040c0e09070905040912020105181c0201110a05090a0e2403100c02060603101a06091c03030212090604020f060d140c04030201080907080a02040f1404 73
    0x344959010b0b500c40045a039a14028001510821540403000c291615415050340c20700110f5168083d40616024a003203895000040881d24081010340703900112181d480180f580903c030b4103400c82c03008019000c3d800c1c00f000b03400d507484407070541c0038240101100210301d0301ca000f5040030082c00c0d43ea980071519104030290040141e00704884007481005804da000914080c031100311801a580c0c074420034200d11500c0700f40d10f084a4180d044c29010711581c00041d03c11031043c841d00e2840043d035405441c1c0c1e814500d040500d042d4281c154644000e242603482100411040f28003011981d055454949416003500050350100d041440b0303201c0800e182c803035481003560681c020f11400d5042c4000541c0c540350f08460715500c6808880081d0886990039a0721410f02e0980d0291181d030005980208002e01c098400394108101680c0c1c00c41d00e00004101802150307000617655511045c0840103001035072a00302e5081c2d90b070034040c030080c3c0541ea0700c001c0b0300441011508000001c1c0305880442805007414a4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 242852005 1250 242850755 242850757
    0xf0903020d0b0a0b0105030114100905040f09140f0703231005010e0705040506162301050a0b032404050a08030c0a020c010207050102030d0e0c030604050a200904030305100b0f 77
    0x1494588113858080c003058158041c1d0144ca058407881d40345000000701c0042840540243c0d51000018003005110024065503540070f09a148101c4110205107540c4502c0c05000082c407419001c0c4841d00601d111414250380040d000c0110b80c1c001c0341781241004a500b05002440008224000c51300558000e501d03c0003c42d0461070480301280d00d5041103035140482202d0034051070141591044040040a90069061000410340790103120300a01011020140e40340e0303180740ea4071450699454804000b2a201c0c0c40c801d61102040c2a005000c458502d0449400d5420315080e00050b000c010901042c00d01108000054026a02950803947c07410b10916803d559042080d4117401449240040f504651001c900d5100321501038000b9400e01130001030345030180c1001d010901152040c001c801d8016038082041c01d000340d01801c0035000c1360341103040500750503442401c003040c2d45a41c11700c510740075200c420025603c69014940080d090721190300da034455514a9200000901010501c40b4804007094 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 242853255 1250 242852005 242852011
    0x60302091e0105010c0c0608070201060b0a03230f06150d020d06081011030118140114090901140106050c01090c180c030e0c060702121005100518070f0903020d0b 71
    0x700916601d0307a90340011503a04000c2d0700f0050101c00718500800010740120211a0004a14000400e01503211390180d01c035134000041800c0002d488440628800c5414072102511a40c40c1c501c000e2640350005070120360100140c000d50046480224200c164034000d020740d2401c20416500750f5880c081440f168024181c01e004032000c84c02a040d8098032030104d48168030074802c45074036490a588c604070a0905011a00e1f10b8442404d40307842000240040d80c12242d0302070203005d841780f405c100c03007001404450741004200c07082523031500e1007483d56900c652846e18111240c03464040c3d0b50343c0600390050702510608100a040c80d100c141c2c045000c2401244010321402130308030402c114040c09204400b55540c401c42c00591707401000940d0310b58207044004018a0b400074000c0404071072402d03c4d03940703440c40080420961581d00c1d0248210040000d811030020300e01181e0706030114001300c01c50f010844d006070003841400001c070141400c1d18080ca5a0340004d50700142810b00b22886400d110121903011 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 242854505 1250 242853255 242853301
    0x1419030606060305160c170c070306060602011503030915050405091303081f1205150f0103020103060902070308060108180106030b0412020105010f030305070c05040f0e16210606030209 81
    0x200c00003440000500e0b41507140d17006075540d48814a401030325070301d4041485101000700c4c0041042041d500d0f020420081c00118401c00000903c2442c00d10001d085404d0602c203584040d00400c4208042503000703075500300751030000b0024040b1800c0400103035420722803a4451900050400f04000352084028001501340e0b0080d2110344c40c5588401e245030480c0c152581c0c072492412003040074404050501c110410142c822012660b207404400208a51540111034028006050750018021942c3c1802401c1c002c080c142020f40c10300b0050340d03002c1c0091100a10860401c96030350006040c2201c400f25a110369910304000b000314941746e0400345143c54040780e041c0e6503848a605802d4405105104550413111003102e07000d8030f581580c2d01219140d02c030001c20348255600761000304160b51144034070040100031620015100c0d85013080c1d82d081c03a100500055006002410400040c84c808017002c80100c1d5425404884a0941ca400b10041080d904041e4200b6021410000c0d0144032090803485070140c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 242855755 1250 242854505 242854511
    0x9020f010e0612130206270105030412050901140412060b0f010c1407080601320a0501030c121508060a02040302030a150e120a090801050c0414190306060603 69
    0x4000015a825410300c1145504001c04100fa203070314189a50203d9080084d043c10800225800d400190381da81140c0f6071b0038400c000c0501d02d08007644105040540038a001e0a000e030452426803107003502083e040500710184600025651240d038070480820f114900c00300001a21141c40c0c9907015052400348008403000c500d44403242d40f040c503000c0c0c906c03404440141d4824820501e66911507008014001c8580080d00c030344038002c26482c4050000c1f602800310380e09581c0c18209194298144c070042c016050701407803808048002503484048a0030160b400038213000c1030290a031401240c0c1c4407560341c3e0214001d460002c1c45001701828480403406c465881c022600310340ca0b9403200d00100c0c8aa072100940c142c1c0020301c030710005041d40c2404041c11107080c1d800100d06200715403641c00d001c402c0315407100c5400006000a810b5802581c81c0000d401c100e4001c11181c94580e000c26810301c0396000b1500c00164841803200c40e0b07518450b2164001300060003410000d03a0b0b0385040400740496014001c00302c2d00f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 242857005 1250 242855755 242855779
    0x70204060603051f08030301090902150406030209090a0c0807081306020f0406260406091403070303050603010507032304050705030d02010b033d0612110306010609030f111f030902 79
    0x700e40700601040d11700c140061451a4a402110801800b01c0c8804a800003503e02140360b10100d810040e1004140c0e17900c001d039a9106040c10010b1910004008940d110300e800b50300001726034031501055001c0d9403801c1044082d26595910742800e147c46000030603d600010303416006241c800060022180d07a52504610807039000c038900b481c1000040c01543ca00c2592002401090140c0c115a1406020f401000c400740414512281150b00551081c3c020a440794240039480c01e0034480c090f8022514503041041d1600c03400616802c1c80b031459010009014a40850103000b030511920000b09001021a03400819600001c1d000e072100740d41440c420701503019914400c4c100c1104081401e08108400800c0c8403003504549a00340344421050b850307940d20031003c119a403c6181c280e20840c0076441c60302400b11258100352a01005820610410000380b60030000520b5200458400e5070b4050465602e8080d440007086600c24248250107410b40100c00b890207030b81c0c0541c41040c1c6107000342c0f00c16040203 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 242858255 1250 242857005 242857051
    0x1e0c1303060b0a0920030c071202010b0f030105060d062a081e220c0b0301170105011410050304060b0a0e01090e0a15020703020118060509060702060f0f070507020406060305 76
    0x580108440c903404030024003403205217250000035a0b100c655691180d0400d25562601e840d0503079030301d42050150b07540d20304000032458030131400c2e520b29904500a000714074006001c101040b2420400410b17882c2c0301c05020220030101e104403001803e0171204003610b146014001401c0070b40941e01516148110b208180400e6401c824251046514506821008260200c0e072100954421026107c080d1105030106160000038000e500030b0042c206828030f103c40000203a400c545069202000c3e030302404140214030340340d10181454400f2242419900c0351f850342070420242c0900380304264810b020310000f0030f241c8541186c441c166440d03100c041041445501110ba5a01b1a0280c080e000035514078200c0c000350000d800400c03d40e4404d01c0080390400201101062f42c026284080381c0302c0380c239902045900081044550740c420b4492008110900304810141503040e0003410302c2100e4031904000410f418015801c82d007080354040c1c01000407503603500b0018001c04059568401d000c0311070440403104 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 242859505 1250 242858255 242858261
    0x90503181807020705130e0607030e0106170c04090512160c0501232b091101231e03160908070605180102070503100e010609051e0c1303060b0a09 64
    0xb00038940050400c107040c4810081004807044480d80e060f078603000c80c80190002400903500451031a1008074403808a07a1006003507a049401060a070154901240124440042c00f6010f030707403040c0c400007103000386424103604143c00d0705449055102c3c006000d903c0c0240109500a03094003c1d08015030325912440119030103010043c0c81895400380300d00721950b1a0200e0010116811400b004a00038102c04c010700180c0c01da074152446046950f00291014407043d00c0d10002144002d10723042d46075a074036034505215030005030915012103901164140301c00316800d0b108040100c646c04a143c803850082c2e55202c1940a0030b42d0100060750a5500007545c40c000101041a208903803030341e40c1060008050b800786a004d10740c645045200761400044c0340d460501803110400c140d03220110f1075917803c6c4045070a640145d4010900c003032030042001503040604440c000114036140610031192680801e1100ca401602d03d100b000c0c1802110000c10840ca41e840f1030240e490a61304500740540c1c40c0c4d022411 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 242860755 1250 242859505 242859511
    0x2060a0f03111c0e160308030f0a0e0619020f04030b040c050f030c0108090a17030f06030d0c020d0302070504060b12010b03040b01060c080d05040b0f090c011e030905031818 76
    0x700c01400c91140212030044d040010a16603400488242079400080342290b044940d00681e000d500000500600541e07134080545e0181d01440c0501c040c894042c00240c1c0c690b00149010741400c03800499108409840e0112602d4400f8010401d8540d61282010b07034152100361000c44030b944034214000f94600741810f00d4000d8110003406080d0807101e00c0010340f04904028491142ca0007490498000100004001c81e42c05050510107900ca2401d102400c09a20010b400580309500c041c08803c07100764028094034926605940c04019541ca91800740c0c900318403508580d52041c101040464160301e80c1003d01460201c0b82c0d6200e929036a181041e10305403106681c060202ca40319001448018014141d0a000d1441505143d1400003659000000ca40c025141115424107140034020b2210241d440a42c0103112407024203412441c038000030b0202d049d0000d010b01200121090030074214002d600c00310b8000c0e04002030700c0e51291b0b4101c0f80300c503c1000c261854461441c0b04003441d040b170f800c4103180b84 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 242862005 1250 242860755 242860777
    0x140904080906070204110301090b1e090705071b031407090212010905130512070606140a090e07050d050f070f030c060c08070807030207050102061317030603030702060a0f0311 77
    0x11401d00c01206100141c3d2001006070f0700070740c84840c003c040810150080d070003021070060001d480302c425001c101641800e9040840c1100c0754501009107680c620b1000f540200c905d00703006540d10030501d095880c0343e81c0c170881400110204d40b0b000003030090f58840d104100741e5a0090303804072034a0750507c0089005000540030545402c0c00184620b11032a44140d0308203000360f090440300d03211540e8062804450340d0380f540000c0400f0030350204206040c0210b102801098103010a103080d0600810340031a8140b0510103c1074555440c2c0c8407290041c41688007804015280d680c207003016090060351220301c86400100d40c4101c210020f0030310020480b0f04240c4c1e500400000c0224035081c42180e0a15211078184c500c3d9008100041c002001c1c40c0080c41800e1007038011744003042c070745000681010030040c42d4203860754050300c113140012000c1070780c20413441d0100b08003074a0f41ca804000c01e00e54020040002d42002d00003825941c0703203070400e80e4040056030a640a001007080c4286000c60b5000c2d82141c26 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 242863255 1250 242862005 242862007
    0x20d091a0403020d0f0c06030b040b04020a0e040f2c0c01030603080f130f15030b0306090a0204090c0801060807091109100507060e0607050403060e07080d11100c050414090408 77
    0x2c4010710303020b10102c0800340904280c050b40f00d600d0316000744480d420f80c0800082640c440050415003402d02540301c114201b180c0c11800c2085a03040a0f118075a1406440d1190b0303561101d015010b0484d42c01000c0201c00b240f900a009108004101004e080300f84410b04540b0821850f02d207958070a01071203054a61144416051041401d080300035600245204061120383e44000b04035060000c801100602a050b400d08800c208108068112814101a03a0184c1c125508118003c280051107400e1f065040d0303000580412142040112075030305030414070081d400c00000245907080000e0742416200450000c20400c0008410041c0074411220129080601d92118154050107000a00107160183d207000c01c2c0c04030040c1e45030b42090400c41705000807582c081004c0c4240095440380d0840110300900408015007000c04031075030382158002c140200301901482c4204080103200c4c5005681d43d4040a004140b0b180340041c3c403940042c0240100d01348403201240c1c562405030807180c095504040301e1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 242864505 1250 242863255 242863259
    0x507141c032102090d030c1109040b010b070201050702120f0f060405060406020d1e0204080d050c03090f03030c0a050a110316170c0d050c090609040803011203031b020d091a04 77
    0x5442280300310181c0b036151076070038012000c1c01c0d110103078110402c82c070030759a541183c0c0c2d081c5001800e00b1480724541d40505904020480052003c2d01d440341560901100152140d0b42840101e40b948200316000350032680c0c51608024a0300001000304500c12640150760b807101c160f581c66a6611030031200500550b001d00c0200e4041201c590081820240103000894843d88840500610300181800075025550000c3c0400c41c4400078011082080001e02d0241d00e03112000c406240e82e809400e00a03803081c000200410b07400e603801c0040307403540c458140c19074100b100c00f414516210440b2683c103a03540c0a20441842042c500491099052074000390b410007254204030b2007503175070150f55181d05a07511501810541c02c0d03840c140d440100c2c40c490002094071403a1030b410710001d01805450180203280200078400020f402e4400c0c0d03415210344840004900c8ca10303003012409820000c01d40711b0121254a0074600195000c04e241d07107400c0c0251108005a5907401c8204080c882c00c102c0c003001800e0034031003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 242865755 1250 242864505 242864537
    0x1260a060b040b031608010507020115050907020a02090108030406080c0f1204030224180a03050d0207030302120f1b130b0903030c0102041509081f0906090507141c03 73
    0x40c41c003480e000e0030000784525a0301c04070340703048501280d400c0741005c004010010700d43d09000700d40e0300032140d100030b200e00d110100c0f4000c0d0202490103580d11900c8048006100310b07100700408080c183d00108184040e5940d4112540c495100340075460014480c900098261b540e03200c21590b06e890021034140c6084a58005940c451401610403030450140c00d0815141b520b880c804890802c104840e85045030034459500049030000100c819816041099400301003030b001010703240d522001420150f95001180307070440081c810070000d4110410701a080c440d1802008191034490581420111040507404800f42814007440c00c1545802c540ca10007404246509409018136103005000c417410b104200c10380d1800c1e40c1054104d00c40f001480d2040400c2654062802130003482d202c4d010301010342c2c1e03d2520580c2c0080342d21031114826190800c0d80108074595001e01c14240d00300c8282d480342c82d21001d0200c5100c1e013103021940300360007520f040e80b4101c0c883d0340c2826060368982c660060824803001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 242867005 1250 242865755 242865761
    0xf02031b07020102010603060c2708030304080a02070306110304060c03060311040b0d0f030f090f0303020c0126010308040f0b03190b0102032104030909020c060402280e01260a06 78
    0x1000c0f4119502c038880000021083c0c001e801420303100391280b541801ca44400d400040c03203114404107400400703503020012a28044126900640c008854070b0b0358400b0144144c2c50300701c2aa0004001c0b52038019800c002c491400701460049100c3d0805201c0c4440c1d812044045d29014040a82a40340108203031900d4605980310750050200903003803d142d6502070b00c0f000c0d400010700302c003a40810119001c013040c4a50082c0d8010241040101c4140c0741810b40c0c500a40c0c808210300000d05000e819100144074036061940808010005013501200d981c43e03282840a507006846480d007400031418021030452014001d80b803140f0140f58541ea607592149042c4005000c000040c4c0d4154041001700c0d0240d50f0200300240081486d1003640505824a8600184240041d61013081c0310b51051000c40140540803170f03c1074000d60100c0744850801c15085816640e5070109004042031602194000307840500000d02c01c2c102c414603904103000c1034040404018011200701c11403d42e400605114000946c3c0c0e074 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 242868255 1250 242867005 242867017
    0xa0c0e101101110d0501091803120510150e01030c0f020c0f1908010218090402011d04020d060e0429010b250506240f091f03080d0f02031b 61
    0x1500204140c07840340c100f603100350b0094290400c4162908014080032a190160310f001e60300840360302c141c071801904d008154038200345c0043e2105403034002280581403840504d0740500031300d298030206407011190241000701075100103400300c1e06204000b030f402800340030b034000e004056401500040300a41c0810100200c40a291584004901c0e0341c0342030702220001c148080c0c000b0400040e07071405110060010b00d441c1c100090b100d0a018001c000040c3d078045818134500c0f180201080854000f04000b4020307026107a00740303480c2494204005010344010402501940c0030307401c2c8101011103002101071401060340f860a640306100c00422030318504000502c6112441900c80450212080ca02080a0104d8900391015441300c800d0100c1000740e280030800d51800502c0d2a018511a50b01103480e6140d0070310654411b90361800051040b042d02c442e0342c8050030844208820841d103a10700102660001040ea02042e4504000300c21040381700c0c400c82e40141d000b201c00c665070008025800703045901035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 242869505 1250 242868255 242868287
    0xb04060605043501020c03031009270302151611031206010804080c0601030809190f121e0f030801060e06070f02040216210e101112030408030a0c0e10 66
    0x85540f684901c00207201802c0c04407600d1014598038213010800760324910151300180d101d113141c000161080030152119a2150140e0784044a01141c00d0a003a82400001950001e070300e076000e0700b000099403070601280d04448250f02c49010340c0c40c1d20100c0742c1da240240604244031708802c1022901642c050740e0700c15880f500c590801e40c0ba00c00d810030001d060500c2a803080b1010702022801c5460f80c0383c16412080b005040c602c0744903060b45404240d40400c4001e20071109000001d0566000380800e0502c5040008030b40c140d1020303041d80c540b600301c01d5111101000d4002a0495001107403407440307801101a200c100400b018108455516050112800c1d004101c1e8070650800071f655114042a02c1c000b1440c0c0903041104e8160075444420007460300b00058441040f0400540503410794500c11403800e03800e0385d8a001140740c1c2c0300c00b848600d00300c004004a240380341e02104000800040d100114401e41460200b4400389001e1070341130320f020102c10483e41d4001210800031460903c207902d80c600010030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 242870755 1250 242869505 242869589
    0x321030103022107060e040c030b09040210050d02040b0a17040f030e120607080a0b01020c0114031302060705010b01090e040506070c0602090604081b0108130b04020406180b0406060504 81
    0x5483c09292031029400640450300681d015100d914207449040d02c5908942003d00010780c450002584901000300300a114251010750041494420010341d14030b454216030856580e83c5a0781c4004142d0010303030503180014005110390180c030f510501028000c95001422500c500c2d00e9039800d07074080a000b0003180d003011035481c1c000441c1201b00301150061480c0d4071541554200603103078506441b000014541998419511421031340da009030b0250000700d000c00380c5030b100d4817402c1c3c00d06800c4c1c101e180040d50080c03011402c00e05004040d409030b007841d08241c0350104107583e98030540242a10460300500690403007000100c546006a085c1003015204410061030060100700064194010b504400001d91003000505c15048040911240500702400c0007a030502c0c205686845a07100140004e05080b0721202240840d101e0341c04c40350162400009a41543c0394a80655000b0403009403050f00c643c0c00c10a001543c02e025100300c400b0f44181890f65241031003082c8080000e40e41d045150741100d06 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 242872005 1250 242870755 242870809
    0xb060f03150414100f1409190c0801090515060708091f090602150903071403040806070c0501200a030e0a02060c01020705070f0b0409051e0411032103010302 69
    0x2d541c1c4100f2030340c4108000da03040c05040c41102c000b0f1001d4035801c1820300c2200e80205106d01d509040030401c0e0f00e5030884044c51540d91b000c15000381000694408070b4824200328252045c15000159035041c0c0d81d0aa1003000180d0310b06c220030034101141c60b0001e82042d0100000c402003648400100781d2000080c2142e0003a100410a004c0b00d415000340060004002082c28000c00d94107010341e041c078888001c203114290404000300350302d034030960000a00b407402c0100e0a00d00d41c9824020342c0e00514070b00f000c1e10600d1510303d02c00303015900016001c0300c80d94070382a03800c09040c2d201521030124841c103009080c20184105070980c010b0001110041040c4101c400110050391044c000b080c403405004e002517150b007000c5c50420310740341e403c1d00141d0384100c644e84240911402c00c1c058504441d00c3c072001040644800303110a80240d03030310301c1c1d500000006000300300030f004200f60301d6200034000390b08540c9400304a41070200340900d52458244010f07000c00042015207407888900101e12000364408130740b60 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 242873255 1250 242872005 242872009
    0x5091303051303050d17040b060d15150f080636011803020d171303050c03031014030c13091406180c0d0b04030f050d0213080601090b060f0315 63
    0xc141d4000c48136541300701c00c05020180e05c400c014108420b051061076032820182c1c0e62440341c8100034840c0c0c8c00385d08400d48910900c4030002c203c903408203240e10704109818244080d1628410b2901170171f4000480c40c02c00084452001520f140b1030703200c0c8414250640440c0140200c1c00e10800703010300856900107003003c50030100303100728400c81c04070924003801c0898a16010382008000784116003400441f80072403000914050400d507000454040c8068a044140740944090042d505441c10b00d10010080011018800704003e05031444140e600c034100100c1c508060b51010800c80c0280c2140c0800640000040c154010b041618480d0802e030800e40080c598052400408075001d0040000c1c010f0020100361080c4445115440c1c00e40b81040804031640f03a071140844003410050402000912040445115000b6560032428846040d5912a09907500c036070142204e000b803042502440000103010145845142e82c0840c014103182c0c00c11000c4000b44610f0781000f030000085547c03900f40c0502c19 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 242874505 1250 242873255 242873287
    0xa0b18040c030e0d020c120604020109030f0501151d0a0605010f05160210120e07050d0809030c031e060a020a02071503090c0b0d180209010515090603040b0615040509130305 76
    0x4ca001c1d500600206103520104200100481030b080c03800c0d0007040c188400b43c1d921041c0c0314152074000c40c24442c8145185406130040c03c40f296484000313030b040500819001680c0c000c1c1c01051501200300d0003103072102007080007201e0840c80707554081100d0707410942405024a0180c00302803090208800360100c4e6401080f400c110140302d000000f04144204154180f040c8603280070141c07200020324050b4204004035202c20420080900b070b0610105d01040c031550200f08c0c40e0a01000501a10000d0303850780b11010807c4801401003120b4001c0e1800120516803610070307100903a00700c3e40248812480c06006030030044503100000205502d40c852013010424446d0407100400c1881e401683d5844498125400c54400007101840c203070b01c400e0101d015070b8030038103040d0569404890603d5542c00c440c241136650303c41e02c8500b640000c000b01c10030040c802480307090752181e10162180d42c00d181a40d07040c0c45140c03060340184c540c00180c1102103a0f550010f098200b001e58401e0030410b02c0d180441c1d0904502c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 242875755 1250 242874505 242874523
    0x120307050306100302160b0c092d0904020a0501050a140f072108010b090307030525080313030303023007120b0303030c22030b01050a0b18040c030e 65
    0x2091000040c00001d00f400100c44201d100d5510301141481101280701003d0100840c0142240d110100800c0700c0c01007070350840f1040203006113010704202683c031101c80180042c580c100d00304c2850343c400a00b5400c0040101d841107500070001e055140c2070000665541d00052080c00400c41180102c041d0041410002d00c041c0d2510008280c0381c50092401010403855981c0045813040c0340420110381d130740c00c10126419601c154024940b1801030340082468602c1a90000d0b00741e00c100829820069420410703007100c80070001e42601084c1d194030401d40d0f2882540e00025050b000c3d00d00070800301c0d00c01e5010300711310f4034580c1030708942c00c2c5403028000513801420b02c28604180c9031420301c00c696402151a030380c0f02489000a02c070011070000080d03100c0c04010401d0030a0711002030840c4c0c50800c01030585940c0300b503414072511002c0d2030342040443d01c030007409014015081140d0204440c8442130035100b80f00d807510882d48000408400b4040a0000c1d101c0a00a140e1980d2140010302414440343c09 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 242877005 1250 242875755 242875757
    0xf270503091009030c060504060c0609140a06150603020a050d1812020d03060f12140a17190201110306010309020307090515040621081e0712020609010e190302120307 73
    0x80010b0940c02c1c0440c5d40282070380001d09000e0104010010f058002a403041442d400031400551120b4038208001c62035805801e40032940600e04c40c5000b0407206a121a919484d11030208228945614040d000c0344900c2d005440456014407081014000d6900110102071030551044140f4045640341e04191000c42c00b1080075070403603040170580c1913042c0b00d000f009012210300b84510034941020b82c080e04081403c0600700301d40c0420f008556100411005985540c05216029503a149080d00201c0f038001810004c0510756083c41c1c001050720500682040c0500c0000b1545540c88060042d070040003c040200c0c4c040c09190b0001900c0001c0f07104161041a40003d500060284401000100d44c5c0c90340100e4810003082141142014101602c001d071603500c500d540769550b100340c1a040035164142c403021070345131000800c4020800181d4003082e01c45c255408407056921071a06150990303030104007280c4964080c4940070007a62a601d40c01e424540680103458080300504881c00c01c0358002c1b10200 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 242878255 1250 242877005 242877017
    0x1050607260318120a270308040e0f01030206030a020a030e0a0311010c0503040803220c060f080c09030604030e040f05010806040b07090308030c070206090907030b01030f2705030910 80
    0xb0208030000b000401085101c80f018160703104898102d036201d8001c2060700d40030003000352071041c034000030301d02c107112140100c10f00086119907a14080c81c4079405030065500340c1c000d18001c50450340e100304000781a00da00030180d03030555a40b0214a002504070204078000c01d030300e4a0b403c07051840e0500400131078074040e5940c041801c0429900380c0c2510f04654a820412100300204400329090005690300070340c0401c3c820789003100c0e50030403030f45100d800304024041840c500c100140480d04072665520003210354a0b01c46d03071030b40e80c01d0283d04c81c3e004800703080d82c06030050400940000e02c10741442c842040000c000041e0315000c0e04032541112426000310115070304c00070600090040c038221443c0c0c4022075140c2090100e0540e0341e0100240805403980010281c0804d51004542e10402130300c509840140c600c3d0624a018500103020309444601240424a441c800e00d03490009401900c49003042001c2180c0540381034820150010030361a070136515400148648201e583d00c641810b032276111709075900 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 242879505 1250 242878255 242878261
    0x60e06070f03120b0607150504060e03040b03040308010605030712050403090f03060609060e06100819020a030203060f0a15080c070507030b04061803090e061306091e0501030b010506072603 83
    0x3d0848844101e0148100d406120401c0060f0f0542c0b80c0002a84455102240c0ea807a507140c01e50241003c030460440038000460301042c0949540007961081d4065134885000e42da80700c0d016a406d2005468410024080781d802d007070b540450b5008181c11031310034944010004e540700c640503541859604101c80042d1120070800000314280030f4880a40a0090302e8095030030f00c41c00060101e0350b006c00a8007400405000500c030f5600b00507904e0380b20030403202c0030355645226800003002580100e448a110700280c46c500006402c021080c502a01c02c800701c2d4440383c100e42e00341a80c203040000d00d14103224500700306640025806000e0080114030502480007581414501501075911401040680c030800d998403c000c2540041904100e0b85030f421412002d40b030301c801080421480c0100e50403c20700300305d00082d17000380326442080515080b0146200a0100b001618281ca0003071102502e04841d0340018403491a0820082c04118800d0301c02684101c00030301c0c004c6801040b5a0001c1c01030101000f0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 242880755 1250 242879505 242879537
    0x41703010902071109010b0412030509040203040b060103050730150905160e0609040b1233040b070819091118040c1401050403050106080a021503070504060e06070f03 73
    0x20891080801c445e0f00880c0d604108804906002e41c1c450b07a030590081c84082c20505029800300c64804030b01a100350365919107410208180c003000d0310707007900080c40d080004040318801c0502180d6121391126500f140c0f815807155000d100d512003942400030766261507101101240381c0302c1c0001400384e0300020407280307031200c50078202c900c44004000078810000b1142d20256548800ca8030100c0003180c00080b90300601d00070403550030307030f203041100c103403041a64140200c0c0e05682d0500300c0c141c035072131140c444180c410906280702030180c4000f029040382c2008229503070b0080005680c1700c10f1414403103482003516001542994030a5070156203000780680c00c0040380c01c00002198400010007503084036801c0c44e03507600f45980d031706101c1c001002c1c220140182080c2e100d070040350002e541040007440001e848018160302d0b045030a408900c03e6030303000c4103509220700d202e003a00d1103103507103855481c04d05240120960300100c00c01503c9500c654208030140c00505c656081d42803650182d9100c01d081285118 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 242882005 1250 242880755 242880773
    0x705130f1803020a02061e0c060108011d0304090507180312020d0c120c060605030114060906010306050a1e27060905060a050d020a0f15021006140904170301090207 72
    0x88066404100080100007207600013803820459681a00e5113036481d20749000c65841030300c10203080c4014041c00036403141c01820001da8103050310041d00080100f0034074583d01c12800400c42540000f1504180401c12007502c854cc0442d920191134140829400003005c00341501040c190811980c041c99041108081c550400a81c20840c0160816003103c40c019182e10100760402d00c108803c002ca4580342d00c00708500c3d604a04010107005e402406130442142141e14070690442e011402800207000103001588203000fa0012034002829595a4a040030780502484042c0c82c540b2500801042000038070b440465061001e1001c08542424032502d0743d0059070079505a42d1100c41080d08000912403c0e94800d02070500b01c41040b992aa030500da9840030620840d1541c0c081e031041d449040c00002d00c00f40e045e00c40c2c000d89510fa82541c204000c04030310301c0b044500c40d0040c2541c101041442c61450700b0500580f0380c00a001d51030070324000c10801882c00b11648240c100c4400c481d000f0a8a108001d0005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 242883255 1250 242882005 242882021
    0xa0e06100e01062316080c010b01030f050c0304150b13060305060f010b040b09011e02030301050108010f0f03060903030f0e0705040e070e0402040b06040b1201030210080412110705130f 81
    0x71401c05076425260303420700c0f0044c000c8201a0b0042c5000511a80140d8804074100d004640c0441c0f02510b900303401701054028400c0070f1403140441d06207918040d8088091040d00c4c800e4905140160868480752030301100c20300b940c00746a83c10f641e00c18030307050a039a0b218000c81078011800700105280d415468004d04051010303004004203007400c1c2c0140142c402e003105460944880301c441507194481d030310048038a594051100040d152203418451368070f560110046041e43c400b83c0b0b6582017640d880e004d03501e40e8100b6104082c0080c04402c41800000d54980000c0c80c1240a8a40407a8286a404194048070810700d0958070b03e6000d09410040c60030180036400c1003500e0140038000c000c0c40c02d03112a0074514010002440703a66a504070960320358442058034003500c0d0501c03490b03445010764004010f40c500203010980c030401c80281c0582c01d4601c50b182e00d521965000c114049034940b080019240c80c0c250403404c43c0c00d406000d00100e83d0b900e981c482c100d82200408404184564200d00000841d0541 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 242884505 1250 242883255 242883257
    0x70309050306060d0b1513020307030c02070b1204060608030c0601030210030b0904080901050f13030c09180f05070503030f030a0c08010308071b0b030403030b040e1f02030a0e06100e0106 82
    0x411034039a40b0008405020740c0c00403521100c55030b481e07070000019110486c00caa4000c0701d000b4101000300d0581c0c05107100c0c0e11542c03402c001d0741016001c02c2e46d07504102d00c241c1c0d0010740208401d090b140b45c1c05582c150024410000414419182c032004c600319004030b060005d0382d43c440e100400a51a11464814074800542010424400c580011404c7c01d5002400903004400016010b48940d10a60480301e0b100c0c0c000c01016280c19540a400040e150302d072200740c0342d03010444008221900107103c4c1c540400141c01d01d045040c0a00d40e00c41001841031003040d1140e000b142c00004140d10140000d20401c41e1801d041aa2450b00d50010802c981e01945031004001e0300c0c6006100081d8900d08980009030440014506050215005284022907401c0312004c04004000e0004041d05508404071000b400c58007403002c0f62100d80004d5480b00c0d074055091604850a00380120034007036500035900b0190b21400483d54411511010717103046401e45154250042c001410424045600b50325400f6180ca = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 242885755 1250 242884505 242884513
    0x4020c061009050907140d140a0308070203040e150a030b01081609060305030307080c0d06030305032e090e01060506070c030506010b0f0d0f0b090703020c0f06010f060e130609020703090503 83
    0x11488180d92a002070142246c81c802d800d0504201d40e40324004507804a0f8403a001ca022510400b02958480c0e090b400110040391214011800560002c015181614400d410810a07651400311151141d0840d4541d56042103000f80044003003494094543d000e804044004c1c1074801c424681c0c010070340038a0b40191203107483d107801070000502c04801c07240c00104901d4040443e17140e4079000f020b2881049040e00380d26103042c00000401d43c0040c040c5100702c20b400041300c00300644049058454030700c0e03611903484032080300050207001081e5014000300488c002c00050f20f5520f0b040030403d00c2c3d11840c400c0d94000100c0c18200b08018003002258050605180705600344048070740c1d180060300500b44e602c02110380300c3c2030074003c83c40c982d404a030601d200200b204186007481d41d40540258030600c020142801360b5900203e0101e4005031584c1200c00003c64005018600102202d46010100c03480d9480400004404a41521802500b0103485a842c006a8481132450f000c0c195506592242d0f0007a00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 242887005 1250 242885755 242885761
    0x103020c060609180f1c0e010801170f030313060c26060f0409060f0b0409030905120c030a081809010e1b0d0c02340b0a0e04020c06100905 61
    0x1011480c540c0001c000c0c2c40705460384d21034020701600ea0000340c40c040580d200e03003100c15290100000354424244501d0401c802d02107881030b82112103002c06907600d0f02103462800104805a00c41d1032085981c1d0103041514400c2441144a904581c0140da00c002c1010503c122842480a02d200324403031f4410030f090070b050f059080d650203401800d41d04040d0a518201b400040c40c41d49440800360914003004108002d602c01518000d0001c14a8a110b0364402e80303070440781030860070b0a00c201c00d00250940c80d00700d02c4030318260810103000b441c01104400f40c041c01c20103030f5040c1c60030450641414402c00e4800d40311032a00c2003035846004030342c90281c03017100c50000400101c4a1a9507907a002040c000c4d40d04c00308000c0114095544c8501e03aa070824403450024161070a55011814140c0c0d00d8808850350001d4070b031240316600c6401e0354112a07804070095102004440b032050014444003072030f07041000c001d87c0740e03800007800c03600300c22040319032a0044000c0025501c0c074006540d014100000003082582 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 242888255 1250 242887005 242887027
    0x909030c15090f16060503041104020a20010509031215100507030f170c070507030816060609020a2c1f080604060807180207082215020d210c110c010302 67
    0x105413258000b441b10000206080c001d44202c80300c0b9075400580103541e40d003030329070b40140040d40806c1d045209401520f0895a0070506009083c05601e02c00000c5051041d001442a18510003030039003019400d0098000000b501c0e69541d610f42a04982c071129110001410081d00c071000e0fa144d48002c1055003005600101142c40301035030452130191b0107985850162611910b80b03481504040d05148011505010030442d0059601c181c5200e00407d020a590740d07000041030340584230034a0041013540c2c20205031540216290681e10101d43c91505041010b1fa0120340844202000131180303c9c644083c00c6a80c0b5000401950007070800e0710108010f034540303e5440d8403240c140c00b03040d40b5600c0d00c00e1009080b0b00c0d5901034481194214203016940c00e2154140301c0c4c80ca00144010342c1f120308840b400543c0c0e4842c060002400070107a00541010f8408910484186581101c401d604010400021111015901c60a80d00034000d481e0b9200c2d40c600b070a2034514042c005902c0c24101401008280605 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 242889505 1250 242888255 242888293
    0x1504030c080705011d06060a08010e070603090f0b0106020d0e0306040327091503030212041a0306060409090507140d0c140f060a02010b0414090c0909030c15090f 71
    0x1907508031140c1600c502a030b00e0003901400001a960000c0e0010f00d0141421420100d40320b40128411900c4958960f03840319503074241c80c81000c4084164202d40000c200c0c1602a03007202a0341403080d103190820240c203988500101000b03801c00d00042e80840c05504c204c5030895814807010404a00820207032419036001442a0204000e05d24405202941e06000c1042401c8601c043c103200e040a024004810b11603080040d441e10059006228040181c1c1d41845100c0448040d6581b08000301820614440100182ea00c003825494005100304000640d50b00f8600c54850050311034405000104c1c641903800350300e4030900390503504c220400407004d00024140e050201c1241d0040d0700c02070383c3e41c0700c42d000944040c1030551120780101c00080c1c8000c6169065110403080c01c0121020072910142000d0010445803c88290b007482e40b012101e100c103441d04040881c1c0c40082082100c0ca0498841d001c00c5c280399080b0f14014100103a030052040d43d94050100d01043c074609801007c0500e1000d0050608c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 242890755 1250 242889505 242889527
    0x1505010b16050304150c0203160506030a0c0c020a0311100806010f030b030c0d0309090f0b0d0f11190302011b031e2705011e020c060a050d0e010509150403 68
    0xc80000072080004014051007510020084601581e0490311004030250400304804000c07407007401021092000544090b0120007a50b5000e01001e081d50340344000303071005180b50300c818800d100c4a1042c80d0016078546243d0700107103118481d450184104c0c1c509200500720714070914418496441c040000c541d90017400400107880501c2c001c00c1440c404000301e420a0304101d0620f030030004401e000307028150845801400c540c42c12008000d61641800d60004845a015040398001f1000080402245204080850b19801000c101040355500400110a060101070030307520f114640380f04006540c0c0003038485825501e1028071801c40301c8240d8006044d03011503880c2064204000580100d090f210b042d040b0500200b204214100c500e000e0840c100c4e1041714490280001c540340b5905104c8072088141c00c0c400b58164008040c2e820442081000c0c641040601004110b014008800011528028911210210720001a142c1006101d950810f0b04000b180401c0707078043c00a010001350b0003012100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 242892005 1250 242890755 242890777
    0x414040314181003021b0a050d121d0115091a06280804290109050a090c030c080105011d060418020405150f1503060f03070518041505010b 61
    0x260319440d00c0780441240041c1001207400000f401e40c40914203070160f00404c003510008001003009816002d00607590b24822030010010781021458904c1d03a4003d400c05112280071000115480401101c42c040c010008450401c0d241e450700c124401600f441c01c07a041c0034002d40e00c07043c4441c010081d0440e891503601c4001c903004800000380c8050481e5449811400f030b03000c0001d410042100d414004051040a5909884a0a90320000348211010008110181d4203040903006c1580c0781850388401064004e008110560301c400c40302d000149030030240800342d441502c80c282c0c034074100000f4508442c0c0c141c02c5481504228201411a82030070140c0c25070101c400c8401040b2402039407108902e0760762140740290090b080c80f05101d4a040003540071030001c00c0a40e010340c203010155080207002e4408019480c806041000480da5030b05181084000810019046070030303d503034580c0807540d5a42d8802100c2c0c0d00002c01400c2c0800c1020301840e0400d2480c6680d004d200b19414015054110310030080f03000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 242893255 1250 242892005 242892007
    0xc07050d02010203090a140a090c1e14040617060604060203040e09030417010b04050a020a0f1d0909060718030201141e030108071805040f1511040b090414040314 71
    0x3008580c4200100c0c1c19800000d40082c80440e42d94109401c4191561940c3d44030702412030011441003200d01c626030941d5020b03518000d01d403003903200400800310300300c03008400c006100c80c003460b0070640071009100030016651051011440c441c80c42000c020701812080c0f096004000c104802a4000150740a40d21100200140d6440d8450003500c0c0d4840e9501505840c20320401c0000d80c454190302c1b107114100207175001c2c020f030b5880010b01e0017284114040030b4040b400c080c103107060b0740f4401c80c0302c0d01103c201800000d0441074414000340c004841180c40100c154842d00c200040241d201c00003d40c0385c40c6841e202130b0420704542c0043c240ea50941c00a00da4800080b41c07008040080b03041181003641064040d5a5950312104003549030354607405400c0241d51580b40514818540d4132030139100d0354000340b168550042968902c07000d1030a5121410302681c540303050810840c0c0030b038002c10040c0410305540d07588903010700910050340c20b43c06148100c0c04249042001098100f003481490782400740c100c0b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 242894505 1250 242893255 242893279
    0x5060603061207080d0306080f06010e180a080310030519170a0e0a0b09010212040806070c03020313060305160305041106030703020c01110702042004090b04020409090b01030303060602030c0705 85
    0x2281c07800c0e00680c010b09045c810f05143c40341c0c10342c066002c001a41d00140c15170b0310b07048607140000c1d0344810a02c070b17500d08192645d00269100303003044c0411030110045010b5036152403180d1035858540d00309586045c2c1004091804108010007084000c0300f1040403610714103880d845444107000002400c1c405424480e000803901c403620b00c100304107040848000d000c100c0c1e15840348910541508290243e50140c4541c1c0388010800c07100c101a6000c580e0324100415080c0d6510304121410305d01c2c01000c405522041c001c54403541c107158000c2c0c020b051250380004413482c00e0041400c0282c15a4181c0d0285450202400b01080e156410144c00b5101610103079a203454041c0100c0083c86284a00f0340c0c9546040264101c256100d03008050303a90003224288840c8441403030103804100304a83c5e524404000300300401295156802c13032070041000420043c180750f505d01c442820345e170004108566078079807100140101501071240c400a844070344025030601640c4038410303a590b9072500603181b00e00032542e15 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 242895755 1250 242894505 242894539
    0x30c0204060b160c0909050a02040e01060b0c1c051801081b0c010e0622060b0a03120201050a0f0627091b0311040c0c14070e0114010806040506060306 66
    0x40480203141d849021652102c500d040d140d21818414011071300150030450009901c51075000d103460726034101d800740c51514500e508010083c005820000d900755203904000880500f44000f801c480c49110000d00a100000a90346103c52940c00b43c1406010050044501c488105200c8116400c2c1c01c1c202044107860300703401c0407840310001c4800211884d0005090010301d0064020400201c003000840d034040e01d8a124040c2042001c070b0a420405000c90410408034860350010319611002614444519031251500300d00ca5106100c801c01603074443c0103101c803000c003c2c030800760031081d5003804000040c2408001d8490f031f030606038108041240740e81c40031708903c1554010b100e80d0307501c0840d940c0c1000c0d003443c40002040c441e2100340c4824140a03154005414903024241c809121a40c0301d000e01c0140d9520181d40044203084614107128055001c140613011482c940c2c064001e850185d0b500303120180005015078001800d940c01142040140041901c4100c141da400c0b001c112030f058a0110991b803 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 242897005 1250 242895755 242895761
    0x1502161809230304031a01052b05010c051804090b0a09050c03030d05100e04150e031306080a0b0301021306030b0d06230108011e0213090204030b0f01080a03020604030c0204 76
    0x2c0d0340c0b03804103916003100e11110000001001101e00c80c9044082c01c1d05031042d080c030080b40900c1000c0d041070450f0101a500100d00d0002d01113a90b40740b5180c2c203a0707405a1109402c44014018290200d0400100858849180c80207010907003401c58080c071002c0b19660301d00c00952006400500c1454a07203920104100c001e20159008000240c101e0f52912024240c0d10080e0005070307000003402c1902c01d0301060b02c141d1032001902c2150440300140b02201c100c00424010030b0100040380c2c842c04180143e03203600742d000c51030000500c89540c40031520b04041c08040c0450b1003201019100340e104004134543c500d040c40c10401240d500c0d0400083d40036080000c070710b411300385035401003483e0f01e48051401c010441e59008080108102c9800d4071070307030705c0d9103101d4202c2d00c039003a034808200141e60b161078401c64690020480340c03600030014165a6170390030f01001a600660800c4401221401c00c0000c2e041c1051705050040c46143d0081480401684019441e00d2010b8000b070104403201c2404825511030390 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 242898255 1250 242897005 242897033
    0x1a06030c0904140f0f0c04140a0302031c020709141504020f070c15050702240c2b0905101d090f0a0c0e130f060f1502161809 55
    0x1030820f02c4004011841949141000c40e02c0050125203c4007080e03a164040070041d11403900d44a50071719090030180d041b40c15100502040d5445400751a012006031014011202c41202255607410840c4540d81e0182c2416115004451003e140036000c110301822808000d0300001042040b41910500398045400781c07082c4100c404a060700081c544040141520a1000700c815000304d10b00c3c1c0e91100d0030122801e10a80401961040c1050400ca150b1403203803202c2141d014405406038504428090140d0625152124000700300080c00100004000074040e0700869a0310781c074040840504090000b00000c090704080c5040060000000d20808030618608000c0400208042d0321480c0c02e5001462050045810035011030801c00f111102e54092811803801c603500420b2400c410840b240c0d40c400a1180804d0320303461350340761000002c1000452034080060300e503840ea940c414002d01070002c0e25017040c5801c82c04d80410580d41c10402c52a900c11b243c545940340e0840850704541500b82802560440 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 242899505 1250 242898255 242898259
    0x606050f01021b04020c01021b0c04060b040302061c0f061a070b010b030901060906090617010606020c12071211010f080108070306090f0c1403010b040e060f04140f0304060908011a06030c09 83
    0x250745686114a89d02c0e580c0305800d45003158044400b1000b0301c01568185d1040c03400d0311400b48018030040c0b070110003505074103641009481880130b80d0441e030019a2030361908844150369401050001050448000c2d204409005910713160a09a59502c4000c042c1449050500b01c2c012011440c08002034101800629841505021468441440d00005e200d03030310400d400344540301800d014441e418000c2c2e00840701c4503009030000d40441403d1142c0d40f012102c0005442c004c000000c206c03851400c0d218801c0d40d018070000c1441300e21580014003091507222150f0180241c40c4010010341e14001401c10035207501c1500440c14410501d82540e01400f290720003486606130308000b24408200302c0d903c003d02d01085009010681144007480101c0d1442e00010307515400c5800091404050101007a400c144100e24080500101c100300508100601000d4030050300300003010090554816444406050100000c002c400c0c004580d2000300440c40c1d00241c06a400800012401001d08064681c08000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 242900755 1250 242899505 242899507
    0x9050c070606030818030a020a03030806040209061314030a0c03120512183003090c13050403260402100e0d050304030209070503070804080c010f0212040606050f01021b04020c0102 79
    0x100c2c0b13400c4003990083c001c114101907403004620040c2c58001511802150054500001c1504640302102d4010000b01825040ba400304008841da03240c01d00285801011234075501c06003405c12290b05051311314200e145100c0d45c44a918032022031400340605044036131100442000300c01440c230580e02d60280c00015a2800502d50401404a1558410350061550030003a9070342008080c0c0600074000c410040e62002c0e624524404406410500007145c1001480c0203c50300804400000b46a2800c0d203034501840070b80754030038441015044540295018110b000706a41d040c0802d0300407008860040003c2d01c036a80c458254202180200142030140b040034040610720401400c0c100d0f0f890740b02c0e20080380500450710001d03c225109005a0b0f00a9840f983d8001154603991907021480e0000c0000e0002c6558520030340c408042c1c41d01c010203068804041200b003901d484d080410885d40d180d406640100c40e40c040c02e80f0303960b81c0811f0240200c00320b000300424540301440031500a0091482c242c94540c8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 242902005 1250 242900755 242900759
    0x2031c0e180402090c03240609030609280f020d020d0203010509070305060a050106020604030c05010e0102070c0302040b01020a15020a02070810021201142d0a09150504090c09050c070606 82
    0x44002001d80c4154002d4810b51540d03203d41403468050710040300c07908403944040d0010348010003c41c50003540c800d001008281003902e10000241041c0302642c10303003c282c3c00300f1200010550300340324032102c40418203141821001c1c151a142c5400d82a504024450005040003c046603900c10403270304c8150f000b070020021880c149403015583c6401c0d0100340c80502c602da0000c1c2440c400c030f008003410b071409079026050a0720390307503810359060384840700445081d500c0d021041c480b1082480030300750f01c60103a1103405200746140180030407218509000c6046401800c2203c01180e60350210200844e0240070040e9940b901e09000c0b4140005078211052034058080072520001054004c0c086074801480980f102d81d9071041c0004c070b808620a03880e60004980460b8454444480703174103088030b020703010b04190140000c500107000d0031469048000f4555540c40b150b2080d103d03045200c006400d06903030411840480d40c03103002c4055050b00c0740c44034064a0300c0010355000966010340c0d0f00c265201c0410b1101c00d03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 242903255 1250 242902005 242902039
    0xf04020f160b01060e032121070c0c08060702152208130509070905010f120e0d02071e0e0405010b0d05030a26270d030603021c02031c0e 60
    0x41003c1c4203c0380080c40703002c0804000e06e00802e401d001d80c032420014403000c402d0031080040715004400540709031103103212400315111500801d58840c0d145039840c014200714910f400e0305100102c0e080110341c0d80c1b01804000d4042c1d000600110940c440310320201e4103a8468903140c080840f500080120440d040c0c02100400c0502e01c00307040c1c00400d61100d0305443c0c0d160801c0c0501c8540840301480020f00140040100d54040c120000160b08549400c0150ba1022500d503010b5500e100389010030f56110400c13120705150f0600c0050040e1500100001c6d1096180441000903075090084440d0103003010041410014254451280b105000c1d00500303000f1058100540c03039401040d1078170040f480e46d00b04491011242200c035400c55000d29010340c030b9038450700e01d201c03a00ea15810200d410b05408a41010903030100b0044411650340540d00490b0403425031040c00101004030307003041c100302050307911000141c3e004035004032100700750f80305000004c010420882d040e207454691250000c03d00039002c0118 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 242904505 1250 242903255 242903273
    0x1090903091a371d090408030a090c0f03030f091a0406110309150c010c210e01090b0108030c0c040501031a070c081b060732090405070f0212090f04020f16 68
    0x5880c00f0303060b0707a2814005805000b4020411140201f9006003080012110400369100e032480500074881015595140d40680d00050041e41064000c608070340f01702c079280da6202c0c98400140c816006c1e0148400300765001079000d4091030103000c090009021000304101c0c0100142c2e84400740003030103203069114003000000264001031558080303500703108407607100074001c020300100203a00c00a084c0c81c0c3d5511074440d40c000c00f20410f0100c219501c0b8400d000101c0ca00411403406001408041e40c0d039400c403101c0c84c4ac981004104024043c3d030504004001007a01242c207200c19440c154090181d0307945002c0f08a0307800d9065007004100d0ba201080114216070848049030007144817030112101074803030078401d0320030101d004400c1103440040c41c0c4200c00c40341c20702460325610702ca10910714240a1000e0000d4140c0f8401c4600400040d030b000321002515504100c2d5903418045003800500e440c1d030b41e034080303440c41c001003802a01803500010700312000399040f0102d49941c06604c80d0546610700c40d14040c505 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 242905755 1250 242904505 242904527
    0x140f13061202150906040b0708090a0303020c030d02010e0a0201030c050f030c090406120b0604110403170706230a0b1c0b0103030f0302090d06051e01090903091a37 72
    0x3d03180c0b040002d203011100d801102c8104034001c0940382054540090482a540069403c0351032500034400d002c04c6072680d600140c05144640c0142c040c00104000b458075200901118504680c100507107014a0314009c2055010290280790209a4807171203d029981f511580b034043e2031100b000010400c2c4008541c000d0040c04c4000c960070310080f507a8903804c9181c914028030140c92601c83c400030901a01c0c00d94040810348820400050070540ea0b5114000041c042000900c02e00100013200801c00c0300d1842024412018a80c04020741c03051703e6503110329081c000701504440c59989080c3d032000e6a900e1040d0134601b000c040e011800688501d0010002103085c4401c1f40440d075032400502c03920340a03000380c50301228050010a080b03003032602c4820140c90301030403100c4800410250108103844084045002c3c20040d600072420912626004000901c03640c407400b040210000c00704100342c621000c0b502440716569138101004410800c4080c0c81e002d0705d05a41c5149140e0b450109030f150441e00d00c0f01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 242907005 1250 242905755 242905759
    0xc070b070312020418151d270a0803090109080304030f0e2205060406170f15060904020907090b130609080102040e040803040c210b06030106140f13061202 68
    0x5100c410b140305140981c081c50161703440e0004100b4070716010060a5000419007805c00744d0510310a40d030b812824030703050044809011006441800c1100d0ba81030312514032075103203003042d4481d0300d01501c034070013034440014000042c00401d000002c1485080c0940090b03224907080354410380d584c10b1607d00030706201c0c2d422558801103032a5416110092414001091161445000303804a0341c82008119005001c01040554415541c2c54045444021055041016130150300240341201500100328a00341807a4140c10702c11030241c1c20402d003611400005500568142c400030342c5520340394400d03510044241c100011940010841103d07810b0013440e2081101c2e42506c0d01501ea0745c803400c0c56400d0344070760b00400c0030381503050002c01c00140da014000c650090181c640d5400c03c5444680440c10040200510b9080a0b0710842900a01060380130054220341d0860007040400c0c48c101c0280c0c5900410a255840f0308803186508803a501c070b0040b0b6146c910407d07001000900c1e1180d01220280d21509800d82c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 242908255 1250 242907005 242907017
    0x30a0f0804050a060e040e0708030a050d0608030a030902360603010f05042003070305030708031f0f0510050705070b0d0f0e070314071a090a03050f1005060a06050412080c070b0703 79
    0x8081c1040c023082040c140c0741c145020b9807810406590a80b044d80c0030001840d0942e54940700060904414070240c04800f81950700030512280d20300410000c0080c0d500a074040c1c0c44250303840c0300001120300310b03002600e560103040141d60380c0302e5001900411072b00000300c50309402c000401c030400004403e401c1500e800c9081180002c1820001d00d50398104a0100600551081004402140c0510013031a07002c0c0d500100f01000d81150294a10540441c0d0b20000c8031070f0141c8011b10161401e44074001d40c0d9a464542142060320035101e083e51031660740b1031081c55003400942c8035900c05498109000d0030482072024004bc6e080300d41c02c103544445500c4280c40105600081c07003000c510210b0048100c4100b038074100740c1448890b407444440d502500d8001d80c8011032850000008806100380410048000060404624050516000c0c0c1e0301c010702240c8600d181c40e10910403207401006517010340d140b000c6041114212854002054402c202c010b400c10b01c188040003901900203c024840207210f1365840d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 242909505 1250 242908255 242908271
    0x60e1c031e05070f110a0314010203010f09022a03040906081005010909080a08060a030b0103060209090703110708070c0504021b0d080708010510021c2c030a0f0804050a060e04 77
    0x4941c240944400142044600c5011001051708403446004660008100c010015a0b969920030301150001100c1c1c4c4903500800100245c0c8442da408400500743c5035030075450100c1070303144070003001803080081490614a900042d50317a0002c0090f01d0150545050170022262180300e030340c5e5a09141c1e101202d40500b4000049041c00c001d006900c006580a5a0300e410015045020303200c0c05401040c1076003100c102040000440e25070f2480a0003140290401a9505601d4090200029005240d51700b8982003042840411092000700e41000360041c01254460400e45400c1c2e100d120581c0c000c41c0d000d030000c21003024103170f09000c00010002405003215481c030344100e819203100302d04441080110b1394800041045003400d1588012491840c4146c0f20181000300b0111200f04007400d003030002070032000d030b0600b410758400b03c0892a003500c0101001d40d002c22900203565400c41c1200140080341032001e106c01c02c0624400e40300a088014840c41c482d07600c581000300104103079500540300314101445 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 242910755 1250 242909505 242909507
    0xb04060e100b0301060f0608132a1d1009150909051513020306010e090102130608070f0305100902090a03050106080a0b0c0a0c080f120f09150f01060e1c031e 69
    0xc250207c811680b01c021103a650070440a41c0c01d2070841d419a018211307030703c000c0240c400891300308548458621592141707505080d070311810485d1a100780302640700340e8000c2c080e0120490340d044045403004c6901155440201108100b0000c0b20743c8091246800c4c40c0c00d140400a0100d61846000180e0210004c90790b5550b1b41100c100071b00b680040d401d170304140c00600c000b10480d203200764000c004c50000f5160500389011107954101640c40100002d40c2d85050003c220b91006550698140c4c6280c28007140c100200905034015091240060581c1e0005001030b1f1170b1108104040210381181c000c0012075500d01036661500e405070700480b041c0c1072034000a9484c0c000c0e401a14400c0c0c000d07a0712078174042d442d551201d116034004240207811300d005000c0c03074105400128482e171185a904c44250301e90300b0410040d51070260000b04209045445204000d40c0901940006044900500c0c01c0c00c440c460041c04903002c503202030700038032090052107150030600d5046081d400301c520405048200171880c1c094 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 242912005 1250 242910755 242910779
    0x20915030f0717070b0a2f0d0206010501030c091502070f170106061b061a04021606050601020106031e02190b18060a02070506070204140f1e130b04060e100b030106 72
    0x174012480c141400010391041c400c1000004244d81181040c2c1003100c0c000541031149003180300a00203512800c91004441d03414003800e80149002e080a02c500300340428090403042c1d06000301020921180740c42c04a07980f08000e42c100030321520108401382c0d40c850065081100b40d0b02e412000640c02c0c801c0014406115503000c000c07806128030654903d107020354400d8060014484480c100c2e402e4000051015920f40c80201805940068000c45074001413a1000c00c2d504000c01c59815a40f404600300040b031f0f82c64030046901003148403c1034000c1e111344005500c10760100f13521842e081c0350700408985d05901ca4020701110001098252007154910304200043c400c2c0c003a95001a040340c0c404110600300313030006d052040d20040c0040f503000e44880d040f56051108071200078840e16144107001041180401003142c00078031742048032580c030344058400b80015280c00000c0078000c03140001070074040143c0c403000300420002c05442a004071081c100c07002d0580140351910079483c2400005130180303100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 242913255 1250 242912005 242912009
    0x10e0c0a0b0d09060c0203070204052a0d090b0f061c080904090c08060403050a1206050108060904020f12060604150e01030201050a021c030204090507020316020915030f071707 77
    0x100030840090510100e40031907080807040c1d50205072601d4100000442e24000e0407810b03a0258010351b00d904580c0108401d545000d0010586100c100d4140341010350501c6101443c290701c00341d01030b40c0d82d4103185007178010413901001420803124a42404100c6000202e030794040d0004072250802c941004800c800d12254a0074002c0546400b00510051030400d0340110303c0700b50041c14940000c641e40e40d002c83c01d0003400c41c1c003100024000250801051f030005071419040100c620108600f90400f00064100c0c0c1d405040c2621a400780380010382150b580005d0b00030154009041d0180c44420409807030350325441a10681e00c02d1b41403800e040d02c44405951031904451b0040507121140c0d18680054aa81d40001c000d501140142381d0058882020f484508017402844d40d80142e6a80c0350095040444101a00f90304c11500204140f114131003040b102140034540440303a69005d80c9400030410950040105150b8060048442e60070421340003280c07035802c403a01e43c8000202c1c040210580c5440e10300e64 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 242914505 1250 242913255 242913259
    0x30506040b011d030307060f06050102060106020307030e041503020d030905010806060a08040b060d1202030408010f0c0503070e03011e09020918030d0f0b060714120f090f0f04110408010e0c 83
    0xc1010f10900340110900c0c0d206000601664a00845502c40906480d000610040069111340c420881944d040041c10700401c601d00c0514281180c1e50b80082120142585440c451070b01c880c1042da40c0d01202002400840d40149200312180440c94040d240188038402e4501046955000482d5410081c0c01c40b128144155103101e06581d84d2340d2059180c802c060032042c1c1105480b10400d0000e520700c860b204040c04c4a030010354031580b6100b65142074502d003a5802d40340c54100030003c0c60032500041507941040d00c0b801c0c010020140500402d0051010b220358540810103a44000c0000e01c1603408148c0e0b1500031b0b0b4518103241c2d9000d41c084510000341d0420122540204201054111b099100c0c07240307060800320105244c0350f91000142590404103094030407215200414007440000c01138001703c4210f002a850a01101e40d20603010390098030030b2070f4010103510501c03941d070340c4d40c3c40350324401401e000340108072aa8190f6401c1d030707103500140908580b5600e0305055803051000015011542100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 242915755 1250 242914505 242914517
    0x303141006080405010209040c02060103050709021305040507032403020f0307060804030f0201140f07020d0206090d0c02120a2402041203050703110a080a1b0f02090618040506010501030506040b01 86
    0x703409801c80300a10001c3c0241c0e00b82d5420700004141c0c0d901d5000c2e0034010940b640c004c1800794150701b000d6081c402c5c070b40c0c4441c141d1403040100d0b14842411000c030400304c85003103500041070342c0d0326681900500004101c104072111006030400c00e04484202101c2035a00035500c60880301c200b5000e00d55a00414081c04000c14180c20015000070b205140c000041443c0d8030002c2600b03070382c80900c159200c0c400e13210f5400e4400c00208002803e5410031035000010132500c02491f890403c4082603072034050200c0b001c000c01140081c01000d54854203025516000c0a0381180c0d411042c0d410700140700303030001c40303400321075040d81c14012004050f900a69055903000648034401d00c05c541c0d42512254002c40c021401c0c005070b00080c00390204180124100743e4051401d15646260070500288070344070f41d14800c904000c4103031503100070400c11a80070020344d5050b1260509a1500c000007050b4800c0400b001465a012108010411401194440c1210340c01e81b014400bd49504080009070740041040307a0000710 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 242917005 1250 242915755 242915759
    0x160302060d150803030114120d081f030b09100c0f090e0a0f0c030c260a020f16030905030106051804061a061611240c1204080a03031410 60
    0x910380d00074080c0c0b140c500d800c0c41640f55290961411900241d00c40302da0780c1211600010141007490000c514095500c014000801c0c5014003c0c5c81614040c084615044280c5003070030a81040d010504042c6401440c00c01d40d9182181d4202da8a5203040300c4000c1d42410100c044018038000e24084107081181d485014206040c10380c0140c0360040184901555611078020b112030b4945880740400d402c00795603002c0341d0f9042005e00a8155200b80c41c10443c0c100c141e203241c000f5400c2141c0e111b43c0249000b02c001d41c0e55209481680082d00a100000c4850000144040e0400d600143c03030320100e900503402880596a140100a100e807040c44160351403020000000340000c1b550b80c4441500003010258031408044540440e506401c007903000c030b90100000c0301c14010b00030540700c94410700c0003c50303442e4045410a0050104d80d000070350701d00c1d4911404106c00300803041c2030012a80007a0024180da44482d550040710347d40310543c40058020a180590705010540c605801f18401d4507050705c1e00e80301c2c178 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 242918255 1250 242917005 242917027
    0xd030203040305070c090b091617090c041b0306080102040605040504240906050909060402060906071a07030207030f0c05071703130f03020111151303020c030a05010e16030206 77
    0x540010021030030400200704013070000340094114409850080701c0041c102e62401c0a0104a040280c926000350780c52010310f840240d40084c1d000d40c001c10140032101c081d10340709041b5140600940400307520505111100c01040d03100d58080d44103010035078041c090b040e074540a45080f88034901843c0000780042005101c1814035400c40d0418a050b1740d4031944c0450020300407814040550440d40082c2c1c2c0300c0b0fa081000303140070002660060400009413545080550000e005482240600c80c001c1074007081c01400e0200881d015228030206040c04403207407500c0f000040c001e511204044020030700c41e0b940c054a8601c96103042d03001c194810000c0070203038100005030080d4401c1400240e0140f0042000640c1c44120701c505900600441d04681c1280f411480003519030380100c0c8000146610404100c0d03041c0404285054120703045420600c0c00c11098202242004a2080682d402d40714104001040140c1540040055840a000e941064800c00c84a105080143c80065404413092011107030340 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 242919505 1250 242918255 242918257
    0x303050a0c0b0108010c0201111c360309081914010b30160e040f1b0602011a010c1209030c0e0a050105010806182d0105030705030604050d0302 63
    0x560369003801c100744001580c502603030740e1098011081c282d444004644c0358a409008415404441f408410b041071071504a09280390090044241629110f42104c2c1c1d01400d400c40c5145420007001d00a03003450341102d821011541402d9040307000034020304001680c0c81d030100f882442202041e10000a000e01c81d00e40d0107510701803824808142d5613900c1303070368981e5079040c070711070000103241c03005110002441ca15069260445a0260259000300b4000340d51030b4000c0080b4801d80b89c001c5042e410070388032404d0520a0040e4800300034580310103820680c1d40407041210440458210798000d118266004a4444905540c034240e580804c1d01e120182e800500030a00c00e030544401e84c58541c0205589840740203211025074460034403801844148402e89005000303e0780501020309003008541001f201144000b6545401038030b200000101003940207900d5100c1c2d85d1002032160000d0382245940d08401c08243c020f21849210717220740c00002840d41000b284051007560032401400f11401851010360203 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 242920755 1250 242919505 242919517
    0x61b0501021614071a160303021c02031f0501050906030a110703080f07140732030c010e12030f19140a050601030908090d020d020303070f0209070c0507030305 70
    0x2655024810120031041121410980e140101860300700d205102d59440c0c1401c420380c11500891910241801c0b24036003c1049910b680c800c0c0300f08500400c2e040c1003c400034081c21b00001b03202601c0510207021840e0f80d801a6020303003111400a0449000050381d405000000d21402e4003203401030041c80c00918050001d1a44089041c201140c68410064511165480104200c02042c0e41c1014040c45401b0001110752203082c50412070018800c0d020240300902a0800003800051107060420058924050f11190303141551865030340750f01c91140c055220b0300080c0d50f40216600c0d0018000748010300090203034101034070302c450b64a5500e03050512204076000030800d000104014105040b202003500c20b540c009000703a81500103504001c003201082e1280a0301c1c0d54105424a210a40803c0e502407c03a1408601282c0c00105041e0798030100d80710190245001e03505000210720b903c14400080007140705240300302d46150752965002801c1e00c0d05190503e003d06035901036101440024011401000c0d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 242922005 1250 242920755 242920763
    0x1b051207020f060406020604050610030c090c030e011d010f020f0702060f04150201020901030c0804030f050a0e0307080601030525050904020d060c030c0f140909100305031819061b 79
    0x400c121094010800f55070007079000d03000583c001c40402080c030405200040e0414841c11807420340610b561540c00303035207440c1d000b0200d017a540c59284260b10f500a40c8544409101c0300024800035030400440000003220720410919075080c5a01c010300310425108a4586000105000e0304042603a000e1008580160405640c114003c010119100d0640061001c511005500259a94601200041c1502d18013282c1009002d0103074103100000390865400d0390720b9030b80c41c07038080d880740c00040c0111125400c414540d900b43c01036800125070840086603180c10b80f170059040b1502000c034842090194401409251040d0140f5002880f0074a07203002010f07007040c0001c013030030b400c0003a9407030341002c50300c81c4504140400e0384ca101f8800042c1e000000f02054014500f801110000c44446100040c07280010051040040c3e10002c0e105298008541c0051038000040700e031106038044298034224a240c0840e8450440004a410900c0c2e100e006a4142e03045a51000300c0480360000c01912074103000d40c221 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 242923255 1250 242922005 242922019
    0x301060305120d110403020d1203110a020a050c01140406030b010e06030c070204060e100e091606050c0709111204020a03150c1e0c020d050106030803070504061b05120702 75
    0xc03880c10030030444070b5078100c00900d64581c0b02140a00464110709800f01d0b890506000800240c2d603582003c0003900d8200c1c0c4018840c0294070821401854009030001c92000d0215892341a507034000707860809107104000302c0300c09910310030056502684600f18102c403c1c00801050154034800c1d0445100300106050922490700800e0005005030022680102c51000101d4200c043d07181a0107000c008204500010f502414a910031560090403400f850340004d41c0a801704100fa0380c04c010345500031080c02c82001c2c2080e12501700030513590001826002c039100e0312030301013420815413042440d401242c600442c507280d10003000030900c0800400c16a444004043e000010070030001240e0000b0040200c00101d900b12090081d00c01c0c84541c1c2e10301658109040b0300f08115800940514040743c048907000264441c52404601510700e0750070047c8036000220074130140c0f41c0c21402030025600b079521594500c609410f042ea10640c000d20025015038010035902014042c1003004004050010703182c1c13 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 242924505 1250 242923255 242923259
    0x50105180106230d0b09060a03020604050d2906030d1404060f02030d0e0d02070609050f0603060d080409140915150105070204140a0b090103030e06030c0d1802010f020106081902030106 81
    0x310800390007182c881d8000c152960007108007446c10550300d562003071044403081200340c02c40d0003094482c00383d80101809500485441c0382400141981e00301600c070070002c00c203020050020b64038000e034400c0d04d01c0c5010f44504c0410b89100d038020303040d4009840301005d04508051400a040382d0b844400c1c1c901005501041141c442409d00b5402001d0624845034001d00400450780e200900d454129480182001305611081c0501c4d542c0481e100e1040800710741c1192203844600c0007601129600c08010442d5500140000b5100010b03004100780d504001410901c0c0c3e529140e0294440950303581503e003100d004070015035542e4080c00f200030a14810700d0014100580c81c0d001c102100c0f011000c1c080c02c041c040703042103d40b072200e0248150f94401550140099407450b0b07006481c1412404005102c0c010101c0050f03041c00764a002c3c1d400090883d4414011025405000701c0c3e0903c031803a0036800610081d006001c42401405120200c46000c0000c14403d458002e08455104c407140d4201d90554a8405c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 242925755 1250 242924505 242924567
    0x6071103100c09050301020703020307060507090e160f0f0c02040504080f07140c0f0109060c03120912080c03011d1e091b030a030503010b03090111160303050105180106 74
    0x1d00d49640040c000041e421898400207042031642d40c0c40984268010403480e40042d901100380c441d50342d40060027083c240c036030f450260b55000b06504001c0031000c1c80c004005110104e040010480324181d2140705441d49210000c80b0f400403011300038401710f00c0300b640d90001070426500103035205014240c660300f030100e01080d07514107900c2040c0944800f00d10700901e030040407040c071241d092220200c82000c01a0a401e0020b05550264850103041c0b110140810080c54040e00c0c0082001c081184200111003051a00030007502c80303484454009a038042c005004c1c85118030480c0e058620101d600b440d00d9640c210094001340d8001c103500542c001468001c3c3c0007a107000c03815405001000c01600911455007480c08043c00c03104000c504c41d600413484403021a400008490650319041311a554030b5032201d86e030901610200d0054400b8031400901c4055240303600c106112541d100c0d44d000e01442e6660410440c0100c4582c0da01000420910f0040105038060000030380b20b640900c1e40901d4480721000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 242927005 1250 242925755 242925763
    0x23070c09020c0c01030e0d080f090106181b08010807090b040e0f30040909111002011508060103020a0504050402030a05060408040321020d0311070b0a06050301050112080906071103 79
    0x302042d4940d018045450301580c05020f55003402050b03070000c280300101d03018020590403000c2c02041d0a8880f52002ca130581d0000e411180c050010404c502c100d10040b003030000c1c000c02c2440520220060006020520a486500c0b520704176007500d0f0041640c1810b1040c1040180403a12145034455950038607801c0f08281804506840c2d203180d0042c000c0341c3c40c079149420444040d00c90000c104050030010546544e903c6c000e45040c2c1c0c2ca400800100c5400614040620200003141641e020304020140c0c84520b42c1500030a42c8410008901e08030940c1c0e030070003a65120341c00cac00007d43c0004440c40c140400d04103a803003189e0041c0010200d880250098a4450501c9000e4406840711034000400f4824421400341603064a4078030480302540902c7c403c4c0c000c0d100c0300d00c110440105921100c5040301e410250b02900c0301c40c0e80008101c0514100000900010052441814083e500300b00000405a210b014000310030342e01300c40c89500d0501c001c41040340541c0861000c6030941c01e90001810f007510100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 242928255 1250 242927005 242927017
    0xc120717043e042309100501060c050601060e0d0501020c0c0a090b1509041b020120070b040b06060c0d0503061c080a0813122105280b040203070203071223070c0902 72
    0x202920b07922a4005200e015241e052700607401b80301c4c50130440400104001440d90443c0ca052410507180b18819001814020070400060525030011030031051100011a601900d0141101d0790a04280e81d00d9854080d11aa60019580500355103841100034520030000e00144034014000102030400705010041c04212480c400c1c0143e6451100c400d45229000410900e007440880403414a043e541e511941c440f1300502c010306403004000442d0281d1282416150705110500580700d46d4005e60100a080347c000700d49241c42464108540410b45079215201401c02d40c214038a580382c00344441c4141c1d400755000e468449034102c4a0081c00c0070440710800907034940401e94421888840c80502d191409040e8075403c0311240c500340620000a03c41208030b0000c0300011081040f0780040e1041d01c005090b802e40580c0c000c1c0c00003040080140d070101c010103007680b1981c0c6051036225204000c84818140661010305001642107401c0e48030304042c00392940c90704c25015080200c0d1101c0c055000c0e03030864 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 242929505 1250 242928255 242928271
    0x11706061b0a062d0c0c020a090b03100c022a03010501060c03030e1b0d022103070212010c051806090a030606090b04050c120717043e0423 61
    0x654001000392a0148411542c0030f40341c102c4c01212440764007610100791a81d6090450f40d96411864010302540d0306441041c2c004001400e03080d6243c0e180c03030280c255406558424000e813171070307405586080c0c070a0344001841c0d43d00502160518011210013000011864140c081010b4030090903503400b401114041c12896403401102c440c60f180140540d55080c455000682000c42661005002e80580b102148812507017a803c034100e13400403e580c07200201d0300000c10748101c82c1c0c0503181c01d0000014241036200342e4454a8900180740c0c0103003224040c140c4100003400400c10708205044010a8524002c0000c02e0286090741c0c1100050340e4030000d6000b04c882c0358554100304402c80036403140301e0345058103690a0042d480c0502080030903114821000d4510300038000400c000510a00d41884a455005550340c65410141004079400c40103c400889280c485c03080240c0740d0000141c0c6641140f10200c00103a20010b0900b004041c118081c1c04101b86140d040c2050130051101114501900003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 242930755 1250 242929505 242929513
    0x518010f0b040f0e0c010f030908030f01080d020714060f0409021c06060504050a05040f2c0c011119081c02070506010915170c040f0f0b030606011706061b 68
    0x240d4024401940c00865601d00c3c210718004050452810100f000740086009203803204800c0810001a00184040b400280030140040204a120008108981c0c1641c46260440303241c2c0850302c200304da0303900e4640920f030300740a41080c8001041c14154064151118001038090801d030b1546070f00c1e030486e0440d000d210780003081c40300c1c0d40242109a20600c405040203241c5076103000d0030070001c1080303581c2601c525405140c0e200c0391983e40070410360220001031a0070301c180c1d0701c040448560004400310b012010156004400640c01c883d8011208012082c40c4040030349000c4030482c114490f408251003003561507003010043c0d6802c900307803030750302041d0701d8501c900060300c1e01030742c2c101a0301d01441608002c80d650320b04444801c4555401d40c0410464507004003070321034010b0040c5c0007800c000c0b50030340080d00f0500307210074180c4087d031541100a000021041c10403a0040c00000c02d40c1c0c80300c040c2d481c1c034040745d4400300d05102182142c0f5041e40c4128094259450140220340750381d503942007040c5100803504 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 242932005 1250 242930755 242930771
    0x5032d06010f08010b0906090402090d0f06050903070308060613030c0b0c1606020c190305030706060815010608190b1f0f0513150c171e0f09040518010f 67
    0x78001c400180b007030388545404001581800c1d00d201483c412010b00c070b48a6000464101060358442e0101d07030185001410711254002c5030b140114417603404032070864119040c2000650800800004d880b034164056803601025180c05003800142c2e4401034400404807520305020011400440c2c0c610010000754440c15501ca001800003424035601e035030021f000101b007010421880c3d40c0054805015071040f10100c0c000c00c400d002202509510350300080c1680008940c000500155501220071500010f003900c2c8401c5004200e01c982e07500074040c0030003041100001c1900c5000d100030290000300001c00026070307a04c0e850700050280500c25088039001c4061a20324607844d9224145288a00003420a1420403e19054040c949a980d000300308091b000701102d6104184a0126119a1a04104107194240b0142e0460030380d40d020000d4a40700311100c624910705000c0c0841161341400c0078914079801c1c001c2007c00c100107440701074054043d0250848034045403000030f20410b2010400c2d010300003520f030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 242933255 1250 242932005 242932007
    0x31e0b0c04080c01050909010b1b070e0712050601081f05040204140a0f03080706020304060b22050108031c23070c03081506120901180507090f1b05032d0601 69
    0x48103c480c05410884280203610541e02c4414031181920156010561900c003a001c00ba1220140c08165098070301c961003001032881082442180207050030b0b07603186c640e07110791f07101c020650702c0603101280080c16040001d260030002c0300222013050254210205159600c1e40094107982251704040080102038200c40b0b041e2500da0300c000700400d5203c000751122440e540700d19103d030041641c080c1405400200041c20031600d1b6201c82d000c5c8600a040007038071102c0c0810704100e1094960400100c91400c0000700e105400001070300c48889280712450500b040807002d8501034980e031408603180b1450410400c5000f145a01c0c1607102e1030081d07031200305aa07c2e90500914241d00580703440ca004070081e080c03420a0303c1d40412102c0c2c0056088141a940d186c1c545070b80d0040094040c1800c041c44410f10b2002008404035064085541b461410710800800210039001c58100c0304007542c01c41d807140a11002e0b1806200039580c45400c41da007196801c1c4031903102c07441080400400405030f04090341001825 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 242934505 1250 242933255 242933263
    0x40501090504020109090b060904060602030c0f06090d320304060b0429030c0303040f090b030105010501090612020f0d0608011a010f0c2103140a021201031e0b0c0408 73
    0x5240040d001e01042c1019000039102c030980340030f1014419200c84008049485000881d0b2800d40050700410600c3e550301d60003034503600300c4416500a40143e200016070814009000d500030320341c40c0c001d13102500748450142d51200400c022141c07114400b15210021101120301c0c0c1c050351003440c004641d00c0c6883d207818411110498035640c461341c984040d16200c0d440001041c07400002c034003d00e460f4584ca80d00000d26040c91505101d515100025000c6180c4050340214401c0b2001c3c0c1005212140001040500381d41007402180c1c00101140010001e00348542600c1c2da02c0c030f00042c2c00514040240c0e80c00740f000d60203540d540341407544906081012000902c45c0401c14a4010f81c07a202000191000905400314072110f4020461b500c00c40c8014000e115030851f001d075954607103411100540c080d002e00501a80c3d0840d581000c80c0c2e230300149201d50070f0f008941d446008021001c00c540c0c00c55480041c0c1d224481c0028016080e90302e4070400013440101118080c42541003410b4580349044185890 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 242935755 1250 242934505 242934509
    0x915030201110706020307080903031903020903010f06080d051e040303170c090109090c031805060702060f0106170c07020d03020610090605060f1e0328050f180106091109040501 78
    0x1c3d4401c22042201941c04810b95000540c032140982c2c0e0343d102200040c3c50750103080c40b5884a01c0c1c5500001034140e030194003c011096080d0020301c00313020400c455400319016841401d0b4140c02001541928034480c0c0c0051448039a00d002050018007000800d0301a900240c004802103090620204503240c25100c08070350298007103034454039001110000270800c0f0074a12030b1139a801d4480401400560094200c14074020102c1902c01200300c4508005543d000150742c250094051540131440e039000c000303d4141070b0b41194440c02c00ca8003030f00d42d501c20812001040c0410404003840700c800143c0d0b0f103003071040040380203500a1040e4100340b440005400441c1e4011101249804800c000c0d41e01c8070b81c10341d4604180921426150b207108038503034604041c010981005d00c2d00000400c28078010700c4694407860228816400d00b41240041441c0c1210015a1800f0103060090005a0102001003103d00344501c14800460140d41c0c03260154141c81960111024048020030526500d00b028820140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 242937005 1250 242935755 242935787
    0xe0a0b041b0b1b0c0607031805100c1b0e0406090b0105190303111615080106020105060d020d051501090f15050a150c1209032f0f0102070915030201 65
    0xd071649003203003007119403140000700c5030000d004015042c1c0d48002803084013501c240180c5407582da07225918006100780c0c0410000d0325012042d182c04503d034140402183c1d6040c40350b80302c0030340c00b88540d1a0503901a00640300e81e40c409042c0b04020410009a10302d840c000c9115007408504075000c0d1170300e00012403050300078600584110880344101044449554101c82c1c160401c80580400b21200500780f0130a103110050052010030001110915102c044141c034a55980f02e424990f2a150100d00741c8405845c904d1b407001070000030002500c0e21160582c50a84079004803140524288605400c3d050b0991000c0f0620741d030f81d55802c100c04220302a4008002c681800c1580103414080012584003080c02a6008001c4503828010600c0c05011a401b096802c4084c1500c034080f00d000c010103001d401c0c04202d03110030410011004500c42810702220180c00501d0350700140d09103000380314a140b07210001c1c80c1184501000040c50003030340d11a40d402180005250343e00a030560001404a29080c10403507 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 242938255 1250 242937005 242937053
    0x80913020c010f0c1e020f010204260c012a150c140f040b25080307121a0f010c020604080106030b0903070b130c0306021207030608070e0f09010e0a0b04 67
    0x301c41c550384545d0080c820000c0b00e5044402040100040b0b02e08504e00c5241c07036080d88009070124407400b268062400100c420440d50070840c81d402c168075161100d45d041103010070309031071401000010340028030200c6c07100200911440e044075151005000c69a0382e022500d20340e54841400040e0744581200c00e851064880302e4501846c9102201e064450f600c514541500c000c112140340144050f042c0102c081c0c0c0b003007180c00355040340c1080300d216842a07480c1004074460404920155100d401103552004000f0f14640783d524000c824040c51407107404c83d030380c1007003a11710f2a03000580d100c03c042d101a00c0d042d40001051421131030125814034001d00b40121980c0b050095a001841c00c0d4a501d030b114944c2200444401e80c149000d4000145c0c0c4d400007000d090000c80c41e100c80c0e82c04154600c1c400c203400e650030f01499507141580c903159000380c020040480e004038001400d0000700c0c02056040808840009980c0d4905c0c0307811760900c4242403048038403076400d03002e21040c402e20f011044545108880c1e01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 242939505 1250 242938255 242938271
    0x50c0409020d0b100b1b100515010809100906060815040b0a1104090c03050702121806092803110a0e060f010908030310030512070305090d080913020c010f 68
    0x4050310300c1c0c410002c0c07112014000048000d12180b1400d001010300f16030f429114020810100400d41c406e49401100d0300ca499050041454240500ba01400c803160044a401c0600801100c4c8040000e151450601c180410320034011120b101d1048024082c0000141e120309100c0b08500380711502103020b00c00800141400080381500d94103d800c1003c00310001448014030201300c82502460384118040d40c6070040600342a90150000391144040d0340c251785854800c2c01004400340528200040840030402d01071403103040c031030010018124000d20300756a03071010341a20580b90a80700c04170020003904580c101301300103011071581c1a884048901d42d90701400c24540500140c40203103003034890703800b070201d080c03140c1d0050002c82c01400314001074907074034a04031405849107034107444203c0d224860a0030114020916506468525900d0740e203552814440384100044502a00e0007960300d150200049100342c0c0d00e405281c100c0440f800009605c4c0c003401450a800c4a0203a54215217040c01c0c4460 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 242940755 1250 242939505 242939509
    0xe060910052403071d011e110a06090f0b0f09060c0d0914070501170408040501050714010204090614091303050a050409050103110907051e09120d0903050c040902 71
    0x30380064940564035958200456a02103500100030801a00450000420303c144140d2240304004190b540c40c80501130240c040d001121041f0310500c01840d5407080000350202180b08800d5400c846540000300c0c0e008030807507103034002158600802111581000c2d1741380020050518055584808855041110340c41c060905a4039040020b0994012040010303011451056a50002c40041c0d00110340c11900028046900c1d41d401c0303d0f01a580c0804c030f102003054100100c040600344110f40c02030800e030515152500649081d001030314100c1e0452407498951441c000c00f403001d040204030b80000404c00e24036100d2402076019a04650a024030344c06010046101c0d082200551800d0380f52922564858183c00100c81d00c3c061900034010b01c83c14080000240060300614000801048924003a6a11080d2055910f842503120042c44080c61240e800c40308100d07100504a4540081d019010342a81a136041c0c1c1081d00c1d101c2d0010100e440307a41c05106216080bc18603180d0f02c0251002c005501980d00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 242942005 1250 242940755 242940781
    0x703020307060b0d0602030a0f06090c05070210110307060f0609020f070209040204020f040308040302130213060f0903140d0905010207060203090409050102040806130b1003350409060e0609 83
    0x60141c442510740c0000c030f006449031140000ca103030f00200110f40ba41000c0582d81e010b0070f00d66911144940c14100c012030b411500b44121250140503895040c82c12003568280720f00e0701401000c0da41807101ea003140895012050004103840c0d803050300005a94030715030903000101d6071690440d44043d8414031410f1803102031031044030b62003a011182c0844560b00d9200040c007034412864034031750610011800008002d040c8001c2c0003a24405c40d2a10700324038889864908030b00480e4010610700f41882030402c65940100c00d0409660501d240c00e54540740c49884540d0741030869004102264080034140780030359402a0b460000e00750902c003502c6c50700d1510400079924051424610310407540c0d80098400c00c502581201c00400644c4140d40262410300d0541c80764034240395042d584441c40500050307465072801002d10560307900028090b1903a85140e100741c251105846042d14681010001d02602c0d146c0a000e04001e04c04401c000c10240c1c1404000d1000c2080508441d015646a00610003810b003181 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 242943255 1250 242942005 242942017
    0x3040c06030e100f020706062309070c020303040e07020d020f0304150e13051f0f030311010216050304090606021504021909021809011205120a0306030c0e010f05010507030203 77
    0x300d80461400309081c005400c00300b50b000721490252404c00a580a46000e80160465500803241042226601c0c0011002c1080200d1940c0490038105032016091030102181900481c182c45c260328500d9480d40428a160f10982102e22060050350822030301640c10800590455498400b07040c41d41d030709041041d0350380154019075600065402d01e01d02c00034410700c00c102004c1c0340200031040030401804000d0082109413000da403080c01c00f510b01111107074240498411289100c1c0075509452031900c3c00c0b00c01403045c035035010300395400700181c185040311043c8074491140180081c0d580d0318941082d0100301c0d1156840303441036400c12484800b0302c811345030205a0054040c0da03000448103940140b14080d807003030b8001b20400c61022400800c024550840d82800100a45041c0000d0b606c2d0481c9508040d0003101c018410b5018000b01140502e07030501424110301c80341408503100f5203980d145940217141ba0001c520940030800100803410b03145c401e02000300310a0800918040c0180c03002901c0340300d21 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 242944505 1250 242943255 242943257
    0x1c05040c1a091f0e0603010b12130309030b04060608060907050108070e1f020a14010c0207050a082a1002240702120315091306060905060d060e010e030304030f0f020303040c06 77
    0x5104031810840c0101180760039035130010035050792503846001c00c40341a082401006800026200001d564001d580110501c003501521181d014134039580d61522003034002041104c2240d110440000d003807204000c46809169503202901500c1e0900c40018809000248104104021031400d1401c54940049065000b5411540721a5810110f04164903044945800804a074105140420807900c1076200b031407007030100c3c0e00b581c0c1e500d40e40d00d0412110200c14007035824160480031002004c00c0344281d0120300040e81414071072540780c10000103404800e62488860250304002100d440910f8070002026a407410150940700f00d08080c10000c1d0f42d14040d0103c140603c0000002c6200110000c80d040780e5100018000103051402182c448045400c00c1070442d9181d060400101d541c40141c0100361203400050b282d00c60b10307501d5441d014042c1060700c0310780107507568603002e001045105000561007036010b82c540c81c10501700c5640c010300300740100c00c5142c02c40d0014801c0c44009404289440121056 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 242945755 1250 242944505 242944549
    0x120f0c090409021203030108070e01050117010501180302060c01150e13021320070311010b011407030905040f051e041208070e030d021f1a01051c05040c1a09 69
    0x81031003c04d00001d0082807480c00c2d072001100029508800003122804e0b00c11090800703000d40d90350340c0199500c00c0c0c01d203400210320982e6001070011394450742ca01c14103028220b900604060341c07074010071230a9114407103101c0540d442d541c0f80c2c104460110303042001401000846503940c9403103081548060400180280b20321440d9200e00d00e018003d40054410100900301c10240c55030609008000d0b41c4000380880115100111000b50704ca010310a0500800044c4c564450402001e00002850740c00a5400c909000210303d01040c5912030344900e62005142c4000003920b070800c410b00103030412600d2644010303002400d0400c400207013019096860400700f400d01503802d440c2e40c1800d44603106111485601403043c400c490300d002da4001010035100718404820b2265070f12a01680c020340d050100c1941c000c8200e04c4035800300c3c3d440f81000388a00d994011000503c400d600e480f42c001e441065a0669025004400501c48070240c82242191303000114201450045ca4401060b0521154480080c200c22 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 242947005 1250 242945755 242945771
    0xa080402060d110306010e09070e010807020114090f251e0803070317011707031704080d0509031501030b0a0b060f160b09030703020a120c080708120f0c0904 69
    0x94010664103007100c008801e21003c03034000c900c620f140e00110380480c00103009150081030b5043c201b0016008000c280c0c0c1da440010184001920f078034070054600000c43d965401c00c00c42007488140118050104c2101a0031503400911199140004540b840c00184640395004190b0848200b10790b0202c0c0c0854100e01c3c0502200300c803c098403081948280058000044c003102015170204005040c003d4900d84a400b9036241c41940c190121035501c0c240166100c4030f014004203188000c0f400070040b881800c6468075803285821820101d40c00810300100b000031441261074502401000c261125401d402c0f20190f24644505008a00251001070b41550301c401c0c0c0301054407100110360311032100c2c040d02035886614410328281481c20120540351100071902055049001204903402160140e00800300d11030705440d18004024002d242e01c5c1480700c3c00409100040c1d40e500036041d00d80c0a489580d8461040c0e44149001c00001050803c81007803050070482c5921815040c0d403002881030b500050084 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 242948255 1250 242947005 242947009
    0xf0d0510030206040806041502040b0901030b0303040f0e0f0a0b0105031602150709030b1015110a0519060506010905010f03020c010b0613030210030e07030b04110904060f0c050f0a080402 82
    0x410300c0d0000783d00034200080120342010000b400600403480750310f0345002e9036031514041049010b0350190304030344c90080151010310761283d0061840306800030141d038941030b0744150700301010045502070b071102c50884040101c0a084680c1d52517014010320418032130702d080c4200003082e61000920390b0341c003641ca60141d9a8024402c0184014441043c2103107400b40c20704c580302400314070790fa20048481c5000c0e0000500d00480c11100e50007100d880303940090400c001800150b494442128108040d8880c0321149004210700f080b1443e400d1487c0044690181c4450070b001e4140d441c024103407414001c0c9060308101e00e0740d10013440e109940d00362900503114114545d5040c05020700500055020101195505c0303500310201904080b40d108540c1020b100555401c280d06440300945000c000d43c000600400209000040d4142d00038811a01c0300407603900200010741c044001d032002d0300d11a43c1c035a51807610301403900c203804400c411410a1402c22405000c14502032285040384010030010002040441d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 242949505 1250 242948255 242948281
    0x10903080a0216082101080102031006090503030403030804080c010203240d0b0a0509010f06031208010e04200f060309010b0a1413020d02040302030715030605120d030e120414150f0d05 81
    0x42172500180307140550b900e0701c00700c0c040e400c00d07240702580032000e090025140e03002c1c4c4145822940301a0156040524589065640c0310000b801501c6a1300200100c04500c0700030310081d0b02c12440a0180d40120910318800840380c03041c0f0401754084c0c50080032060100d105050302c1580452000d0011030142d46002c400c5000d080318900701c1c0c40300e0f801d058020040000f14101c990644245568a40340390381e9a1401c000b50700300030303107018200e0701070200c03104502d0840302c02d640310401c80613064520100241c004252150300848043c40a40d40d1589085402d2034055241001010045640782d030341643c90f400542e51220300c01151b00840d5001401c010024943d4050710015a0001d0941e14681d0b51507554209405804520500282c40c0001c040741c1403402411488501d40726500804502604503400d80013480e08200074829407244070802e52821903800001d001504c1051f003400325600e414001d01040480040300f049100c0800d0001d0703203444c000754080d2408420019000304840e01d0700b4507034610f4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 242950755 1250 242949505 242949547
    0x629030a0e2107051c1209030201140f040b010f180506030109050f06071704110f0103150b0d0f05250c0209100e060a1404240305010903080a021608 65
    0x31190792941180414440040c110b6540141c0a590754014295070352011040c0040301031006c941c5d280e150860401140d80718a501600c00c6c000050590b001030b001c10002c1004645201d219101602080708110b5030001c01e500420518000000e01420101110410056640c0c01250701d95900300241007036409420410b4000d0b0800c00b0355505c580e4514040c0e499400480706000400d511003201045080c01400321441b96401407510b001402e070701010081030999141c81d0a04240d15004141c1085100310300b044020f00c41090390f44e903102000041d003015109950710304054079203024200304c0500d2400024002144081800800d010a004000d90360001c5220002c0d41104580f420454440c40c440b041703105581e01070148001c0d5549a204100302c0004074090300a81544c100314403001400c007900650b10001c241203822003101603088800c212501d4550042d6042da448091440c00e00d90045815030b0003c80c02103040d0319007044014200d00c4600c00e46401403039404005014240620044480c900d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 242952005 1250 242950755 242950783
    0x9010311130f020a1e09080c0405040525050f03060f130305071e0b0c0702010909110c101b0c0b070f030f02270a08071a070c08010629030a0e 62
    0x14440110311801062590002e80c0d403141d00d001c49094001d01c86c0607050740c44c1101c800b500103040f0b07940e21030284400340c003015100701d52600c10700d01550464111412a050136046014820214a140c101040310359010521428020740054043c0b060300c900c400d00603548603800e03421f6400e20151a207404c03101840340d030b03501600700000c401e118189428601c1c900403174603004d0354510304503031a4030b400b0001601c01c202c4003c0c08903d098500300885a4140c104851050110740c080d400d006501c0402e40c108a280e40c64010700d60755070348140308003030f6001e0780107031164001d071a00b0204100340765100301c070140380038064805014895903181c8015200350032504c803c51034a00250340780c00605d010414545240f41c100e01302a82d00b18410003d80c18103d01990031906444020155545862044d03d5405190701406080900412a07030001c5001090141c009008020000511a1810015006082d100240307031030003021160001c0550841502500d070004a0500000398505c800321281d4500440c0402c821 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 242953255 1250 242952005 242952007
    0x20d050304030219150f02060a0e1f0203040b070e0a090e03070816020306010905090307030c1a0106020d120605010903031b020306011409061c0b0408070506010e09010b09010311130f02 81
    0x4074400309035602c900301c0d8410001081c070017541c8041a5540c071005500100164019000160654425040589401a24070980b85000341c0c2956104440c04a0302a603103042e07400000f44802c0100d01745146d0360000b40c3d03140500a4a00180c0004c2e014200e03485066451031300d4a40c1014400e0741030088500715580460003030340d0f5100050909801145186003a8880c1c05440000207040900d4040e05110780b43c1c00001c6e500d042c5096034242e5001d40701e0f84091703d03400c0c8103034291000c0c4000841464041d200540042c01d180c540703024002c082818000750303480c80a040280410075641c200a9241c190703070341410402c4c090100c2003c000e640d0414507001039070503c42e403400000c00041c0c40240c1012800b06891501c1d00f60f030341c6814001d804222102c6145550715010a1101003004841826000b61190b201c1514009890f103607940307854400e03000b02c201d1442c50001e21510480920801c010040c0641e291a00d81d803440d180c1445228a8507443c0e401071b00c02c2c4900c40d18491095001072541c1341403040c21 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 242954505 1250 242953255 242953279
    0x9060123040f03120f030b010822080a180b090d11060c0d03020310060801030b010b0a1b05060601080916181d010b0103051803070f0c03021206060103050a1503020d0503040302 77
    0x40d14030700104007980082034817442d00d120464401e020b0780284080684803c00740d501c88120340c0d0b46e1100032009e00340b102c005007400c0c1800900c00e4001014160700701e0395241d07004401710301005481c0c42c06074419000900200a08515030320380c3c18480c042c0e1030700301d02031003100c601050110341d00303110354102406640209881d502940760958061400b03008000c001100c00f64950340283d6810030203000241000446400400c400095100180f140001501d0511504100212950341003a9000022140c0d41c105108111082d6400403426610000060082862407182c080110340d215240c0034448140560308102c07060008a5081000c10004226000e226000c0b0b14003924003d0001d540854000380c01c2c54041005501c0e0749a0141c013000c06d1070084d500e007107a50340d20040718170300000f000c6407035103488800040940d444054a508800c3ca180103400035240c0040018102c070b0004210340451031411030004070300e0745030101403829aa4180c980000c130081506041d841c50007240d00003580300745c1076012 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 242955755 1250 242954505 242954513
    0xd080a020a170f0919051207060603020603041406060f0d020108180f0106150306030b0106181d1609150e04060b0a050a02070b040e0f0a0902060a021b09060123040f03 73
    0x1c2d2134411000503080c0c507030249000d6144d02c1c0b03c15a40f5030140459000c006c0c1c0c0c0d4907040c2c10600030042d1074890200040e030141d1381e0f03000c1022500119801c2e01c0000c00c80c114180154001d100f1294000b000b1280300450b10204000a02d0403c414100a8104003c441c000ba84030301c2d01c0c00c52030765560310741c00440302d84a01000c1d6050290a050103805404540300c000560032500031f01545064a500c002c143c09a41c1c207000c03048a80410740204010362442101c400614251704a0002e00902122046009540f0301504aa00c00002441c501340c10131500350010808008420460108030b003c1d45400e07014a4910f200050240c1b80b10f03088640000343c00140d00c845560000c000f42004607403034081e503c3c0e041d0f0f14410291507008134841d0101d0406000700080f64910840200d40d400300d13a085d1300140c080102e03008120346400003881e440142c0d22026101615441c419010404030004454003807440c075142c0002041e241d50f1134888014600d0a80928001c0b9140704180d6000c1d01501c0160500c455803424 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 242957005 1250 242955755 242955781
    0x70c1710200403080c010609060e0106020d1707030b03120408070807080a1208061807080105040b06090f0603070203071704060809010203090a02131e020309010b01020d080a020a17 79
    0x28410080303441c001da010364151071101440400da4040300d07014102461610f074002140e0105d105200d0555072517502003505c1c1d416210341c0300500f006c0982005c65606000001e0302c0c02254013001c105001a4400f10f00c1d00c64102c40070300d0f03404902843c020031501c40768004a840c04801a00104038440c000c900030417402d070b001a40c4011a102ea0044a81c4141e5841c0314684039500244c018020b09440b40100c4070131401084010b030410409444000181103050340700c2403d20047c0d6000c40044d825000411043ca0300d0b000324408007504035806444c0020600000d0059038408034102c0c0115000720005400034002c0c030a0ba000540c004070300041e824507030040502154090b0140303c001c101d46c10003190000c40e051007640c1c03046c0c02550040030044919000c1110100e01c1807505035211391a81d44c6501129031526915510308640710340582c40b410446409400e40303440001007030455000859090030582c0c807004207504039610200043e0f4801c4203040840f9061103981c40ba16200c4111401e00c150044014 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 242958255 1250 242957005 242957023
    0x20c0a020d121e0c03030b12060f0609060103020f07060c0c05150916080c0f0a1a0408070b1615090803040f0308010e010b07080c010204050a08030d0b010302130b070c17 74
    0x190b00da01c100d00d80d540ca002c010521141c018400a00504c02c0c100029000f9408048a003900070601c402082d0070a0001c0e1400340c0c1250340c45140709640003841072038103141612542004090030154102558011421558080c1c0714000c3d0126884d910390100d418043d0004100050f0403a0640c0c0103140da85c005040842c0003900c6290282c82147c01c100c070aa4111450241030303501c200c002c2e042802108080000c021040303482c0035440780405030700181041c0d04044540c0030b4410b40b000c02e40c4079407a01c07030490f050081541c01070b54016030030041e41d41c0440704915500c3c4010b0344030880780f401d09070700070450000b03100c2400001c020030380020500050114041c4420b0590303109564101c160780e01c1c0c924043c00310200384241c10b01040203004001c000360004000d0280d4000000005007055034650009101181c140e11654594000040c07240360034045000da11039204081c00d0651601e015003200c2021004c1c41e110324241c400020803280200000f804651006002400c0e00c1111300d9500e50985071649258 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 242959505 1250 242958255 242958257
    0x9030a0f203301050d021020210403030215130b190513020306060f0103020909040c03030908010209010c021026010906061706040b030a0b10090606030b13020c0a020d12 74
    0x212403201129a05010181d05072440a00300c81700f4000140d003405180b000da85000401e1001c410452100c4940c0030528540041d5440020249840142800c80c07150071354008280800d4010081800800d4002030890110b02041000c004155075401d650010380405000060036a40400e042c4030503811502036003000c14034500e000300899110f01c003424003075038200c4000a4064000400140e4680303841d018000c04050107040152400d403110000401038101210100c1e812941041d084c42850380c01010311010708580402107180001580018110100b90400284900310011000d8000c40c1b00e1130907000b011182800000980100c04c80b50317425003000340181d900041c6040070005400f4418050030038100c09119240125480c0c140520002c1c005180040d07403d8842c00c4901000a040c05842c148500d50019080c2415410721580c6001c0e41c81c0f030360002007010f04044c220700c1640d43c0c02c1040128207481482c0141e0702e409010685003030032031480d130103540034524064034010b204541000264411003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 242960755 1250 242959505 242959573
    0x3090f090c0f11070b0f071403070b060a080606220507081605040e18030c1c080a0b06090d1b080709061a030c09060f0a021509030a0f20 60
    0x107402d500325101c10110003c40301030743c0031640420001c00000d006141d201c841d40b8545142c4900780c0c1703426400c0c0b580c1118124480c0c0c0001148014888200c4040f50480310886180440c0c0f840d006680303030744600142a15126450440c903081c2d42103103032085d000850805017402d00152030101005003241034210341040c4180014003900301918400ea0886054800c031310031741c0d0020b48450143e800380c4103e15107040c0651108112252071000104141d041d4200000d2004110701c024400007802400041d0170300030a5400c140001d01d445da504002d4030340c0c40354140c1d414008041c50b07082401e0451105804066007000c1d00c0c40114200c58003080310301c1601c0d81d140c010f01030140d8403050004480741400301020203040a10208500382c1d40c41000f082000001006141442d1381a8403000b401e6200307140c050056444803e90b40017003115a0f00305644064200055400e00c0d56044010300780d8591052104204400409603040760b10341d00c0040c0548110f640202c440d41e08000303004c150354402c032008680741c6d890 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 242962005 1250 242960755 242960777
    0xf020a090615080402060c010516030605041b0302071119061709030913090501020a03020c1c020c012312010602060c041a03060303070b0405161a0301030201080403090f090c 76
    0xe41c0a000121041e080000503810141c400441d50414080d2049038004407c011f204034042090180c0c40c0030340001000c1110320019007102808684a50340404d000701e00700304100c0d6094200c0d0300c90f400c1c0c0344214180580c0d03c1c02149400f42e6420035105900f03500540091080c50203182071940e150035070701c1303a444480350701c1c0c410200203200900032200302c001035008204040031810140103117007040240388004607020410b9502d180c20fa8108180450000c0d60208143c25800341c104003030700c54034905c003680817444c06100700000d480f641180da01a050024130a0084140101d491000014540d8040001d45403101544241d05d400820311507200148501404074180c20208404c6074102c44c010810600800c415040c54001d64100405003549400305100300c50108401489045c440e520880181915210300c208010741050141c200030a00c2c10030b90481c0803030200240c00c407415683c09003080742d000e035203e2070f044034011510740111501403503940c000250030280ba00045819480da4a801807806 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 242963255 1250 242962005 242962019
    0x181e0f07140609150406020105071709060a1d03040902030402040b120712060e01051e0c12060402070602072001200a1218180c030902031507050909040f020a 69
    0x1005004210304600c0420070244907141c580000c14a602c0c001e0074030840d00986880f642c1040c1c10962290001d43d440e1710410051540c07215411301001140c804084036030802d40c034615507441e001410a405a90385440889034080c00c03184da400140c1c10502100d6a480e211110140a90170564080b23002d541060840302044c681240540c0303140400700c008110041c5444048185c424180205460300f69450300144a2079400380100c0d40329540c45048484001e10b10b40c41e20300480e50003480c21070b909105000b215040110300d503806030402012100961a0711560900314000d00c00d60900030705008808922902c1031035158400d0340700d03041c241c9803140c09035580b00c1150010100480c1d1105640c0208600344c00041801500c0c844510403481c049a484c417440d1201d0400b401c250b04030a01d14803820022060f0880e42d8042c0c10420345032481c0600c1407840650102e99107000751409080310324a1140010016807040342585c000320070041c01c510321404c180c14410070101e00700d00281d00815100c0030200ba08 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 242964505 1250 242963255 242963263
    0xb010b0405090f0705091c03110708070b0f04050306180c010318020409060b0604080a05060a0902030d0f03020f0706062409061809020309160603090503040b03181e0f 73
    0x203480280c000c0403156660f450480d80d8510050100040c08801c0c801368540c0c0d207a8444840124109a144e01c144490031300700580805244ca00342d00490384071900611400d400484d842040b11004a80c03540c0354158400726050034056038200541500c181010410315510b40645040005108415120803891100044058480d045078000000010f401c3ca5001030600d0b522040e00d05000700c1e030004548005200044456000b17a1000302142e0050200740d080c80f80510031141c00905103242000161081d03804a511080d00b100c0d6801444004018480403078000e0701110344c40e10070807200d1940e03081c0525207000100100e0090100e21118244007a01c3d200c00c0300454169842140c81d480d0201d8541002240c0180421840700c4400c4d5100f00e00190051590001e10b000d160030070301070019840c0c4413181b080d4030300440d41304004040c10f10b910200410030200c1141e0944103900001da58a94990003040d1101180000108403881000154030f4000710201d4a83d42504505041d40c0040c0a010716a07662 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 242965755 1250 242964505 242964509
    0xc140303010b070f061b11070512071a0f0301060203120c090d11061b0f010b0d08040b03151804060501090b13020a02011104151719050a15120b010b04 66
    0x500b40104009408036031501c02c01007189200d0140854689406c1d1000d01a03e00100c180c540403940700035602100030380c00d00844010748001e43e6006400a981c4440d980d0310452441946050340107071601c030206412102c1240c882450320019580d903941e481d0340096a07980700d02000c0d4100c3e07001d80089103809203035404503081240010080241c0105070345036415100200c00300e0310b9000004001e90004c01250061030392400c00d985c03004c1c088050a81c0343e1142501c0c4a40141c5101c3d44844410070001100c91058400342c64100711225200e6880c10418490411147c410f580e1045070680a014203068505840e807180e441020203002d40e0342c1c0d5910b498240d4400314400ca611001e0a443c0144000d00c0d5405003480d10340c2d901c0045018090200d1041207580705401222010200b4000d000d070b07141d00083e0700182c01c0401d941480c2c4500c0d04c01c000e0500396400c5a5040310403600c50002ca02c0b1050643c0056041d2180c52501110499580401e0800d03100800d604540c44d44005000040b4a0026020707202 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 242967005 1250 242965755 242965769
    0x40507170616030b1305090f010c1d03012a02010c14180604030f08030106090b030402010503180a02030d0e010305010b07020114030705040807120201030506030105071e0c050d0c14030301 82
    0x1607580342e015940c2c140d075022503480e50405aa50240007115074400e008100010035400c000503050a00030707074179801d0803a071035480b800c180c0c10b22001480d1143d00030300400c101c01045200040402c01000040e0141c040501e001e0420f01500c40d0980f10302c400300c5218214480b4a400030003400e5510042034551414030034603200322100a012540e654940070902c03040140000b0304180c0781ca500d981d500e01c4031000004c020707a07c6c12008030040c0490f40e007100446010b000224030081c154a015070000b00f081c403000304503028030f0a010100042d011030411101c82602c1e401800e4a6446030f01c0e450041010441018282c0040d003481c000140c2044810202c0303900d240c069481c00507100b035203407504200b0740c40541510f082080403c40000c00c40d01c01c1c02040d020741003441c17181c0038401490000405030b5601828081c826450300f0301b0312a01e00c5c1c1050110304040c0d14140d096a14074032040302564000102940500280500c5021072142503101a241070071612401c0f05c001e00d518040d02c2c80e642c90000f401144 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 242968255 1250 242967005 242967013
    0x206010504022109010b010215061f03020702041e06240305070507060906020a030b180114030a0803090105060a0807060509040f0612050a140c0312070309050d080304050717 76
    0x2100d41e061075001007070600e06964000e000e602e00030445241e00355007202d102c403180e5582d4441c46025070b0f041c40044650302481d0085910703802d184000611030f9002e018942a5820100804820300d4081c0c1c041c0e0701e409030014004c1190305c0d03500032a503a50300451800c0c1051070f0301c0c0030000300380c0810a00300100440c080c84200070600d5031000041d001841c000d01140c0038040140001d0340003405138003030008800e104a001503104c0d802a9005400c2e00c2c0140b50940c0300340340303061120440300341c0410f8590455102c1002d40004510b02d001080c00d2605601024144010001c10842c2c005415000140118030a80c1c142801950350a811500e0301b4480c007448000a008002c3d0340c01d1840c041d00701910034480810b0000328190388401c4004503001407a0201d03110307002160040244801c500c1921030f121900301c040c0c08038068110010351038110749500cc0c102d010001c01c01a0030715105640c008064613020340a90318216090030314842c01d810031102100d45101c3c40602041451a80c1c0741501c0c4403220f40024 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 242969505 1250 242968255 242968259
    0x60a06030b0109140c0d060806010902041505040302130528091101030e07063b09060f0a030b04080906041d0a14010e040f170406020c04020f09010c050f03043003020601 74
    0x17444c0c1c2da600c10302c1500d09058507070130b01144c520410301210340200589907005075500d1404e03e0380804413400c20004421300c44140070802c00340e1a444200113a4090900e80003660342d440c16807083c805c58250144103d00c141000c0101d036200a95400f40701c2440c050485058552014001101a21f032110200100382c2c21009040041502400e00543e2640128107400e00d451030001071060302020100852103501041b90440705941821011183c1140c4261407091040314170341c000c1000c5010724400206406403220008090000d24003d650720104000c051039903859880d800ba49982400244162180b801d00022900803603181c45155281d00c200b5807080126840c001208641800c010000c5d101d00d00511015030000d0403104041c0004204400220f485600b0503200a10b81510444101e00580c4100b00010317402c0120001e07030721a41801d103001040b41e0114641181841d4450507020b0713940c440468040340e41000d08618003c03103041900080c011007020040105000c08051000d03002d84c20031001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 242970755 1250 242969505 242969521
    0x170f01020c0a1505100b1303080a05090f010c03050a1101020c0102040e100f03050606060a0224160302070b0c0307050f070b060112140718050307030503040608090715030b12060a06030b010914 84
    0x40c03d522100c41f440c10310001c4c7d60f41c49522103540400401000603600150722030451414103100700e600300c000c1c03030300b404400900d54028150f880b4014005050003110510074420083c25012070341c490300020002d54845581d041ca0f01040c200543e129000d1030001800800c00401c10118202100c1d0443c0041c01c550311910140303c0a64020707440b050031802000c0c00790416080d4aaa8044140c42d603940e416514640303c24039050030031401030303605c08150040040700080307244d00e28140d411900310fa0040347d40391103c88003a20540f140c0c07100c40000c000046500d00c10701600b0300840740300700401e0302c4042000302900c6c550340032540b01000109050007000701260342548101c4d1300c0d58a900c0d81401400582e511000001d240c60070b16407044031142e000040502c14079a103c00b00c3c9800c00d108000410b1001c0c00d0501c5042500103240b18041003551350085c50300c1c503a80b19851100001811415110242803070000d05000d41f109010940d0740b41c091000000d00105107203c2d000c000c1e40b41c0f01d8140201d494100c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 242972005 1250 242970755 242970757
    0x302040908040506030f0702010c020c031b06070b01090e1006030f11011407060f1d070b0c0a140d11030a0f03020706020d0c020d020601081204170f01020c0a1505100b 73
    0x10055460040502c808142c603203d0000650041240c1840d203011403405100003425107181c0164901190000003010b00c89440000b503550100001038200e8103107003a02d8000c00c01a0040390300180c00244003c00020b5002201d0b03002070380840118080c1e40c4034040240f0400203440a41c4002040143c4401c500f0f00404c200d1150150030040500d403880c2c4080449101303d14680105100342c51880c2d4410b034030007281c8607a10415407611940f890905060403918182a198040c0d44140d03005000001614110403a043c882d8a00007544045840a0b150341c01c90324030b540b040c00605441c0030406d084080c00060400009540b001c80599680d50305284110508a020b5000500e00301c0f4400d0b0203101e01c1102c1303440b03401102c20100c1194014441d40300b11440c002e203403100692014800343c10840500c800c446c98034085138191040e02c8213007090441c2010500b8034182e007507041d094882d4408908a540f402012844ca100240904140c2a955404184110844505030350000303c0503c40e84040125010b240 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 242973255 1250 242972005 242972021
    0x20a051c0b10090905130803150a170c041d0304051c0203071d070201090c1401051605031e070b01050f1f050901030e120d0e030c0706080609180a02191d010924030204 73
    0x5085e01c0a01c40c0c0d03030501202c2c00d90010360702c50202d420400c140803084c14144190813b00c40102c64807402c06001c00080ca88920460260b0f6020700c3d002141d908800558091000729541e014048070344042d5241d1054200c0100110300740084002900400c11440c0305000762800181c21110b0603041d41d1410305d0040340031a007011141e050100034003d1120400412440214480c01140a10356500031340000d4200b000914a800380814024003041c1c01150064910034190f580507100c8080c0c02a8840c00a02076010080740051136084080907081c601d03a01002810f0700803003e807001c0c458070712000306007621031072200941d5000c020b00b885015114a07041e085680c1d0004050141c074a810395280751141081815000200480c2d0784c502404024100761549136032000e4407090950440c0004d00e21140c803580071500280c841c210007403200c0d80b4504d40c0310030304004003007040c44540030341441415061880d0091080c40c10152411290003410940c0d002c00780180c07a40c1d90362100d411415542004000d044038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 242974505 1250 242973255 242973259
    0x902030d08130b0c18010207060c1b050301090510050a06120f020d08040b0406170c16050709020403060b04140712021c0f0b040b04020a051c0b1009090513080315 71
    0x1c0d190b40320104180480c0580035400303000e000c41d0741e86900101d510b00c101d5001c0220b030441d80400c00030404030303510840b01003c5076804040a15041e13000c00440e040110250056070b41540f802a070113041240015180c3e40c0c03141d840205020b10741d50b901c451821949a8800c0341240241d0700301c03500015030289a8030303803020b200600e40c400e03540c003070f403503008013500f00390861625880c00180900855420180780000403404080000391751170664124405405450401140030346030707041c82c2e0108034061004001601c4401c2c0c085450784c1c4e827820104050104403801c01d028074a0b01c880e5461603203185005c40d200342c04035242c50030310030158042e03007009510201114030351644603019111085d02e81d0040309403183c2540b0700031a210800741c08210031940058182441140304025043c070080d0080160380b507284078904004074110300c0402c44c0c006000305408056014030b04452200e180354001d001841a520b18200401003550303030700544078070b10500310005003030000c050000038240929502600002440 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 242975755 1250 242974505 242974531
    0x2d0915060f0f13090c0303141e090a0503030307021b0603071403070203070606060c141c0c0c0b07032607050306040b030f0d0305012d06030513080d090c06030902030d08 74
    0x107190f0850b0071140c4124084800240031305c01001410b034401c1e24414000d44024081c0c5c030345640c8242034490070035080588000c161000c160000380b580c800e400304000b0000502641c1e52407501000007034880c09002e8100b51503000c00c0c542c003510b5080100130f50b8420340303070341d26030f841c4062400c510803140e50001400c041c1103110401940002903102c0c007460004140d07588551540b00300510701020074107800c51540402d81d00c0ba40c8103220611400c400d45d04500d0980c01c08082410320ba00f4203042032542500700b42058000017400d40101548140380c6003040a040300304610b1551055186807607d84207464120000780180b001c90442e14042c0d100c0d0301c403400014220360100d210078030a03600300070343c21744008007082d81c541c01044a2800d6456204c80002880c000301c04011503840050107090b00d900a59003016a40c60018150040345130b002e0540c41d03000006a40c0329050300492174050030401c031781102c2c08071008030009201400f0780150b00c40b066000313010f00a00d1088020454148030000d04105050174 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 242977005 1250 242975755 242975779
    0x303070525050a0b090604020d0209060301150b090f100206010303030f0603050105180c0301060302010207030b0a021c1a0604030206031906050d0c0e0615122d0915060f0f 75
    0x40d103541040c01491142c0c01800540c40c1608041c00301c0300000380b42d0701140d00908200070042c1d944200c03014919604454240c420344070324000c079005003500031020840000d69038012030365030344100c040c0000090444450801c0721030201845008203142800e0405a4840c000500003c0c0c0290004098203100c1b000000ba03141d43c0e61203050946900351841048100480074400d41e8400c10b00042c01d40350300035002030003c9480d50340000d41d26031031444013415840b01440031520414558044900c0600404203111004001d003400c1401040810000380b00c1224540b1404e07958140b10040c1c038101c81d00189203030b003540da03200c0c1111100820811740150442d940c01c0c01041590380d2042d2205020300a03000e9490304c80c100f004495000102809a078403803090100c05040e0701c8040402c9500395825022111400d0300c85105005901040b6081100e10302d58508d401040000021030305403043c00007104688000b40121300a002c0d0f604291205d84e0440c000081030b030418101a84000302001c1d014100400d414 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 242978255 1250 242977005 242977057
    0xc030d020706020306010e100c140a05121b01050105011d011101020a0c0b0a06081905120d050f0a0902030c1c140a0201020f030324010c0b090115061103030705 70
    0x81d0120008481c040e501005200b000d59000f0318251030484165026122075a4010f0042d011030040d0500402100540010601d45942804400741040e400012106e003994621f0003e202500b2010415204149149a41c00e9803803050003098102c58068481410154403003041e182140d2110954034140185400c81c8161100244002c0003002410340d56814100710754940000705c0e00c070151100005034241041400501000300b01031144260000c400030a080706071610030700307004111700c2d90a104880401c1c035182004094000d94030541111100300441c5e40c440f00d109044071003031000a500341e4058080c00c1c98904042d01c88990710084012003081c050703451b5545816080215481810641040d1919030442d60100500301d101001e142c0a1400d600e07102030004018003101c00c0e5401d228140000242d4583d0003121001151904131144850515150b51428003815500c0d07051944844011000584181304200459820509201440c90368a60741d45c01c0781d40c2d80140310070340005500d41280004030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 242979505 1250 242978255 242978257
    0xa05070b01060905040605060c0705190b0304060c030e0123180f07030b010605120c0a0c0506070c020a080d0804111f020706080a140708070216030b01080d050c10020c030d02 76
    0xb01429520020101d051006102c145c41013903004038007a9005200745c0c0543d40d0b002c40d00100750b81c000d40d043d030b20948030341c0210f03500c0f0718031640090300c0c40e280041444103001040c0c0203284103810944090006100e1a2a11804c98059030380a0348a4400800ca684540003681a4107400c507440c400d4410080180503422814a33007124150220345e44800c0301007081060440c0758078014a80d0303007456810304c04034a18103050388a00400340188107000107401c10045008003201c40190783c000085400c0317854521005030000038038040070b138880c040900c000120f4450025a84424041e01e50354260036407902d503660540020004016a0f001c0c4000000e111075880340c1415036110302c0140d000301445840c0010140c034071a0041e094450181c2080700c4140c02030400c110854200c44e0f2403500100740da49000e0100c2c00d08400b0b03c030615125600440c004140460510317940e0594a164082d68154030850005403008d20030361003451a04e41100c0740e495204042a03016020002042c0c01b0340c1d20708000003440f0022 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 242980755 1250 242979505 242979509
    0x270f03010e03070c080c0303031305011401060c02030606060307020c0918150703270201050a0903021f03060914041202070801020d020307181a13031b06170f0103080a05070b01 77
    0x542c0c004280441405462100280107000c00c0d0040e01c10305403c000800d1302c170702c030060510148144c00480001000701c25804840f04000a1a001c40196101d4400034001c03d07c030401a84a40301c0c44c400303c0c00f146416002c590161280d0340007021030040c500705019541000030002d0700f00102458070903001260600c80d081003400043c056002c02d207003200d00981160b088144540c264007074942030344444401d0640e490070198090030714644409035003808441030309882e040250021900c01025000c0061903041d250300c03034882c1d10180072441d02c6500c85000c54072101c242c0302c1d00c0d0b01c1540204001c1854008039a80645041c41a581a07030346690b83c0c80c0c2a80e126886072004168000100000030f81e02568080022688100345251702c3e00d080c44540b802080420360646070080051010042454900d00708011580000700e161051488414515280c02c24802e580c00b08800c55003d4401008444420f17200b100341030303c003103610317421a111420a0b0304220003143c2800030400104000c20b9400c052280 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 242982005 1250 242980755 242980781
    0x50406060302090315040209010608190e0f01060b07020619111c110c01080106030c0c170301030204061a0301030f03030902040509010506030f0d0512060f0a06080a0b06270f0301 78
    0x81e03100d41e0182454600180c0c4041c0302e120408000070b0000603514048d02604482e003915054120340ca40300c4050000741000b000c1ca42d0f400d40740c0320003000d80640100b0b0004640709100020008a0380d980d24807460740c0308013030000358081c10400007242c103807180000700c2c140c8005910f018030032103c0a1202c03a140981d050705040845103a81003480c031040c0d02000c1d90b00c1c1d04d61810040d02801c1d188a001030300808040c040d900600d07031100c4450105610940e074000803c1e42014080031040801c3e03050380e05c964028001a4044e50400701f000ca029040c1030642c80c17100003d05145840d582c6561185819890040c0d81181059200c100c500c0150b41e460007070a0040c1c13080070001a603400d04404041c64031581084801507500499824410a90408113481800d01d000303080114540d034100014103188101c0c1c03c6590f210180b05070109800b60301007030726441076403a000c080190000000400189000c0c2c03400c04c5214000e03990721184001040c84ca8000c9551020702101c5048210000107825100104000c00c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 242983255 1250 242982005 242982007
    0xd020d0e060106030b040516120b040b031006030c06020d0210050601030906060b0309010b100509091005041d0105070e0a05040b0420090102061302011e022109040e1c0c0507050406060302 82
    0xc2040e00d400d1041d20341001a0021804140e23002080282c5045107420045a00075900c0c2d8140205440f50341050100803130003400c1d81c08064440300342000420550009517090582248086040b034000a4840d401d054280c004007980110700040d50041d003801860a8105516500c42d040061114000c420282000c0f564003071b168900340396035900b1914084041345c842d8072500d201039551a0894101c8054050a07950380415039101006803400c252a9481503400900c4c12a0411110307048038007070445026004000c2c0190b844241d0121401110f20900c2540900350704020013030f5281c96800800c04050241c8042820100c80c88030210311514122404880c0300002403089181d07a042c003000390300c09454030700380f205d100031074000801e40c1801c0300d2003440b1507200d4804505141c1c02040b40300401508526001c0005840d4407074509280c00161605014a00302061308424100126101a0340400d07103103231031350b02038900c00c04031401a2881c4094449019000010030203840b50302a12001e81040d807009 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 242984505 1250 242983255 242983271
    0x303031b020703080301140409140304050118060203030c0307020c0a080c0f01030509031801021e0a02011b20010c08030915010806091911040e060103060509010605060d020d0e06010603 81
    0x102032111880028a04640010b042400019414410741c0c0c1900c03080007286140f8050700c0040740043c40c1c802d9003e048400c607604284c014100c00002402503036020b0343d41c040514900680c0c07590f5503a07540108005a003051000820380c04140b009958010742c584101c40c0920b017a240441e101078034030741050070f035504840404045800e094940c0744c0341400c2841d0410081c649210036507141d0043d4103407010022070800c00b02485078402c01c20304100c800302005103406070b0f007403000b403540d41c03802403a01324080341da02c64460035568400200c40340c400e600440c146c0c1846841d280703c10b40c516660701c003072814020500440d1000c51070041c0918031940e1880c0c0146650104201d404501d403405a0100005502c10003c101200d40c0104440b90781083e034401c1000400703424602400c00250b1b960001d80c00c40c0c640750441d64210303000541c25040707074090300040109845403c0d6042c2030300c0b0a40100c0f82c000e2000c00403111150701035402040e00c004184000525442d0418a443c100482a4040800207843d8041 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 242985611 1106 242984505 242984531
    0x50d03092c0a090515041208060a17030d06120c06030f061a03060f010216181517010c0e0d030302180306011e080106060801050613080601030303 64
    0x159014510740500d82c18018102c0003800d540510400764041d03400c903941e0121a0040d80c000d02401c15400340f0400c140c030b580c000034049640103418103000194000c410282c0c1013118448001031030380d4980840c440b034184d9040360003c400900c1c801a11100044c0d1003802e030400c071002428003103104038100c0e1110005181d5079000700c09024007881c1001c04509464025486108100e0b0040031070034840b801243d40d174540240b048001d920101c0c090009420304004501180308002c40480c0c81d849032200c1c440c04036981e40c0403000482c110203058a03120803c1c040d1299000ea9494250324a2550500142074079140c3c0708050103040e03000520705410011142444041080a0101c0e002941c1d1850f44200603c030360240e15804150384100802c0d0180c041c01100c3c01c48010765200400b0364200002c0001640c080300b509035000d134002c500005d03040000d02680d070086010b170314000340c50851824 = true := by decide +kernel

theorem cover : BRFrame.Cov 242805755 242985611 := by
  have h0 := BRFrame.cov_init 242805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 242805755 ≤ n) (h2 : n < 242985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
