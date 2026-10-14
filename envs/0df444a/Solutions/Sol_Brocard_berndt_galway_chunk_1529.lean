-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1529
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:25:37.989575+00:00
-- url     : https://prove2.me/submissions/2917af6a-a5bd-4296-9475-5ca6a7bae924

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 274820143 ≤ n < 275000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 274821393 1250 274820143 274820173
    0x10204030c0b0703020105071d0103020306040e071e1203051c140705070b090f2a100c03090602010b0604090b030c04090602090a0501020c210727050c2a 67
    0x890181000c0940c050f42c0b05840d140090860b80010500c0b02001514001d0018030b8800384e425524448003407038091b032241c60f1180050000d00c00404408983e1141c0b600004000180c1005110603400e50780801480691312a00c094002e040441c0c01000107000b0070004010b13010708001400b0100e1081000284201c10100004240c04181d403508080340001ca01882003119400216910265080c060f007143e0100e41030141d6241c042011000c0a07002110382d00d0048400900f1284103480000d00401c5400d400c483c000c2d10801d0f1210040e00094181440071a45034014094407021200103458030346014a0849c100004000240d143d56044c0585010011181d5a40c02074281060140c1c1e40145d071a4501020401c4c030301c005501103030654100400e0780081d0b0391503851140c440c1032903201d40100d04114500b414204100e60b002501180b840c160400703c0411513100071411100b5815042120303482d10981030003e0b0040d00406044004c0300034034101c00180b1300c0320404c0400107840880e44620700546607 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 274822643 1250 274821393 274821413
    0x3020d21020c090a18060507030e070312020c0d05070608040c03080a030b0a1203090308032a0306030106141f0207150201020d0f050c0f0f040302090406090c0e010501021e01020403 79
    0x600010303803042d01104a54500000d0450300f00036000001c1101407000b1400000c0550280c0f00900840d9940380021403442c083c0c2c00c1441d65250210684101d552240781050800c50300043c1d0800510682c00d011186043c1540020886a0840c00800b03c8502d4400c040f60b542030300910465915a410000200059043c0c1c050070001041c0c1d2408120025680300303210200c20300740d02100c200484c3c1c1c07000b10040f0b81c1001011051381c0d0040a00c550317075a5050703000742002c49008141803800c482d400c100708542c82c4035000b441c01500114020b000855440d600d00f0b003080080d0541c6c643c400030007500c410204c600345080d00c1c035204c0140161449150794004010030703403014103c40800360b50001101541c01203d0700c6058488144080100113a003004140715405001342c02040c5880e030000610b035000281c01c24150740c003d43d4010081442c600e0035161500103001e4044003180c0e90700310388002041290901000c9416508180c0c000c00400c04807211840111140040c4101c00795130821000c00414582c40c5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 274823893 1250 274822643 274822703
    0xd090b010806090c1f080901020405180f090714060a090801180605090d0e1e030106030c0e090a0305090418020316030c0b2107021f0506030c01170103020d 68
    0x94002d52414444050410a0a02a507407240a5031032641003400780050242c00041c0141c5800561582d90012040c0240700f2138010681c03018100300c0018502d024525990b00c504a00c11000b0403540301d908440e582d030605402081b00c0d021510ba0310640a08003c0c0140401c19418901205280d0752901c4041c00c45030f01c03680006413000c84006910502a007801244d4000c40c1c1403006011142400e40d0041000603c240024070a4030161500400b088440d140e6060a1000400030000e2542c1d0b0f14246028242510038600e440c441c00700010404000824500949901a11410b00e04021003041000070f08001c5000d180d4440f0340418100507031010032140305004a40302845007100d080d41010380d011400b6900000d1b004004104001842c4c0d09601802c0012105000710031540d150352406030b0905040104960f0180140d61004140c40d240d60000c5004490031b4080d181d051404100444030101c00d3354507c5071118090004200600303014400c021100d0203001c200b00044555007494151032100c81c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 274825143 1250 274823893 274823909
    0x90c09040920090f071110140105100305090a080f0d051e09070b0412080904020a0315051008130809030f010209031b0d1b0521061005150d090b01 64
    0xa01c00c02ea82c0c1c030001a114194a007264240310600c0c0c2203800000044008100d20304200311344201da000c1080411001d440d030050000203000310720f400b852001c0c400b0070034807401e0300c261441048a0943d5000340f09642c018a03159000e0a14280d1948070300d00700e0f43c043d82711705002071810020039044040611031640141030002c4015884a440c80daa9070310074501031301781c490036007206100300704050400d07080b00c040780e2280615001d25140c508103a0034900a04114541149c0001500074940c1d90580c4801100002002d103444181d4464040c003041088410611001c11103003008940580480d206001505d88640392462030282003d0120f401c10440c40c0c02240d03603a4000c2a000602c2c0307418040c0156a401c42e02044101910007000550080250240a0841520366000710740030080303412807030098000a0100621012444161442e0041b9003e14280c0c1d405a60007080040303034004d00380000c80b08024004046200078000041480d44030348120509655151007a500141d102440c16008000741 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 274826393 1250 274825143 274825163
    0x1602030c040908270108010e0a1419110c070603020c0a120801080f0109030e06090102120406021b090403020d082d010509130309060c020f0414061903030905090c090409 74
    0x1c2043c40c05401000b90803a0443c4001d03409021345039038407580c014110341405002e10440c0d00c1c0c0f000740400500c540d802d0310000528130340c2001418039101d1941481000861801c00c80d000d15202007040343d00400a01400a40002c0820805548681c000e8015507020000340c80c017005e80d6a4071b60000764142e00102000c42c410900402101c0d10a0101c0e44a200d02d00d4000d1090305020b40d4007c044808454982e8441c980100384810164420006101c640800c08811690380340c0740c3c20069a0381180c8040c00b1110342900380b1000c02d508184009902a590540041a000781248415030310b4400081403101d511944180c02e1488058007041141c2c584074503115050740d54100018000000320040080004107081505503000a0307000030107100321405c9252003125000c0700d200044900c0c000c54520359110341014000b5008035007441405009003003c4a81802c00410b5500d0b41124200c50321000e0003151180004000600b400480c042d840142220f80624260102d80000d0855803c403000351004100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 274827643 1250 274826393 274826407
    0x30a02010e0f01061d090109140f0c18040602030714040b040603050f0403120b01020705040207050303011401080f0406020d0e0a0b01061202070816020d0f030f080604060b1602030c040908 82
    0x244080305404502c03070000d0014908141404c52140c903254076800022000e480040c40042082d0300210f8800d82c00110421003200c81034003995682100c4204050a00500d15126042c0c540f403045807030080c214060010b200da40710b4546100035000104058140b011021000c00c900301c014000700042c010039443c081c5c40f2030402e00004c0865038014001d40020680400b440007098004981c0344440b40c003000701080707a9200c0b4004034100001c603846aa04035001003000c13801c2000c04805181030364807101240301c208050302c004440316441903c01218030f9080b900404d0110321107400614801003c01030103d1030601120609107407000080301600c0300d2803503c0050044039441107207a02c100320503040030350600000d522041c0c107901c203502d1943c162800099032602151900021740032126006040010b000085040c042c00e0901c0c60380c0188001980f10000488600c5e0503c41d031425240c12440701c90034200356610348101c500c0a800306903458814000d00b04c50340c2d0f6807800345258651140c0e5449840725a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 274828893 1250 274827643 274827671
    0x1b0703210e0102030904090212070f0315050105130507031409030706060608072c06031905060102060f13051c090609050307030210140d02070803041203050f0c0c030408030a0201 78
    0x1505268401080a400759202440c0c1c0d000060b1000350b40100c50018600101d40b000451511402d00c80c00e13140d00031403400007140c540c915081c6c81100d0250b0180300c080c2540d940001c044071003d00500d41c0c009802005c0c010000d00300d0b030200e0b92000f11400c0008000050389543d210b550390403208001d86030302c0003038114100892400356200401142c1042e07512400c016402601140c07454000c40795a090b042d850f16901d226540044c021180064843c50760390030b003441d8620410405854a195560410700071805552000807110b105080410f913541c00b40e2668070070410950b050720303003e031020700c6010b601b030704400285040070b04298800d8840120700b516000d000f40045403940c0c0040d101c0d400c512010409a20f41001c02e54202030a40f0b01090342407044013a004050060b032811712070707441c408150442001b108800941c02940100c1809040c00100907088090f0f440442d80c680300c0c0040100412140c00c3c10002902c28101a0010b0728102500c43e1503951464000e0780003031780107030b458a03a0303104804 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 274830143 1250 274828893 274828943
    0x402030403080117010b03191e1205250302010b01080903040b070212010f0e0106090b032a0604080304080109031b0f0b0903090d0b040c0b04060207051c0605070e01080114151b0703 79
    0x80d0308000b41e400c0e107140d40354901144080850b4005000c3e0014100e0810740204480b40c0c981d0f13100c0701033625154001d080c000d000341080c41d255404203581802281c80d0308400003d541c12102440d58061400322355500388212070b403803122110700d150f49646c44007078100501d0003480c90703009076200005005490181c207074060316031000c0e0142c042d070400e00740d44c1c040d61002040454030040412084c40489000d0011031124895580148403601012602044014040d0002680b083c004c3d500c02c504110070414843d00c100c900c6200610f510806c00c5145c000800002e00290b00441c85000d07641088003200c041501d24000c0e11040703403036000311801c0104000510000601030300e204142c0900705070928202a40d06d08181c000c17103105202185e00c1e510000340402c0c07815071065110100b4003403030501c0b004c09414058030300c0c40917003c40d03624070010642021440315943d41d144000e20089014904200b10341c1035074844d0300d07014924110300f103000105000030410440150302c030311482d203020701c8807580b01301d284 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 274831393 1250 274830143 274830173
    0xf02070210031415130902031203010602070914131103010b1c02130522020d0f0303200f0a0302030a06080d020303160f09150309150e07050402030403080117010b0319 73
    0x101400520301e0941c50700d0f2000c174520740545034002004e00f0350303000181c07906580b1000d114035144000004034007258041844011100483c209000416000b24150525001260170504044070051400c0105180c40f81801030444064000203201040b0800f04071800c03460000e401211211800c3c00d41141040680204003402c00e00d81000b07181030942090001205800100c03401d6021061028155504d072640310042c2903000e244480c0800140c90090060710b1200711203070014890b002941c050710b03081e40441e060360842414940c6407100e40c9505074000d400150251401c9130b528400403658401c104902840f070162074006540705d00e0260207002e64804e900c0c200f00208401e005580901c0743e0400000300030340c5c0084202c0e06001e0003a501c01c400038580d0140181289507104246594603915030701c10452407000c00c0903130703803410b44a106001c2a8401901c1c014000b4801000400c40f81104c41c0ca503070104403540c0700111705480c030400028a40b860a105603411001e4108649003000720f00700000c0c0071 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 274832643 1250 274831393 274831411
    0x1c11030a05042907061b0804020a0b0a03150602010203060a060e06090d21080610030911191d270a110301020c07080703060e0601080c040f020702100314 67
    0xd0201210001001409244141154081c5400e0081040701d00c1510080c00d19034280f49198584002d13040007000b8000000a00040090b2028044c01c0e0620801582e03104680151418207a50f00d020b11402c0c060340803070304c0101050b69960340d510654914240101c01804181c0c005610f9007843e408006003d08213500010502c0740707031a0403113890b45995095903000401100e0480700381c005410000000401c08091903200703001401000c1010790001c0015001e050705072241081d184250006900311039a40300d020f4010030004c0452607051400c01d4005502884c1c0c234041c2c2c0404c5644100043c0310f400810b01c2d80c075864280f40708000d06500078940b42010010501107012142c140403400c039407503000b00c0b400542400140702c5411203a0b20300350119421514008120349040f035495201603143c0d1030074003040741c406080c100c5482140a00180107816a400c45014000d1800c01a0810000304040b002d07001d4119000d01840c40560f0ba40403e01c580034000d80c6012071054241c080c481c082c03c2c00207000110b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 274833893 1250 274832643 274832647
    0xc0a180f0f080319051309020c010e0606190510051209030319090305120a06050d0c03050d0201020a0906052a0c0a0504061a0304050c060f130e010e190e1c1103 70
    0x215540c1c901030310134244003940c1072560780d84042d4604032441c03c2d00c542151150500000d5402045141548130104a040d41d105694103034480c5410881c1c1d001c030340050320b01c800c2c0900c00d040c4010300d042d80c1c81001c0703820142042e918015030b4003400c03940940d003103d000d01560000320802c10b00b0408220454007503406404200f100c0d41d020b0350041e280d40110343d841c241e00498000021244030490340150050301c0010030060307115040d864060000700b894001100c2900840500e140090b005000792500c0f00d50984031803454070304140e412241c503004140200c40c48151072010380010100040c030444400d1b0210003030400b030703c4d448007803040d101c0d440d5202c1802249082002c220f00e0072051400b90399003010900084e56911903050543c03800802d5002103600940008100704034000700c8008210030b001e10307038000c42c0b815074408030600c60460920070500a091581e00282c1c0f0020700351180c0e40700300920700d400201820007100035494030100303030340303101040c0741d500d01003400107801201032107581807000d0081d8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 274835143 1250 274833893 274833907
    0xb0115080103060509010921020c0f100c031e03060321140a0302041509030c15020303040204050624030604060f080a0305070c180204030b010512060c0a180f0f0803 72
    0x10300c401014400503050565841c0482e80090080d0005005240c1240c0c59006404080c0602a840000c400e107020140c0314000c24030540c1d04046c0f07018942d02100400f070208054110100391264010800304904000394194040c003100c03a00380001528691903a0006005030a41c94190200303064104031103000801140c081c510146e02100c40d600113001c882c1415200e0741c100200f64040e02036600504d0031442e04135074408034558071000600031640905c001c1c2c03e1940e90780c0754108004481d8020600160030400004015040c96003040e504840d01510390300d42115800f400c8511310070300c120a5055181c001080c407000e80b601d4050003000c1c0141c5000500e51500e03014400b540c2c1c506545006050180216007a0140080030140b00020708100c5507030a1100c503042d0400c002944203000c11500801c2400c0040707002d0030242194030000c07540e60b005005c59100d403510610181c105000030f40c01c10501500c4003007110550f1811800410704071034560402810b01010350301c4854150001c0200790310a008038 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 274836393 1250 274835143 274835147
    0x8030a020913090f141e01051f0b04050d030c0213050a150518040c0308030703050604060e04110d11150304050601090902010f03020a030b06041d0606270f100c0b0115 73
    0x605807080d4041c502d0242040c0712454581403034a620540300511540a21b140490170043d00654410100c0242c01281800d202000d508508034900403403030040c000340000c0c0020b041c0000015001c1d4024140041c40d0000c5500040845800403041d042d50b81d255010b100d162042070240114160307600f40f108410070308000c0404c0105005c000340c1e00a030076031a4049030600c1002c902c0440034503003207004696680390802002e03000e02003e643e0389019526007000000d40d2070b1686180ca001c0e60340000b044c00360704520b10410600c07110421096408442030904174555507911305000d8104076504203041d46926003401c103e0305204050341700f2802d5038240085100180e9001d112201801214140180c0f81e002c0d1140441c018000007035815009103000802080b03c4010055125065100240b4410340d0b0b0f481ca0b0900c2000e0260103002d070000401c05002da0221000607440280002015104904a20070200001c03035070039401524001041381070301c0b0030050002080e1b0060140c203000740c0540500700c4590340 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 274837643 1250 274836393 274836413
    0x140105062104060e01050906040b0108031207030914190b060307030507121a0f06040f0605060a0c11130504021c021e180106030204060e0108130f030c08030a02091309 73
    0x3103418041e00e9080003030104105035005400598180300200410310704429802d5685505072001c1d1403070441c0000009a05400108540644010080250150b1201c002c190003a103004081250005030134028034994202c104580381903100d00c3c2445248035642030030300da002e03410042c1600d402600050740501c04141b000074034000b114003070503001500c040c690802040d15241d0324104008031075088207002504554050150007440704660802401c00c0802d1408105e50803480b405030003d0090220200d030301c0c018140004803500a05007072800c4020a4006004480c0c0c1d00d400035095540d40d8180000e5092208511500e041c0d070700220811740a00e500017412103d501000304a80b50000e6a00d41006d0b03d482c1c8c010350780083c0c0700541d00a696161503003e00a0741180c00742d080003449036071104444e98402c00b1030602800c03000c1603030655500640c4410031400c10445d01a01400102c04078600007a102c03400940c40f90074070840c0182c41d40548c5080004071200751b04100d1819003425040d9004c80d516141c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 274838893 1250 274837643 274837687
    0x7120e070f05012a021f0309110405070c02010e0a1a0a1103030f130213020c10050603010612260a0309290a0c020f0d09030501050f071215050a0914010506 68
    0xd800001c101381c40003500d4480d4001c03400490b050101185810950540c210310740842c41204880300110b243c030309201c01c8550495800c1c0000b0039881104015500824000c69880405407401000f00d40f683c1c240da01a48502200300c40032480040d906480a0348410507140d525005009185582401c400030b0034201006805e00105031042c912480466840041410a18070070300010b64842e02000340702910361070f900000306550f03030a00000602600e018800e11094405108400c0313907403003003502c2e03028151000c183d143d01d010343c86000145402c0c840310040c1100c1c10650341c000c503800c01c0528012900324a01c110160341072030740002414103040c8040c00c843e400807503014000b69034054500100e1602e01542e00c180d0b0a40105400c02105552200c2c6800a0324002c1000340400d88a400401c0b00500085491000281c010303c070ae801d03080311a0b00b00814010305d0b2811504500d4803940003400c4441c1e258040c0101c40d5880350154141c1503510f800c9401032030211502420101445030000c1130715040f078 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 274840143 1250 274838893 274838957
    0x80307050901020a1a0a0b0907050f07110d0b07020d0306270603080313020307120503090915030d0305250e1c08030903120c03070f0807120e070f0501 66
    0x1c41c0c9502a40d01c20850401c82135040480c4100b040742140f0300107408641610070031002400c1902c201c04500308001c040c0c1c0140c0c0761b591582e140c02c008a03542d01c0d840d00004802c030740031035050703001a407199100906020410b001d038002e588941070a01002c0d1070101510101c0c0103040c180700c1c003040082150b0a140611041c10200141000e0024205000808c0a90401000c0b00d07808020310080900d0355050f490094820350072901c80301d817185910503807070300320380b200518540c400c0211154a04045106940001c100c43d006100ca001030000a42000607030924000026501e80070025000240c102c026070a1300544282040c21800c504010107050103140540d001c0c107814000300c0410a54211402c113100d0b0800341c2c40e6140e0400c00e0b07001c2d40742da000c02c1d5070380320443c0c01002066218000c2e6040368092021922150000c07140035200b500c0c400c0000b003544041c03040590420000628070300500503045101c102500d070590a240052921070f0254200718100074854500c3c8050007010f60700310ba0aa0600c03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 274841393 1250 274840143 274840147
    0x1103180703170318060f070f020c0f1c0609030201020a0e0907081b0c0313170d0e0f131b02010513030203030a050a0b13050115110303272d0a08030705 66
    0x8194a40d2030305000443c1c0d5045032041707070100000c3c42143c40e90103004000f19075a541c99010740c6c203000c0342e80d00c40a0070540c1d401000c0405d142528944426054035681c903180e030b018001005e985600c0100c0c0c000440a40250b5000a1100d41c0aa4400032036058880103c512119070305010358001e200c030340300902008400340714800004041b9400000d0311740d107600f004110380d0b4401c04014001d40400c42d03445981480c0a1860114000420114442c0004542540c411143e15422401c200714000c80c04800c1d034101c0c0100d140b030f0300e02c090a8025909411200442258040304d03141d002401c48c0c8008240140c107510060000f030020340d01100f182d410180813400800c0310b84071030205400500004180302e520010341045034509203a540c011034101d0b0303150041490b0710b4040b440b066032042c0354407100307104035002040011401203803846400e20400c160180c29100c108101c105524002610302c01c0c06000420000e005481d80c20b011800400c801d540000e804c1f214401d03659020a400003904c507809000b00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 274842643 1250 274841393 274841401
    0xc030306091806110c100c03020906040617070203091012180b0a0510050607141e010b040b060a092310030507020d0e03060c07020109080111031807031703 68
    0x2180e0800400380c40e1445080101d00004072500900344000081140c046042c4414100c0d4000002c081d00c42c1c9401d50805400b0204d0a40f5441c0006c0c01038404031014154244440d01180d00c468011f04081e0287d41c5510300301070010000c0c80c03c6c0c1d000040c070a20031540104400075603031b01e03401c3c0f1406c044a03181c1071071544a4091030600b0007400100042030f0000d01c1a0390700600b0321512032445802110b40c5981080140c07140c801c030360700304800707030203080d40000e000c01c96100001c0e04004c21801c00d402200603204103030609000c0c405070444c080300b2801242c9d181c16114641d440c0906ca02c826184003121220314240b0000c034090b00180c10f038032400a814001d1288004000720010b480c0ca403100004010b540e41c680d00c2d41024004100603950007005200d851204040c0e0342c001c9090200c0c107403009005081c1542c0e000b402100c0c1d584804401c0341000511040010340700805d02076124a4000500401d803a8601414941c22150142d50201c403554040142080400e9003171019500010b52070501e07941d81d903070b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 274843893 1250 274842643 274842647
    0xc061b0109080703030902090a090b13061e06150815060c0f060a0c080f0601021e010b1309052a060304060e030711030f070806010b0703270603111206010c03 69
    0x128030070040c1000e000000c11a00301a8180d100e2110703140b00b00c4244902e92102d0154404640e881c08000b440d2000080100740c0058a207464203043c54411500422089900414442484848071191110765280c2d031050004602e00003800c0311b0140da500d056249032504071409019601c440628038082c5100150003002120184001d60755550840102c3e500c3d801c280710310200401000f1200000038115102040002c01d0942241e4040c0005038000c8c490580200d00c4a2400410b1208a074420b6503104070310495070b221404082241e4008030310000704000e00307060885c18140d941c0b4075001d010717602240c12064074824041540b404038069420399100d995901c0c000004000d010440c4070703180b00100c1c914081000e82c2c01c8880744032a068061350405420035408644da850540296003c1340c0190006010850030350300640380c140d000c0c0c40c004040591102d40b0741030800320805000900e40e075190044c8801d540501440c3d0216a8451900e89004110505010f2042001c1c005504010b421420031007458 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 274845143 1250 274843893 274843901
    0x80f0613060213060e04060e0606070b06120a0b040b070c020d0b040503070803150103110316081b0703120501080d091203090302031218090103020f0d050109210e030c061b01 76
    0x119907800100783d11a140c050162200c2c10300a52648514144040454442c21420555000f80c501600c91400c040362640da009074500c0007041280c12800d05038a00e01e184000700b102d210094020b404544c92400c003410028001c99000301040148401c81c540720380140ca030020500682070308004c3e0b0700c45585852a2480c00e501c50100c002e0010030011040c4150703210340c100810780520b0262810484d400b40e001b1890650b020803200140c840c0d034002c00240d002d5000307400301984014608040410500d254800b06441d0304416000d07000201d40e002200d035040f4861064501614140000300034200311607000500da20300d0b03070240d482046900030718a410140280c0c00030000e10307402002c0d151850b0344121080095005000c52121541c204541007a643c00c0a8440da41038030740160840e24045048030900a0001e42007000f112999a00e0389140c022445140c1503d910080300300580809200180c4002d04251210381c4540c841d400004c862441030361602e040f154400c0781049000080382403800b05134010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 274846393 1250 274845143 274845157
    0x20405041e0c030c1407020409020d0f0209010e04020904030e0f040e1f02040e010501111504030c0209010501050c100f020702030a080a03051006020d050f1b0c0a080f06130602 77
    0x908004015145001c109101054118100c004000380c2904000c02c50030b80d2041980200030038903030800800c503212454020246540003820110701c0aa440d4042100500b482c1c1c400d80e04042040c04190441c42c10b20303111401880078070940310050034190001056400c010304001e05000e042e0881c9161a00c2d410100521424001c00800541c000480c000c1c0e110480c81c1040b40301455003040e040254000c5100303560640c1c10301a51015160300b00b00055440d2004540030007201d04c560004083d000c0006643c00c1e01c600e201c0c2e900c150115150384140300f000481a04214140141440708010001000900c0f4190407038044000c03403c800c261203440000d1080704e00107505401a80016014804054010003104004c2e990801c0503941c1ca40210340030324200d004480068100c2c1d1501c2c19020b10500c0501a01e01940102c00d1620500c0060182d6000070315100701e140e42c0000c3d80f0b080b42071410b104114010454603000e48161400f948132103456600042c041c02000d4040c021600c103200050b4103489503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 274847643 1250 274846393 274846399
    0x80c07170a02070f060906120e0721150b010e151b0105011e050907051c020406020f0d020c0d03051303081222031d1503070f12050606040e040501020405 67
    0x344401031040252030340040d000e8240304d0200c0110004541d80709400d610201e40280d654007022600c4001032130701802440300d44100504c52000d000c00c1e842802046003072150b902e480002500403c52400c1c401503180d2400e41c020180c58141030006076600851f00e80c0c00c2c82011601141e00c0c0005172038040c110700501d104986001c2c0c04088100b91b1107015403055040e200e42c8854a1003904075141041002402406110f03003010441e40483c880d01d0068010f8900300700704014a840300d10203201124202e0308564480001a4800300504400510030b2241c1104c02c1c00c0d9101814107214201d0114144811141d00101004070001c0c0847e0070340100001c94001d56400707144195140c005600b1004140020350300c54882c2e01da01c0506060300300104610a12080d03140c0c40e840318844070078100c01c002e021141442a0000d51a1041c9507019103a90300079803181e130041c1c0f942031280d00000303002816064205011a0b2091a00702030014030360703541040e901191440810741c1050396a525080d03003e402260b1103290 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 274848893 1250 274847643 274847647
    0x130809012d020f030901020327030a08270f0111010b0604060206040309120308010b0703030b131a04060f030b0403020307050d0203300c250b0402120d080c0717 70
    0x40742914059a010120026422950340c0c902820750fa0741c50303200c2c5102481c0903038070402c0524100040704103440c210f01c4c82c25600c0b080d8080004040b0381400c0171084200d501c8900024008001008080c00c0c00100c0c0c501f0301866005c0001402140340d0085c09a0358a0500c1101e458410f00caa409401500707241101500143d115a0b941c00d000c3c2d500c041c259000c0380880c1441c4d1000c40e0041982c0c80b4640f0701905a914040e035a440c0102a0b03005500240307007070381010b455800d0919a03891b030880544036840c2c00303a000143c901c1040940c841305018200c11500c51800c020080214401249842c070942c1c1d00080c04006a456600d8144d10f18410708100800f02c0c010311120b00309140d0003101501090054000165111220b801c3d1321071180380002c12a1b408c01d0036140441c5002c06440c01078116815016004160300e0340100222200c6030081c4421611017039028204811801c1060f5030b0301d55507480c030000300303041924104007500f9400000c105182c1840040b4240e0306021200e010300104081144001e6 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 274850143 1250 274848893 274848947
    0x807030f0213291222150914060907051903030c170909160e040c02060412030e101e0603030801091505300c03030904050a0e010507020a0b0603010513080901 69
    0x1280318008a5228043d090105a1417010803804030301c440070b46074848441070a8140240d180d100030b0540c04420366040c040309007070601080080040714028130801d00141145440c7c101002011403121800361075a0548440c03c00010f5000741c294655103a0084200d005c010401c814415540620700301282d118100c001800342464940b0800006030f102c9070f4686804940c610240300c2510050700c0342d100182c3c003120028000ca02200c100781c14108061802080b030101441090b40391160781065003081d0b40d5140f888031210808114221005040c1c080d040c800640b854a01400c090014031601c422680c40314000829041070b9503140000d000001c0c0000701d5040c286507200b000f20701d0202101000c10100f1102000742c0000552048c0304c3c84002c7c01149400d10f00030030301016240141c03040003416280c910b15138503400e0038040c0c0b40c429027055008007905500c0307091100d1142006030102e8000d034504010311460160f2030508022494104601940e07502900780126641e40d0a0b1030440c0301002c001c1051 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 274851393 1250 274850143 274850167
    0xa0c060c0b100506070b1506310e062112091e0604090f0609180209100609140315180106080708060f071b030807030f021329 55
    0xc44241e0060301c00c9105541c6969110750801c42501983d5400b4609001490000e880010740c29071002e41e8a42d41e102580c1f03110302007085030b0048400c01b80d0361180c001c810a0032610091040000c0c81580003420304580c90000c02c01054007001e40100c0c0030f80c00808151211a41d810644020042c0400486441096a04803d442604940d50a512545515103c2000c1c0c02441c400b980e02c83d240240500d00d80740c41c12071800001e0040e002d0510703415803540300005c0c002d520b600c1400c13400388403018100d9400080d4410004080301c001c0801c140b03589040341c2801565401200d45d02540d040c1c07200443c1e0070001c03000003481c1c0a01d01c0c6100c03050031019002c001455540c081c40c03144110843c0c0090206540303c242858480352580100d2080380d000b00006102d910800740710380c0e08a080d0b410964000922000c0e56490342d8900841540424800014090340035403522402c042045001411803c2a03201f04050450b0040d520454100e03046414140340d868500c10015503909140c030700181e03a11640d050003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 274852643 1250 274851393 274851407
    0x70e01090b1003020a2c03031801030b120607081e0a0f06052209060e0303010605070c05010c0209040212101806050f13080715090305030414030406200a0c06 69
    0x102405062400344000c00c0c0c2d8000c1c000da1307400307440d5900c403e6109804291140c04115003242d84090b034402080480350140c800340014252100902c1c2ca40111500d880005000d8503240d0a0a5010301403154852051300404100160070506a15046860340c070307050390f44900b00420780f0b100d5191442120901801000301e030310231100a094a482404450340d0341e000c01c0101484095411281d03e41c0308203150345100194005400903100364000508c41c1e0710420a80c2c0f5580090700860007180b40003c60f0300a20450485840041c00b092818820705031641d404101d4006000c8c00083c00340c240d22050090019080c4144c1651185120007040804240120b8a40421440c0001c0c1c1d00d41d845e01d0040750842c0901603001d485100006110b8268600d50383d03c1041a5110b19801d03218074030701035680d10f00c01038035008180d900c500070740e10306403a4109401c1a20759050521140c0d84198410002005110341000a180e045040440c0c134034032800b40842c1c1700e418040755990043c1540040d10000c2003458000031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 274853893 1250 274852643 274852661
    0x30d08151008070809030a1d1302030106020a1401051005010804150c090e010b04060203031f03050a080315010e01080c07050a14031207020a0309050d02061e0a0f020a08041205070e0109 81
    0x243d0150140c1720b00b00119140d03c00c45194600280010b0fa544800c1c1c1403102c160260143c014100c6500c8454515014040b42c000b038000f840160000f1440000703010400c240e41d02d885040c0402006507041103c81c0f64080d010b6442124140508040050f050010490181d400c0b016811004d2040402040340100440401e02801500360101000400c5101c1e400098405603101900154a980c8559124808810150398074140d1512300c0840400010740500425100d540700d0250140c41f400d14811044181e00c034406c2300b90401c40c0c800c890101aa070f015000c02d41081c6220000d6a44030180c2c180b1500f800c22940d07019180c15a0702400c980c3d00c040c00401402810504410541e0319190400100d841d074011a40140000f080010306008520380080d04d07442c2c292000b081e071403034403100031741d4001c1c03000c0301200c20405a40d0201d290050642c0051492034081014400390180100360b0341e9800590259009528950401e00d4601d400c104040050718042c14084180508540e5203403484130192200e56 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 274855143 1250 274853893 274853897
    0x204020c0d03020d0e06010f1208133b150406090509030901021c0207030b07051207110c010201060b03040b070203090d06050108073804050a0303050903070e06030d0815100807 77
    0x11800c051715070380483d0b118142c0d14044000c0381c3c2c040c0f50055140310301c0040901517540c000c082000d00207402c1c40042050090904028102714040c540c100d140c0c2c14610034910440d841c50980211410b43e004815090344080344c0d103600070380d1118102c0414000c0040350841d00b0280d10b040207000d501e4100002511a0309000d900b15071680c441c1c03400502d20700d0110104100944d02c202000e000040046004907441303185454400c0c1400c051511403144580151382c200d020032042051a25507001c00d01c80b05400c9442030000f403080502d000b032982814132006201a14140400700420300881c400e20031503100c04401030003601800c0c02230900d400107050a218400e8240b0946000003042940c019008003440e0f000b440310780c8010554000f6640b1035000a040410503142000049256610000c041c400b6500a0340e030039440720a448249458400f9030f4120844120040c0d04008040d90300041181d0341c0801440d207000303140c503a250340901c0c092501790007a038062140401600341640c020b4020384152256 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 274856393 1250 274855143 274855151
    0x8030703200c1510030c21021f081005102610152a02030a02280e040503160305090402040902190e0f04240f05120c0d0f0204020c0d03020d 61
    0x401800304510a103100080446d912400300b0404d101d45510501582c1a1504a00003009451f9000800c01d42c4900401103140c8181303643c8071036943e841041c2c107a101e101686100e140310b0810000540300003044200d50200104a04410841c00c8086d991007083e9000008509450403c0c580032581040c050044106821645802440491145200d070b201d0380341031807091400e5800115840d16000c1003010998242c800d482702c400050303d9111050114112181c1c1004650001d25035040465207207a01401c2c50402003018400402c0300401141c0c10900140c2c001922010140341c26242c500030100d096030300030b1004c14001101a0141c0080c8080302114501f03007050f45211000740c0d0070003c40c0b81c1a039088540b0405207105820184d0041540ca200c4244a000d918100d040b841e40750b00081e08544050741c0c0891080095082c950b12508080030810080c5c07013241d0030354001c205080d000708001b07490504024015410340d01d40c0e5046500c60000d007401e503488012030800180c0030307500c054100070b101890 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 274857643 1250 274856393 274856401
    0xc06091f031b050f180d0f050f1005040503030604050711060421050711090709030203011a0102060702060c0304060b0a090f06061d0a0b0d020f0301091b03020708030703200c15 77
    0x803440840e181c00c0c4c010403004c1c1c10f003100c200700c1c40b101034030380b074440f40d040b00102071400c01080050407004540780c4114014a07080c00c40280460912a119081c00440d031b09000a0100054000c41500c0d44981c0607180003e95903141d843c11140c8002e8155010700c90b0040078240030901000062040b00d10403801d0785182840f843d0b03c0c08503113a109070f090180c0001c0c8c10b92040101854485107054110340c0038640444415202e400081c03c442e202c2c152005c01410022100c0311a507018004694007a04a0001d4070803460048246112480f005000030420759403000d40049582d2555040070141c2808242001001902c0341188001c05140c0500d00c0850200c461080460500c02c00c4100c858001520752100c852410000c52400e401103e0540100e40c0c0074401002c0380e6008a01550091440000103e40e4019401e441401c516645400d5800c143c0100000c1011600b254200c81e0040382a00e00000c1481448a940700e040040303000151500300b0009598280090004040700484c40c01035502401d515 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 274858893 1250 274857643 274857647
    0x11401030c0f0f180f060b0f190f1706031e06040b0901060605090f04021b1c030b010804230d210b01091211101106180c06091f031b 58
    0x5644c4659254082d95207040c0700f888180350851000114141008121991078940e07010158100d500071402050010407542c080000e4030b003024151042c0c80c10101c0c102c2840010040180c2c020100f2070101c034254070040b640a448c00c00c441610076034205000840cc0300d60246403034448005650944030314a9000204010f240103100b00c4080791400d4541c0c510b0710240d0010b2000c1c089002416990007075003400a003442c1e20703481c01c44001d00c0540c0006001d5854021f90800d00213440840050304240c80c041801d02141d800919842c0c01c203802011001d400b4032094050141d41c03c06502002140c0600c0303981401c90342d0441c2c41200100303884c684840112420040903000c45070341715002800100d0440c410009804c5207051200098000c900b010802c03200c44010898a118070b0b5000c0e00003c0c0c070009801441d075401d110b102e402002c2d0056005406d003941880c0c03a84c0f02600384409125200c005500c8086644240d150503803040c00782d402961035035014001400401150f414101c103040d4592030102d83e14 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 274860143 1250 274858893 274858919
    0x5210f030d0f05060a0f05041e02030c070506090a08031315090501020d0606050f040b0c030403240605090907050402030901020c070e040b0c19031a04020d050103030315080a020d020102011401030c0f 87
    0xc0d60700c0d41b0b020046142a0070030001c0d21084c280300610b0500c0003445420340c200ca00040d03200d241001445992034056240440c40c10308000c2810100d0f802035024a000150b948045035040607000280d481c0038405410b040c007100309020340c0d11114a183c0900e500030440f06401030b20300014085420000695030780d80540d00752180f510f8201522004001c1800903e0100c0003604d40c9070b240e00103c030300305a1030b40c0c1d40080c1c0d000005940303200b410701172006452b0042c1074040d01000e0102998040200d003084450590381d501d56000e21031149801100081c0c1703481095064664550480c81110070340d5a9502c01c803400c508081d0340c00c0e20700e04c41410028070703644e0926013203444505021000e1410b0036a1020118001c100d03448600880500020596040b0398407130010300f00c511104240080d0b203500d1898064100c3d0140b580c00100d6003a044810050300c403012480781c161036010b0360900d051501510040b40140302d1139500e80055401c0c40300100a019641580c10b0980d40d80011105580341c503200c500d01c0b44 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 274861393 1250 274860143 274860149
    0x151805070603060e06240c1609020708120a151e0b070305030a0504110d03020f0c0f010906030203040602070b1003030f0201270f0b0c210105210f030d0f05060a 70
    0xb007951801085203803c000c568450302400800060350209410046c400556200300240c10595020620100c2c0c110818400400200340860701140381001c0303951030464a01507414481c0d080881400001d08c2d4000d250400404204000e10704c2000c1c613110700340c10740341c403841445544e0384208105010400900703800071515490f070940c030b805040d0380e518801070001d030500034021244401002c860048c592200342900e06501e1280d0064075404e402c85001502c0d0051400701c45124003010700d003c15103641c00c64445003e0302c000c1d140c0582d8a945905005000c2e01ca41c9000401401c101010072842c250100c51107401d0782d2003644c82d14150807280d901207003624894080013010109050400070f0725006200341d0041c4134450072041c0240803040c2c88842008100f2211032050400000300709a8203c1c0c02e84504010b04c6160741d491900e0350400e0085442051424110740c1c134540c21a8240d080f0403c00c01c00c1c09404130a92003229a40c3c1c40b405480303005030425800b2028024144004242e4510384a4104015 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 274862643 1250 274861393 274861409
    0x7030f180c181b0e0102010b0307050a15020a020a0e2d06040c0c0506040b011a04031a09030f0a030c0801080f06071202221d0c031315180507060306 65
    0x1150401022003100c511540944001d256640d00e5010741802c0e1243e181c103502d0071615643c1010303540000183c02d598032a50600c0c0300350004d05050010fa95059155000d450002122500e444507142d001da02c2d20a2400004c0c0d40240380c40000034214240701c8085124402c660072100d01c1450483c4072101d15030380200007070302c1c1809100001c0c0c6542415031000600c40c005240405480c603140c1c840d0303414401c060780d055519103600e50041c02080c0c902c1d49000180c0e2a6146141c0c82c241c615260301088041b0f92480c00752107505136000ca40503039020420f403030403511110781e03480d0b41d0035600d08090010414480d00740c0c0400c90b04030000501c901c011540400405250002c0c1030341d40d503980c030210303090840c00e100806270660a1065210580d0340844902000301d4650b80340c16401c0c240b840f0380d2000d595041c104404005a102040902d00b61101901e070421900601c225600a685c5072100d8444d42d444e01f0b0070007081c0f5144c104200645149000d225070b034014415585015202c042c11000d13120103020300c000d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 274863893 1250 274862643 274862663
    0xc09080a020f04060504020c33180c0306070e0406050105070819180305100509010513031b140d090509060d0807050c090c03070f030501050109090c020c0907030f18 72
    0x3000d41002c84010850386070081000810940351030004d01207800400d60000b080d0311900050f000c6080001181151061056100c0149102c0407130542c02c5110080c188406500000b4020400603010484503808150041c19a03210f4a4164401446403040c0078106214a003400c0c00019503500540840d0340b0b46402c986d82910708031040c200d40307411210707c0160004001001c1540031080038004084d5000d18440c00103851280d60302c10000c0103482014100d2810f0f0792610090041620821030800001545810300e40b09156558035440703000004000c002c0d0060b50041503080d11b00354003282030740c0840742d55100c04000c540c60f4800c0c041062400c594842e00305182844240224503140050480a031103141100e40c1b4190140101d0883c00f400c0d18440c07495a00441440840c0350803200946850720039107402c2090390325103400200051994461051300c29035941c2c8020109200740944102d03184003404680c21811300d803034010000c000450f11b100c0c00301d141070000c00711100854200a415038010400384 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 274865143 1250 274863893 274863913
    0xa05190305221802090a0905010f05091f0e0f0f0403050a1206031403070c0b070c120614070f1d2103130b0d0e15040b1b040e0a0c0908 59
    0x18101c559801c00303450b8004a000c000252103001c0d0340e2200102074440c0c800740e100c0e200007091103509034042e0003c0031a11f00b484014420702c0c1f508140203003183e404842c02c0105403146007442c42e44180c0c8a1466807200c4007078002042d00384400200a020f828a440e405040769600000c0714441e00040e100100003502c00c011b043d03400340c441c201165203810a03d4000032216030702d64524600d01a4061b0100c500d40011800302c081c04407181100009200c0800002c1c46d04001c0d40c2c03158086089401032008030212501c03c0c07428040280c0c030455014540d800e002400c2e04083d440503106000f00c00ca01c1c000911003131201d44600915440681c141440580b1284661032081030b0303600d58002c600c4100013607200c00e2044500c4100110369110080141800700c950f9151888501c5007550302c2150848025440f400380750b582d070700c80c4c401c42540c82900030074a0680754590b29021503000303404010f040d104003030104001c82d4800b8403041190203000d100204210320340302d01c81c050f10310007520311446001d030300100e0301c403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 274866393 1250 274865143 274865167
    0x309030a0b090f0f0607020c0109080d050a050705062e2402030c1203010305010b0402030c1e0c0a14011805150a020d180605100b09060c010603060e0a05190305 70
    0x80d0760000c2c0b024050f910625041120381d4130704400c4425002160b030107142800700d203030f0301030040711340e400000c1c41d003096081d0424210559402000c500350040000c002141000c452051040d00c01c0c03103501005541650070225800c1c00c150b070b400e01c42000c1034018a110f11805038001d1107002c048442403000681c5c440402c41042c5841c814a0300c100f41540002c10451400750f8042c0100c0f0145401816000d840e9410341c1030142c21a00c0c0c000c01e803401107104100b03200c001550070701900d41000034441700402c40b040701c141d40f40441c00380741d5071000700c0e01c50408090f04100d06501e16030324030f41d01c3c00000c100390404032903030701050315034124054071640000e0310803020a400107840680c400400c007030140c9888a002040c1088030200b0a100c40b03894281000310b810031105005194102d68504800c008150074154130310f00e184102e40d52070f40b00e0140014494140c0348290881d400864011404111520030500b48503150342c140c650071105070161012084640c01c503503600b52505500355440701d003040b4408000c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 274867643 1250 274866393 274866413
    0x7031803050309030705060907030c05010203040b09040c11010c020d12050106050301150302070b040803090f06060f060c010906021305030d0203040b03161b06061409130f02010c0b100f080309030a 86
    0x503043d07072404100546008202d04104050080c403400c5d0081c481c881c954105400e801e05940c20003411500b0801040000c0844041a280c5055003154002025000c201080d00c4104454914903015401c050030f0441c60340d004110b0807400b070b04a0302c0340b90304641045c1d180c0d0210380f000d0180c2d81c0418401c1c00107001c2c800c16410002e501c0305460034010b15006490310360410306c4c9000c0740d040b5031082c00041040500c400510460000c2c81280c1d00402c458108800010346a0a40a0405008100c08590200080c900350400c058454105a0855036140340900201d51140c56005407400f81c400d540f000035020344004121001c4510000c00c0c2c40c2142c54050100d041079540104250411000080703818074805159900d1012910825001541302d2400d954003010035101c0525600c12071503001080600e100a403428840141d205c03544104581c0c0620058800e0300103000302419074a1103404101404001c486040252254500024005a0b9881282e80d1744d10071106410f4064002c4490040020346501d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 274868893 1250 274867643 274867651
    0x71a16030605060301032d0803060f0111060c030a0207061d190c05010c17030a0b040c090302030303041b120303150f1805191103100e0c0a080c0702040c050c06070318030503 76
    0x14100342c810b4414030801443c4125000c09448d4840000b00340015880c003404034404180303080c01d0400c1030900e4813101d581c8603540200b407084181000400104c1c1000268112032101c1c0d80100d04110b1503969001903410160240d80d118014850307440491080042c014218840c4c2e41d01030099070340182403400444244403032501c102d400041107800c82155804032005144508400303407001600120200410056611341008082440003410080c005030310084100c0ea030058000382c00413114403420a000c000302105602128902b40c24a041a0070958036804c5401482d421260881e403a6488240201d4045031521400e4100507581d90359099450702a00616880700c1900c0c4017606103c2582c081100b034a0640c031465145203800410000000b415000350005410942220003080c901103000f040c030b40c402c1003045400d0200c00c1c000203014038031420855010780d0340500140f0515140810160454005410409131405140005070596210384100010007240b14213141d4113802c5a101501c550380060 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 274870143 1250 274868893 274868933
    0xd2024070203070306090b060108100609030605090f15070201051f14150f090406150f05030a0603080714150408090409051e0601050108090a020907080c071a1603060506030103 77
    0xf00f00040416a940b00e80d000c041c3c000c035180c42c6540380410005040020061001e02040b41000d002e0144d40e6012001d1015241c0c0176900056644130a442180703003501f200c811040c82d11910740c02c0c0340081e480d039040358003030f220a4000b800039071510001b15030105c1040006591a00661074108100b1301240c0807182c56100180c55070109a100d4841ca42043d4044042c080000c08006003103c0d2a06052080c000103049480035071900808201c4010040c00e100003100f81048008000710741c241141c0c1d0320500c01150301c0a80280c0d201a10314255080c3c0000d000d1f803103198042c0c2c2000c40d60b01c1001c44901842035a020400714942110f04040000130414980251420700c105680c00c12401c40c908100001060b44c20002c14140d854440014040c00005007985160780280000000584400c0040303078010b400c6052481c260740e61102954601e01400c40e0180c210100f01c601d000d9041c0e505035401d40242605201c0582140840c035061341500e940380314260304030504100410219080c4e1964460a101e44 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 274871393 1250 274870143 274870153
    0x724051813020706141504050402030c0103020918011503050631020c03030c07141207150b03030a030b0406120203031c06030c0b04050102060703140a0e0c0d2024070203 74
    0x80d00e03084104c85c9919504044242d5070710900c9200304010606101e8900f08a805208601d81a400f0948964000e1040c80c1415004603c0d0358035691011002842d4002c429204401c0c0d6075030700944684e13850f0403207051001c00d1031b11021403950f08002c200c640048018000c40014420f1a20082c40405603120825051560034840c50b0200001800190b0117501c603201c5c010b4a810300e40c103099840301c1c47e21428a07944c0d8060300c1c80c04c1c004000a0140c4402503000700d10b10500c4c003100c12004001d416840342c0154580000030f140545641c01d03034086030400c0380694080046c05e4656403074000d0710305078000195140d8410b01c101108071454038034071140d000b402032012079030b580c1e02ea0304c0014014103034010b001c00e603101040920455a041000303680c003162a2505105081207408442061074010385103c21140c2c589241c00d0409004003c1c4909040700a00744244d01400c50401600049004814184001004621030050320740f43c5110300b40085141d100700741ca085094442c1d0700950284000300e03010300039 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 274872643 1250 274871393 274871407
    0x5040210122c010c051c0c021002072001080c070b100b07080304120c020604050603060301060302060c0705090a0506030c1918020a0f0f2f072405181302 67
    0x7a0542880340100994032404840c0410760040e800c0d2001132000008001042c00080000c525070102450342503c0300e10700107150100c1030000c9080201c01010300c080c06000054420800a4a44001781101c81e850203032410100401c0044500038802c0e59880088101807003040b001c00c0405c0d400540100817101c55140c1d030b03992000e00010030b4119103000e0319540340200030002801030090307680c844501c0615243c0e040030002d50010300c13180194059203010710b06c0800007a019890962042c030255400501c0d113920b6070228400076645214a0081a0041440380042440340e43c0b02d019450103400000d0203010800441800c0c4151000c4140c01c40346103031000d100025085000b4104156490307400c6901681d604c10303c00c40504038500b102243c0b800c0000d00ca804944c582e521100107407444413a030440c5440940c410300e000500c2c5d214118507148a0003046400151405200350681c0fa017405110703a802c1c001c891380c00c1a02d45d401140b0840c210040700b5603580c10035150404150441c00721800e401400d0501e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 274873893 1250 274872643 274872671
    0xa0b011205070905061c050c090c18010221090a15030603020915010f03050604091502090306010506040b030106050702011b050a03022e0c1b0506070e040504021012 72
    0x11080e48500480358540060100384902800640c0c060001d0030b00c103022a007040d801007042e074041c9060b21148150a450b02e181007003024040c2c2010000014a61185810715042d01030566000001313294400e458007003c0d0100b54004a241441d40c2c3d880c0546020705400080802c00e10b034400301d03000b64030203c2604041041400418a915446101e035130002e0380c0c1c0d0641c4140f00341d1541c082d04102c80c1079009680020960390080050720aa02507143c00700321511140c02003405030080d0741d002840350790405076080356040c055000d080042d800318112401130366900b0030320100e481075000f201341240d8104018800030b4010001420100e1040c50206e1844103211100b0084900c2050125240c0d00140503e07001d06904000035441c0b540c1c1032004122180c12307030802d014203580c0c030051181040c2d103540321f04a62034017a610f8003504088900a0f084d511101b0b16026850350401c4032000d007c10550819203515003400d100d01881194050300101c4800c2e04180252440c04030070f0201c90303030982c0352000c07104403803 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 274875143 1250 274873893 274873913
    0xe0c0702010311070602070501150312110c1c05070e0105011d030c150706050a0c0c030c050a06060b030f010b07080405040504020a050301020c0f06060d050604081c0c050d15061d030a 80
    0x130340580001070b207030501c500e0321900b518a40e0407810066801c005044c000f0483c820514040300c82c1500b070940c901b03200314050781d04005540185030740c000b031003206582901c000342000c800d5162282056808407510313242510003052080c001c903400203030452031201075007580015058140348000c01f00c848881c01540024480c001544201c0c800950200d6200100000c60081030380100c0c0c0003006001d20107510400600710800714102404102c0e100802609104040c4595145140c104a06000058440e000306a6950080e2103a41c00440600000201c6000a50035101ca0580c0700b110b0300d280a160408010140c50007030300c1660f00c00070001d00090b66540910042400049a201900e4003100464000c1c4c02c1000c003d0519028642070b459100000d040820455030040e070040c001511880d00a40d078103551283c46070704c641000e1400c0c401e45407060f0008041c0010b030b03410b03580a0104c51070305035034032a44014500c900c0c3e0200c0c0403880c0d0160034040e5140e19a402207006402c58980702402c1e25098200 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 274876393 1250 274875143 274875157
    0x41a0d090c17070612110f0318070b0c030409020a0324060f030e060406180b040b06100f02120d0f1a09090d020715110607270e0c0702010311 62
    0x152003030071420000c081c940360036400032822040252081e01d140c580040d000548407041084015560b641d00c914003910344055924a110324540540c5a2030408803071025a80d030b0802e00ea65510801c08000b030341070107250480345001c0380d500103141028500244840650046030b40d900c103054481d04940501c40c89040c0f09415088151003c03c0c07046e160040141c0480300e058280c83c101030800003200c01e1200009207a036001030b4416400a1001d80103445182e141c40440302c0105179640140500c02488810884140101401c54001300500b01100e0192428061084500090b03000102d0711241609090302804450741d6091000c1034480d01095004219200321340341c0860102d1000c1c07661520305207040b0843d03006481000501d9007040032000655a0119446002080e400103500a1000d610840300005035035a040704550003130801c001d004e40b0010441e4007000c0d60440c2c0340e40400000e0b000c41101400c49900b00341c00080c0d925100a00f4030b41e6403181006070305054680d06240f5500480c54014105 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 274877643 1250 274876393 274876403
    0x1030e0303130303060501180e061804050d0f050715050702030c070b040e010510120b0a230907091d040204020f0301121403030121110a090b01020c0d08041a0d09 71
    0x890150b42c074001d4200d038400e030013a9040004440804070181c0c9801038003403d8803400d484103a10381c0c1c1e99100103074950541450008144022400b031000300701002400140b081d655488051120700c4820040b210b5014520002c0c0002040c405082e680460b141d01c40303500000b251060388d2400180c4840b207803800e08960b2041999100029003004101d102068030307400340c00110344100300202084002005a41c40100c401d01c034941d00e800c030491503034034001004000c00c40d250340022031003030072116020320080404d005030150030200006003220344940b858005070341426552411303103140f03441055004040104200d070031940c200440552804841c4c0610700038000680c9400c004031081c60080501e148620782c29495500600050100201101c10b007040034030200034941690302103050845003a859001402d0b00400007440201e0184d540b904401401c8400380c08603001c480c405010300002040406000e0b0400b54103110500140c00303000c2060a90070058158282855018074250040b1041c818045038 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 274878893 1250 274877643 274877671
    0xf0406150f090803040e04081c0911100c0b0c0c010e0102040e100b07030e0d02010203070215300406022107050a09090c09150504180b040b030604081801030e0303 71
    0x890a0703400b16640c0c01400440004c1c6003001d182c407a042913035890240005010314030200d4038883e1a107a10880d480e18409a800610181d02035051614410007082116030154203641260704c0c106000c0c004080810754441e0240c1034980c0d6400444000d03404c0350301c00d9607840d500d500312240b10101c00d0000d030024140d0300912084504100700780282485599200c510b1014052100901103600041c41d02405017042d0703425202a502480102e0452081a40081d40403000022418907501c0340000f42000d0b285003400d144002c03048084c1141152066851148a0b0300c0500000d00044c6031500a4079210404c0a1a00340c1e81c0a040c0424034031050440c1c0e03020006401007200003003190b0060350ac0000b805c4940c000c112859a04d04010250000303401074203210000d40001c603911310302c03c4007214000c1012100d002e0309074244414000103800c0030f04c00544075034280000300c4030900d8081422030085902c9942d80b46800f10010042c540005020300680c18160b4034814944041014002148a02408000c441c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 274880143 1250 274878893 274878917
    0x90f0b0a150e0129090d030c02120c01020f01181502040f150206060604030b07140f18030c0910090b0406030b070e090a0506010207060513080f030a170402010503060f040615 76
    0x51221413034101824881000c2c102800c42481c1101100c003241000d1390810340e1001795007004d8605c0f80c02170394000d4020306d4013804100c1c001c0020602c01038200d001da098901c0c9010158a1b01c2c00c0e01d1200c4001104040000001400220303015200480d40005500140c1020f81d5a8400703010305406074810141040c948040290341c070b50600241c0d6016074111381480c201801c685403c0b94401c0018280d130240100820316407000b81c540c50a813078030301140c29602d5540307600030707649840d20030725000c3c0d4240a403040e100c2d01c0d880c074680000d17010312854034001201102440d02402c040074154a545194000e90380d00808004140d000c3c0d080c3d8401d2655803101d084880340f0f0070510804190081110410070701c1d0805000483c4e901051076070032079001b85000f42d01c03009000c00c407441c8002168054501d0f481907032000d44803000044050024101c040e00c07a062481e48a080100150034200c0d070003800590108005207240c9086030000c0c0030203001500000e46140c84210482c44a62000c1d801d07008a90664410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 274881393 1250 274880143 274880159
    0x20150a0b041515050414010503090c031006030203120a0f0f030e060f0f09010b0105040909030e1c030801080c060f0d0b040c030b030f07030f2a0e010f09090f0b0a150e01 74
    0x1442e265003840c13520768074003460300000700300c07481c0c1000a140c1004400004510001c0c001c001c1c403001120000e0030b45004c02800c07111380e80240443c1c40102d009001d202c100b5020514000300b50303810b910568a0341c2c11602042ca900f19640109009803005060381c680064103100c0c810040c0500c5036005078510720341401d00e0220749020070340040481d05960304100c0c0403051030f44e100040d1803c851644001051020951400713603800c2c2e05400741e8035000703440c0040b8000c3d0300300d009541154060080d01e9480310f60342c880855540721080082c8141d00214200116540010f46400800790b0714452040005e60111500004003175422110314907001a803100003005240c6014801030300100c0c2d003d00204007482ca1956800110a0b5122000d88980b08451052920380080e4000c0900c202650343c0c0e80400980390807200080340820b00503054070541003400818241e28904c0b8019156030000249007104600340c0e600301d5414801003820790503e4072604420300321001480342c0c0c2d020b40720340b0f04442d240758140100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 274882643 1250 274881393 274881419
    0x903020a080f030703050c07020127030503071101030c0f0801120201090b12070e0105130905040807020303040605030a1a090a0e0c060708040e1021050705060c0d20150a0b0415 77
    0x440c90b207c07400700000e80040c0c0e0450030b07200107485215188018603c5104185540300403550015141380000240c44c01088007950010b0000c1a013600e081001c0c4610301030844100a508078920003103203845005104800b044441c0744181c902c14900451100d4a801c00821640c21020868071602410010300c80380300c0d00031112918002003071a04a04002c903d007031f00001c0354000d00c81da201240d40e80c0041010710400c01c08584002d80c000d02200d607120b55800700100203038001c5580609203841c1800e4040d80158040002c1c3e1607880080400c0800d441346003812005151216294540703228840002ca5540c50750720103455560300800d00c06485500e45164490310b10750042c088135080c21181400d2101c0b0b48510301144c02110462559003412038907203022441c1888541000c2d41c0008045070318445c0d0040018909140b0140340c0e1540d004030a20300040c03a92031407a1002600c240c11111210300340c0e030070f0040c0c0140c1c41030030018045442c2001c003001c1411128500c144030034080c1042c4060180e5201140 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 274883893 1250 274882643 274882651
    0x201080603120f16060c050d0f0c0807180302090108030d0510050604171203250c030203092403040507060f020f0312040f020a080609010c030e100903020a080f03070305 74
    0x2000c0c1c079020702c1c01e09120610744120303070070b8425440e07000c41c2080345504071600d00103000d0340c003000401072290078400140c80e03608041803071881c1d03e0400e4560722004241d400785512205041c2c0700da00441e12004010383e6007080d0b40c03c0c10402a12a00c5001015903034800d0440d00801810300515540c021100501050380e80041192070b05030303881030080005440782d108450843e014411a446d104008032125802d2030003040c0002402d460220601c000c05441c42800c02c2d16003907400c0304c009409048941510320482200c40940036030024030544845041c00041e214485440d4040059042d00714010350403203030000e4409407141d51150317030140009c6400c2007040d0403003100c0f80020030703110380d00074038a41d0380b44540721014a40c0d0700001c000ca030800c5210b1440b0185198000d01c3c03420219107034155a82d80700411603c49c26550700300b4904001030b81c000d10681412004000c0540401ca4105905801a0030b60f00421405c40c0f1500008501050540020b04030300c5d05049a01c3e81d032420100740c028150307074010b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 274885143 1250 274883893 274883899
    0x2210c041a090321120f0610020a021e220e0d02060903030a09170c0a02130b06040911160807020a0b0c150a0213060206040507060926120406080402010806 68
    0x441e40101c3d80d0002295403080407001c3c005050341c0802e00c41e40c0b9580c0500c442540d44c11a110050042e11607610099501c00d0311b007035130100544e8160b5042241e403021140d90103500039041d9071100e0115001e200c020341502070090100807080001c4039200d00c10104001445c203100ea40e440c4082901070090016080605603403008103103034144851126100d11020300554400d503510076050040110844500e5034400004101d50340b5031042c14001034542c6900c090803032052080008011019500e403258051481014192030300307142c1405091001042420b09651022005018a15003450820300100030355200c1c3e4201600c902040c810b00c2441080f41e00030b421000d0052020105004002543c03810b0040c20012824a6072216030000b0300a06c100148403599030924500800c40980025290340aa0b114008440c0802e598000448082c0d00b2809071902c3d04500c441d112040041449151035601080c0741942c0e4801c1c104945483c996000358408000700f00c1c15020482550f80000034164056019 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 274886393 1250 274885143 274885147
    0x160512040b0d0b062a01060906140111160612090b282003060f031915020408070501050f09180105030f01050601050d091704090b0901230402210c041a 66
    0x840b03107911403826002a042c01751142c00211030032140e09400920040102c0e8001f0450141c940440c3d006e00d040342c1003054086614000c501c44804030014510104400c0603400c403c00a04124007160349400ca008200f0b032181c0c9860356400468000d08440f4000e0744003241008003c409000d4000d18410040203e14441e4580700100b500aa880030822402c028003c0c4086e6980d611b00000540d540010030794a501440741c0e45140300d0280004403240c0c849401450030096001c042d442103020ba10550243c5503440d004580200419401100a802140090030241c0d0400d07202c44041748000003116658100112200c1c01000681070900402c0b030070300a128003c0c002450030345c00103401c903c1054105108540d40d268102c0901200c104406860601c10b40c10b29603a40da556003040c003074201a0f00e464810741c1803500000f0b10104200d00324140b94400000c160b2103082c4ea9081100940015441001c9049926200b4100d40f03030000c5800d20036071000c044151079a0904000e030742c0d00c40c0c2c000180780100340701f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 274887643 1250 274886393 274886407
    0x30515040c12020301020c0d05090a0807050f150c010f090b090d1d06041214010e0607090618120b0a1d03040311120303070807170c160512040b0d0b06 66
    0x2075801e5210688510564a904030300b02480400d00920800e24501250300030380024030906540301000b08241d4074100d40e03900c0b07801e07200c02005441740036610880e030f03000d54010b00381d08040c1404100b075041b95014503900d509002c1588651402d4900c1061100721440e0342d00e030702d507040180d8000c078213400c48035460050140c007025101c09881d1000a041c0c01d040c041003110324400941e00c0b081114094960502481045541d074641a50003008402c054540d950a2481149512400140b51b92081c0b07403d0b44c4810860745070142c181c40f850703064079041d80480c0f45c024011842000b680c01800c0c002d44958404980351405040c103204441c841e42c1c0024164a00e58000f5499400000946041d41d801003900c554409100e0000781d035450b09054200400d000c0403007003040079508000401e01c140030603100c56075005035034240414400b50482c1d00f2500900c06100b4a030400c143c503140b506a9921502c01c80340c03268200e201c0384429030419032003401b18040c0002c042c4a1540385000e680100c090903103d16003400c034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 274888893 1250 274887643 274887653
    0x3070b0a03050f151302040510051e160f1707050a03020c0f0d02090a02160c030c090506060a030903020705030f1b120703020616020a0603020901080f012405130b030103051504 77
    0x8404950f90b40f045c2e200c039805030001c405035030460300140750003008160b000b0f110100103082600000e804005229180c0708564030410034170204c4008400c00041c030741155000ba0b5685228440e102d8007502e11100e0b03520002221420040100091802100280764180552400901d024002d1120340c1c0524841c080b0403a4541310003600615682d81200e01042c25903401500d0340090180314404100d041124210100307021034000301009480c05008680b221545030303510442629026225150031600811403041010b02c6940041c0c03806109105a84140d0340e502d00003440d0410202c13586131140c10148a0080403140042c04107403100007651230295500344541c0203500d440e19440084d0080c4c2c00040c039025441c0c154002030104582c0100008140ca072501401070080d00160440f90100d503901c00403038000d08041c00220b048030b035690465807000313a4140b40010b03610000c0c0c000c80c052050038001c00601c00307a0b648500f40a000c80151007610b0750701d541800761070249004034103031794a0605001c1c8070200d1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 274890143 1250 274888893 274888921
    0x30d0309050c150f070f020a0605030112060902011b05010203010501180b03042a0303030b0f33070f0f051606140f04080f0706090b0a02060609090a0203070b0a03050f 73
    0xa049a50b110f50007501449040c2c107200c3c554000a08100020b8004100000035408190850080c2c0350000c50325101e05064aa5200c28040c01e410110310f46408030004003e50807050302c4903c1807421410b201100d0002814210004808540c1030b5000300c014401942d11015000c012001030020711440d0746011561030140c031001c0e2000d00710303200400b50317094083e41284682c5c1c641c0c0c80750054680c103150f4030f05004009140721a8498800c1c10208011f02c007514041c40554000c910401c241000c0e00e00b01a0361321503120051080744860f401c140720301c20101d2a00c4020f040303098041c0490840c07004080c94018200800510740e1001c0d2800442d003404142d0b80850b00e0880100c0045065958100501e03600105000e2a07215013035510036000c0302030030380501091030001c940003600c03000040d0b6200e292460b0030317004101b084001a40312800250b02440d06100007a0410110419035051031102d401080c18524a90403a41a04200094615003507500d40301d2242d210364120490030850504413102403401d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 274891393 1250 274890143 274890163
    0x15190b09060d1107060c030b010e0f0405062715030307080301030b13080703051b030415030203041e080304050c060a0807110106091b0207080106050105041a0c0d030b030d030905 78
    0x484002c20140240481948801403007000c1c0301e550b54803aa6a03192080140034800d42d5840000e0401840303041035402401407101c0318034001c00142c200c400c040c00340402448020302c22540908001380c400c175070360304452401d03000102c004141c0000b454501100300d10410030910b464001d034800c000c204003140600d420307681525445225155161504002581c046141000140c280791000038490100368200d4010506da2403031801501001500c844280d4690086e8170401c8080588500880000e5109900440d4002e01c42c04481c022080303222203030301c4100502c0004842e608000014081809070400c420310390f210040311100c0c681408140014001d40c00a020481800540080702000d40000c8d00800c1c0134141c1c10b070081124400c107250003034000c0da4a0000c580940103240e0081160001030040d5000e40360107031100d92500d49000f80c2801d0b21002071080c1c0050749002d100039003112005020b14116040c860350003091011201c4101803c21801c02aa03000b458a080d903080700117100030500c40c0c55 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 274892643 1250 274891393 274891399
    0x1050d0803190902040f0204140a0b04140103150b031f0308090d06090f03030b13150e100905010b040302040506220b04021209060a11120412051215190b09 68
    0x2c204a4803802402611140c0e500030f51140c1486480e403c1c1400e1a80500300315260340700e5001c0f46410304014007852000500807900d07058401c00041c0031302100d1044074500208103160001d801001c0c19011310040d0306903000306800310b0002040c81040410300041e032424115551685c00d00d1451942e0381800343c0303d20190039019007030410100041c40b00e1940300902c0300d0f03000303a03080c0508500c519005004115640c0c10910a20720035503400c4e1444076602c5000424102d03419048a13a6040020317560b468440205008e840000c900740114401e400c500400d80241070420040b601d035411231041006039003004100c54003944445040420600503001280003400d4030343d20020390301c4880c50200300030348500244002c181d071642d03050214840700090024800c03084190704005001d0364624041c0d052140490950140c0490ba020602192913410030700c014016a0500701e1030141c0c4003150600c0014102e8403403040c100300d000c500032a8200b5172001d100300c3e280380c0d51002a080c1444400c40c0b15000b21000140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 274893893 1250 274892643 274892671
    0x106110a0308100b12012102031e1204030302030c060601030b100c030e120f0d0c02010903080d0f0f020702030d03020f0f09060409090b0403091d010605070302070b03010602030703020601050d0803 86
    0x46411070006260041c2c244e80c00041c0c2d55140e4019205c80c102c0082c813442903c1d00e80e03c0140c205072501140390b82c008a50050203000140d450108482c40346d03c9001ca988114000c00706094504c220035401400218070a07009140c0701e4003201802420454028000e9043c142800381501882e5501055140b21a02d9030401c803440f400d25040442d50491040c0ba02900941c2180c0d1058000d40000fa000524850642c111a03610b80080411603420703584200c02130114452920900004002e0b1b4054005242c1d64000003540ea40c0d40303030318031003a0b440803040001020b5002900c3c80650a0074400c245240040e41000c2d46421808040c1c1503440c0f24907115071000794004600c0c1c842542d292070071200100780103034040c003840c50107041c0003220800a403000c40120b00b848800260b4043c103510402d120048200d420380c0c1d1b5a10b4184c003998681c0c07051604170114060340001240d10b11118000d140606600e600454998006143c041d28054040e00041c0c802d01c9048182800504500200c9a010045240d120 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 274895143 1250 274893893 274893901
    0x20030a05100b091612061806090501050a030c1a0d0504060b01021c0e010c03030b060703030c0912020906012714190803220801060b0316030203040f0b10030b13030201050106110a0308 80
    0x400240125003041141f00340c22116145003107800e030061030a0342d5016204028a9a0710001c02244420780d100044c0304d08502d0104000b4142c483e202c403034481c0384070396103030b881c00a9100d400310840d0f01c129070482d555551504181100d5a040000b00740c000e402400711244410311000150001d0001c00e000b43c10001c6c603e03030300300c201442034000c2e21000201825558841040e80b8002c3d0240207906072600000d040f042e40041c041e541a4401c4032108d0300a09040600c0d25801e00448000110300480341c42400c0ca0860350181d0500030103014000e103202010380070b82042004c100408002101500c10f0700c90702c05071080c01544808070403100c030100e07100c03000080601044a05030075540717250704c400c02035440e001c00001e072003207140005c52207a01c2c840e0403c8150480040140c04901050710094180d000d020344c902d001840100b07443c0d4000710782d050340001e81c80c1ea82c0e403810390036001190b41520250281c00c442c0300b0150240034050241078141007140149121104c00d60380d505e8800b030054100b0100c00082 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 274896393 1250 274895143 274895177
    0x109061802240d0204030b0a050702030f0a05070c1805150a03021f0917010606020c090c12060a0b07031e08091f06120609050606040c050720030a05100b0916 69
    0x10f85081c00e900070195280c0d03507242004001408215403441c3e66505200016101601c0841110025040001e5080c00c02d005034004460981180c1c204030b4a0150720b8402141600808441c50060304164202182c40c0c81c10341018001b41c4003c20201380110100c88003400160b40c1e40d5190501c11000d24840b0303203580780001c0c2c2100d4070559680a18400c20102c01c40d08803261064110509854082c0c0132601654520001e0000e004400c8641403d8420103010007241c84030002052500581e0051280c0311598031800708a51a43c48550124042801a4032140422002078059810784c00c5a090041152424a05503503c852507807044040010b9403000402070f48000e41d00030006403002c4126410701055600e0000c4c010085150207481e14421a00091500d18041c01920320b403181554400e401d02400d40c0d40c050003181181a248192031a128148500392801c001e1410300c5e500442c028000200407285120031240009009801f03a00030b201001401540402c6c94041c24406181c121110780c951008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 274897643 1250 274896393 274896397
    0x4022703031603090f15050409020d060314031315050906030a0f0614090a0e0d0f02031207051306050301150c061409010519020306030a06051e09010906180224 70
    0x840c00c026421101d150241a8402e00001c2a604245903044420b5182c00c11b25007038007290080b0000082d0204402e02104000d600a040e00354450303d004200140c40703507201000440c0646444926500104002c0b290201d000c3c2900000c08605034442c0c1c0c00080790400030900c0c80b5040d1054041e4000001007255008940d02a4142036061202007000c1c5c1c0c0c86a510f1840200c0c070000c80c0b842000701502141034148644a04c0a220103803000a10070a21040300c19110345c1768448918096000034040e10074810806a1070620641503940e420780d80e027070a415072981c0402c0715004481000381c18001400a03032141e402c81150110b290405a601203a5850040054100b150407603855040003418003004da081500042d002c2c180c3d80500c0340d429041115404124001200d1943d4913502c08020400418404e9114580050034005d034200340951a040310100c590095540986a079074584810003448428421041c0e4203244c1c048254a81b111034001602c1301c40645a90004203c000f2144640c0d1121181 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 274898893 1250 274897643 274897657
    0x1b0e120a062316030e06091b01030906151505130501030f061d0a1b3204060f0201050a0528020910030204050f0102060c040b091309080a0e0402270303 66
    0x9007502d0340c41d16000100f850300104814001281c00c0581c04030a880000c00d5440c407621001008010b00c0c810110440d61144d11044a2030500d50344100340c0c80402da4070702814100080340b9000002d0765103402421640904100d8100040010920003010000e0181d0798200440d5024a00446e41154044450000b010160f21844100079009100b0329018144200588510381035107081081e410126103802c072008078010050001405002200b2202e201a042405845011041c1540442140c65005007580c015040000402c520030045030711580d0900450394080b00203e4180118240001c00c80000328920b00b0000310200601309c8803448c6213940c0e05884140000910380301e012100c100c0040d000750b00600a85010300c56010071030300d40e5400015403d02450003a01c42030f190070700d400004001c83c0c1111540683c0100f440a0741c0560b50064000e90603c40c0c0101e036034954503e020080075007006003010003140114010710070b1101c1c0e00c5984000c000040d6a00700445900141038001905500c6816 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 274900143 1250 274898893 274898951
    0x40b0f040b030115030f05010b0a0c1a0106021c170a0c020c09010f03140604030e0d031103030a06150807050415020106050d0c18020310030201030b03101b0e120a06 72
    0x1000006151004c04180f8001c43c0d41034074100054003540c248801900c0003400b41c0c1c200d0f180100306401d6013500c1014181d000900480d8002420a403d01100010860030313070109005030320010b100e03030300205c90482e0030290031403604104014810401d422149514010118030388d04da5070300521201b40d0f000740400103405200800e00c1d907403903071140c0d803c822001840c0429180040001035020300c0050010b04d0078003450309a03d0b80c0e444245502d08124808018100c110104150002801c9010404001450040e080044086009801e1420368a2058950300f40b11007081406010b00850340d400034100c1e404d864214089a042842e4003c0682c0500b0442d403110b40c00505100780c1e08203000040107041c06450035181001c0f0700135070011040099002c165400001c129030030004100640c0a54884000f0700c1028040d40c103d4817000c1111000ca9600d40214007a040ca601d40f0300d0034071544248541c4d000c01d400c5880311050700304515040c6d0360f8031449000a0849a503030049035001c50703007910700c101041c2e504 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 274901393 1250 274900143 274900147
    0xc02070501050f0705070806190203041709031e100e01140703020a11060c0a0905031f0c0309050d03050103021f08010315090203030a020c0a0b39191401060803040b0f040b 75
    0x15015980d90f48821998000740040312070302c10310709e500c0b180212802643c100c82849950050a50103010aa1008107200d0303040c810100c040e40d01405030001001711020368000380112149220501054070704d42010507060740d142c5605100d10000c40c48030990003045c0c1d4500161960340303d06041d585480024130700c0c05103219810812420403144401819a0681a501d55008c540c0e64403c8c103541c3d07800045041c104c0c1c038010080b50110a03259000f075040c1c0c502c07450046040c00c6c094132140d040c40071072405800025110001442582058400c0311003440e008400a1030241361306000502280c0d0600004004001c2600703034401203001c0d070308001165900241030b02d50310001060081c0d5510f19a0100f18014080342000040640201068840b000044125425400c48000c06c400311110300034641d07500d44250408011111000304140304681d1000b180c140156030359803c01c0394403201e442c4c0c40030800360305120090000c00b4010090710300712024815500e8858500d5071400c11540600c0c4c10030900d040c00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 274902643 1250 274901393 274901399
    0xa0305070207080f0a06062103050c01090807030c050c010e0d02120a1a0a0c0201020315060a021501090609060b0c0a1721060103151a0702040204050402040e0601120c02070501050f070507 82
    0xc45d0b14802680724400c01c0107800d44d40c0e10704508000714411b0113046130000b07201303c40219000300e00620f01200100000100c40d000c940c0c030081c01c1e4220060a500090130501a4005c0060030403a0840c04c0c0000d0270b0204400b0346580000b22003003c000790090003114412844564421b00300036142c6110340c403c096504d0020112124424250101d40c4148044e003002007048915006208880c0138140c90b014600c8600d0005042c000c0303d5104c4048081144100c0784c40036030070002128520b010345101c81001c151a8640340130740060b600c6030780241001100811255251560028810012640c4155a90b0940454007024a0140150401d4244080450b040001d0001110341d40303600c1400b003600c0401014071079800228a4034014010f400000c00392f41c540000b40c01c1e4550140c08940e10040000d03290503201c1002c20181d820503440b803180b420704a01800403d41e001038440c645c488440788204804180e60030002d41c1d401840c4202030501000003403400600c400001200c41c682e410104444101e41d03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 274903893 1250 274902643 274902673
    0x80a020a051608100504031205070905010201060b18100c050d05041508060d0818040e060106081f05100e04140708010807080705100c05061513050c0a030507020708 72
    0xc90088070240500403003a94aa51007091040a54045070f00401c04280c60300c244400401c4085c10940602001101c4644c54020070700441c3d00c07070110f6540b603410f080d10b060f002a080d03984903000100b00c15030070720445140102500182907452011180465001d030708141c161000321481d500909a801440d04145009030000c0081007103452075203454041100410f811526100c1c2034030b40d2036105400640da44046407840029100c40440c881c01d00c2c0d00c004000d00082c0864160302c2154190382c01c0b070001000460307000fa110726401112860000c0c184004010201d002da510760007018803807080301101c20007407481000030740d40e00d010152040003803590b25001444217100031a40400001d4000d00080b0b00000c1c0403840030100d80c0403000a0030941d003088104112401c3c05400f0310700300041c444d800004144d08000301d60046c4129401295481c0c200024000b4000c200d5030603c02c40c504044c1071000d516500710032600500910b1800144549801f04124103120003036000881c5485804070b10080300c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 274905143 1250 274903893 274903903
    0x40b060f070f020a06050c060f060109080d030e010c1803060203040507050a09021305060f090f030a050313080f010b1c031110022104050c130212010e0618062b080a02 73
    0xd000f11481184c031582e4040c00c076424411725244122641001c0e011030001854466600d0b04400c0504040c4a4151102d80180c544219452042d0020382c85209a02c0000028412550070f01041c0c07820400d88600d802c44c000c4000000d00c8001c3c80c0560000c001010702006128540281030002c1982211580c1d80700104040c0d0003c0d4009411515600301c0054103143c104121269456030031180c50511080a0400c070b00780024a403040d070580500050f4500080050005110100403d400520f40c181801d8105113031280c140c031614841d0380f40403002032450781c4420121030b0300c1c83c002c085400031800f50b180c1103503032a84c200c1c0040480d00c00d080d42034403409000d402a1001d141d04d25005084541b4403401e24014480540d00904150420200401e00e0705044805000d00760780740c0800752418030422992010007600746e0111240c49600c3c8148442858041001b00e4060181060300c03005040140c0000c80002c1c10b050f120390840380d14149940d08031f6558100405043d08140300300e858200440010b0746603 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 274906393 1250 274905143 274905173
    0x80313030308060307050f04021315020d110601051f05090a0303030b01020c06030c040e040812150111010917090310090f031b030c1101031d0a0b090c0609040b060f07 73
    0x110310400000343c1c5074100020b8032001c035480145042d503003103080410301009502103c1c084805401a81002c0303928807000200541c140c241c0e50060004000c0d251004225a218440c98040c3c0d40045004000c15070782c013203022455990f00381c82c801c21042a07000995072481581142d542006a00324000700745901503002c0c0c140c008c000e030203864803260410108151403108070f070040c540d56010301003403010900707031070041d50301501c1500300510300040301030050034680e002c80c2c4604c0d50246034001c10310ba80d42c0c040c0b503c8000d022020000d21045526540342034010014012412000704080344c0041d5030754040081003000255050101701400c480d0030807131000c0b01040810760201d40089181404501010500034403540c15a40d440c05184286e5140c2580c2d0300600c01e074a041603107852002e040b9080e40407060007408400c3c4020460070140340b5240c49802c0000780340702072940103000c00d03680c1601d800d0b04607007184400700c40000300d11000c1c0c0001605801060040d01ca1140042000c0041208121400d041 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 274907643 1250 274906393 274906397
    0x9061c0501050a0509011815060b1c271106130305060105030c0f0a270501060c200f3a110604060f030207020a050301050c1c0908120c040803130303 65
    0x115542d10b00004d003070707440c2c030900300c41581f0070f1012041c0414280d05c03100301403101c0c4400101c1e0081c2d4610300e00ca5280c01880c4114800d119252020041200c9403040981c0030720030031902510351004881066200035441c0021300400400360300d1803003d40e80c0c038040f00d182101e44180030401c00d03182d0030035a903514024001d55000344034202440600c2d15080100746c001d2031004001414690605c1182d40102001d1080c0400318140055041003072150f5000b801d001e444170f5038900315080c4031400c01c0849480b04514034204449240038203005a11313008003410b55200256000710302c1d110b0325004408144088007c4a8080e01480c335102e41c01178105280c2240c25010308125080303011800d04200e03461081d4410326010803c0200408d10141c0a40c01818115000504000b40d481d5101c02081c2500d400711020b10303581c4400100b0b0300500411041038900c0f036180800030403a02c0c40b166140130340c62040c2c450f224100f00048000030b0010068000b100d0140481c0c0040c2d940340c090031190140d9442d164042180 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 274908893 1250 274907643 274907651
    0x230a02040b0a0e0c0c1207110906010903050c1c0209160206090102040f060c0f020a0b0301060908011401031b030c0b04030b0a1e0c030605031203091c0e09061c0501050a 74
    0x4003860030800798016181e03c0828000305403140c0400c0b0074140c1c001c4800c06654010400340c0031910742128040d0035003e02500b0000c46100c90340003000300702ca81c02820b85060288611040c00414800181960f0b168410790b5400a1600030701620103e0440c40ca200a41c4081510704015050075a40074004035051541c08032401500c40410302c600340c2c0158019850a0700c80c00c4010408284507016284415000320022440b41c0c286801160030301c401508403031880344000004009203170344110713204001c098407002004a91803040045140c0981803002814a50041141150030140500003074011030344140810001b130f598043c4900c03140c000b880305035195160710740003c01c5104503000d048085000f0351100302003103103582c02c00340c000d0890111407004c065a84d100455161010052107124040010b9042d8403440c180e0552858003141000364a1300980181550000c0780e0047c040501a00080380c4a4115503180404510320700b160340041c8003990081c2c1070600c18003c0c1940064091668500184 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 274910143 1250 274908893 274908911
    0xa080f06010e07020c0f0105070503030703060f0b1e07080c030c0f0c09060904151d0604060c0e1507060207060507030506010f02070503071707050405100f0609030c0b07230a0204 78
    0xc5954411183c3d030016802c66400c0c82c005140541420041caa0141803203403d01d50b05071600d920b1b44e00112040c4d004641e6682c007e1040c05140744000c00101452801c8a213841401c181d90240c0101c0840a10282d20022405030100a10301050f1944003500200702ca449140c0c0c100115614400300400340c04500807040380300c44038100030074454415403018003a242a51500c0c2c0d5070b5681d942c911106840c840d0b94600300d00101016240501c2c4240364884020801403d1908081d07080340c600c501450140403600400380d450f51942c1698080c0b00034615002611607100e801e05402a10550700014010f900e404108006d0503010b0317026a000360b40c281e8601207440356404080e640e520b001d000707160741584802070030800686051507034001501610260b480d4903a81c2c8001c1026a10252940049010782c100d00b40103100300204c41000414841ca000c560051440c0c59130300440320300d8050342d90252030016440f02440b00303115568000090900803034603034103080e20015840c1c68419504034172480c01c2c14400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 274911393 1250 274910143 274910159
    0xf0806120a03082a0702121204080d1803030212070309151710030b0604090305040312050903100212011502151816030203060a02070201140301081c031a0f040204050a080f0601 77
    0x7884c041c1d0803c0b803c030700c0e1003071680821844e4040342884016a00c14051040f02d10803450000c2c1000b40401d000500350f2403131900010301340004280d105400c150060780e04001280d0b0002c1c4071207504010000681d617400c214201100d001c8080e81005482100000325002d038a40e2061070400082400003108000c0d07100c1100080d1050018132010b00034a0524000c1000da07e07055019013116842414031900e400c0c0c0c1d0355242c1865201402119002c240081000030981c02c0510200040e1138031041c0861404d401c0b9650103607401c206000e000b80c00d007984003009031418020000c0d0244c1208080d1018104d103007044414401c80c0d0400500001d60040c14580c80400ba01d075482142940c1d4000c0c0644855910700310007000940003158141d0400204d14180ca940c0382500c00150301a006a0010b418044114a00c5c0002800608110b50030503152610101e08640301004414490404030780d06d07503a0b510301c100010044d025940169501c10241c03c1d00241c0c43c2f138001043d10790310304030006a984980e40d40c1d941e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 274912643 1250 274911393 274911451
    0x801051f0b0c0c04020d02091908060f0f0103150207240b0607081209031c050402100c0f022202040906050f030703030c08160605091501150f0806120a0308 68
    0x105226907400000b43c50114075054025107030182c1120001420034a000000070b403a040718001602001d50707c040184142e610034489240c0c09007a0074001c202605040004440c0e8850510001d451039600743d500c12500d038025011501c0b010340013424100c2550700c2c40c02d060080b5061160344080340d4034102001202c1e04001d02550081c130f4114000a05101407001940d28101008000b0002404100602c9102c107018143c184403058903a48009602e103454814000b0207400508801e00b4402c0700911480000d180241024550754182d880300c24450b501c0c00c1012407201d1140c9400b000500210b0049401c103101d502c05011600111181c1120200b90001c0c1600d4052a01003d000654042c03440804240701c2c100a200707001e11030140e104142c6282d1214400c6610a503001403054000d0301d22044504690100c80d40540001150200c19840a90f000380c01411140d01e0501442540f40028410b50b03a2600c059103030507550006c1e00c20441c0680740c028a41c030400c859072603d00030005a50300c801216495 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 274913893 1250 274912643 274912657
    0xf010b041205030c010e03130801060b0a11010608060705070201080c0f0a180302030d03140a0c0807030b0307031406010e010602011104060c08070f080a020c19050d020303040801051f0b 81
    0x90500e49400c00d105a45408a608010b45692008000314415844240b040380c841e000205d019640350483c0c15a20b056000c150340c40185940e05150080c0944a000c1c0b048030044842c50030203c410b0404955214003401440d4030034213040c0207140811981680000040903014801d0b41d40c443c032a0740f0703480041e4036401000a13948440a0a104500341e850041c003541c40d0841404a400a03019036030f40c0042d240040d00c10182000030f4a0754400a9094100784490750414900b140074801000c44d10402000008010082e0041640713900c1240d00340e0702c003030003610051a001440039507d00d001503045659003d0a100f00301d1603080400000400600c1840360317041c5c40c0381001c1e03020b25081c58414129066038000c0700503100000d0811000307000030403410a075041c540c800c8000c7d94680a40800290a021200241c00d001d061803058010041102101c20401d46604444103008408180046855409540c02c001801e610704401d0190030015500c0000321032650b82e840d800c8554075400c840e40b441c0a140c0f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 274915143 1250 274913893 274913909
    0x30605011d0f040209040302030c030309100606050c0c0609060c0a06022802060402060d0f0216060b01050906030f10081218010f120e031e0d0501141e0105120115080f01 74
    0xb000308005181aa00c555001400b0344110303410120941c02942c00c43e4000d5403d1642980040303002c00b80c5604a004160007000c0c142000c6042a1203d0025601e0b54a4507890b240f044c44c0000e02e0081070345d5482d007640c0620010200702e40c6040510b14154009511003182e030310074104207603100e000e0000e584c445801c0415a90b0301404d03c984941e400d20500d60000b42c60000321a0319501a024906000c0c8080c04a814201114002c855424284001103805c9102c000b41042003c105805194130380004030390700035900c98418450ba03642c0e503078014010b400300e0300403a06a0103446e264115503402500a040c084150010707080a8207208001528000c1061000801140e00c0e040491510011a4400d0700c2c804a00c0c800c1d02d207441c5480074905400c1d0324103640142010b4001c102c01e83e05240a1080501515841c46545216680c0100181f0701c1c50762921030910080519101c51141c1e44514103560741840fa0041161903561141210802415100700c2840050211000034603030040142c84641250601 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 274916393 1250 274915143 274915171
    0x40b0303090a090b0619080402040c02031923041806080705090f04060e070902040f0504050403200703021915030c0824060a020c03100b0105180415030605011d 70
    0x44000f030009441d0f0002c05561010f010702c510010340e441006050202e96450759000e1041ca41841040110b13015090f584003154000c0c0034040350b042024043d564800018200007103e03044078000c0f0025209003408048030707010b0109000800145103400c0b004030f01000d0340d0a10440d9110922a03030349448920625030310081c040003003a0445c00300e038406600240501c00c007040c1d20608250380d6180c503030341e0b5005804043e8006010009584ea900b0f042001e0b1004682c181302d01c0c10247c400400c070440040c1181003c1d2034000c50405070139401c02c0b10000441c0c0c0640075081100343c80360210a0700c640c92064030360448100d0300d5140716910034401e1051020150b111b1401c02d40302e8031500b441003a0f04100c4031040251010f00b021499903002c010b080442070319130060a400400505150a00072250300a260540c02c12340c1d8400300780e0300041940c01208441700c0e00e1001010840006000e03000940c000716680040003004000d114203600700c00d05035982414005285603000d11441081e59084480a50031824 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 274917643 1250 274916393 274916399
    0x803130f170604020d060b030f0303190509030301091d01061814071706041404080d0b030f060f071e02010e0c0114030a02091906020615010305070f0804080c0109030c02040b0303090a 80
    0x1c00b46071000c005d4051200001e8011100e0086841d001c8a00007200d032036071003c000c000b0107103000d07107009000c15485201400b0300c4c2001d4026a580380018085d4405007500e461f00807001041c0024a4001900780c18002e000c0c0641ea221425000914021841c0b4843c0c145010440040031070b40700705010740f1081d580e542c0501c0e880707018002380c14000f510301648189c4900d803000c07198146a4859008500480c42c6a6480c3c45004003003045075040c4441a020b41c2045015003005080413034042e07030040302c42c201c02d082a0340300c1108565a001c084c01641e140080e01440c0034180354151f20030000c07210a2011076611040d00710042d9850692007404203c001030400001d814a0a950050000310703e0241c0600207040150300da240740180e060b004100142c2c0a8410406903c5d06e40032180305201081c01c4c00c00c001d0070b0035800282602480c4801d10140300019006c201000031100498201d20307400f0000300300e03040c40c518001b0404150002c05a1187c0d00b068041800b9203008000c94044841c020121180c0c0c40c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 274918893 1250 274917643 274917649
    0x20123162105090d060e03211f1206020304020a0b070327050312090301060e0f160804021e13020a0e030105010506040630140612060f0106180803130f17060402 70
    0x16446a00101b2030200b8007a07421544100e44100000c5440304001420510305008604001c0100d21905205040c455404004485a0540041d17a2507004200540d0b25540e60002c9803280403143d0210038170140000300d95043c0340c0d00a0800480c000b10064801c10807074801d103041c403145114010150305402c01030801041d000e000b40280301c0c40030b01400100d0195030750408040c98a90860700d9203c0452104104101313004106540164510b007410040d03042c1c200341d00441d5903c845136102d8210301c1c51950500140381d450941200280801d040e080d503a42d0b4400350f0041050b40d103200060300a60070480041940c0c40c000058905803882c070703aa1020f00d039544a00710a9541c038560815944d07801039981030072405440f4000c0b003103440e103030288814090402c5400d1041c546810046040c0503000301c01800b402d1303d11121164115003c52804029014044c004841010f003550b101444c54400010100b580744a02007503031040b188950094030101d030703480c005000c0000c114500804039070440000100185 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 274920143 1250 274918893 274918901
    0xf0a050703110412050c03060103062708040302040905100c050c0c0a083c01050601080105090f0721021206030c03060403050a0f090e0a05150d020123162105090d06 72
    0x1800b59040b075800341007101c04223007080d40c04c0e04141c0d43d10340c5401c40801060807040008021740710700e070390b0700f143c4001c281c03110740072401107010017441152604041418000100001c05440b4500d0700304000344d0000000c081d02c076900c140d60104080c01a1207002c0883d151482010040721503440160222410b85c69110f100120100c210700002a2030b46030001040d068552a52841c042c0e4000000d03290404070700151031060145e00543c440c0104c0b40400009000c0c1071041d0ba00038050381004003042c00c1a0b211100342c03030140b810617081c07244082020310341c241d004c000031401410140c098a140b4a00d040a243d2146411100540418420420201924400c44003082c44d02e100746040d0100940750b100b04004840180c0e50100b80c1a114028456040d09035061307100b600070111014611040190300103072010030518070134803080a501003249249c1c04d40e102104d5516201100c2c01d403407000285007510801c198001c030942010040c10000f0040d5004000701e07408100d0042c58102d01c40001d42c0d42e00d02030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 274921393 1250 274920143 274920179
    0x30212030a060312090602060a050103020d150609020706021305101d06070606060206090c040c0e01030908040306050c031605070c2105030d0c021213030b0a02120f0a0507031104 78
    0x1441d560540000850041400300d59200440d9171008031041c5400720013482d10700e0141008901da40307014010001070b903d150440f10610740c003004200c225446105428000d221582c85161254000101e940c1040715640c02800b003440d244036240d02540e140c1c402e1122128400500c0b00c045008030a02200410060701c0c04000c800c0c0040c8818500040d6588240540e07080d80d0026000d40e20001c20702601000a100302a50710300296420081c2001e46030300181184444140581416a600382050901100000f264042c41c3c0054050150342000d04414001c4c0d841114824045081c07203100d113100718800c2d000c51b10100d40000e050540d0303609103401d070214815022803081001070303051a213800041d0240003901c01c05011440c0004c240300701d0040030781031040d80714860316810010085010159001036042c800da9800010044496441d802c4035002889450038070901c24040600300f050300038040410600c03c4245010500032500d40398015001d031413903209103004950301400240f0002c2c2c0080410064 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 274922643 1250 274921393 274921411
    0x41a0c0a0204090602090102010c1103040b0c0a050d020a03090f0503032a16051c0b0109020a050403050a0c090e010203060901140d0204090b0a15060507170c060a050604110703021203 80
    0x90412154005001c65482e030b0030446130b450f0082021103440d038081c4240c8082e0400350402c050801e60084c062902c0c1c2c41030f0300031400203c0d400300f0310580e0101d00300446424180c0c0031048403020326409a0182d03071283c40c0201180000d2203a48080340e103e0700b8441641c100c0320054000c40c1040030350a00c2d44411203840390380c015a500c0320141540e00d01810000c4500144004009412942c1032a050000d18104101d8424007440744105e8000041d80d00340c0da0b141140c1260300c0040e26115504d0007100c0340e10560307001610502c01c582840041c020071407141c2d011114902010012400400401400c1c1e0008880e510b41c0580c1c03100c01082004403411285400b000024074003540d5034190350000f8119030449070140e44107503607882003000710289485000c0c01500d04041c2c40450a05e0504010070794031a1134002411780c50140c441040c983c4083d03007a110a2034803802644c0807481c080311450002c0104440c0c040c880c034203140001e03241c032015008031895190568003030700600d0216070b6144000ea00241280072 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 274923893 1250 274922643 274922653
    0x70605130e0c2205030d0e030615010509090106030b01030501060912030e0a0f0305072138090c010e0f0a030605090705040903020a050105060901060e0d031707020f010f02041a0c 78
    0x5410b401503c03160741108000c2c0d20028142400300b807501c1d1405840d000b800340208140782d50385581d00041c00f56407002c6080640100a050840102c41078095000516049500b140000c21140c0c0c00d07400150580000381c3e802c000903030783c8020444501e00944200c6040c654090180c001081c894401e1041108001d070112803019a1001c428008450540c0242c403503801096060200d400c01c400a0055541031041c6220700340d034540c4685414103080e580c021000b04031021440300c1031a0a02031800702c0188892043c0c000c1c03400c40c04031900c0d0058002d030240000c0600c42211500c0c6401c4110340f000701d002810f500d000c2800c0d40d48075001088050581000380c81a644009602c0da038034000c1c20703070f002e00c01c0e405071146015038070305030f422354001820113813043c07850400520500390b010103070461300202140e01d0350805c002030800340c0b400c89030300e11100120400c000402082640010b40029002d04071002045502403c2c0011802ca005601501c610300050001071458203101c000a407080303089200c01d0720 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 274925143 1250 274923893 274923907
    0x1302090409020a0801090302160302090117190b0601021005011a09040204030f0503040314070501020c22110c12030f040204092d0b06010c050a0210020c15040305070605130e0c 77
    0x15840c990f240c0d01070400ba030f449400481c209903040c03040d44880f4903004a0034040504581c00695415014003801000c880400045c0c0342e9014108610148003d070f1080c0d049906015040c40c40d0804000c5441601503c10b408562000300403a01c122030403520001008504501c40d81c41100c0c0650001144c1580079809010210215003400729040c0040d100e02c2c0150b6860346946042400c0022040c800c6040303801c011020405641c02140800c241c80080728144402030203080700101c010309004030382d1308143c40c0603040301440301d90100400101f211141240e203502441d94007031132035200c1188d100998501000101d001420f19806c0404594824400207140f440c2484101d80020440d00c201c00820050300c80b0407084c4200c51081c1c1e0b030030100a107000c0d1121000ca44034540c2d00c240000009019046202c180d5031007a10074456007400650040c1034a0303514484110060a0350001e00041c0e84a0080d4040026464060360031120b034075000083d1a00c440d440c0900d10482c1e01030042442c54002000c20400c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 274926393 1250 274925143 274925149
    0x120203040807080d0305060a060504140607060c03050a15050d1e0b150a0e160c020316030318050a0830030403020d030c030203071b020411030c030703140402130209040902 75
    0x2c0800342050000411396544050f0006081c0c0f01c028008a000d2040b00c0e109000e0168404100c030240c5042c00d0b40302c08400510030224049104440c005441180b81000203065968190001805500d40f51001e01c50b0071903414400047c3c00b070703501c2810340c030094100d207640000f800054442e4051000d80b801e0302c00721840352207520040000b1600a694140e030300320855201e1500c0e84408c8042d1412503540300a40c5841a0f4254809014818070707424400701c1d805031000c44d03404002e854110b51035403803000c2c0c00a580e46805482c01108008031b1150000317002d00441e45040001c03800f4121a1641d0080080d103201070041101c40d800000e402940400504404d503e24000e00025401070348030703a00801d800d2003111002401c84245500768000c0600400500081e980d002948900c0c440d40c06030305100b101c0052001030020000c5d52215840b009001c010803050703c503680003641c41154145c80910001d00ca40e48040070007802140c000754004003804012001d2150f80d40500f06140b00a840010110f05603000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 274927643 1250 274926393 274926403
    0x506102307031e090609060509040603020a2306030603120a0203040503010c1707140a030b0111060103030305090d0e030d080406140a060f0b1603030903020a0f0602090411161202030408 81
    0x81c2d000c201007a0744038540c3d0f01a080e00c28503005261601089840c105000202146601d00c24202041004242c000050780e0b01d5001e5001140d0041c09000120fa58941200389280c0701c2c01d20201c800c10001c003d0b00181021001c4a103d6080200904240e0083e0043d074042c030380003070000c0340840c4024440451107481c24428008203441507110031029200c103482c00f422010b40140100104000b00c80b840003044032210a0702c045a000742000b05a144400c0c004072541551010b003d44a4440c0c1e00000003410740547c00103001c5c800d4403065508080b03c5900545054203c80e00582c0c05038040e001212a16124032070854125128500c00704440241d84003c100c1e08205807105d0b01807568a0100f0003d0907a441e640720002e1588880031801e28604500469021506400180c00e054071502c2c403c00b0503100b4099074400d10381c0807003900d03141d4416003080002500440820390089182614115000b54050141d45440e00305411324000514141c0c4d50a0380782c1078a68101055103c10310010031401c40c1481 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 274928893 1250 274927643 274927657
    0x910050901150902130b220806041101030902010801151809091407030b0a0f0905010903110105420a0305032104021c050c180a0b0616061a120604020102010f05061023 73
    0x800d00ad040030b081500000c0140144030303040c50b251460040060342c0080c07400d0f044405d0020120034020900c0f400342d6609082116464112590320804035002200d45e018010b010700a101241c042410300703481c00e980e00c45600001c0e01c491a42c2c00011a004803e170484803c00041003804181d20b40b0690300c090035142440c408401203003080c030f103550000e2000d1003143e90106e04049468804c0e9004005030103071610103200d410081c05000302d02c41100c000950321080d605800352040083c2696420010340b02d803c406000c95090a0b05c01d161102d24040b5203060340147e03001001d41421000d032441034100c46080301000c6a00d4000c0151a050a41d40c0800459004600320485100e6151050500301118041301215106034001d104000c0ca02110405100080d903000b4130010b00042e21030031030101d60851040080e40302c269800251410240801e806005900c01c2e0000e00010010105040c1039900841d0740340d800c07092455448058602c194858458503801241803141b214080f5854052940451 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 274930143 1250 274928893 274928909
    0x90a03060515060a0f0309020d0c030f0b0f0c0301060c021302040611060a1407230703051b0a03050f0706090206120105180405060601080910050901150902130b22 71
    0x101c01c000403210450100e034404101101c5003858000c0c2903c02400301c203403030314420003056520300c044030442d15401ca031003108540110220040658900c0d10504041861104461030b16085c400b0907080c100c02c5d07000901801c030a2160f58156828004203da2403000040f0580e13104081010700d0341e04a00910042c006030400e607035440039070900d0903442850300c44094103403512a4a46243d8000c0041e9045031260482d48614154091030a0039004002c000c061800c05031580c10009118070801d60403800130500c107007079002424006184814600d4990124400c09004200304121015520040c000101416445050005113900107078010030380d950061144003282007140c00c014080c1d1b180c0010b404008016079221b00310149080d982e11507d43c103000c2c14541c180304200700442c46040051201000104000008120074075081d645580a04034041e81c10410100c100300c04a0170140354000c942c280030344003100f40c030683d15101d49a10181c4c000d40e5501c1280c1c00109440003d00b4540c40b00e640148412 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 274931393 1250 274930143 274930151
    0x705030610020c0604032306090a0b090c22062601200f07020f090a090c0b041a0307110a06020405102607020102390607090e040602090a0306 62
    0x103042440045481c0d41018000c1d50311428000c225540c94104135016207501c07011005100e14404c0398100c07040d00d220b2001c1c4043c0106810400d40e2032001802c5200c0714007c5d107052485403121444282c40c1d841c146803241e000025200b03d4486500c125500d030721441110840060503650782d07000a0010400070317400274540c161548036410284070034011440b000300401c104c100045142e2501e08034600c500c19000c40d0059001c0360000541d075800a0311001600064001001803030300000490060220b0740048075404c492000c089158405002601d0581c2e181685559000b010b82208404503000104200c04108180c010784003038000901402285510805c80940c80b5400c1000300b00034007100148a03410040e07202800c01c407040c102480d0b00f540d040d8035003030803200b6100c010049019128554800204104075088490814446005102051001424100c00d640c00c100c106490f400280d40000000e030103002e0a100004d480d49445800c903214442c01071800407158041800c0f51134550043c2c524684d5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 274932643 1250 274931393 274931401
    0xd060e0309030a1109070216140a090204030f0204050a05090a0204050612070b180405040218091501081b03061e10030203060a020d05060f010210090c0b04090903021207031b030215070503 82
    0xd40c600c2c0e81c06c00d48500162628507400441030703000d600103200d601c501500d0308030762010b5515500280c0300a01072032501517681e00d8880c141034500300e8a48004a000354640000039201c0d00309441128001d65008018040d40108c80d02000302400010b0a06a84503030080d102c10060401001900300070084800400c0d12400c400c890821000440c0000d0f40c0128204000c2100580d202c2c992045803090541c4114465281c840e1998a091152000120011002c5002064417103002600c01008241007440304042c2e25178209140d100e980a840600b580100ba0a2080d02a00340c44d00103540f00241202110005981c2d0700000d15109041c2c440d0342c1aa40e0000703140f8000c1c4428060a07522120541c2c5440c001100840000d41e100400c1c0719080000381e40b5403186007004119030b90302d0010440400e0f483e403a0f6440d2107220009108581c2c048000d4130a1408074404108130740c1c10307507240d2509074840e1004210803421001510301c1707000040382140200300a6252203445203074264010f242c1c80c2c0e900d0b40c40c0c0c58 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 274933893 1250 274932643 274932649
    0x203150102210324030a060e10021201050d021314040210020303061302181305010f120b07080a0e031605101116050307020307060201050a0f0b0d060e0309030a11 71
    0x103004802d508405202403507034415160300a0803684c005030380501403040100304900e140d0520140c40b40d026414058205420144070083d001001a800d4443c250f942400035280d00307000324030a4949400280900c00010015803900558140010380040d10121a020203180b41508850f1003603a00a0b0445074881448203500b07141940602c2c000b41c60006500d981030480c0064034000000a607419087e4002030301c54240c0107641010f803038201c070141030311180402c0803010101504090252441380c52400c04005001c1c10030b1710a242c0b03503682041898065465000e030480c2c004c3c4c0000d1840c8021925076106075030801041009081048101c50081c01968581c074055041c01c06c0b0b100a07664003800c100001401b41d503a0000c40748100d4001c48000480e14032441c01c9401c500030b202c0041d50501800000081e45a01900114850b285044003045030381c10703044516045860314120039030418010038080c000610303254403200010303002500312820140f021000034581040d003001141c08030000307114134072282 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 274935143 1250 274933893 274933903
    0xf0103060c05030c030402120c030d030207050c0303160f02030109170c010b030d02071715041406061801030b060d0b0c070510052203030f020a0e1f0f110c03010203150102 75
    0x1c006190803450f50824200d035420901025001034803401ca10001146001d100b00160b81d131203140a070950300385002d150006002900490401e40d030034050701b001c56100e89004412a4407075000484ac0301c410b03104039122801e0300e0707070040c00480c0c056503288010f0011500740483c0075481258808295601c0c1000d00303005094444007404c0d00e010354004d409400c03a0540114079641a690b01c14143d00011070510349041c0b030488180004070f18030030310310140030a104081a121004100400407104537444150a00c100305207800c3c80d400c15a0004001400065044404035800c800c0c020880c80c00c2a0345600d5000c942103040d9001c404162000900d4002c109040c861103c4036140d06c1f5040103d46441d9072041d100c140c200b04c0b2800e003015081c1580381010f020380d2003074200c650714140854840800c000060126080742d41c08522a04414040180c203070b45400460245010903603800d1810b8044203402d0360b41c1e5211042141d034a0145480c0305210303450901c003840c4a0003d070f0240706044030095001909007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 274936393 1250 274935143 274935161
    0xf040603080301051512090303071106040804060807020f0f0c010f0309110f012a020a2705090a140c1203031b070609020d261606021308060f010306 65
    0x1450510904001058555098070704560095844c01100c6915444a031369501c5840700405c9010300f99400c2c4070310f80000002552040203591030b400f40d030620008405684500448000309000c42c104000e00059104099254004856004583c0d0405410200c9030904000e4000484c1d60350042e05e003086c40390703442850a03030b000f102030400300002d040945a02c408031f00440742d00c07405000140251102a4410070980125040954246075800d0301c094800081c0c0300c0c0c0b440c2c180d1160040e880c020030714404031096000c180c80d1540e4050448081202100f02508009003070f80c01901445040c40040b40808841d00034000e1110080c1c0505000541004805101c2008260080d4418400c21192422014000701c0b0055011701554a8850a1038504082c2c551050001d401801c06400f00c030801c00781900038040c500c4241d1a07011710018154001681b03004a44000d50289841542c86000c40c0f1107500030310150708070207902e096591706d882c519031414400745d032928000a20103004005129040c4202490 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 274937643 1250 274936393 274936399
    0x1603090b0a02070512030906030108010207060f11030619080109030306090c03060303020607140d110a140c0d140d1107060605100905061c0501060e031005040f030503090f0613020f 79
    0x18103a45681c0255030380307180e0140c1401a90140070284a0050400584050900003043c580e9130350b1f101d00a0714082e4010390002c07110301d81041d42040481c10300d0300848800c8004901c0940c29070340c40340100051403075000346450f00500d07410300104000e0420700803105250b010b43c802160092600d039000c0115180c240003a0f0801d85001030030310000b907010584681110310b138981610000058440c261142c494145240911132510b0341c2e0b00c001d00840805080e4580c420b0b144c20b1800c03203800c090410b0500c1410442c0d4031b15002089000d920600802040260005140005040240075000e020445e040f101040b9078400300420107004000a0740907200141c801502c00038840e04405402800d09101c600030148142408240e0798440150010580040300e1028802c1c400d43d69550300282210285d214000c0c06400b03070294840c210421409441d000784d500298904451406071011078480e04040c1c4860814000d03007440f098110000c01040e800b40300c84800e100e8440080d80304010a10418a54080c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 274938893 1250 274937643 274937647
    0xc070c0e04050a1728030b041a1c0501020309010618021e03090f0a29011a030903160309150f020703020103020915041409010f030f030e151603090b 65
    0x1c2c90120b26070304101d510041410755520349550940241c043c1004d00e006580e180100345500030044c2001d01000001d94a04010900c0c4400600094030030080268441101d0850f0200b410300300044800c22154200c85080742001c8075a880500766801941c001110381c1d143c450900c01900e050707415048110010b0411443c1a01407600400c0103e5a080384507407a200200004000e2401030111580580c2c03042c040d80c02d11012460020440103200320800001070241101c401003044072600c82d030507600b6444100101c15103400060f442540020412a0103010901c11410340c501c0c0402a019418846d4645c0d01550b0b0030940440309600c14507080d03204105091646107c981c0e00401d40380705690b02882c0150340c9000000c080344501d00400701e801000c2d10009000103607404031070304038413100e41c040700d5072110360340d9402e8101100c02c0305000141180300c5a28044000a0140c000000ca1840c0a030000a542205000ca0301c4c594100710300c60070022140c001e41c441015400b00281d005842d0030880c180c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 274940143 1250 274938893 274938901
    0xb071106040b070305180303070815180a02090d020910080127030f03061505031b0f1c060302060c0303090c010206010f0612060504062907082205090c070c0e 69
    0x2c1d00ca50409002c90701850f41d01c5002c50150b100c510303c45407480011404590ba00c2c100150003c00c4190111010360456151b00d1841e44e00c0d160041c07400d10304c80c104024038100740d00c440c030100000f5800002c400d41e005000c1d0b80c0080058a03103488562090499071982100580391242c81800d60b040103008015940e904050b0414042c0006d05040b020380d01482d02d0002440ca000d015001003ca81c0c1094255080c44010481684e0f8000300452148403016500b00d00b4001e0003403444562301031049821548c40c0c051282ca0340c9100001d08800401000c100e0220740144e0701d801140982d404000c0420303040d0070000800c04040710802c08405051820310040c20150725214140010b00c44a02541d010091005520001403020f03821032000742c14001c100300f0540b0394a04802c420300542c1806102443c60103003150301c600c0d081d10b00340e40056030005101c1e4500607020010680400c6401000c001e4074002d40004101900c48504281c801e02081240c1d40e900c8001d07041100b0740c446c55070302401041c41500104 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 274941393 1250 274940143 274940153
    0xc08010e07080c0406080712020c0c120d02070e040303230601081b090d030e03072601060e011403030c060406051906050f01051e072409051f020f070b07110604 70
    0x104c00315090b6240220468644100071500031868105042c0b4481c000718002e0030844010950500140c1d08a980458094001142d90344407201c4c1c40d484005604080d004101060b840c0b8051760b40305d4840c0c5400075104003100c0707107020280b502d00180409480c00c0710801400356081201950054540440c8204a4185001601d01807151340441402450020302c4901014040e001840d8034801c010151494a40c841004801d42450741503840100c152400a980100750107226007002e5601104c69005030760b0070540060612100c90203032503094803081001925200042c40218001c0344a285c010415062441201a4613a080300b00c03220034501d0280100107607551300743c3c401401d030000c2c24016111040100d03a14001d00110401d03041e01003000a24a0030061203200d90700741d0000035080744460f008000300c100102c440a52006045a00ca5480c400b2040c0c80681d003900013541d01235000d45002007400c600041600f09101c22201010303c0001c0c80055500040b01c1c20b030480d034042c0200018a020388070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 274942643 1250 274941393 274941397
    0xf0e0402190e0d0f05060703050601090305281b031205090a0e0c16151406090406050a0213030609021203030f01090504030203091807140a210608010c08010e07080c 72
    0x541e03800d02c030760780d100000302e0b480c1d4a02d0700f807415400c4610718084da15541001c540321041200c81c60300003880c220000d1a19806140d07842e0a0340d8004000b005007a1680c8401d441c19600b0084c9243c15080885c0002c002030f0807107000d0380d030380e04511012080703051039854200900b090b0fa000d000c0500c86c050103024299282c45411208a901e01c042182c041c1c3c607161090b20140c464011100001d15030326a4000030b01156040b100010740850303004200d1918060040444400305607036803980301034041d01140101700907400890f08020320003001494a004001d00300b40d050403d500c21036100b0384540311304096103002002d80c2a2030a080010314590b15044280d0010003205005600519a940000c02e0601d407080040e6001c4c8400500031a144928100300c1e0b8074400411105000002e41c040c0c403080d038848010040d140c0e010240c3d100e02c2e00c0001c86501b2038810440000010907900e650b8540014180b00034000d004c103040310b0340c44400295060446409011074001d0407101408004000d1013018075600003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 274943893 1250 274942643 274942687
    0xd030c0c360f1401180504200a0f0f0305060c03090303061003060f06050415020a17090d080721030203010f030206070f060f060807050d020303030109110c0304060f0e0402 75
    0x281d402004802030700d0801031401c841e0710606940342c210300b840012400c41d03502d4161900010240300b400450901902559030440340180311403221044080c04000c6036801d49400700c0c0007003142403016100e141c01d032007030130b280d9100302d14102c1c2c4000c0810a0000c2846419000400d070580341d0301d980b034442c01c242d17580e10001c0c003441c0c02040301c2c01102154a110794043c202418201c0c5903002e1603651a10000c216800500541d62001c1c03c1984103800c0500004181c1d1180741c1c00742c03c503107080024405e2403c45400c80e1811540000c06840f1000000b040300d4001c02289204084d07220150700b100e0802d51f54441031800360001c0c5841000180104001c030303c204000c0301c1c0d046407000d6580c0200d01e02041102d01d070400060042d0b06103000480150040d8004d03078141e40201c0e04440d070040c0d8030300c10031851401b013002c00b940507001000107002e4400c998101180e0a00a040c002e840d060100e00020725561141d07204100141c207419042c90a0b82c0d2140000301e41980413541941041da005115010308038080c2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 274945143 1250 274943893 274943969
    0x70210120f020918070908031306030b1e1203130e07030605030a0309291803060901020a05030612010603080a02070806060105040630110909070306120605150d030c0c 73
    0x800050100d601c1008004060507d0314180c1e52541310003aa818544500350103082c020a0810f03c0c42440ca00b441d18041210380d41c68a40100c003420700c20700f804884541e0f140903000500082013000c1e002840d240480780205040e11440240b46003c84004088804d5500128400e8001c00c110f01c0c08a5480325901c415a480f1001c280807101d0351112014028501d407546c4400c2050100703003560341d5041440009410101501a00d0281d6101c0e1806803c0740306001804012580a0002c5003060914420410550b00340c03800014503d9201c0c0c80340440340c4c0107005c00500681c8484024094100240b003425040300c03083c28898100760a00901a0206074811310324505d002020842003010200f807400c7c00002c0703086903000c02c584502c28407083c0d06a482002401d00500c8480c0c04107541c54403a00c2a0340841396a60a20a0101c50980e41c0308040c141c0904248150080402500f00c1552149041b44009101e80ca500142c89010300c0d00c112140741c0c90b032150001c2c400000c90f80c91340d1a072565100307075164291 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 274946393 1250 274945143 274945189
    0x20f0d14040521160516080c03100209060409020f190e090c07050703020a0f0e011e0614041806050301140c03070309030207081204061d030a08070305070210120f0209 73
    0x1142d40025401000d4a4072081d6640c41c00810034064045201b0700702c140c041014102071601d918000d50788000c80d400058256010801d040c03000034140d4084c1c1210071005086034641696010a403041e0781160205040050313001658050400c4042e450303200005e450304240b000c2c035064100054038154000c00b841140d00c400202d00301000710a10144000d150300418401c1125290140c1c15000700d114050a116004140c0020415880d01007003190006501c0d60444805170505800f1912000d042c2c1c034030b0744555400c1c4070210700507456540c1000030000c03a03d40020014641004c05023907600da01a0b00140100c200700344680e244070081141d605c40c9190402103068902445c080703141c01c2040c0d01c05141800f501c2000c510002890b4020000c0703507250394880341c1004130080060b4511951200b1654141d0000344950000b858400160864038000d0a1590070a042c0e030300442c00550b6802c1c80d02001403140506218844446d129040c20f44501c100d08605205480010944040c5010b50202440d000313 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 274947643 1250 274946393 274946443
    0x703050915190606142a0a06150501210b0a1814060a0e1b09060c010c2003040512160e1009020309151009020f0d140405 53
    0x421610250080d00d5603041c0461801c200070048442000d40001907242c185100000e005118041024051014200191400a181e207103541c50007942e01d0303542c020300c008045440303052500b80103440700180211408244850b0f68071031306102100d80d4003c05d050120081121003070001142c1030300b1008900700000581110090009012a0600d0340401600809551144080c006035000303450b03550310030500c0d04019107800c42000701d4040d45005101840d0080c500094640410511140c0500c180106071403400f407501000c20130350381c0b0048480c40903079141d846080d104e540c082c810402d100301c0c01c00c1c0009090304092250741c1300d210307a1041c2d034400d694001e16458810020301c80310601105900b02c540c1815070780c42080748069821201000030108101001440c00f40a0085070303c41e1007460040c21010603142519400030802034009180c40c1c001d98000b06100c14140700070b0501c1040343d240181c41e8082581900140e8030401c1b00103410009120901002403030000c1d0000c0f04402200080042c250 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 274948893 1250 274947643 274947661
    0x81c0302130303030b130b15030601030b0901120c09020a2001020906040f170c0d020d14010e010b0a151707180e0901150e0606071506080d1115070305 66
    0x3641005440c04056801c002007015010707401104200000e0300d080d82144441500001113402d0f20750101d0700640300035562502081c2c2600110b52050f0141070000e0a000c2d000041020702000343c0080055141036945602400480030152005018065041d0f02e0310102c0e103402041d11b451044082c00c0c0c40c50208148203621029010385044900242143c2c0c0c807181d5900319013420590900c81c0070300300da060700070100b0000340c00304a400000401a081d1903040a01d40d003400200c5030500400d170b403020340804110102650a01a42c0070300380e0341c2e40020548018034010407504075601e62020103481100e0070100c03070341d6800c0340b100746000811040310b052300e503a641e8090f07440403144a085c40c2000304001011601c0606028200d00a69a060003004030000e0141180310740e00c254000c248020244c2000030310585040401013606506c10045155017090540380d52040c1e881c1504180825004509041c5659501c519265130100c1d10200500705001043c406a02c56080030305110704264441c2c0005008107 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 274950143 1250 274948893 274948897
    0x902060f1305030a030f11030304030e15090d03051801020c10030b120304030614011d0a0e031317060f041109070c0206030f01030303050c09090a0e010e0601081c09081c0302 76
    0xb01800f95415190980707401044407a0380c900364030100f00030804040b5004000000e5170b01c03c5a058890080d825400010403103120b10103140510484803c0204031a1610f80841c1894114443c0c0c8034162203103038101410088040581825045610080c0000c68036901c6515803d2444803034180001c0414a110204e4112015000f107501d4510002a00004000245c0c5c4a1080380d400302841141036621400b00440818102c2c5914203440110300200301540c2c1c103944008003481c400402c8a20f4804124215004410030350b21800302d0400710b440144960101344000c50380034140d1010060540341c00c2d9a101c4540340c5411070240500c1c00000020762550095030990b20f42070300105115100c0c07800104089008500b4003040380028200710202d80e8210041302238a407607280040c21203040d941c0d0802c3c40b0000b02002c1c8201661503403511001543c107036003400710b940a0072250000d000e40488903203c001c1c40744000100c0380200200d186081101e1078020480c00c21803c0e5003100301c0d03003040d00040b04402034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 274951393 1250 274950143 274950149
    0xe0613020102070509070c1e080d0509071205060105030c030d1d01090b0706051006020f0703020415030b1003050d08061804031709070801150b07030503040c08010207030509010e040902060f13 84
    0x802c482c90281b04c40d09801c103881d8201c1c140f0481c0c2c640b40a09000148680c4503001000080c025035007441100741c00400394014541c44181d0381d003225042a614020410b42500c8103e05480540108e0014000d9060130b101000e50114254001d004038078000764003c1ca4040c080c492540c10070200d9110004c00e82c49290204006c06903c0091a01d035201420820020030040c0c0f00c807408a600d01a001520500200c1c104c00d02803034001c05411014516024400505403038100c03141c2e2001c4440000c40000c408069140c000c40c0d00b01d14241649003985002c515203507113055900d0900c5408003c10410fa075800c2c0301d0701c12400d030f0220f242c1c000c1c1d11a45070560345584812a10799845d00c03480304101000c64000745500440740014002e018459562410709a00942d6000d10b108041007005a600070900400065400c11710500250003819954210a030072a0415101200000c0000810564030b42e8840b46a1ba03001d4821641040b60445603030001e81988034251043c0104013011404003042d5144910200c01 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 274952643 1250 274951393 274951399
    0x6070b06150408010207120e03070605030a020c070f090c20030a110a1221110405040903110307152a0806031e03030117060c030403050d02071a01030209010602010e06130201020705 79
    0x5540c001d10b0090021441c2d04c0400000401c8c21640030340a280c00242007040719080d0b2616440c6490340040003001c0d51000d40440100d22503e000040c0b072004100103a00200f000074800580d028110400400c051000d0359884d045562400c41480f4184012040303610080850401c080701000071643d050138110b0616020b000900030078401e450f01074010203445040703030307007101c42d6007000e04400101c004580110341c02c010116018881401a03003426071006170030038000d081c8000c52001402d01540b440d0b101e55012641c403603c0c2c210149984146003d009810031030780c8108210048250024410601c0d00c40c0ca178000c00210801050302a201072004688a031455142200d0217100307454055a284d10a00c18545032500c0e80c4000803c0d041d010038841d010300242c418140c40c5403200d880465079500022942d2150503400c020540004032070003980310108600c1030032542150b00d0b6004000302404142e110200350b9060650403186500301040072a8400d854a00e840301030021400101e20705001c54002d2a0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 274953893 1250 274952643 274952647
    0x20c0d0f081b070501020a03021005040c0807151409010f0c0311070b0301050f010809061303031103130303271e06020f07110a0e1305010b030d0f0e06070b061504080102 74
    0x4140e081c2804209000000b00c41180d44040c0d0303030001266140141c1401070f005810181e030300031007403e440e08115006400b03508090403940c0c84021581c10160f151340301920724030200a00070751182e00445980d83e40d00941402c6030030b000e40d000c000f034100503900355142c003004040070503281010b02541621501040311390490740c8007920399040401a910a0041522410b490300d0000c550b503114043c540d21072402c20020304410380f2489521401e44c0c1070201e080f0213154840061024425108016510a5038800c150300a5a00700d4100035007120340c0020001c105001d1802c0d007020304800300b4988506203500550071200507036034880c2140780000e8000024881070001070124000d141990107404068000c5803000c07500e40c0300b801004007180c0709106610801c0320490001d0204001c0c01c101c0c092040c055400403520b82d0035440020b00701030b076007605000890707150750800e82e02590004d503516403040180c0f01240741c0303940354a80c2d8680718001407030340b4812400031000e005000aaa4240d03401020100c002395 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 274955143 1250 274953893 274953907
    0x61a04091d1c030f05040503040b0f0903010f1406090c0a120609050106020601050111010c0c03030518150115030b060712170f1b031306020a020c0307090501170a03020c0d0f08 77
    0x2080b140a092a02030010382400490980d010652040a00840d4030100031752a15141c450fa02d030305038002881c10b0b2540703407042c8030b005041c3d1020301444600c422002030001e0303c01c200c1d9840340403c840240c0203c0c003c0c0200c004210401400e0790845042c881d440c01e0507d00e07074180311100805018540c10981c030b0305050200024116400003840d9060764002d803175900c4100b87d00040107080b900c46030366050028170488000e0b00807a0180c1d1100d0b4000080e811081340541302400300b20300c0e11106241795110544d65000410060120140450fa00482d13841d00b07101e60655100000c0b0a40150303007000d030000e0b500501080e5240e009042e40705009001c22448032403881d1005000200500c1211018401c2c000030135040500204202121720540705145410b4032030b0407a440d000c1c000c0d0000085402944500a04940c09a40c1001f40c10000c0c410710801103081c0d0f052004038580d60b0400084042550300c4000320500094004c12501980e034800e94010303062007854204501c0d445011030014101000c002001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 274956393 1250 274955143 274955173
    0xc010905010b01030c1103030a0902010e030604030f180f1e0312020c03010609090203101e110c0712020d030f0210060b090102070b0412080c030c030a02030d061a04091d 74
    0x442c0c2d50401c2604c1c104200191324100f42e581c01034101d81c3c200c40b07810400004588403071075409440c290380180b42c002c0b0b203015600003082c42c008042d5400d801041508e501381507003a510804035040312201061a6140901e0807904146141080c010100d1301000f08414410100404202000540d00400c00c3c0f90108000000607460b1040000020f00a5003841e2020030708400c1402894121540170b4001c102c7c605480c5000c1000707092080070004810400d5800001c0c103079213409042000010007503010780c0c510414004a1801c1101d0b0b110484070200c4081c9207001d40c0d240141c822646070107083c40101c1c0b130740303451049003448a444920750034285480404550010303081c000c2c040f9a1420b03000c882110b03403a8011b01e43c0d03d0149100b291003a0741c944941000041d41c41014001d548543c03c00c5030304084090b41d4041c2150842007001c801a4008505500ea0b40d18601941009141402c00340620b664007d07c1034542d071095028031107010707842c0c1c03046130a90400c103074554001d0780300c85083d05c150740b20040300 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 274957643 1250 274956393 274956401
    0x4030f081216270605130f08031201080a11100c0b07050a032004050103091509210512150d050f0d091a16020607060204080105181b150c01090501 64
    0x10050003c0d0000c08071101024664030312001209107041c02032035503480c00408503086c0d40120b00848001c03c9890300084c6401264008401800b4600f000e035807074140196040d90304650582c400d084941c01043c003180441c0e03200c01140f40000c009d0b03954035104800020280c5d11009a070070020520800c02c1d0400a516a0042c042d1080c0082650140045140c40406004440001c84103050460080004000560085d80409a0360380305007000e290740031148241d1012580c1881e8140c6200820300c1d5402150740b165a1640004081e6041247c100501d18002c00c0003404d004000d60f50311281c09182042c00e654403c900314400d0b0740542116100800c0264542d102c4451400c8440403c0e000c803000320301c0044282c614041030070006038090030010782166008589020250a0303800903810011040860350a0004002510880c400804c03142031049054070001e18800381c00b1069004100c0b030207403440075114030f02d0700314004503501d51005401c03008400c094401c07a10b01503415031038440030004000041d04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 274958893 1250 274957643 274957681
    0xb09010501140907140306040608010f0203010306150b0a03090f050a060c0e040c14250804050a0b09010c0209100b1b160e04031b0602040e0415020f04030f0812 70
    0x102c200c00c6408041c05004411100f510303508041140c2c20540310750384401e0350243d6400031000340003103140b0395180001d500711200030300c00b40903154000005206010840c0180c040c0d02c45024840c0b10080d2614080005c903005058584041644851099042c014003181800d103071a089401c0d699004407034a44003000b800034001c3c0c0340129a58203d8940b1601d090301c540c02c6100c40c079854090503c01e001803001c2440d0b0088145030032000c03d4900740024140f14170048000d25210b140c40c1030341c0c6e505040401924444e0350b4040d107003540c000c0158031800d9074441030000055606540c4090f00c3c1d04d64400708003610b1069009901c140c3c001042030030000085601c1050f043e0788501c2175030f0341c12020a000c040c0d440c3c07035409a14200980d038001b040000b4883e0705200780c96010000b886214001543d10401603900550200000038084010302041c0080d01864980608820008600d0542c100b07824400a004600c00500f286d81c03268102410300c404a811140100c811840302601031a0900548000341030060f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 274960143 1250 274958893 274958909
    0xb12072f010c0305060609030304030209040f051c03060b090a05060d0f020a03060e060f060f0d06260f06040c12051005130c06050a0c020f0f12010b03190b01050405060d0b09010501 79
    0x440170901e0743c03c3c210111800c4840c040e010710315243c156002d010710200040c0c011952040c1803410040450800d0124041c08900240b802804001524001703060300e2068100d40e00d810410446400079548040d41030003119819683c1540f80c2d10a0040000140000300000c1c51107070001594004140d4545d1011065032051403140c03205840709010301c182c0f00e680c10103640e0086130070402085812441d10190006012618001c00e0b815100c0710006003207014144420b03110703044100152a40d420030701402d0f000c03407086802003280e450142c985403540300b805d109500000c960343e00740b0002e2100a02491310400c014140600c05814014080111801c140405035000d9010740b10210f245445201200e0b0440d5441d0b603003852420032034080007448412581200d52042200c1c803002c0c40c42d146c2202c601c88403180e442c000690054036109240c01e1810f03640c1d1280000500c48070440018913200025415241d0a0340c001880e50303141c0000c9000243d0502003c1c02031501d0004002e2008015041a030607a2464 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 274961393 1250 274960143 274960151
    0xd09030f031701080c0a141c0c090606120c08040f02060c0106050a03080c120703050306090a0207120216060e130c090305030f1908061c02031204030507030c0b12072f010c03 76
    0x100340344507c0041404501c0c2d480070b511450705c100041441e01007a01c450103072001030792141e070311f40403101155210340c01640803800042080c068100c492080c000f9000044c149030076203113015510503009103181880244143c4002c1513180e4144d500350702c800050300c0080c0248107020345900b0500c45c00e4220422400c0d6030301c241d640845080c19840d082c1d0350095490b4584600b1900d0302810841c8160000f01094041c507424405c040101e070f00c010141c1c5640078150080e19805905181c80c2c601d4800f1504148240940190b020310f0b60703141c030300303040114500045002a5038003110b101112000442c1d800501244000b003000f109595054000f010810800d10f00c50f1035400c0c1c0c100c2c003030b52901d01c125a003a5120401414035844400c92509a9241901c028152082c42403007003110b40b081c1d00140c0060710301e580254810320800c54142c80c4000a041c3c5654072904291203100c95036003a4034010048002c1185402d04018101c806034802c60031080304e1544030f803074404e0041c1c4560082800e00403220000b418 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 274962643 1250 274961393 274961399
    0xb06031606020703030f030915020d0f0c1202070611070b010e0603070311040b1306090c1101051501230d02090306061002030a030b01090b03040b0906090d09030f031701080c0a 77
    0x24800500c2101c2142d00a808a1407a64909540c07138440001010141034a52001c0f20001d00d04682800101020010050b2603200e082d1001c0d0072503001c81d140c0f500d801c0ca0001d51543c901e811403c080700040c03010300c0150b0b8510f075614258000e00f0589185410380c12002c250303081000305d500c2d08107040c0c4a04084643d03d503580c18080541c2c03030801c0c0c80702405400c418401401d00341801d822200d441000074103400c240c0d2000c940880c04846407640040e010b503903201248000241c0c024000402e90b40202c00a21081c203150701c24541000000b1641414407101c0c550400181c0780a40301400200e100c45080c680320284607003900d0103940b01084881c8031b03004034400545203140c035024074100094039074020340c10051422010340041c24000c0e0002d061280c125400103500c0c103110001c41c0f00310300c82d40c28000c090030100d0751f0390324003400a4006600c40d001121114641a8800e0580c01102d420480d00d160380c45460a0940303500f401c451000301c1d80c80d0300e031001189600c000900c41064800648000c548030359 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 274963893 1250 274962643 274962673
    0xf0914130206030414030910030f061d0f1b07080a09060c12140913060f2103080c160b090f0109110d080408030307031505100507031101180b0603 64
    0x1030101009510900c2400420003184002c0c13842420315401c80d04a030325184606002a07200c00c00c00720a83d0001741c43c3e11803002c3c0c03c00140141c0d402011030b4814915100c0707070780f91401d10100d401411145003114a000003407060b1281c540c840344d030940503a04103039141a40c1c1000096940110195800315a184000017551840b8003410a20182c000000c2c50340c031500ca1100b11540701c0d0300b03030030209400000d1020030b1041e511a40151031806159030000381461a103400304000e517216a2004080e80c0040f9500002d08000c00c00a11100e641340c40c0440780b5503288500342c0785034011014103011203016080c2c40d1080003200080796010364601c10440d014841e561009909840c03100b0001416400314021000142c20420342e690581e52045008505007038807540114559002101c800000030b458a010101c85845605d0340e1016042c25108003190600384a070141031072150304001402c00c040444c61048544007035212400c1403442c0820f08541e4000b908001c010b0750360984500b4843d0240344500700000d8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 274965143 1250 274963893 274963921
    0x3030411192d060f0309020307420207060e0d060905010509010e0c060a0c0f02040c0807080108030412080d090501020a0507020f04050603060622020a200705011b06060f0914 76
    0x181c240d9200c54051131110012009000c03060004c0b030701f5105401000c0303541d0300344603107070300084480b400c00c1c3c1d029100c03005100708400c8007002c524031444108028074080c20340c08159042903c401d800c0c480a007000d5400410780f5000341510107400c00d4035144d19501080010b41003540510354040080c4840100c5110312030711a2a038003000e84d4401410032040364003e0040c02407442580c018445e1100d4038980d41c0108083d11250402c6600282d50041004412a04001780501403c8450020b6041a080100d40d12842c1c250355000781c000d1001040b00040d016054202d0b50049900000039501e504801e1005411a0010a001c920030f000c4030035404011b050900c0303860700c50300c0010003d21b0540c03200e509026000400c514070203a2134038920390441050849000070081c0d506142c5e5001d20003624806411410a07403200d810400e6041500c0c2049540e0b0700c4580301c103c03120b852034104080d903031070b19017000200310541c40291145120000091400d00ba54011a0701c0300f00d010541c1841d42e251131240c4002c03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 274966393 1250 274965143 274965149
    0x18120e090a02040e07080106050405040c050f0304050708070f030b0408031f03110315040c0e06131a09010503031e09010203070203061302091003050703030c08091801170f03030411192d 81
    0x27904c01c2c042040f281c42e00e41c02455090b91603080041c509a000c00090300360398011602601c40b64044041040400003c0144400802e2225180d80085081d5524401c081d100075202801d48940480411052001c101c0d008c1c204813204451032a0090340e9203402c5050102c010500da1282c095008003240341410000d59610403035020400c41c0c0300e14100b20060640481c081d044030b0b0041100020320300320101512400c101c10003e001d440c00344005e40400c0103480c42d01600098041d40082c09461400c054000c00c0300e40d000315648807252180c0c4041e0040345140514240658103120300000e01c194034008400d03070a00c550003550074044943e589031070380f000c03015188002012a40104001c0001c2031140c02c0200080e071152107a10318281034a400142c0403805400312000d42248100100109101100c000c0c510b010b058000d080701400e800f0940d0b031240001032000e40400104034400072241d071010180319003103080134072a4240544500c070852801359101c60840241c48c02080c800c0c41d0480b455154411 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 274967643 1250 274966393 274966397
    0xc150603020d06020d061d01030b0c180f03030904021c0c0c0c03030f030b0402070506060909010506031504021216060e09010e0423031b1018120e090a02040e07080106 73
    0x418090f030341d40d00700030b50001d00305507001556248003143c0c00d0285c0503c2c205041340740c8180b44540d41503041000450710003414140303500c4010082c102c25001404004c8800020444441680e403d4200109045114001c0241c0c0d002e80f0018841201c550002c400d48103560f6850010010642162419100510f180c20302400883c0703803c030700b000041e1141d510464002020f20b00030801d201100c000c1000d0740c0224404680c3c640210041000314108103405682c0540c80a000f03007c03609002000c42e84404104130320380780c0c1100210004043d52a4103115024030f0884204481c040d1014401d0b040c229039143c011080043c903074041071207480c500844117a040c0e82c07541c800607202c1c0d143d40e0340d1500200500825a0036600107a558005180014006428440c60f00e1003000f000052000070241000351320300744d06402e40e00e0540c0c645004540c16140c070210550041c01120344082e41c000641d03e0411000045510684070380070403c10045a4000d001191341d0210024204d840720403090710260802d00400f40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 274968893 1250 274967643 274967659
    0xf030a090b13030c0e0618150f030c03060a09052b05090d0b010b1c0204150e030a0f03021c050a140d02040b03040c1401050c33070c15060302 62
    0x4030000d40c2400910400c01c920b4080a1410780d650f07144e00b043c0c0c44e941d008116101400c4100407150406205020304003080703000e2413240d45405105154003510728460340d4041c10001c2180388042d2010810391a80040007803c0b16411320b015480d41e0060050f01c0c804460038010b8400c0c6d4202c101c11039056034034007c00828842d0002100d005c080361242c101004807988041240e84c502e011850055055020344101030b0629070301e803144a03951061000401c81d20b0301c00c7e441003004104459683c1091143c4c52100d20b4040c1c1200252170000f85407000c00c0341e01400e0004e1021401003096000a104003110501446500074005881416286401409250030114000c03441102000c0188130080440c4035001000500781034075828941e809401c01c03a800c079500a4042001e020584550b0503480b00ca0000346007417450140480185074403114142100e09181d064070f6080d99034624200c00b50010455144141c4119181000340141120b214030400e44511440100301c0307184020b41d004007004d41c0c3d00034140300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 274970143 1250 274968893 274968899
    0xf030301030b0403050405041a0102120c10110c100c021b090f06120d050c010b100507081c020c030712032304080c16060305070f0804060e071707080f030a09 69
    0x40050005100b101080800c200206d2036903240c0c85400400110500f0701c4412000304000a86403582840b2041504d81037400484512000020b40040a1124000200384001c140f103643c083c82c0502c0c07292012a0090307542046920081c2c0c0d01c00202010160300301c615885d841001554002c4012900980190f096400156401070554000750003203c00740495440d140440103907420b280c805424440000d1002030046941c0b50b09014517603240390101c880400306c0000c030401420318070605100904022000c03a201069810b8400382c40f038201c84024040d5907a07000d1402850302c2c2d6012510440b2080c1168121200481c0301c1c1c400d40b42e040420f5080c0d05007046640c514810f50a5000344100c2e2000b02c1008400800d0005006c6e1744034041c0e1698001c0156400d00c2307405019175030014412000c020b508012114003681c002c6100390850b40040c0005070351002400780354140340041e00301a1480051078682908228001201400c481b0401c0c159044041e100e4400b5849100e440c2c82c2c0000100300d03480c28 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 274971393 1250 274970143 274970153
    0x24010f050603130210021b060315090903120a0c1116210c060207030506090c0a060e180709050f12030a05160b0c1e0a0c030e0105040b03090a03020706020f03030103 72
    0xe5411044081d18031070000000c4c0d000422400c260280040103030011440c100c00360020f0712800d80c4000c1c04a40c5541540780041d0000700031490042070f144101e600c0310202d80c00c1c40d824000c4405400341c240707a0310341c1c81c9021810303070f80030344480c5007200001202d220001740414804101d0030110103071074102d40c907601d10709881e030180c3d0041d01170036410380c100051208000980e240d403240000d0049402801c04989503082583c1440001480303070000390442405400c99546030f0400d03c1c203139681c60404020041c840c002007a030400f100102e041401c00f1090502512540200b030f404102c960849081e6244101103081c8480b1548040441400c1c0c0c0c01481035420031030140000d40780b140725003190151080d110303855894951030705603540c2c0c0045000090401001808a110245501d801c480d06441d004030548020a1025001e0010303007001840703552505c590703200e4801c0790020308002d0700c800d4680c2004440503803a0303402094220054816104000b4a06001003462151405148095030940c2c0c46c540b20 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 274972643 1250 274971393 274971397
    0x109020a05190b070605070212040e041b1e030c050414010302040905030903100207060c030504030e0907030e030409020d15030218040f080a0203030f010f23060f0c24010f0506 77
    0x8900110318182d000c200c5002020251010b14001d8030040303081d0400c01400303420041e84007014401a10100070a00001008040c1031343c00c0b5604c40e02d01c0b01c0c0b080b2560030340090070407243c05c05105204070042d030340030342e0240d074101d03c0649001d0340305100fa5607500c00c00c000071510030132402c03070342e035a0b4800040025107003590082d900c19024406407440d0050000000742025003044a0362a0a03501007040010b2040320b00c6000800806803c00704418101a140a8414090306460314070801031400021440d0340b0981090b200034030010112601ca9407074407041e00180d004030320703040700191414541c0c842c81c400e10042c0304101c0750080c00d45d0060010064134808800380040c402c2d100c14440e030040ea40010300541c01007544200c0c3c6e170b024645074100550692150300d010782c00300d010907404480502005040880c1c400395070855440740c040140030703000490301ca030081c41030001014501103a0100200b00101d08881c0c3d8010340010a010035850b01140b01890034203009000209603841c2d414401400c00d200 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 274973893 1250 274972643 274972669
    0x20316050d02070803010e01090501050d03120216170409050f1510020102040e10230108070e010e0603040c1707031211010b120706030f0207050d08060a080604081801020109020a05 79
    0x501503d02045a2102640c0c3c2c2e00030703444854200040801003150350300d20f120789805460219076664064410303032001011076452400e2402030584c001018109083e84034104c85c0d0965000314851416101780e058441d10340c120f031046200e06070501b07000410f03000700b01e11460f204c0d09802072040c1051417010309201440080c11001400e5640c20003000c030b203183e00c3c1c00d078007840380a10004001155007498207a00d9100790328a10644024079810b007041a070782c1c202403250b9004140e4902492449180c0d00100c401e000000390050300020008107000520406164550603112245012400740341e404140c42d07902c9001c0c1c8005000049040a00310450740b080c0b010700740b909085170000c81c00c2030302d030000681361140302525041c0581c4525800c110076605030241340d2f00c140202030b0450a0106a803030b4191501e0111850030b08100010f00001c059564041c1c1803800b41820303a048440500e01450803a87e02c2d4032806180e10301c800030741403d1040350302c14060725614036400b400c142c00262915042c012090540380d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 274975143 1250 274973893 274973917
    0xd0207082104080105010e041103010203090c1e0402040305060a0c08040302100f060b0c0c010f0207060c020f0102010617010207031707120b060d09050a0b010b070203030412030309020a1d060402031605 88
    0x2c00104001c0c00d0152138040c7c2510700d4078000d0303400e251501c0100300e003012031b0803406a401070080100b5030304040348500000e0001c0d6042d03102e82c0c1100d01025021401c60305140d500c03a2021a01105105000035903611445ca5400c040242000792002610103031011180180168014024070344c8070445034100015003020008003141f040d8507810950802d03040080b0741201030380300444094466038090b0640c0d0303042a450010309070882c00c0c504000c1c0203041540c4040e000d8804800d410040740d00c05d40c0044000e1020014000d00e0009023240180030350b20400d806d6001800311030f5800d16a0410740b19440c01030070641c80d444502481281c405003c1d02c1101c40c0240d0100c0300380b0801210780400d004e21450503101e4005030842050300c0c6010003502c070303041e001084500002d105500043e00c0020403941078404500007490b007500149000c40103003a0954000350481c41c0410001111103403003070340050003415422040d0740350340d952051008074001164891101c6502c41c06000b0384500400003401c00080c05 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 274976393 1250 274975143 274975147
    0x1403160f0f0c14040c08093a0903060e0102090d12090803031008100e03120405010b04020d05040210030c1d0612040305090306011707270501030308090d02070821 71
    0x603454402c0544419400000e0450344040300580510349442601d00361802c40c10161541d0404160f029a03900110380c0700e840300b01c030014008a00950130750300700e004032140e010040c003444040c01e001010380d03802c0d21085a0013410300400c1c4c908003006009440301603402804400384681c05c0e03160580346d01c84040a01042c42a01840401c500b0000d0000b94869040a002c1c1800c3c21314140f400ca103840344240600444038640340c00381c0454440807080312200803011421501c66160303428264010310b00c2510055201c3c1c8006003280e01d0b81d10a41010b4407640c0200c400c8502401d529600340d003a203c003440640001a26040d00d540f8980c00c100400340030b40d0010b08014213142103d0021a01a203007030f01c080e4049900492031160300c2c03404011043c05030801050a46900ea06100e0080da1403850b801580c8001200c000040c0c40c80140c2d14000d02d60800c0e491041c00956920b0402404440040da260802e134054200280481400011054100e820050060410882011020105400503050f0030504842 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 274977643 1250 274976393 274976423
    0x5180a0b0a1205090604060e120301120204060801051302040510210c121a06131503030201060506120c0c0c0d0624030b060d02030106090c0c1403160f 66
    0x2500209401402911081075034880030180302a2850702c142d1580c0c40c10b41e007040100300040078081859604940c0c040408038103d103080070700c141808030401411451544c0072000043c2340e180706105061041c0255402c012068641d140c403401e940f0225807404070415895260307001030820358030a660003860040c2981040d80c8842c5040004242440c1c0c10a0504805100c00c0c14400716240c000c001300308804490074004074075901d01854502170400c03900c00c0b4141d600020125120807025085580703c0b0b00c0d0821046210785000d1041d4850303404260010b41ca000004201c50a140b01110f8102c41c2c440c009001a542d040a0415580e21056000106001da0101c842e840c0d1181c0b030242000d01d03c03d501c046040542c104a50610003614100c059401c84030210400200d510300031116080710b01a42c3c6020405981d00201c0c0c054151a0300800c9030a1820a052600640c031008021030306125180c4111100303840300c000d0f540c0780900030354090004150b01c440b00c00902da4200c0e4401040c4510022404008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 274978893 1250 274977643 274977649
    0x6011d04060303050c0d052104060b060708030405010e07060207180b120307030f0c0201050d050907030507150816092105010c03020a020f0604031e030615200307120518 74
    0x1460b07000720301080001c200204803030802c1c44180150714041c503006042184d070452445103030482100200ca0190010b0105041c0241074001d80c0c107111001c3c042a03513520f50382c0703441c0170303d940101c4054585510b00341e2580d400d80008901502140c40030741c010505242001c28521280a542a01080b0141c1d41c010b900c00c01e40b2007440060341200302c44081c544a1905060241c416842e071406201044440321031000141c1e0890180e03441c15800000014883e41e40a40e05458400c1c00d8102400912032400d0014060a040c00e0a071000e00311a6a6014240c40b01c8800241c0d0a444542401c08500c10040034800f48004007150824141d0b0200c000c901c80c2541c1e02c603130782125010218200007079000924441c0142c0c0410021108045c040010003040ca440e407402000ba10f41c42c2c4140080c031108080390010144a034000320054242e07101d500d9442c162109024100c4150304205640d40380c0400c10a0138224008001d4640c05508040d10300300906400d44200c401e54000c0610002d08101d035410050349071 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 274980143 1250 274978893 274978901
    0x1003021b0a02120d0c060c021509010b0f09090a03030e16060804021c02030c0f0103110d090b10060e090601050d0903031a040603080909090304030219061701080606011d04 75
    0x1014000c0034201d00751840c0140074006035010105526a0b02c800c0070640116400007050034038541100000900e480d451300704905000355000080c46255081040c842c900c030041d40550341c0018100c81a07913205000744203000082d04201d0f00c07480b00340c1100d804030010900a8004000c4150420241d810200d4030840000f003000c55508048001800c0c00100011414002d2907030300c3c04940701a11000020456001a98030030003c0b01030750080d0461080d949050740660802c01c1c114290760941c60f2155020b8100c20001d202c441021b94075820700d100401c148a00e041d10304400c0d903030141e460482e001020703418004846c10140441d0b041200402c20440448218418a4009031003aa030108090700168280d0321401d202020700303441180751400030800074100d5022944031030000d07907000001e691420143d03421405181d1019410141b203114200c1c1506025210328103403005501c0c1d40755282440e00c064254807109000728403103544410042a01580a820002403181d00412020403c8081001040580e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 274981393 1250 274980143 274980187
    0xf0a030302031e090307020f010516060209030d080618060604050603042001032708132607030f0201050c011b02011a0f030604080304060b04020307120f1109100302 72
    0x90340401804181801c075071106081000807143c0020b1401d010614a40b030f880742180082c41a08030f001d91081590203103040d240744110b5029102400025800c2080c0a0361010035024468098854a0740c001d60103200c20383c0c019080503141101d0082e50400a450180703000d80700c03035070108061100203503941d00c04000714030452060003000c040020380b52500c208601041c2c42c460603d4105400c1501400c000130503031040710411026800e040500c0d0404201e18031526200c8080c0030100c210201d00032000c2d082980040c1303100c040d484101e03401d14080300d03215203150100030140140700181d0b401540c483d501070003c159050f000011240300c018410f180c402e00e100c541c500580d454a0520702c0606540c00100a07031002a540101c8041754200001d4a500300100b00902c0c890005c4045400d201d915407141c1c2d19540c002c2d10071541c81c14601405001c8030b19290703070300d0502401e140c0a00a101c17401e014483d0a8194020b019023031072072000420100440544c1d0310b40801d582031044824081e000989402c030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 274982643 1250 274981393 274981397
    0x3020f060a0e0d230a0e1309050601060305040b010b030606120103120f090e0a090c0305030a09050406080d020607030c03020720040c050a0f1b0503030f100f120f0201020f0a03 77
    0x4141c1c2d10090690621100340042800d04c0404c0030448079a00348410f0309a2100010014a5030b2002c0030017054441c4a502408140c019403224003800c08254a94004400b01d4010402c80302030741c0c0d8a1108500f036032000c0b0f030002c0992407004010000d9005c141e0145801404c010412401d01c4403d807003002210b00241e0040c0c40503501102e4090240b600820a1080702000c1d06d0003000340c4c0e08000075501d1003030028180c000a9030b902d40c42c3c03805016140c560000615401400ea030381e2804400d200400c05462070060303500c0740d40b8014002600d1940080c0010b0681110b070081d10007540c070380340250003c0c800c82c500e41081c5a000c201800002d608415120602c502000d0f04451505241c024001100c0a9100c4a41844020082245202e42050a40100c00000c0c0f4041c4c01c11168240307108200d0721003500050507480003000307016900f404a94018491074a03006848941551203106100c0b0314040e204600fa07a8070002d0210020400032540280018010300403107600351800e481c542e03c0d242e00c900090b00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 274983893 1250 274982643 274982651
    0x3070e061c0b031615050403080f0315010306081923071a030106020604110a15121109010c030e040e0303090a03110a0309090e0705090108030408060105060301030803040b0403020f060a 81
    0x12a0809110321400407030168014a8075446810841030804e5550041903c282c0c00c0c00810111540700d0b070121000b640e072000019440d44490060041d40b601700ba45c0700f031402c1d80103100c6c03441c89510074071840b0102c074407080041101407001004600c14480d5190261089040c600a21003280019840440d403401910300925030149060001c08904004000c41030a4190400042202c1c550024406070019000300403d070b0030040c0c400000c2c01650041d401881d410007074061175a03019801140002d410482c890090140500002c0480c10381e1240d891701601040e00404517801082c41003501c98681d0002400001c1c40481703807a1014515042100e031101c460384044288010154840910007101e0001c9000700950750040d40c0140810000c2c0c0501221141ea81d00c004450b5841008088000d0502400729450340d61240f18240e12680a40940c01080c492800005800e052100441e81240d811210507419030712142c0d200070380c428010740280e04520549040e90f00e03495044c0a014050041508002 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 274985143 1250 274983893 274983937
    0x415090206160501050f040503190201091b0501020d03110d020d0e0708011d03030c03070f05090d0b070f08060d11060403061509110307021b011808070306111e03070e06 74
    0x582511001031020041300c070000117120010348c1c000152039884e81051820408141130500490040581d90405440701c2e8012110103080c083c02000c0c0710546400380e00703413500100c40c80000e906441c17942001409170b000803c00100d524400e035014081c21a401007003c034901403510291407810760103030800c1031507940d00c041d4080c01d05150010308103000d9200340607509504e088640c0841d5030100404141c01d01038500002c2c0303415440748040341c0c0460070003071107444007000794144034030748150444a07034010900100c00880c03214040c070030842c0b05800050120205130b10035038440e0003a42d004020250420000c1c00003000040300c034015a4055400e0251060400780391140307030025208201c004c135542000030418884d085a01040360b811091080b034004440f030340307100f004175864964035071111b4400c3d10740c11003c00d00050200e481c600f12401203400f80a15840101c0400340c40c070503541422051f10301400c44a0b00002884080c562040e8942064807424a415000c0341c4071f0340c4120b05048000400c59448 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 274986393 1250 274985143 274985153
    0xb0a02030f0106110d0302030403050c0d02100c020f0703080a030e03040618050406060219081317071706070c0c05060304080a1106061302090604080123090c0603041509020616 77
    0x58014649407138080c0005070f0240c2032a444800e5581c2103010150000f00150034513009904413051441610103c840b80002c0d848001e484030100140c09000a06085034040c02c21710005401c2c0b500001d04c1d001c0d00800c2e1947d61a01129440144100f0915464081c00d01c41c103c01070020b8001043d403a15501d000c459110b00000c46c0000c0754121500c0741d890048140200c540c0042c81ca0900116480240c05034641402c05203807070702a40300f81c0300001507011400301e2041205241c1c00040d0580307800f00e5103403e459141c181c0388290310340c10b400c220b903201300f0009554a10a100c481429400790060311034144e1500c0110307580358011581512042c90004640d0825a44400d00b910362040150190009041000c006030003092030100c3c42c00ca0640100b154680d0b036441200b141c0081002500030800c0c5101c80f131900c01c1645e44ca91f000603900316148005204584007080c2005400b4000741024515502c940d02c04821100d0219a81d602c2a59894a0801a00d07004002c261601503284070300d05138001781c604 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 274987643 1250 274986393 274986421
    0xe19021207081612020a020a0209070513050604030b0f040f050a0b04021206010f09020906040906060306150804030210180c180b0a03020f060f0f030a02041d0f04110d0b0a0203 77
    0xd000030706100400f82c00400d035840015500344811512016a48a0f81600c00321f150085500010354056220001d0100003604a0010038484030005154074695586004001c1280a02d1202415010340040002e0007021a0400558018410103681a505603e9180c25180c6547c105e0108d4900003400144001c1d0320340072a112a400000303000410782c2d0360600a45041a0b0164031a103000a600811810307856940e80f4241d8019080f00b0b007041010540d02e080082c043c10f1144100c2203c60141d10034490001d00c10306486128582640003081c0034491244041c1c010401480ca200c5407004809104000070071821a980080035a500d1f101d94542229400804440410682c00c1c0706014001c41000180c0360240c080c0d034601c01c101c490949403e0300141303c8465125200008507002c3c40041003200c4140c03d41d0140007a24116030300c26403681400034402c190b4034001e5034a9404507600400017000030302c1065640000680291141e003658005507160303000c080094554080b8690080200440c2c11550b0034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 274988893 1250 274987643 274987651
    0x304060504080c030f1c2a0c060e0607110a03080103020913060c0305090c0a030b010308070c0b04080304030c09060b122d0402041a1003050a020f0d0b01030609020f040e1902120708 79
    0x13504000e0304044402d002c5501d098194000c0340711440d82a50318007d8000c00099140c96000070003402100d100c1c01e021030b2501c00881d0100c000c18418413068082d03800002c1c06040c641e6243e20340c05207a900f140c08000550400403c030044002c0c0030049200059081d0103002d040b050366440c0407415080c824005414030711903480c210b020b29803149081000c10070041409044030780000000c0d0352602c180c204001c4000f641e030800307410142c0001d0000f40441300003000b0000c0b64010b0207040d030390795251007022050b03a899100700013404c3c0c8284038502c401500100000d421100c1458440300c0d03211004c0d101220340d00e001050840c0086103074108001c0d4101409481d5400c0c294445241070a000840041d04c0e91740c074181d040c01056030f5600010080c940d80d074126241c2500345210161941c4c5070544503006042d04011850019060607400622040700b8025101100048411300b8201400d01a00e5074940d840248030102c1010174203038001c600700642c801001107070180c502100c0503151008001d0a1500c0140c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 274990143 1250 274988893 274988947
    0x20a0518090907030822060909060b040f05060c0106180e0105010801050103050a080705120d091a0c09060f0928060503040c0510170117010f0e030304060504080c030f 73
    0x16040100c00c002c08034001003030742e500050f101c1d219440a401e400c9402c81040c00c0210071720080ea4041100c40e0403800c1d403c200c0340c0c40c07102800310507100d001380d50341c034080e500c1400210910702000344001c0c030304000034003910f092000000a000d81d6882c2412084a8001e0720240341036500e5041d140e416100303001c1c072809070400c10300034441945150350f040c2d03030340f2182600030b031008501255100810005002030900181d0030f403590358541d0031400c03410f0028442c01034226220300f1078403824210001c0d4452070500c1440420070103403e1803448410300c41d007548202c050a150000c1000b10100a036180c191444203068800304505415042d00d01c580d14805c0607400240500000f13104120028200c044221b03f980c0040d90000161072006005803001030002da8401c426003190360000c03a0800b006070207045401704410080c08401d00e00708403c01198141d5004010540003000003601241a80d0001c40d0410f1289552520706501928000d041d80c11240c4025100031000607507841c0407281c400464041d00000c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 274991393 1250 274990143 274990159
    0x21e0c07052d03030c010204030602030a18120809031209070509062d040e19120507050307140c030a030f030c09080a0f050c1002060108060c04060207090f0609020a0518 74
    0x200080c42c1c42c0c2650200641c0c0d8403200c2450b41d0034161030900a031003106003100d00030764a5a4880c680038001c0c4d0021184400740f145050140011a082c103600c403a5056000716102c1042d2040082c100d49a40008121384120300c0204684146072180d104902d205401003c00340420301d0500d01004088100a84010306c030b0880310003001c0b0341901c4402070340080c404014012001200c2400460060320000c44403400501455514281024400e405640c605100f20035038500c0010b600026600c0c2d002e602c034040c0c219442030040034001145410300000b80340340c1400f12101250541c00182c5002c0000750100c0c0080c0a2121b0355140e1a0140220084c04620b42410f2807140e0601480c1907403402ea0542c0a0800a02c3e10065424040288106401c2071700140000d0061055a232010b941c3d03c03020b02c1501000c0c49050b001806251a010994090b25265400340810515020342180a04034460a07811500d58442c0c000854a03041d03c010502110aa210503450b004110794405103041c4e450040c0c1e009060b8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 274992643 1250 274991393 274991419
    0xe0a0b040b2b05010b092d01030e0c030d0903030f1409040f0b1c021c0b13050309090106110c1f03090305070506090114070c0308040305090103021e0c0705 68
    0xc0d0152207650345002c0d8480c09500d1031082c0348110514500c2000b080c1880c050002c80c250b01514010110050b00b650300c5400c0305410500042e1140e410b4520740000100c2482d44a4a988a600200c03a480c500d03204581c142e21841d00042c1c05d00312040040404030313100c2d0504104240d0045003556015640d03042c2a600011701801c580321f940716190030b051047da692001c0d00c160542c00c3e40003a0843d180035021100307500e4114a40b0110404086099224030707420000d01e40003141d03c241c81000240d000d6900303e03050300c86801c0300030103890600088401d4041844a0001600c80c4d1960074000d22065498502840c00c0814450814542c1d0448902882c0508205410f03000c4200008403407042ca0f00d800152540c803401c088407240140b40e4001c3c5140a650140609000150408110036100300e5801d00b03691a02d80d8103031240c00341008010082884000000c0c0402d000720054156a5010304000d49070040d000ca28100c2c00c074010100e104580c1020a5013090205c0803c0311001400c0181c0303100e000520 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 274993893 1250 274992643 274992659
    0x24030b0109030b0a150303091d04081b0703050d05071e0203070b0c19110102012306060304030e0303030a0905060901060b09040b0d0206030405031c1e05070201021303030e0a0b04 78
    0x1e02003c0c01d0505040d0100324030039190b038000d102c00c0f030a850302805802d40b00c0c50010b050645520580120f200d4100c0e0081c000001c51044a01a03503020b48100d01e48000e00100582c1107442c00404440c0d806896400004030700c042c4404a0f058a041c5e0747c01d070f501c04036407420200e070201a101c010308503a8801c03440001a103000030f10100b913800e403040c1340f9221100742000c5072800240200a01d00c02c0340000391403003040b88440070300c03000f404260024003586c0c0002c80d254808032103c2c0c08002d64070b03400c0d101040447c2800e60045030014068030f0840e1100a01c080407900c2c6620a0304c500c03054603a9a82540144041070051641000049c402400401d1425030004c07130340c0c0120300c0c4552103281d07104500905907071605002d014240d4080e011913224902400c1080d201d8110070040c0c064843c184440c081504201c2c40b500b00226482c800c0c002182d0504506078005003070090521096640c2007040c8203113680e50320055001140b095030740030354214480061000c4124070b03610024403800240f1042c00855 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 274995143 1250 274993893 274993907
    0x70b07050a14070b07060f0c02030703050406030c03022a07080d090905060607020415090605030c0d0b071416020411070f03050307120c08061801030507050609061324030b01 76
    0x80e003242ca00e001840b021060350f820030f1020b03400000403070f200081e100c00700522a00301c45900d900b21501082841c00144050340c0742d110360800100001da00300302c140001400703603011250035509840c00608080c000340204200f5805480000c02c00e4410403007070491020104941d1002d0200c680107091101e02e2084003800380b481900072070720b05c0e9072a200050015100c0900380c41009800030000d00c01d50401801445a80e038007070284860040c00d01c1400306440c00c00013404269007c001d440701480307440702d40700c0b09980d0101034019020414442c4000101040d0903000d000044036041314103421908a01c100011100a0030341151820000c0c0000808281c0505241c5c0c5c5494041c10710555950710040101c4414030429100a1040c1c54410207001d281e40c070280c000d20503c4107803041108410400c103070202c3d0620900c002845507100c00000d00050401a000d4441071101505450908190240300e681caa0029044014640303000007040b0104804070b003946481080d2800d081051078180c0380020030700 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 274996393 1250 274995143 274995163
    0x14011104170a0204020f130f12030f03181b1a0403030309051204080105040c0603050f15120303090d0e1e0603041505040302100501150503150109030f06060503070b0705 74
    0x4000701415281da4020500c000c1044030360040c0215540c2140742c402c1416030300525205022403032200700118400f07007815000801d850b0b006018442d1023009540440d82200c554404008054581300c0c1503e101d1020f05616542c244103509030314001c3d8028481b02060001a40028120283c0c141034055440c04041142e0540c2d4041c6808540304245051030307851700494282c2d0f0407848500260000d01c4900641c001409140300c1c106a2001d00e42d17a4000320165601034500d810025210b80206140700c00200c2e0f00a041035015140345950394521407814216001121586400d400c0011010b004550025009281d64005c540384070300c030411540f012102d4603001c02c14034018180003000c1020700c4900015601d41d45514074003400386141c04d1034000e4aa000106600121906140000c2010b0901c3c9516a107407011641d129819aa0394038026040344040c3c840361414409052008030128600989941c54a03024850108050380b4040515160002660240301d041100b4046140029804100c0c4458 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 274997643 1250 274996393 274996409
    0x60c03090f061116050a0c0909021f12090c080f0d0215041b080c1503130f17030c13080a020a0509060406092d0c0c08030a0609020a0c14011104 63
    0x81c0554140c440070b40348286105400444c040b0301d180020030600103585400b052150000300703481c56440d01c0000c04d0700c41e0700318025805001d0082449800b24800c08268664031380d031402480c00d00005e16681c4c2160280c0c00c041c0ca400080240511074207208000c0e400c041c2d18503800605046409a41c002e40b00c0d00c00055035441001141d000c1002e01c546c030520301d80150158500f04044540e0307001426514410258040e000da040302e02c0c243d41c00e40c0304000f9284290340210700740c829a622641c9000303600888107004c60b92511301121800701c0b040c4050103580f0400c11803100039902d50042c224415003a0035a4481011980010a414010385600306640d04592050f54140f4076a11100005000340031a6003044840030b00e4880c1003400e1811040c00e5a1a6087d408040c102880c860b800c04030550b51081c01c40808039204000c0d001c000340c0318a0066521408000d0005542c640751030040703090343d111045140001383c1b42404202444150860160050001802000034444034540c1d080e850280740700340c1031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 274998893 1250 274997643 274997651
    0x8030a0c170c041e05030313090b0d08090f0d0501020403060608120a050d0906141906170604080705030c0106031a010b1e0d0b04060b1801080106120c0e03061003060c03090f06 77
    0x13101c0f502e6060f081d019000040c107680c0c03103101d40d910365260228244540000582880c031899850308184005000d441d40203800b0519107910142072142910f41c01c400d05400088040207440812828405840038600c2144085030081c501140305261103218071808075620f40070003011b0b40da80d0b0010100d94284403510404aa81000c0b41440001071a81412078500c00400310104000f1624443d4180c0e044001824208503151329a80b815854200303465600420341c0c0543c01203408100c4401c05440301ca8402c2c0200c0f460b1410380c074000b40c01d481d000c2d1310894039480e201038100030f101d4409141360301605140110701d040c00550415040701303000c1030f10b40c8080303624001107c0070100703019003084c1604400500140001a614400040c9070750010000a01c403100d111610300d419803049840c24105d500a80e14441144400304c000801040f6400c031010030b20044130201400f580f41442245c3c460040c0c03201da1036425186051480c1030740c2d5503d000d5810589040070150009070f03014100c1c110190402d000003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 275000000 1107 274998893 274998929
    0x20c01031d1213050a0312020c09060d02010804030927060602010902060f0c070e010b03040303050f28020f0714010b2e0c08030a0c170c04 61
    0x56003900000d030040071201d0070b603018114008060304220341c150b036030b00e00103003618085600c121002d14402581300985a0180049144044107032010062440c0413030000748a00d0003100001d05000f5250085018144240f0003c00909414400c00d8502c0049210b0b820742e0b46a00000a2081030904e0030125201b44180105a1103035806000103060080504a20700c858002c1d000303404039485000c00018440b1030351050300e4001c001c840d50440d5241001d0070010180c0b07000428640c4440641024099403191111440303010303980468450411142444a0002034400d0192076122a5404a4a5000d000301009040141c403c074030f002b0000842403409012040290868030703a400461080d4502e5603c540c1001044001d0151529995882c12039940b4525130301f0546903201d105517200115841c054024813110741d07180000102c40d0041c0780c4007841840b94880e074018020032501c0c00c0c0c001c0d = true := by decide +kernel

theorem cover : BRFrame.Cov 274820143 275000000 := by
  have h0 := BRFrame.cov_init 274820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 274820143 ≤ n) (h2 : n < 275000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
