-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4866
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:59:49.154996+00:00
-- url     : https://prove2.me/submissions/77e6cf23-0560-46c4-b876-680abb413a28

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 875000000 ≤ n < 875179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 875001250 1250 875000000 875000033
    0x5090604150b180901020306310f0b0423010509190903140c071701050f1f030c260703080405151632120c03160c17010603 54
    0x489159040c0007402070103d614444045000910500810000c19070041d406900b0807100510001c150350b202d01031850045408921411710f82007036041d5a00c0a40000b0714000646600013181c01400700000c08540e41c00f001844446c0064003041c10041030000c105014000494500e0f460b441c014000d0240ca51564904089281e2103188482c200360282c00d00a0741c50f400c4800c06a240d02400e140e05a035403009124210702200d620000c00949441031003601c2c080d280d400100601c90b6183d0740c0e01410440c030b14031207900a1004090000104076411000005052079000c0b041d2519060004101d10101c01e40109440360000c90301040019a0390040b50115101900d04955404218100c2c2050b80501d0300c090110000c6018510204003c2d4041442150640200020708081c3d68824260781200348880119940c0407002e55280c0c1440c4101500c3c81e100008101c0b072608403842e807100c0307103814120b204032503846030070700280800c115040910720365402101c000c000310792550b04c3e038924031046000d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 875002500 1250 875001250 875001293
    0x80402060702060d090c0e071d0901090c09030c06020106150509010e040c0302070602070b06040e0601030c030320010f0e070503010c050d09051c0e010e010f050a03051503070906030605090604 84
    0x3a2440c10800507080580e00540211b0701015140d0346030b110200c0780f10204d400c17000040c0c4000fa05050710b0743e0039503c203900140142c42184181c1c281488000104402001c1c03e080c084000b100200040341004001301529060780041510392404920380261400c040302c0c0810b01900f8059002540d92240b4000d025000441d40460035014241c0185c1c0284260308002d0302d090700004008041c01003410410b4002e42d0242c03070800000b40d401c0700e09501c4290030b010042080041c1041007001ca0f214039000c0d608404501140c40d0501d00b40e017032040c2103525031011248d0305512080c4528004005200c1080100810303002841072000987d4028860f04c41d0406165101d9918010303030041c03020030051444000040070b001e24400510810182110034028900c2c0d001484500205690b075100390100700d031468464a4103810400d403140180c0c0035000c007c00c990181507180151102903901002580c009040390348001602908604100c1c050390700040148910781c0c4004144000680b062b5841000c10ad159413 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 875003750 1250 875002500 875002507
    0x30e0d0203102a0504031a091b01021212060307170c040e0f01020703171f030807053318060c0a230c0d0207180f09050a1a010608040206070206 63
    0xf26801d12071060385400c003940e514041c007038000baa0400010400d8a00400e0303902202c200d0229442040c1c0401c8072002c0c129008030800c0070400360301d00f407840e486100c140143c6d500201d200116501c0c039049010903005000100c002d000c1c803803e050015101600d04c80c00c90301b40d15629000007980e42c1490054441c0100e940d03400c11100003005128824111031440004e640c0c034415801c0080040d4168401440a0700304d10000c21246141d803468049007080c41e4840104591548e01d90100e641c100c41015182d074001d141905000151103507001c1210081140681c042844074120440165001404c242c10b01030151078102d0540000213500d40d000040b40d9a60340c1da04d03401c801c125032884020070001000c1088594480c00d1403100005800c0c4071021000b120341320083d80d08101da079002c99100c0c50440c00c10b5002c0c1d0841d05441500102d400841c00d140120311044959170f81361920305d1001c02130b103401800440356082681101c041500400c4e080c81c10141a050540010f4030a100d80c000082c401d22000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 875005000 1250 875003750 875003771
    0x1030c181e180b03060a0207020a060503060f040903031b0c050601050609061e07060b090609072318100216060503180a1202190c030204050405070b0a03020403030e0d020310 76
    0x22201c540c050480020801081031000012901801264028a1090154900086200d8024400c0e902d20702c1d00188100c0e012803503c030042d5490341c80a8203241d08000421460390250312940a9501118866980041d0511358101e14620502c04080840104650110b000e000302c1c00c0020300c0e90540d1313000c0350f0b06030740c80c668a00090418464005120900c0b2010141c01b1802c01c101c80140064500402060040c031000c07004208001c00c00300c451661001d509030108051034030aa1401c0c0d241d0b8040d98030b140c5551401304124102c3e40040030310701401d100704501c1440b2824008500004070f0310078002040071181c40202c801a4034002d01032102000720220009610340c0f00c090b1400160f00e41c0c1d4054030101802400c00801070812000706038094803d00e40c040045074202c2d94036181c4180c0080c101900d4900710340c2000050000900241c5091042c02400310307a0340b206200500003a0000e07100181d5551a601d8050300b103400e01810240b00701140000500540c5005c0b550880155900704000307003c5640 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 875006250 1250 875005000 875005049
    0x60f0903070f030e01020c04091208040503040515180901030c0b09010224040303061502031c2705010e01022b0908030703020c06091915230601030c18 66
    0x11000c01524030250400d0b06000c2c5600206440024002a400c0da040780c10880140300654072100c5005161804942d40d90760351512030000340340c1041c0b0030803e407441c043e91100020b007041c00b000b84030400001c0002c2e065007045861070003901007200546026000d98910b448a00d4002e08900c50507901d01c400041d1001d5603882070284090198410404055881480d54041d40700d0000b2102100402c2c60454086085c0104144410440b01658021494407040602d01c04c3c03001d04005404088541364142c02410740500704101c240d2010700101070f415083c0d241801800e4820183d020703800e50344108110115151900c0b40044810060a0f151400c0d10160700100000c205101015106800200c14002c180d41d058000b0004d861111040390944d8544458658803404005207107030a80040c1440200040c0303c0d40480c0c81c140c404207a000442e03000c2d424500c1da509240c06144107a8100520400c0705035a0103121714a40d81b00d4510300881081c0f104412070400c04060b0103070030140c0038442038581c001c1a1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 875007500 1250 875006250 875006257
    0x61e0e01031b090c03050610020a0c0512030403140f150403080f040203030c010507080a0c0e090403030914010906020405100503060d0b2d0405250b0906071202100f0e060f0903 77
    0x300c1c083c100140801c861000300244001c0e61024825001c1903090304005200082048281d500001c030f0500491800c01044100000300b1510007807404184400000f060344103240c040d44804100c041d2250300329050001d070400b40c000c01a4940e4141607418080440d07804a000d6a104000346880300454490703000291a500490045145075070905d800c01049a5014001d580540341c203000c2405140b40000e002c1e20042c0d134400c07500c1c3d001703410f9400050120707100e038002448140c0200e60120240354020300d48d03402e450004a00761007054001030108024100818002c0e21348000349409411400d00c400000d141518128020389002c810602043c10100703851480e215544142e0300aa8009018640b103030590442210141d5960040121002201454100d602600d110750b02c0181d6280b820600010404d422000b05e20350003c2041c405803001a40642004400c1030b0f07141c0090241200d4068220243c4e0b8102815110341d0741416805800e07c80d000076455004a1786000c0710320595100d4009a18502 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 875008750 1250 875007500 875007509
    0x8010b0901200106030c14031018120e03070609081b0301240e060f13050a0b0a0b0c010501080c130b28081c05090907091503061e0e01031b 61
    0x20351215100504801503001204483c89040141b020698071001034030100706108180350076030082d0b0f00d030035440f4003154446400654111080c541c03910007600c480341502c154003110300100d41000d2202c07100c6d16007009000b00070285894900e0800e800d1002d07964980380c62040700c81254140c3c04206032a80d90030340011410025520311540c5000d484d81c00302c220244a8404e1108174050700e4007254071814100218101c030400a84100c0d038601040b41114014040104030314481359840b0306504241d5140c0781a10b000b07020103450a51134415074a08907086030b0040e48142403551002c1c030303444d035561601810300e501c0c80d29014000a82400c030308049010a16007180e0401d811501d0300c80104d0058502c0201c1c41610509802c03079043c00c0c010900b003440e82104000d4034012030414030000d6040d1034000500b6601c02d6407460540103031a6a80d00f44c0780c980b829005240003203500c9010070301c9500815030020b0199954007000c0725441d45030001c91011040180006005654604001030700031402d242c1140007007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 875010000 1250 875008750 875008787
    0xb090d051002040f08010b060a2d0804030e180a020d15120b070503070c120c0b16030c0825053105300a0b0a0e0d0f08010b0901 56
    0x50850385500000b98414040c0e11118401c0300303408117000905100304d41c48168060445494040c0500003500d2180e2080300700c0b48641d81d03c0644039007041c0010081c21201b141a2a80c0d8618281072a018141048090800d4040c1550600000c812415600c0203500800340c0701d0016503c50382008500042c0a0701c0c0d1408480111003d00001c0d100071f5079440441a6005203c1107981c1cac1c1b95908100c2d190721090b5040c1001480c2d29030940c0201d60f0076001000e50411500f003400700031459503115140c251382210b060b81100704d29134490040c0c40d01030044018000c070500d8034940750300c0c20703545d001005424482c03c08440070501c040070b02c02a02034400c03107017503031441c0f0000c0042c00d00d5114400310803184280c540420001d6100009207504010403004142642c1003031040d800940c0240619444070520908120381c400e149009d0017142d4104201801001f0288002c01c1810004400a1600742c800c01d03004100642c1c4032118001591240480d0305507407164651707a030fa41c0d20040c012034100c002c00e100280078 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 875011250 1250 875010000 875010013
    0x30e0907050d091406100b03010302040b0d1208040c0b040302012007030812011e051e041d0105061806010203070b07050f0a020c130e03070803040c090606050309010e0a020a0b090d05 80
    0x521a81c0d1000d601c44c22107000480c0d003940e40301c04a00e807240d22240b140c441c50450610041c0010b182940280f846010b01a0210702010119220345000b0241811a90082032881c8144030a026507842190040c002c0910b00c903280070b00d10b0303000801490740f0707081d65200301ea542070040b0140c190500000000710340154a45441e405124510341c101d2000703228008400c01d5291188001000c556462001c482e00204030307011120f11700d02203c204406c0008019031207607803052401c01d241d05401c0450301e1f0050030070001405160000c18400e0180c116225a04a00380d640c00300101681d00100701d601c586c1d0700000c0030040e0303224410300b51401c0c06100303c184800b4102040552410b5030004800b10035040803104107030038141c809100e1045414420b00c00787c1d260420450407011500040040d0f4100744120440e680c25682c80c06078400b1901c082d0420750028400005001c00a5402d015a00203095500043c050082140c1d0004060422a119440344420045600401945c40e072a060444603006803d5850 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 875012500 1250 875011250 875011253
    0x501050702031b060f0403030c0e13060f1208040b0c0a120f02011515030c020708030d0b100e180405011e052a040e040f0c080102030411030a030e0907050d09 69
    0x440ea040004503000200c0c4010308580114000243d59000740e100c040b181500d6113a41c7c608030094046070020406100c001c6d000707540f040d202d41310000302c3c101c581100040c441c1e042001c0320b52007901944c05140030640907000a070201e400e007011541110705480c00d4a9448980341c1e501c03810544840009070400003004043c022040d008012141c000d0707681d500030090004030926000103000385001361130030b00304940d0404013100d0099100014419190044401244d42d070f000325071841d03010352407010b00552190b83c00740440c00c164205495041280c100610031040e100302288241122400d04030380c402802c004541440402e612803005200c0a1240e00580142d0003400c001070003080c0c83c80103d1003220000c42c4d041003070440800d4440310b03211010601d0075203005801d000d4081c000e0016030b00e00da0181b08510000c2c0c0c40da9940c0b0001c214400c00503071285458107240e05000031080c1800c3c020303040b55200c00c0009034886000c4050a0003200d00c0c81b81c640b10407030111024024205100707140f03407a0540038030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 875013750 1250 875012500 875012503
    0x100c03180303120b180604021e070507061e050901181706042102101a12010510141c061e09140118140a1208071805031510030501050702 60
    0x103d05503880f014002081c0718400e21144c0c01d00915040245c0c0c80394030218005240640080c080f807444440724401249040407001013503070086400f101c00c3e1b48074031001c001c07042d008400d0041e8140000541445c100c075420b00070b004c511544401504100906000c142c180030501d134a0780103400d841200f11809000c42e01c0055850405031816074042c1c800070041d005402d003c4d4803000c0041c805501600e134850b07005a681000d0046004402000015803070b500c0038940f00d00403c0c0340c131001400000301d0141450019510680103e4111010b1070304081100840740d03c601400c0c01a10703406400304000340f901c3d81001d0000301940d01c0c03005001181c640308000800b1403500400640346c000c0003682507046200180c0350072941101205040c1c0f810002e407110114050403a8000162021001c0d2180ca550581d58040701c0c039100d240c4100440c03ca54184100540d200700440d481817109081000c865080c01e0001b5504c641e10444980d820700103400207000303028004892801940d0082c02889a07040a0700085d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 875015000 1250 875013750 875013767
    0x150d1506270b100e04151e150e0612060d1202010906060906050f10020a1a04210801050f03010b0a03050c130203040b0a05061c210509100c03180303 65
    0x400303114144030300ba4102c0d14100640110865080e214460302d4076260041c000036000099945d080b804c03640c0710001e0314083d12030f01035050344190150060b440381000a100800c40d842c41100041100e83c40e201b4000e0380324071003161a4030490901c115030341e60399900024400002d41c00020007480d4041102503039180c054000b0100c940c45110244001074852848508903200c92040d560302001001d02d0704040d05019650381401c00091040d10407403a880e441700403401c100d4a68088949000f5020402808100311b449440080e0a41010b0881700e02414000c140c5041802828450401e4441c4602181e82c250f100e064020005000300501580c0c0b410403a40300d2004051684c010800b60b048508200f00b54070071244604e070710401c05486600e803a1284001050010300741b541003070360b0401100010700003001801d140d610802e0701d0410a180c544140c600f40f2944420001403103010702028159136500081c200e1489180c0c0391840c44040c01c2c3c101154840c3d10710310080e0f19603c3d5400d02000b41a800b0511 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 875016250 1250 875015000 875015069
    0x100e120d030507090503010e1011300105010e10180807091b0c03021504060212040f110321071a07030e0118260c070617150d1506 57
    0x201000e05568030305047c203070760b2040c05030031480d045110b0b4410004030641c0700700a08181142020300f400d1002e103140b031034105544440440c1614180c05242500942d0326030074007401003845e10307000036044c00c4042510300c401c10a4650034082c142c41c1d151017034001c2400c04001080001c0444409a543c2d140e460000c21202000021002702e00e42c401d082c01e8001c480d00c8200d644d0640c000c1c419900c1e003042d040c5052034003030411101d05408000103111508105820f038012401441103241040203407900c0e00d015512151524041e4110b025035008800000004901c60f031a880b078144e907100b0a41c82c183ca203004100c070000310b02c245903400348803e02d40d06611019440c80080003c004c0714040508003046481c080000030008010501c401c0036160040210b000d1b8540e04280103820301e10f00c14626801c08070142c02180010b080303401032011040312100007580045100c0d052554149029011440c1e6008102c4068611000c484421069041a80c040001420180e46006d00642c1d80f0084441c1071142154 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 875017500 1250 875016250 875016257
    0x504060611060f06040603060f0203070306090b0d081b0304030b010609081507110c092e2d080610030201081f09090c1a04081902100e120d030507 64
    0x1408036449006680040103141c40100a1800307903101d108850101800420854000e80c0740d5a0020005482d4080c11801d018050405600c0740703004c1d5401821204158040b221aa0500ca0090801e4642c0000300c000c1580110f8402c0c0c2d68010120751181d07119440320b1320500c40c80005400024044040c107594184e41250350361005080d0b5402c8640d17500c0713000515118024400c20f010032640d40c0203001c42900e0107004804d0b16610080c1c1d02c00135a4490007180c00c00c01383d5042070150340d43c1d07070101754a03002c2c074800441c94164a80c2c02c03d0f0380038002d4407008421030311012050165030311a59203c50010000c0150b04100d540d80d02d449509150200100c0c84100d01041c080c4000c181c5002d0b01c04030402c4c1c168500740a4900303d1345000003440103030030620410f4841e40440364010030394a00066001544074a210f2500e561240360a09451510b861801824450180c44101c840180c1c1c0f0785041001c0424a817400c14050341502000a10300042d41c035030b80740188900d808500c03002e501900038030b00c248800e44 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 875018750 1250 875017500 875017511
    0x30105120d050301050906010c020310051504020c120a090e01140906090915060607061505010e1002250e0f06030c180f0408040e0a0b03060a0603080d0c02030c0102070c0504 76
    0xc01c0d80c60340351a0900780420030520042c00541800509a90712003c1403605d5000380f601c41e00840d04154944c64040305442c1c0710b900700040c8800e0038000052040080d50210b1030318142400954032400b007001c41203030b10781002452800d0f00344a03c2041c0c0140950071001a059691107400d141040c115840f02401261410006013103458000d01c5d00703110320941009001c001c151228120245803000303003260780c400418483c1d00301190452180b00200e1107060100944141004009405178529007900c501c074500b65803d980419602164010151032800c9070700c815089200d071641440141c0d0341111411440400410508020f100c2e4031038064501036058400d02c0501b070060040021031400c00a0306c038000800450101c08100d405d01d9401802407101608245c0c540e0100b0050f00c0050360341c201010b80f580c6001c44640350034000030b60403001301300303040100c0e5113541d0383d1b0701f003901404900c055102e130380c1c00100c0c1700c0e24024021078005010311402155140c15614000d5405096030140901030342c5001c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 875020000 1250 875018750 875018779
    0x120408010606030218040e0f160e0109111c1b120b0307060f080405030405030d020703050d0216180f0c09081624020f0d09060206062b1a010308030105 66
    0x1d208031a580000400075544c529070190500018082c00750944105229410100411940901032701101c21040e03540140d00c1440c100d0345200c50030042e00a0754019141c80132224a0f822041e080b03602c50b690342014010764039280044d00006040d041322001440c03c0340d002010354154855000141b6420082040020780514800d06944400900880021078982d80d1040c2c12540a0b04400e540315214108680c5065101c50210342800e0040c200328015074000c140c140100030f4140004400cac48c000e0710050113010030090010301034510500c03a078500d00c07071848001142440300b40c01030000c0e04014003040c00b054001c01380061001e00b0754420358800c1c2c002c112082c0c500c1c3d50300e003542000321421b06542c4000d844034400003162040c03074020070409512074007804000300d074028041d01d01d115060303440b10a07055185c00006402c20a005002c039104910421024181080003040d08200415051442c445103926180181c0520500ba81c0a001820000300000c108050640118140d540c00d407020210581e08 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 875021250 1250 875020000 875020007
    0xc030105040513020a06030f02210702060901200307021507020d0f030b180c04080d02031801080f0703112817010612050403031d0c04110c06012303120408010606 71
    0x1c3d224003c2d44505d52850030030459100e0340100d010207120382c0006260000c86001e00c807001d0118998502c80030701060802252540500c000343e48240c081000340103030000042c6142c4c2654402000d80900741c004808191b0080c0308100c00307846507141440c03602d2203060911010303540e44000c48031040040c41c07400795043c0d038500c64020381140c1c003000343c200100314482e04031714074010034014211442d0080c280000039030071604005e07036141e900e0144c0155940b010405e160444001d5207440780b90521100c0300c00c6c001030035441003441c0e0f48030750a4038000822041d40440b03143c00d482080f5008003110704003201e030540c0d0501d20003000008d4038503440b40022030200d54400c0200800c00d00c1580042106010007440030203003a0015540180300b458006001d0b40705029000c421001403100c81d125500030020340f1900d041c503115645902003030203541400d005035000c0b1150f542ca81406807000c000c100310181c0d0b4150080440002d202c00e4024141e4004212400d00d0310b81300c1d000f6200b605000e40c00d0110000e0308900 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 875022500 1250 875021250 875021281
    0x2b05090c060703021b060c0a030e0913150504031b0503042c01120f0c060e09060a0503030a0302130b070b041106090a151202031815070f0f090e0c0301050405 69
    0x51580190040241140f005c40c4a42c000082c00c0c3d410980070018aa0740381020311040b10014820303210095803c1c90700050003000f29000305403000050803103102c18007003200200a0b140418240c030022400d90344034942101c525001841e01810380c118646010300308000400580140d40385160403e1000210f0150116040a060f0342d41c5e0081c444040107100051051819207801c42c05100c200e021200c0b190f0703405010104641c00600083d646040d045140e15024800b1504210100d600701811420076000036101c1c428105034101703165000410800c500d086968860050401d08001c503210011400c107850081d408403012210b0401c0014220300c0b600d045000c0d03986010b00540412000781c00e00100e8241d204010710a0f000340182c03d11a2101c0903100c1c0010743c1f040301e084500303882000b081000103142107000703054110302100480c108095030f50f12410102e04d203503641c40d003550380c44404142a00c8010380b0f07800c02c079500c0f4400b008108480b40002c0c01941210f03820f0360100640d54440b807162402a2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 875023750 1250 875022500 875022503
    0x60b0714012f0f030c0d0e0601080601211a1906030f060e0f070f08010e070b2a06040c031106130b030a020c03190212130b2b05090c0607 60
    0x101d41034403030290b0701c400c2c016030702418110070740d0500c0c0180308001d5425941044610780d68009002452003207a2200e40144003100140e44001c22055040c00e0105480e03034014054441b551407070002c074405000c910141d940d802600111000d4600d48291900104400e08840c070304100040c00401c90b004c1d00c0c2a101d89002c0b203030403688040c0d05501c199070311b1014061b00701c2c841016104194112101c1501880810010803448484441480c80d1051309403e5a5160400c19466042414100710b07400c00b5204460050302c00c81648424400c4001d445042c82842e900300c092140314410811007001114052070382681d02a40001d507115041c02c0c10489148a52442d2a08041000004000b440010000345402507178142002d030525100a041c03510b1078200c00c51580808880c42d01045200c0e4040c0304400f0385d500b48510f440d10b0044010069034944030b02d03200b1b283c0b0903100000c840303c1c49440b07800c042d0b108410a08060741452610942500981000d49005105003e1001e20000341d00d881001c468056 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 875025000 1250 875023750 875023781
    0x50d050607080601110f0a1214030103020f12070f050a0e040f0b04170708120708040f260304080d0e0615090405030c0f0706030b030c0d0209100306060b071401 70
    0x10781e10301004a49486000e810181440b421034a42c4010072400c0c000d040c404403c0000801800340a820580c04060f90102400706100c0c0c008a91814441c50b00120303410b59030140d503501100704000011031240351260341222081d0289020106442024200000807103604940150071161074031201030f20351100b030780d00800014032031681c2400150080c0d685603000c0d0255007018182c401070041e00800d0340c05880219540c080c0090702155442268040c3c0350400c8043c9803a003000c0c0307082d5960820b542125030f0060803185494000c14600344550200c2001060550000c9449090500e0884c845410084150101070301700350825a0450001401d103104286c1c07104c008401603c00000d0280884018005450b107000c2006100f00ea000c041043c038000e0b0f00020300400541d480c000004007168440c00300d45109070050103010110703950f004145107907180c0450391442903444800720500c0450b00c50f4001040e44d070524600040400640028000700c6015181000260340c0e0203800b1400c81d80c1c503142d9440a03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 875026250 1250 875025000 875025013
    0x81e1602070905330a06110105100608070804110402040b0a0305060d020618030c0301150807120b0a020f0903011401080d0c0b0411150415110a03020c040b0103090b0408070c050d05 79
    0x35030130310040000340205540c0c0340e00c01c41059020408a0f1020307080320300401c008a00b5032000c0300c0c0c01d1160350f501c540890880c0350041e003044002401c646018155004200740c6401103400c8c005141c001d04090200100304666599072840e150b0580d802584c00240481e2070800050054148400b0103000a94010101d40c5010000f4414509410125418503014481e00e01e805819440911800e29511286c2800c00400303480c08400520b4070034030303800840801036041b80c00c7c0001000310140390742010041c58056280c00c225140fa281c1ba00481038040d13855801c0c4114580d0240c2c2c1e13442140e058480c0602900c4072003107035030710503642000d441800030450840400000c02095490001c0155498000c00f2001c20100e603282d41c041c0380c1c000c6e0f00001106060a00e030510742c1d5800c2a0203014003001040070704180d035095140603488180e920002802662507559803490390b0b01c60b07840414240d40c011001e103494106410800c44c3d070341203043c084482801100005c41c0500e00340e85010350310f90f84100207024 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 875027500 1250 875026250 875026291
    0xc22090b010e0a020c0a03180f0e0a110c0309060a171e06030a02010903021302120906072d0804020310020d200c0706121103150108061e01081e1602070905 68
    0x100b1000b8108c400c0c0c9035078140d160100b21030000c150804000c080c03161070083d4506000b01520f0803160742c0d02c03510708440b40c200500419010040b040d1040707003500715081c980310318111a00341d50311780742d03c442c00340441d040c4400c0140d040c0c0444804c0d9038000d0040c0c100c0c17071a503a84c0024599989940c000c06408100000c10800051402e0815030f0101c1e00d11402c05070501c4013045100880103019105003409822203020050342c540c1c4050a132100050304500341c5212400700004000803000c1c40c400304200311130389000034103648041244100410b4000811552a40186030140043c8441c984042d600c031001c40d0184802d40a6806072101c02e4036101c0901601c3d883c2010668a03644400102044a51140c000c4819a42001c000d11311400300b9554480740000a40001001001c00031f142610880c0031400f6001c0100304140c0410f4104000e00704800780c1c1c0c03a8288541060031000c81b13040c07032900c0c0c240700b0090312820000210800807007580884250684981e44802500c0c8102c55032002c08807100012607 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 875028750 1250 875027500 875027507
    0x90a050d03060620100c020a0b092e110d0605040510030506160c051b04240b0d090203030315030d050408100b010c02090a05010f170c22090b010e0a020c0a03 69
    0x400d0001c1500440f9805a6000d01c50000da550f00b03c00c1c46c003d0380116200c4400c0c022213107142036212991070080c048181e00359541210f0341e07554403e00d9241c401c049241c0d03545880c0d43d5104542a0b82100c05444c0c903401d601d00c000c1c0151040c0e0240c0da004078288800b08100c00070142e43c40080e00d80c030502901084c1d0f2a0741001690f5880c4070211001c12a00304400e0003c241c01744480c400e0141c0c05071048080c4101f510512094500ca492041180c428000d4512000060f582280303042d03030308400003a0b903121090754444014028a60001c1c0d8076000000511403404210400300081c0c00007a810758400d285081c40655444c040d610035030303165400c0442003c0341c1c2e450950152601d040c5c141007032244003a03a500480c800180444d041208599200010703c440600e590f80c000c001c0070848929410138620f0b0354410b88800310048214002c2c040e501400e6400d000f9544403218500c8060001c21003003005040c1034a42171001e00ca84030a9078170440101b5480c00d0130307000312030f42007500740d00620f0030070416a4101c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 875030000 1250 875028750 875028797
    0xf0a060b0a091a10021501060302030f0705070c0b0a02100608060708060603040b0703090215120702010b0301092001230a1206061b0c09060b0316090e0c031e090a050d030606 76
    0x4d10450051066000c0c000040d10311590181190340d40c01a101d1a24031003407075141030090019014040c05014000006086250240a4485c0205129150500f90005900c0d104040420b018410304140000c9164580041c9007482212195118002a203500b03040c01142d00c0241c4006d0412104280090304ae540250451541d59101412400c0064441803501e156500b1030324400c1d442100c00d10a119602d41d090241445c41c4004038003c01c404a0b8558803084d40202880105000922075000038000c0c4c1e0080c801c19500b680f00920007211290356a10150050344015540760204242100c44139009032288602d00c20384403151248205071404c6400c0c0e41440d10301010032625002c1c404030101d030818082c0110402040700207440c0d500c0b81041c80c0516200c03191090301d8810400c552008100d000710022441c2d42040d9890903056482c2c41d001746010200d40501410300704040c0b18418405008000102d01098601810035030b0441e0420010484c1911454421000026140d01e0318950a4a011046 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 875031250 1250 875030000 875030029
    0xe0f0105030105310c0c050f060105100e13060821030606040501030b0d020a1715070f0f090306021c1d0c010e2b020112020306010507080702030f0a060b0a091a 70
    0x3030380c0100c3c6900204e40d06541c48a0f4100c000190308242d4441042810042c4003249007c16014040660400000c582451248100c50040005900d1503084503243c0e0b0381c0000e0104d16404082c408541c4526020380d03509481441038840e02d448405603c0c03052400015240183c50080c10307140b40c589410f00440240401e031030041c0c4e200c44010f6980e00184e4418000c18001c01c0216624040d01aa50f01000e0030044902c0350b159018100e0000c00840c40e6000080c50700000050510004170015000201d4032850b454000500941c40060800c0d03012290740103a26041d44091000d01c4501074444040c800c0e00c1c2c40c280384941d140d008070b5001d04d2560181020103409030001d404e40326002c62240c035056080c0d603840c4041c810012003107001d01c159648441c100d04180e484090661450602200082403403243c04400b4100300e41c040f65102c111364086c440c802030003691400f220f440381c807a401d004d0300030603100c04c207580b08044100b0000f03884812400787e61945001c1c544075443c3e1007240b5080c4000225807005 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 875032500 1250 875031250 875031319
    0xc0609051603050c01020106080c0d0221030414120a03091802070c0905090607050403110d02180a060602010c26090a0f050604020301060603050108300a0e0f0105030105 74
    0x15074115201004001503000d50024040b40c88100006821036003a5003103000190441d20302e000b0f80307444400395409440c3d415900c0d90042c4c101407184c600b0070440c0b40d88480c0d06010004000900c42c8820020300f0100000702d13a615040a24102610341c1e0746144940140814a00074041100011001c411030720052647d00262400005550740a0107090540001005079911414000803940802c031a43c3c0c007001c1390920600d4542107440b00d01c10b0f01119060244070388150000081191905c2102040d0b000c0e5000300012582018442800508558055000158a08500c110078a0300c184028802c0a03800149000c0f505003900c4203105000307008101280c288111a805000109a004628990b40c0184d010340071904083c8101400d503011a4003403003c040c10440140000b800200b0007500e44444200030401c070b80d484200741d05a11002d00440d0703908174008510008001d400c006003113004030f400c82c0c00440d0040042c00540b030900080c0500c070707007204406072801c001c0c00328030680d1002c142e4440f0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 875033750 1250 875032500 875032513
    0x61b2303072d1509050c1e151309050c0f070302031213031e030b0a151e0f050c07091107020f0103050c090d1e08070b0a0c0c060905 58
    0x444245164070240048800d01445924601c40d031424000c40d001c8a400600c458201105640b00d0301010000e5420920040d6601c0d031904080160400540842c508040c02c03080170b84007a1201040803c1184140a00660034035480a000325002c4085500f0500700140c14000142005202e1000b8100104441400e10041041d02c441e2051503015040041c030a500440c0d481b140c400c0e070400d001801800c401e000c187c0c4524000002600242010140c24181258003030200d1150001c81c054107941440d1508414858000f103040340034058041d0001a040c3c42e68520031800c5402064041400001c0030300081031b43e022980720300c1c4541c008141c41c00002c01101d20742c607190b046a200302d58250401074964240096040701314200908003800c101c1090900300071030f15200c005205240b02e078000503032040d0703c0101c008041065005000351114954441c0f900cae03040061402c845075034000c24045ea030406046002a1100d040d90044020301109603a88408241e40c503501d8001030454a23000301c4050042c81b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 875035000 1250 875033750 875033813
    0x118181a030f033103063206040c050d05240105091516051203040606090902030c152b051305072303031306030b04060509010b0309070b2101061b 64
    0x4520b1003018500810002501c1d40c80100b640587c1d140030320440070600e20301c03414071081c9980c2640caa80d00643c00d03070303000c598000c0a010854481c8a1640004002440c0c10107208072603802103004421819519003401151444600569036400760244480d07003c502c0011400300428000080d240282200c103040710a0f8403680c5e0340030704080f000e0402c001c00b217401000308414042c240c02810024181d4217020031412a00d5000309842e0b0302c242c2c01c014086d140100815100322440b40c00c96103001e0321506070400c400030761080317108041400c04130001c000e400c0101050f4181070410000342c000364003000820025141150070f4402000c00c919010754800090810b01c0c00380c50910041802015603d08001920b04103c4050211142e580000b401580f82c50418085500c4902509041d42c0804101e02d89a1340d51001851401034580c01105641c0030201c1e41c410304105140d40355070456005850501c251383c0355141200c540700b5614080d0503111280070004007082400c80c445248414810400e42c110801 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 875036250 1250 875035000 875035087
    0x3021c051b0f1c021801080d0c0809060a0806151306030c02012a021018020f030304330507031704210210060b03060d020118181a030f03 60
    0x3c041a030780b410f041c0d02220444c40c00b082a5214912070302041e410650408000698400c1034101c940c00b40681d07080c011040c08208816101003001c01041140c1e80c05403c0c0b00104010002d41d0f0050291004680c00105400440d054580c03220401c91902d211621b04441100030b41040f5580c0310a45d561030003921004e00d2142070045a5041c110440d03801242c000c0c2009141c12900c1c100510b45c103140c0302044c0e820900c040052245140c0441c0c0c07103a08514a00002411842580c2c04410300c2c44039410120340110868864480d505100c1980bc21340e0603041005a450744501c410042c001458202d1403055254040d030354903000740c003a2108100220344840d003017a001814400c01c0015234414200e1859002d90b600400007d030803510b00f91800d500382075002c11035501e03017020300030305021b46540d469200c149002ca00b000180713403d800080c039203c003c4110a00801c1c50149040c0300d8040f2280c4020b050500081c00c00c141302054000398640703a13038200420311541588a082c81c000c0e10050703010001c00d18 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 875037500 1250 875036250 875036269
    0x170711030106170c101e110f010603140c012a231902030d0c03120c170c090109181e23040b0411060405130603021c051b0f 54
    0x4040f0350000c000d44000c2d4140707400c0000381d500d07104820708850040c4442d403101c8070340440003103181500048504a1010b540c0100800c61075052442040312000248005400c2401100c1c0203860840301400311b6130307900342ca0706240380704a40854180c040e40050203031590030504204202c1001e031403660380a5a00c00401c070500380300c0024602140c88128505500034404064007080b0140e00c2910302c0d2050340425129417540c00032100b80040c11240405250086e03201100030324481c9420440c09410100c041e00c04104604018a900710aa001840c0180742008581c00140141c440340c01051030104a070125160308032541c000c0b03e0301c9107080341c0c1d41c0101174070300e456584040032b001c60410480381d14100000182c207280403c01003518140400304180d0380c1c0c240d400075008104c1d00051085400880d0aa1003140c0c480d641120b040001c121100c0e04036071111090301c0c4219034512034005103a216a040125000001e0a00c4d000b102c001c04022910071200344503608054501c2c081e240c2d079900010a40c04 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 875038750 1250 875037500 875037509
    0x10c020c0109050a0501120911030604080408102c0f070b0706110406051204260d0b030606010906111002030c070302060601140301170a080a030204170a170711030106 73
    0x38400d203030108007507801481400c060301050310350b10705003031401c03000800107800c1ca0100800a03503540d1085050008100a004a040d400340440d90300c0c1c106440c1980003a0710610905086003c0c2e40c501c0504210701d0f010ba0050003210382c556400f0340110728071031500312001644164181c82888140e00f002c0c0c8040c0004801403200078850780d120a8a81000341c15101c44404d09a4039031402c03c8140110364121b82640e00b070075660381c07084000f961246440b504c0498900d500000e03c001c1e83c05038403100401680200800c0c2440318080c482003e002042c15070300c101c1070ba20a03000c81c4c5041e50621078135119200042c02003520004640384214031340c4550040780e1007641d03441041c0e0b400094480a00d901001429000381080ca8500d001c005110aa20328500040c022001b080e01c03404001102d0355010007000c103440d50400d1700f1980c1c5041145002c1c000b0b500038481c000c1c2540320484441d8a1004c0880e0380e031034ad07a070420308049100c040026035055a070711400049514180820305402d443e1404d100b00f10140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 875040000 1250 875038750 875038753
    0x6060e102001091703040f030c081c0f14060f0d05010f02040b0408190b01030b0a140f1807230105190804110d111012090515070507031b0c0305010c02 66
    0x109580d01340036540d000840d46000c80d0340d0040080c0800a5000003002d10480d81618180e402807001c0d01d0501a148141e110790b10344841208241d40101c0c03840d9011981d83c005c0003a04002501401c20b280340f0411007191002e071f02104400c002c62480c10011100c80d00c0314441e800020b00340c2c0d00210740c1000c80e0000d810074200c0c100c0105e011b01200c0e100300704800c1580d4484110811508035950713170b4070b4003645c1400002c007222141c0022811000b01500051041c500405a08001d80b40c0303103004c800c603c81c00319040003458a80e82486560b081010454400303940c64441e0112100c0100d0300119443c1840302132140c10400c0c2000b1210070030f1980d20b0320200101e45680e99441e0307810725040c0000f0060b04c0d48810361143c0d844002c07180014083c1d803031547c040c41c01030b10034100254007000141d8090416803101108913081c01320560030058003141c3d150b001c0b01c1402e10007400b0f4940d030400f102c940c064030000a0206440081c4ca8192084071031080c001a0711500382481903980303c4c2d075407500b5104058100c01c0503 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 875041250 1250 875040000 875040011
    0x706140108012717070b1305070b0405090f060a050307090903030b0108150405060f0a14180402010f0806030313030302031201060e0d17090405040302030301031506060e102001 77
    0x40800e00031408040140200c3d0f0219080b00020494207601000700101003981345428910050300c0901641c9009821000704c550618015140c00410302c580c0c082102c840c001d00c40080703842043ca0003540e065600140040e030181d5108448144c0c851710103061141c0c84040309100051a5500f0803001c806407840350400700d40c0010740e14002d01595040d06900d030500910a00b0400384d03101030185107400d80002c58011072151600700c00f148003003035a24a4660030400d1000042244c0c1e60700040c410a003c815100760760f8502c10445c109440c0325064500900240c1b5555240c00c01510408841ea08402c008040d030346000c041890108401000f0742c02140541c0010402451a00b0310265a034010103160130a16115010440083c00c0e0006104001700842450b000040780746407582c080e2002035501070000c206074101170401940d43c0d0401d00c8201c4d95100d000303400d50034400f064003403403044070f0b039684902c208107900800300889105034201d002c040280000c820240710041cad0301e034010140450b400001c1c8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 875042500 1250 875041250 875041259
    0x705011803111005040f1209150f09080102030c040506070618031d010e0307061d03010c0c121103030a020702222019030e0f0f010c030f0c0806100507061401 69
    0x1031002002c1e10f0b0b0003c510b00340c10480414070038217140112603440b00c481001340110000940f251061608640d40c0002e11000384200075801c501403459082c4181c07600c401e111f5407250b10500342c6c44202e51040410742c0500040195044c007001915807144540008a06600c507109000f10b5a0101306c416000038100c0024150a01410301101c90090028a090351880c14140701095132100984550401c20004403030b9000340c01d03000502c80c800904010001c3c441000341010003045200040c0e400d40c0c032441c0700d0b108410401c4c0161500c420840ea06809541941c1d0358000c90300083d00680d0307050b44c000d07190031103034102c041d1410414002d80d10045c1c40051406440d5040c1882886080c50a1141d10400c10031401400303040b114040000706245800b00710001e01800e280d00b08201030b07079000b01c184070364032854655000c103422100c0321070441e035000c111107181c080701501502c41d911010400b046410300803542d2801c001100100420003410558034003005031791104202e031241301d02200310490500c014403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 875043750 1250 875042500 875042503
    0xa11061e0906160e030c1203040303030c1e05091809100506010e0a050405090304030209040b01050103110403080904270b090c1915030f020d020306100305100b070501180311 76
    0x150403144000082c00d80f8a000302d1460032191524a090742484190030304400940d0b410020006089409070094104041d03a010040d43d0380c106000c1100841d0901c0d00b074030301040c410100e000c004520340c0c130031244c050103030502501c0c1030b0300088609410064141e442c4411602c8286000e00422903a0010462202c100d03446c44100c0d00c0182c0124100480d03900340c0c00300c07a0386083d002800c0d610202ea0000d001c1c0c0711030780ca4501d580700c1c66000035040046001007100384210100940c1c1204c3c42a2010b2114502030003c0d501103110724040104508018002444035017000d41c0030944030031400103c44200306042e11464a40c000030402100c00344510001c0004001c030a0000d5403942c902612000c0c00c0c9506072132001c104022a00603405595262000c01c5211413080d0011004010080011076a6030000c000c481d019500071030b14140a0011811503911040c4030344202032190015030344d141e501c1030410090f445a07603c441c500b5240c035903e0b0303415010304a005080020309036210b500c81b4030041d010702c25041d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 875045000 1250 875043750 875043811
    0x40c082206060e130303051f1a090d26040b0d02090a05040e0a030210020f161109040609260a030e010e07140a0e010503100c11060403022512080a1106 66
    0x70800749805102302c108506480c040e5500f50f480c2400003850646520f04103a48038090301c1d1076940d0082c82d210448090040e00c41003081803520301c0b0300c05281092001c4480220b48a18401e5840549003088008800b188a502070030012000a11003050107958400040c180c0e031500161a19a4006040d2002090b404001c4c0b2413000d000064254100103880a4183c1c030360043c6c510036a1a086d880d210041000110300500340c0c2044014180e448a09081c10304500070a0080821101d4500303501c0c0c46421a20004040040010864100751800f90301c2a000c40142c404142440020740d2100204460f10409110b10700191900184030a0708400c51010400848450350102208030a144018002910082030b000201c00d1320a002049400c84a10200da8800e503030110701039035000b4041400201035000c1015441c00540804501a1a10752480e2689040c030922035601c0400307001c801301e0001a04a4050080a89242000c00c00c83c410024a01e003081d908940d0003103440c0c14800c03880e131860a440b824 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 875046250 1250 875045000 875045011
    0x9050d05190804020f0603220c0e090a050d20060109020307020105060118090504020d0b090723091f080f0f0d110d2001020414040c082206060e13030305 67
    0x9025800c03c4d401007080c0d890400d85a034001d00e0000001a260001c07500308000107000321a2410f4607210074104080e01401f0380c00b80742d492044040c00f04426031000505400ea00e81c03c50007416100c80c1020041d104840744102c2c5140340a6040429120f03070700309210710f0340240b0358088090f82d01d20740010020300f1240000c001030706010050030030002c0814400c1c004400c3c1d800f00c5000007805d0f00d0303a000045007460280d000521900803082041031766040800c0c40d504803084110040380c0071301418140040c8101c04034196402986070f0000a0b580480311002d0441800900207506000d070300e944880707050400b84510710456601c00d0046801440c82004600261505c918091002201401802d078803485c10580f4101040b00d65081810007095940c01103d00d0040f2000071540c481d6a264250800d850b5891018440d07843c0c403140c40350090240c0c0400303100c1e8000030200751145180100c030519a245408080d00c6039a0f03241d4002c102c0c6c0a286807118019101c01d50f020500094a2500509580f0001c04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 875047500 1250 875046250 875046257
    0x181101090f0e0601051c0b030c040605220f06031211030a050904150e010909031803020d0807050709090312230c340c09050609040803060409050d0519 66
    0xc04100840c46200c403003054568804010885807152030040b0786034007424410008850b45442007400c020b1166210780d07039204050b401e0f5243c02910ba02008200c0b05c8504c545a0480c0c20715401c054030245100030064941842000000c2c0982c074070703000c501180d54980044400c141c1941c00c4450090308642c0c80741c51516018001c500d840a040c074010a1806103581450040b615030380d158600b00e0040c80364401405841e0548a0550782d01d65840c80079007003040055000c40e0801064401d10000160208107494020340f0034904141c140e41d44502c9a4008001512a405903a2010607600518010b4500b140e0203a525801101040240700044406000c520901580003119a800d080d1616402031740c0b1007881d8a203107481b03c51000030703c80300414404d106c00c0c49100300c81e0290648941c060310740520900420007071020030749800d040811900e0580307201c0c0d0300c4241c803800500021110340c0210b920003800b88c40414070101070f6690514154120703050b203010581c0400c0504240b4070000c00074880d0a082e24 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 875048750 1250 875047500 875047517
    0x1a030708010b0324061908100501031404110a080a03020a140102122a030c0703260118020c06090606100c020f0d050708120c061501210b04181101 64
    0x4c0202240094007480c580714121003988045030340e0300d0b0020b45403a04103e840418015440840003002140c0032605030305680701130301000c60594401c0c425156005598054192240c440d52107041e4000c00151550340e10000301d54001c207500c2c02c02c0c007090b000039109800410a40d00c40b8544511380500c4071441c1002c9078810b11000722104000c203610f075040354088000203040c401032050001061025034055408260001c14808224080c200404e80140a99140d801c040111001c00c5401200340d44d900c170815140a00501203401801e80000d0b10490715040145040c4552805506044080b10419880e030010f80030801c0d0383c2004048020704c41e0040c50800706104250b03000800c98807052810314010014950300343e081140401c89140500959412144882207180342181c0300e81c0104481e9005002d81e0000c0345410710100018a00188c05271a07030708010840f0600c8212880903150303001141354442a01d140c0c0303034a49201d496859186c2c40e06104018034181021842805810381c428104034008 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 875050000 1250 875048750 875048761
    0xf0608150904110d03020c041a0f06040602150c04090c02010b0405010902040b1803010b040e03071202010c09050d06060306050712140103030e0d030903021c140d05180103061a030708010b03 83
    0x2050f140c1c5000045818009080751402c00f246001425a07142e41c11a1604140c1c88a03444034049019001038111003c040c0041c80740144035060059124040240c0c1c0320b504502249285159015404120b0f003505501b0325036140c00000503603c03004401c20150355030741d809500604103801024050700410301e06500d803d16040c0c010006201d600f0b00103034448002c1c442695195002e4208082d460001801884012190b0030240c0c0c0329800780c401103c040015207001c00d0103030300602500810540c503031a000703103c1e49460240302072900b401000f21415640c413940400080d400f4440d090141c0384d6540c9501a9181d40b140340300441310b0030000d0795102c0481c203004000081c0d100480807034080c0c081c1c0e10300484400515045d20003281540000f54048885000c40c040180601800b2a240c0d0007068144120b40c02c03024000d4440c5131641d02500042c0c000c00c1510414501c6151801000406140000340320759a90000b52602180c040e880641650003c1405540390780304d030720280035103c81d4582c4c601d1403d00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 875051250 1250 875050000 875050013
    0x70b01080d0c02030327041a090702061e1f081e06010506030c07050a2109090c02060c0c0f010905070608070f090911040b070f1211031c060f0608150904 67
    0x25200781d03080a20a03046c030030200ca0402e626071120440e0290042c00882180f4040d441c080320400d003154014114400081e030341d54400610a0f0040d2001150681d44104900c460580c041c802884980c080641014201c0142c80032500c0200510844000c0d0900c2800b490f141881e8800010b80c05126a115200500c25943c4490449421105020402d80d4a18044c07600500b13003604400080d10043c06c41d80039014003441c5c100c04d103035071000c0303951000d40f919260b00c1c1c01d038129401e04e0300c02c2005034000301c00102c42c3c6c1e191800030310186280c030049400040070750307003d03909481000c40704440e50b40210300c0c2005583d4000c02c0241d001a01c1303040581c4203d1400400034002c0724544034000303903989c6070141d4001c2940450300b00c40140c01c102490301e43d40c00b000d003408844246080d500303c0f442090b01d5604030300b0b5441407028421640091000d10b03e410b0001d001d030704080c418a030f0021652951180000b400b861250a83c40052659481d0000c003413800201c044010250742c0385060194403d0001c100002c0c1c4c8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 875052500 1250 875051250 875051257
    0xc0f05240117120706061e090f02191103190c23060a0c0504031205070b06030c0d0201030203060f0a120b060906130e0106030209100305010b03010908040509090c030102070b01080d0c020303 83
    0x100300f0102c2d840d51200d040c00700242030303a0f60064940304400000c00c0314441138946180291854003d00b880b2141031404070808078801d5001843c2a045849105190303d841000c0d1040c505400f401181e007002d04001141e0031500b034981425004c2600a000703002008076407194542008289240300e109000c514288580b550001044c40c00110354529204201c42e0044068802454122444841806408101038001e5022210a0341c031680b0300000508140b500140d845c5031302c0c4c2c01620f00c121015042d401540650400f8100580c80340300300c911100d00d502d0300000200280b07102c464058400c5d2650600c070b0a0360300d000c0c0c045030081d0741e00010041140c82c0d00521301c00043c2d20308400190303085541d41c51801800217400007940844802e003072050301c065400c4103500b900e00940080124280c40301c1058222281004010507500b82030200300071a01d01841c0301c50340040181c0540b0880c1c50050300290890b400000c08450701041c3c1c1006011000040242ca0400070850070080a0400d450f00001c0d960300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 875053750 1250 875052500 875052523
    0xb01020d122a054b0f03011202011d0102100e0c060d140a0e06010b0a03020c0106030c090e01051e060a32030d1d0d1509030225060c0f05240117 63
    0xc0c0d40413452451300030404101c1d000741a490002640380c0d40c441240c102002c46040042e400511942a8076103010a08101d0b10001c0c04142c00801c0c105d00c490344040058051000b03000494021f84c0f02c011042d403141001007013611030b00200000c01c14a43c400c020b80714900a450080454603080450388245000140941941c421513680350b2104003d0302c04401a102d400c003041d142d035080c1480001040907044030300d01560000c070700a000080b01004868200e0f8000c9410b03108004170480c41c42d0840c3c40d8405415007040c400f800c2242c9298032040d200600c1400c41410205481d2207000d4411300c01050000112000022000307820110031104009050200c3d5520080328641c1212007c055030303840e00803501d081d6900c01c1180f004c1c1c074503c05c100c00007001c202500b90f016000e0642c00b145451120101105099414001145d40f0b50410780200c582902c5040d044070840130310354054001c12001c020f0225030082e003d07460041281d0b401ca5001d00c048040e03200030381040c90403101a400c010041a81d00120 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 875055000 1250 875053750 875053867
    0xc140304030c0f0204061509080f0c01050d0b012c040c0f0c0201030b031e060a11070c06050903120f09030106080115030215040302040e030a030b01020d122a05 70
    0x103e007980001002040d49501c4504001080e0882c1580290040009001c546112003030700e4212130381c461415107a4201030074040c00500d0400c03040380ca01032107602110b01c071b1006250448002151081802c00c2951240d285080142031440001151409006c0c610a000d12490540c05204183d03074060100c43e01c2400003810b140e16042c00d00741c240c504102c1a02803603000c410300000500c2d40d60010b51a0720090750010f4003582044180450f4176200c10880342e421f80c1c81045941c41a241035022110782c1c1240080c9589030281040c00703000782c1032032009003240d5040012a295030b000078a04050031103849510243c2980d05140505055520085140003100d4065401303012500700c0160300c0002e0322840c2c00003036200b440c0c03007220b1801c01400070103050414900d032010811200c008006998540115000000040010154a40c400d09980140d0030f501014961700d1841c41010312100f214402c0078040e00c0015401050500c560441c4240400710031109141414184900a18504034100c015420310140c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 875056250 1250 875055000 875055023
    0x10c031e0509010e010203070f0305090604081215062b060b030a0209120d080115020a240f09060b04060f0323030d0507020c0a171018080408010c140304030c 69
    0x1889804c0d007084c0c01540f0f910008558914121070094402003010341401c00007403500303000070701340e001c0050b9103402950420406070600f094040398100112008118074a42a102e4104462a0f2102c40140000011041c07001c00290b950459004410802d001c000c0c624a06012082040200f484200c0380c03c81802c0c007025030340b00c80110109032080c00001d1740d08214850400401021644000564180c64101d0245040300f5600d6104990ba07081001c409003c414603036a82d80b80310314855891180030342c890301d00410381c6c0032142c403468126403518005542c52034403403210b0b02452a0a200d400d0207048555680c3c0903840c00c40e101c0820300e41041c8203e903402030141046215945003081504c0100080900034045032034600b030000d4855100c00c034400e0147c0704030302c000310700304182d1200c0f92032881c4136000814440c40c448603244054101c00b041041031502200032100031074000d100400140800303800224409801c030b88000c0030500c55501c0150a00d000f801030000181e44000460003064001814614 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 875057500 1250 875056250 875056261
    0xb010e0105090a0e0117010b060f0f1e03070f080702010c1205060414150901060302070b06041104050d0b101208030127141b0a1704171b010c031e05 65
    0x300780d65803c6249841d68440000900303145510346ca03004843d020000340140c8410030140b02982c041c14801d405040c4040c80304640c007031080005801c4403001c8041085520221100d90145640281e61040005072421042c0c5009600140110f401c1360151000300200003e081d401070550042103018900540c66070082212680d940c0c2040d000441840928030307850509103000180b0070200002c1e20f0003541c00c0c600000355140a8070030340da582d85c0c1104102c0c110341d9844041000510382100440e102d0780c8144008079032900c0d08200c0035512885003c5180c0c0c030781803c0300340c46880b54440d409004045400c07002c02002540d1681a28111103111600c0c01c091b1071048002910701e217440a108001e035203861030b000b90709403020005074002d8480e4111804c40c15000c0041140611881c0041808201c0001c1c002e0520b400717004195500901901c5844104014803030717084119400451000000316103c032104280f1102813080400e2030f125401c0801554000d155410320312000c020849940a03681c900161 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 875058750 1250 875057500 875057509
    0xb070503040e0723122208030c040503060c090604060f03020c011802090f09071716030c1805010e190207021f03060512120a0504082d010b010e010509 66
    0x28042c1c200481e0506071440d01d000c0041000442400480407481142001e0002ca4410741c1100d0790390711004900070099985110600454044900001c1e40b034000604a001090110010794010241e0218007030f07a5a180808041ca40040540700c801c0c03144042000a0307507a5240d000f200c1c1203c5e41824001c1d40c6d000c280d142030f402400341202c009a40d50809031401001c440169141400074401c444640058558000b40f0344050070855401566900140f000d211419076031405e0305418003840101c0c0c401d9070031292040900d941c66441100c011a00c0b10b024044c0c404900c103a042141c00141c0304008942c9800c181c162983e001620f00320b1100d0b02114941400c0d031083d012100b0766070300545141a1040d12640c0350074800d40d00e5001c00c0c0000d1034114003107000e24080507210403d0061200421001102e003400c80602d41c001e003d41c3c02849020400010011401c0c000300e42e041c008202c10b811000061840c030010712000c2c404000300d50745420043c002b1070b80c004002c0491464286007154542d241c013070105 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 875060000 1250 875058750 875058757
    0x30e0a02192d06020109110415050414061008070e01032712111b0f01030e1204031a010617060a081605030c010905060a050708070c090c030509070f0b070503 69
    0x749004404600090700b01d861000b18108915800c2003809200c1e035403608124202d5104880c02800a89900340f13510355450706401180100143c0c00561402c55500c100140031039030485100a0b80070902001c1042c0e0f854040c12110f40c001150820f140186405000108440074006006043c07540d00e011039800420a107032000004850510711020441d182d060540000b1502c01c1e40d480001d801c1034452602c140041480307043c0030848105074040040c5c100c200901d00d10308070103041c10165120015070468104101c400315011584018503590360a5082402c0764214090b1400300700c01c060401005103544c0101c14028220b40b41240391110748030345c000206901d13011f50002e040e40c81294001c408c0101d51031005030071141c080301196552501000156800581c2d031007031a620007001d005054140d40110000e0926034414861246001400c1d91002c0404d88140c00802005550b8a98030b0034094040c03144030b40210581e0000c0602c00d281c000403c1c140c019902514030066400705240c0100300040064 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 875061250 1250 875060000 875060009
    0x408220302090411030f0f0a080906070609080d0c0c02060f030915070e0f04050709150903052a120c010c0f39050a03020d052a10030e0a0219 62
    0x3000c105007010b041040030080e240c44c07094840d000c0c0c00841150860009803140070040078a014060011480e00c031007655400c554102a0811010002c020010f03c442c480d2412440c4100742c82c40c0c80710421110202120030010f127440603c101c1810310710140e55400d043e1444140d60814480d030303942d00e8290042c00c00311000074540001c03000c041442026500020305101d030fa1f100351000e07a9206e0558003041b050714800c0d00c0c41030106d01c0c5440c040c000350360745040f00f21440d00123060203030b401d640c1c0c0d84e1603034170b0491211008014a10112111401903100d4048007c1d12030080f102064810b16001c0c5d81c03501c910725102018140301e0b4a2580000b009062039103440740175040300340c0ca50110850012226169084141c1e400003c00c80d411040c51456142c0c1c000090392000307017510301103508540c2403000002e8100c000351403500c54501e4060b1121103010312918099240740041031401c80010901c02408801a80a8107041c140340e80c01800910005171400349680480744400701d030703200080c01e10486030281c01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 875062500 1250 875061250 875061259
    0x110f0604140313030f110d12120209100804031413090b031b210102130e10060c02012006070c02031c020a0f02060906031f0e01150c0507050a0303030905150408220302 73
    0x70b41f00c184175512130090744d140300c0c1e81c8030b41e141100d4441c840c1d4100d103c2e0b1000c050740414800ca4002210b07120b078440aa009100c0d0500d90b840d103807450911a5a40c100e2550400c3c0700032042c07014042800507004e03114402c60241c0c018a440c4100c50410820360400c0c403003042c000c0307181c8202c0b520074080e00c407000284032041c00001c40d40c0c0d44020380304240070380b40741c0203202080c509803002c503000600780e0310302d101159040e54400124030890382c01140c0c841402c01d000c40340340301214092810384800b805641d0080795580c8442066100300e03c14582000034212401c040c0620003030b508540141c01041091650f41c0c006420103036081a4800111680150310099403c5100442040116022012101e0310300e03030002c408e80d00c44c40e03944400c000400001d0003002e00c1c0340c0342100c0d84c00c2202d018408501c401803042d01070b0b030407440e00c4001240030421250b0040d40065100c50070306003440800e100055448580303400e0408240f401ea1034480103445440101c010503c0740d5014100f164000303030055006954000d2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 875063750 1250 875062500 875062519
    0x1416080a0b06150a031a150d05061302031501020d030516050f0c060103030504030b061c140c30010c08060112020d0501090212090606010e0d03110f0604140313030f11 73
    0x50010010641c00340355640703007030418060308041d00c1c01c1c1c010441031f81004400c0710720304100800e03044081c040140c05240c100c1101245031015240c02c0c00074611a42001100e0480031500c0c100080c604010800024289803506041c0917203039007410300c91161160241070150342c8500e802c003c1000e43c4104a02c4000b103000e542e001004141d8408000d104980c0a032070042c50300d882703180400c404986400b4100100325402d075103070000105011900c5581550440070340e0324010100c00403401c000a4810f07034110f0034255240703154502c007130a048a071030032400d04000c0040f40c5e0404405400680d002d4061414084001c003100ad01034403e4041b2800444250014445541d4401120004e508103960b9588105040b000042503400000340d00c5111307030016503460004580c1082480a10045460700390108020740350f0b00c02c00b490040042c4960852800020402c80c03406007050340145000e100c0c2d203070a0340c10400009003000c1e50a0018002d498000f070058044010501d00001d1400090850641103540b11 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 875065000 1250 875063750 875063767
    0xc11060c060702071e0608270c100201051b0304020d080a0f09060e1509030f01060b21151003020c06132a0e130f1416080a0b0615 57
    0x41440ca0040620741c0880c1e40e20307600c54001442182c1500c040f8610405c1002007080741c00e110390b104c642c000000d60380b442800c01a0641c41c010042000343c1c9075006030701072103002115040076202098508000d20007008a07041540e5841c50808407002c43c80401040400450150359070803a9500b03034560311220b102d89d41c5c03000440c050305256030742080c0d4006c52180c00340040c0440c010740b007020041e4001402e644103221b1100b22442503401c80c2c140d55815100341168150011405d205e11005803058000403501c1e203800b13140302c000090038084128000701840080c009500800100100f40d14004c907401000e003504408118024003ca9410a00c54801d0b40180459801c00c0e007108858035010b0503041c0c6a400040c1c8075503986201e40d1844103480e04030518104001c0344203441290b00980710000c001106426900c6900c40b12031000d00035102600030303400041544004000844115100c1901d43c0100b61070308c030825846000300384014007101c840300c000561035624012082a4944856020b03922006030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 875066250 1250 875065000 875065003
    0xb0301120311030c070e0a0624050409290a0602070603050c090a060c03021203060d0f15090b0f090109030e06210108030a020c0618060a0309021804210f0c11060c 71
    0xca20610400102c07006c046100c50110b030198a013560300d0100044200d80d08200f4242c004405501078808001007071202003410769290050400e80c900c0034400c01600034103500030300480c10402d02d01c00d204103407600703040002503004106802103c440c1c0c1400611030ba41c20030f109034184903040c17040d9441004000085a00d80e0041400c159144c002c0c1d084a03000b4640c040c81c40200c4c80300348c850581c000402c10491000442100d000119039204903481c45030405c21008039426034180c804d0440d1030b22107840421801e00303405a00aa0310800200082c000d211403600c1c0503050460b0f02c48224011500010f10290040180b42c240060380081c049001d402d43e91400056241e81000422074018051150b103403e041c81c01c48141d403824064410400ca0415003101001200c1c8e120f070503a60103141c1c86c1d412210141c1c0c0c1d03101516800e0a1000003940162900e45081c801351003600b204404240c005071412100c1d154040e0081545000a0030b11001d650210309000119a480322400c070342c0b00c04009060b40c2d90460 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 875067500 1250 875066250 875066263
    0x10030b04080a0818060c070606181d060705040b0306040b100f0e190e1008011b030605011b1101050f0d09170a0c080d090210030501030512040b0301120311030c 70
    0x1280d55211113501c0d213451140d0315182c80c004c40c070856031045012815840c5400024002c0900c1103800080442d52141420b000300d154107592686030355244c0000400084d80b16299503800240b03c080d061516201c5030282170303800340c3d000d030f0048035901000041050310346900c901420780e001040080904019080146012091070002c0005070050b255a1128200807456014803030701c5c0b10042150a0401c8040400c0101c01050100e42502c4083d00081640080c80740b1082d5070b07018500b040802c1802207016055842d25030180303040001c2919007450000c1e00c00303a1b54030610743c4401c41210302c480540c0101c596016021007640781040c00540e07040520641c0c0d210f810498415414840041c0082000502c640075070046200030403c0001000c0008031404020704803452030100c0010010100e4001c26030510b4030605030008a40e07140010b0bc144241005002ca0130700f41d0088061810741020103844180c08180b081644401c64080c00108140c040d00803001800129002c0b40e842c0c0015503c0140d8442 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 875068750 1250 875067500 875067517
    0x60a091e0506071413090207060b0d111011100e0c0a0b0c0c49030c150e03040608101a04030b01081501120f080d021c1803050310030b0408 61
    0x80c81131402c04125600c99080c2c501020000c0f0803690b081d40b820504401a601078001210000d035200c5101e09180e030f440040102950003000241000000203062140d2008581150300c180f158181c20f00100c0c2200256180804000d450046200100d80f45200c2c58089605040c0b684421021030224a054030000500750a4000e00300721070401290005110a090514065052404424800810358000e010b40075009454036481c601034041001d404000740094440304a00258180d41544c081c020300101c0c1c902d6404140700e0400c501c0c154003101030303902d2280741300742e01c10300c240040058044040e00c02220002e160381128500b4034504a003d0b80003603445030204403400c0b5180d00001c01e21101c0007888002401052606621503420001e000c0a4281e000c58120786902190303502c9000200303c0005481107600040740907840e5104030001c401c1518841c150318403800d01c0c0405074020201d110a551003000c0d050300b00503560341c403000102d1500c68510340001e041c000d070705401d0208103c0780000514020 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 875070000 1250 875068750 875068757
    0x2010c052e060f0e040c0b030a05190b10200a0501060501021002120a0e031902010c090e0c0706050c0c010c05040317180108060105090910061808060a091e050607 71
    0x30100507804900700c4a080c060a41d014484031014490703400005003c60f00306002c2e01c24240c1c10b5a0310702001180740d0040714a09440394445c41408201000031440c00003c83c02c2510500a5940b0741d80407403990481e00340348808129580c88007403004c40ca2802240e0070800300d202920702c1c1c500e03030341001c0380641028411580144141a482c142a1101d80300b51150403541800404098440da0050409050b90111039402400104404010030800342c1015a030161907800104c2c1e0140f08210181400300d107a404134030001e01c030750108422030341910100d94640c3d41c0080006055110b1817401d41c900c0c010040351002661a082a900398150032502820480388a400601200c1420040805940c000e2030500d42c0c903400c11000648066008041031070b0300c0b440601d81141440360b4031001038030024055444141c010b520030414401940e0050810003403400f1071840441d000d1808a01694607078000f4140349202d0341d034003245c00c00c118081e45101c001100e01d07003260f0807001c4542080c2c1e840c0d560503a140c1011 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 875071250 1250 875070000 875070073
    0x15040302091602030a050d060b07060509010c0c05030f0a1403010617010510050706050a0209041e06050301020c06010608040519140106090b01210e1207120c0b010b0702010c05 77
    0x201c00001810300303000b00c440d0b01071810055640426a00c0c1e4010150a00d8142d8403507d010500074020b4019045185c000caa01041c0d0f03050030101c40303003100d8003540540c00b00071611000c01c0200d2000806c0300d443c06002c1e51807640d2140d200030200c400b00d6500d5090b145604002000187c45070b0f1003889403601c81340b4020200b03541e0341d94400704103100e54070401340e0000c15010700c560004a0381355404690302c4130901c040545031442000004048400d40200070007110002c2c00a03c0407121188900310141c41c3c150700841c50081180d001541c0c806051042d0760030014140005000c10100780080424210031942c1981c10302c2d401d04e40000740036040300e030000b929880c01c070f00040c00001a0144105140043c1c442c3e441c900c1c010303009180c0f00305503c1c0070360314020b4450241315401d180c100315004d405105402d5154552501d841c0891021040d5500581003003d000391980200d560400840e04490400e90304c1075a42c1458401030b0340c803d807145405449030080d01501c6141c1100c08041101c00390a0b400c44030711 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 875072500 1250 875071250 875071261
    0x604030206031b0c06041406190905011b1d060f030105090a021c0f05070f080703110912030403030206071d0621180c010c1110050708180f18040201080a0b1504030209 73
    0x1038171041190032100320b5012720468149050355034480b94019024100100e0340c180c0c42281054942c0b24070f00341c003000892a1751644020700b03028100c2080b401e8125003507842c10b42c01180300d50540c08113004040c03240b200080030413880081d0b903048035400120b040170502081faa0398000b034014101c50751001001e5052500207042c2e144514028454105203441c0c1c4c80840d240d10000720300030001d00d80304400004040201004954501414a000c0711540000b03556a07411460006c0c10004003504140520144240f030a0445465040341c050b462410b403011034980400d83c2032203e10003a80600b201101c0341400600842500a290011495102d10200c41c0c0515002c001114403100c2d0401c0078000f04c1c034a11012406140102d000f10319100a0300d03100b4109401501d0710031055000f061540e41e244044e0003042010b00b0000c40c0c444c66401c0841e05854140d8043c0030240558800a000034100400100003840d071402c10740c000d0742d46401c0074140c10511504100c032020305038001c1c041030348a410726400048 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 875073750 1250 875072500 875072503
    0xc030819030504022d1206070e1c0318051806010801081f0b0f06031f061115070306080a061d16270c210b0604030206031b0c060414 58
    0x30f0140343d000d4014040030101022030444210102c1c0b8040007184141540d21240c1d8403089640c0d40028032001400b030358100103402600b00301d07502c0011800703000c04880c5001218081840e1003140c4e501030401521165034010201d800002c035401156108880c43c1c00d5016a590030000c5610610007030326607c040b0b90700c484c542a1f650310310029107120141c0d12107042800c00e6254000c040035501c0500481c605500500028400d0342080b14490032001b03107040ca40383e0180344c00340004000c086604161120b00a280c0307919448082c21114940020107103004a400c591080c1d000c00000e06200069800508283c40c105000d81050703030070480c0800d1118010b255210340840d100000c0c1e2595002e43c600b0510f4100500241420248041d148862250030080084114010341300e49000d2503458400208052080e042072440a0032a0058a49083c0100307519464481c01c940c180d80d0121141030303c1c0e80e90079040d408215115140003c03030010105102c550160b0004120380035038441c01c070104c541001241d816 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 875075000 1250 875073750 875073761
    0x2030a0e0d081b09030c0d0f110114040e1305030a18091104170a2001081e130813290307120f0f150609080105010e04020103180c03081903 61
    0x3c004154405100d51001c010300010039032004054140ea0280c0c0e580000126503810302c601c285c81c20f002d608115002c210a1003002c3c0380000003400c040400042000307521030070340210301400b40022030f2440400c0c40c80b8a08030960440c56400012a0b03034501a00000903c4c00041455064403050b51040126403d4018003d90342e1603034494100c0c0b42410b01e4684e03081484503081c0e000404030300410b100003000c1001c103020b4400303e02c807082110700801d00c081c000515140004040b5445000c8442c04280740c18072000700ea80d0002c080d021450081101401c0c051854130540c00c084960341d100b00e00005071203a120030402c0702c2c0a8504140682000503031100c2d0300b548000c0700c0b1080000c1d0300320010601c8410320340c0b02d0995107081c8030000034804280740f5290101d482c600c034814521183c5200400c40c01e50f020039440301418072800248050b504d80613601c00079100c0540003d06040c0c0321200303444598480a90704000300d0300001107151040d80d81c144250744d035100c4003183c0c41d810000310030005401e02034000c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 875076250 1250 875075000 875075011
    0x6020a02010c020f0d081e043206070818030706060f0f0b09010302030a06090c0801090f1404020d021813020f04140402010e030c150c0601090c0903060c0203040902030a0e0d08 77
    0x5403105c609800c00c02c60346940010a00030408805296a0522400505400d8401c42c8100e01e905102010101c3c0180359004003d000c0062803101c40007141d00701c50100703025400c584c01c0d05112081d520f804c42084101102c1e5500045c15101c04120a01407203070542058080341c0d0f910201104054840d00c0c3d4401e90682ca019004603604200620040c6512a900440d4030034240c030302c0081e41c641c552a00506403019012540c2c00510702c034006102c0800c03148198240c00811203010481207002c2c092020381000c00400181c4140b0300364060001b036403140b000001000302d0b0340002d4a41c1e49080c021041440d804848140d01030040748000c6039050070715114101e0840340b150721801640d0313940c3e401100c6041c110306605415009550201c0d0040e280c418a280710140079002c1c1c2522100b016500c9481c001050f0701c0310200e00e0030b1400f01d07080305c1e8011a9941c185c0780c04c00008101c2c14000c105c268598442c591108080e00d2001041042c4002d0550020035011056010782d40251035882080350503d806449 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 875077500 1250 875076250 875076253
    0x31909230d030f03180f2a090f020d0c0801150206010b0313020a0b0319050606190507140d11160e0a18050d0801030c0b0a050322050a06020a02010c020f 67
    0x80710007290241d030703c40040d80b895150108082c40960b41e80c3c05000c4007100e0844820366a01c084800b0080008800a8020140103a0b9880c40024644e580b80c1407106200d00425030340e030b4042000900e400c2d60111908080981420701c00c8602c00900100305982c24881d40f0311070035480c5c040041702c03440070403001d04840300440c0190a40c1c6403400541000100a10704070707031103901008009030043d465005184554903a0070201407049410b0203e00039031340010031140c4079020401144004c0030b03101810001c03002191401903202c6195107015401d010f00400c000441c0d01c01c10880002d039580c490482910003410000356a8225840480681c3c1000a401006030740d0319440005500c219050f8030010682991540d584c440403e1070300da69040c03c9101d9032a000086145005009101801e818200204022480c4078982844650000e0407408083c0410b0704921007409a81000401d4101320030f0703096081002d03280074004c20f10304000290b02c80410100554200102490084e00109400140d00a41ca0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 875078750 1250 875077500 875077519
    0x140c031b0102150109021305010e0303070f0f05030f360f0411040e060307290706230a05060a030203070e18060c0405040f110d05070203190923 63
    0x51810818006203110a03045100307642d5400300604144012500804282d240160b0702d001e141c1015460307490680059050141c0a00c04c4102a1400030866003140e0304180f000e0070b615014608500100310040340903059120201d00500b0805a10004000d2018101e178010400500c01c00c3d890380d030940590030f80859804804228078070b401d21601d02884c002000b800058400761004074110030384c00076003009101d003000d202003200302e00b410021500a0500c2c40b440c90440c00c060f000380b0b164031501048103141028081003d10402c5101e400c0b0612a640340e01d802d000103000c8080340d844036a41218840b640d2800e01020403150f0612100d9203042e0303034028004d00291414506d4010327213454007910007032000910b40c4400040321000e001140c0140d50412040b0760707507443c0400304401c5d40d620039a0b0451051420240707540c402c000004a1701c1d01c9085c201e011032590ba504800341d085009103408000c14201b94a000b600e8254055421015030b022206002c0c1c10300c0703142d2400303441ca48001c1b09541d045923010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 875080000 1250 875078750 875078773
    0x60c0715080c090d0512070f0209090f0304090e2b09050a082a0a03050303010602010f0212130c08011a12060408070209090f1603120c030906030f02040302040216140c03 74
    0xf04d0007045000e003d00308941c283c0e800740340b52101c20781c807090007a0341c41f00000600340118a0134000f81c580000350342004214001d80b21802d19100d104611401048136984c08000407008001c2c81240c0074800d68410070440260101c0e080662000710426240014240f00c4003c00e81c0e2620407654010ba404400007040b0411b01314124150031600c4103240c0f407c40c0012004d8205943d0b0745010381c006503200f00040c545a51426001900350303906411010f66a6006000ca0890031501440c9607034040b90007285d810303c801103814040380550032034001e40a6942411140d54a820301070400240010381034580c0c0d2005401e0380c10403900c0f100c0c1950028800c0300104520009464028511038110540c401555210310308900131516040c04000300b54400c0c48100c10400920644580d12407102150341403404510360260380003031201c41c0d540101c1c8189691910040548186c0b43e05031405554090b00465880c07103188050008050f40140803030b404030104480042c0000301080318484448090028850141d81 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 875081250 1250 875080000 875080009
    0x403350408030105460f0b0408060a0509060708061809010219030b0307050105090307080d0f11191202120c0717070f03080f0d0513020f01050f070b060f060c0715080c09 74
    0x10a070301745400d00911140851807074144640301000300070340a2085d81c1c80b898005068204640140002d840926100400c901c803800030468030340c41b900c145800c604940d511400140102d11811903210301030100c40420112060560040500403261500361180c03200c039a400702c094400c1582c0c1190503421115080010707500803400f40681c040c009082d200b049484081d070900e454480d008060014240d02945005250094402c4040841d004081d0021007070009007002ca1062219008110805520b101100d2a1084c03065404003034018201654a100f10800260785543e1400780e8800c0f00300705010070f442a00b0000383d4400b1628a00c030307010b1545140d5181e07812980c10070101000042c2e07041005002000d034912076544a804810310042040b8028014001c03071b40884d02c42c0b9810300c2802c001c0d48801c107140720280e0b041543e10040302c0c20190f41c1c00e00410014403200c1c0c46030f60491004242e00c40700f180081180d0302a00d0f20b40c8181f05013542a0281101c20180030b03100700c03018a60400c83c80e00c00c0d051 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 875082500 1250 875081250 875081359
    0x120e12090a1707030309090b01020c1020030301030b0115090308070512070602130504020a1205060f030d080a1521050c060d14010e0403350408030105 66
    0x80400420360b07a02c2c4100c0c0d065101125040109410080c42402015000709078800501240b81c03003004030183c0d000c0083e41c0c41000b0202c0301d10507400804c04000a074030075101c1c1016034000e9036100c14000d80f129001130782c9400070f0004681c3c00d10800c1c0045082d0202c100c100c60108c0e210350b0b59003101440e40d1105103103503204820a42d034502a01070389421001c039140062426902c03a0000603540d886140806034a020680c0051703208034010841c0c030081d103501201d44041181584800100c075192a00050399000e200050180c05015400b403050000c0d03000700351507101c1c0907901002d22160b110b0b211141d0080406000d888260040c0d1191000ca4407145540d070b4490a1044040f6400d03400c0d1040080c0d09a000ba020380740006458070f0800c0b141441820303603d801400c8030703400000e65040541d0040c1000710301c040c040d0800740411300140c0440002e540b11101d20110102d005506040c07030b0901034003545c0700740500c1e8000d0070b0758a0080311144401c0032114604003800244d6407045c0d00440c2c126408070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 875083750 1250 875082500 875082517
    0x90c03061f090f060f0f0e01020c120703120305191107170904061707062607140309010b0405060d170f1b010905010c0c120302090d050a06090201120e12 67
    0x41d1603003001c116124038030b43e10710140107240c40d0354041c1d41c03495a008100d402e11a581d0800c005046002a03044d0f6000203100c40603c3c0b044592003149103410589c10301d440b896074000b4007190b14150349550300755007580c0007a00502000b0130b1030f088800b40046c05001d54040c0c0245e001e001004010b100d0100303103101d04080d02c11300d81d06025407515106a00003800c1d41c401d0b03005002d443c04805215000b05100f0860341c0c0081625040030300d8400b0f01c0000071040c0324036005400c002c06040f8000550b175148526941c151149002c015076807242002c80041d4000d11141080ca801a0b181602040d8607280c031040705801c42d40d010314080e1800760b800c0e80384843d41e0080c840540e80903030305000030080c10300b10054081025501c01d000048007220b6007092400d540000325105c1c24041100c50f01008200c45502041c80011142009642d580c2a1008945a151509400780c068081c00c04000108800740c1c01524405000360307940d0301c482030740600c100c0444600e1143d40c3d01540c071500b030300101410118064803245 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 875085000 1250 875083750 875083757
    0x40e061c02031c03060807140d05010209090103030e152a0c03030c0102130609030c03030516060216060b120c010309050c030303191a090109090c0302031b090c03061f 73
    0x81e40031074580340d9140841d02d026100480403040c4954076205d15001411100000c140e07003490003003a10f0000da10941100c0c003c101904c1060b0070b2050940460380230441c050405100c41d80c0d6400e004050140740c08880d442500c440131894440c40248058454044001c40302411070b0030030031402a4009040f800c2c1d200c2a02030f01640d16156a414400390101d440803100150366045234014080c500d04043d01705005001c0030600502c04100c58960340000d0300d6060801030754803103030852559030301240d607900180300c4c2d4000584054023010002c05007407890320601080c801146801c040041600216240b09115800034088000e19031080d00000c003103a0040302614001d00d42d030000f0a0960340b003210303216801d421181c8146050f01445c031a042011000f0000d0300c0e105103100340040c0c03014206219041f15079071683c5c94441401000784c510401150300400b164488459641407400302c45c1042050b40c0718420a030b00203580705c210b9204492003600c3c02800602d410f6060004a0b140854401112040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 875086250 1250 875085000 875085049
    0x406030504140d0203090112050103050a14010b0604030c050102010e15062b030e090106171b130807050406091803052a0705090c0705122b0c14040e06 66
    0x102da00c00e011010b401401540a591307124224400546040d28030074070500c12501d8003004001090010608040c4a0340c080703100ca610806101003140505045829254004000200007041000c114591001c441082c3c000340102001d200017652a001d40e00c100f8062403207590b0003d6041d25000440c4040750306080ca0910050b0401010411007009203030086010500c0100c0c41c132880c0c40c0c5a11590300605081c035103451510009005170b10a000040d0540d4081ca030120301d80180c40040c0d10503100002c0c814084030030010b55482d04140d540e4141d205d070a005174a40700300071501e0051030040c40e4801c1401d44546840a94541c2e040703609910100501d02e5030151402c41556964544c1e03d0f00c030520011000515003241004200300710300f0300151801040910401c007050010343c010902c050b1820051410342d03195000c41c1c1103020551000c0d40003c0e2407201504010300190519801039821032800d980e02c044101d00c0b0390942c20741c0d2082e80102181414004000340c2e00d490040c408004000002590905 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 875087500 1250 875086250 875086283
    0x1a28030c0906080705150f031b21180304150203040b04030609031b020f3f06181506041d0a0203010b0a1508090109080a09030c05010c03050406030504 66
    0x24900001d4121000d4a41c440e4000c0040000810104001d01411100500d49407071000e820b00813445400f054410b111408000a0402400e02840f10302c0418482091640d0351450706401c20461400b801d180104100c07a004203c3e0081001c201d100100d0402008601e014101034401d001008030790043c4045100400c00401d120180e20054401980700d5140810a0082da10300a0300c0461f211016074034503540c182484000da5515190305030084426a540c1c2c4094043c20440415618840104503090000030000031104c0e00010f030628100b030302c500031344049850381c3c0c80d11420500b12001c1e1003a03030f9012249180c03803065000585500310f2002040007621001c0f0004400e06da201c001d00c440000e4002000702000d40c102030065150030003040740c4c5020b0391800e0802ea4030024216403003c101700016440015a1310f074096102d80c1c0882d400c0600345442c0c0c108120011f02d00c1205001c05c403011402003074001420b500844090102690548400e401c090501030118001c1c0001070054034858241c2d014000f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 875088750 1250 875087500 875087513
    0x21519060b1201151409010c02190302010e10082e0f0905060405010510120915051803030106081b1b010c0e030a150902031c020307061a2803 62
    0x801481c6003104070b0b4503074412030035222030a44168442d0040b0182c440d00e00440c01ea00400081d5062101d1880a803184090801201d01c84000300000750040100e4101020038a240b5840c03000b1a4401d0765000c05641100e01071080c519810b074080c401045416010800c61094034801c4401140800d8410005251002c00b02140140543c011a860380c107120080c0302e60880c82c000e681d40444140c80600440d49001c0200703900c9000d90080c142040595003030000070121a4101c02200c0d41c02c03a121000642c02c1d001604c00a01d001d503400805039805c0a2421000500481540d040318415113410342d450340c454446030039940c0403001110722564100450415403156102002c6041c220a00005944450701ca024003008040f1444522036403100b002800000c1604510620b148480c2d100401c041c4805d1000c0392815110342800c00c49070036110a0382100c2136000014040e03c0e40540c1c01440301c500004840c04c103486e012403a85800c0010088064051f2440640d850344414400782018055585c1e601ca01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 875090000 1250 875088750 875088761
    0x3140d020d05090607021e1006170d2109020a090c0207090e0106050f040b0a181416020d0f140a050415090b0a030504020f15030907090606021519 64
    0x401459034003107203000032516a072042a07070084081c00144014141004060769070f003006240441c00d070f140d4041042c08418240004503001c501210148007840c0c8540000082400ba018203c0c12842607180c0c82140781d20800b10890000d11805500c0100c6510781c000d031010305107024041c0d1b00a680307030b080050865002e1140e0900545940d001d80402400c0032429415103072416000600c580c1003840900042d626610000f607ca401110000303030400700e410100e4031850b5141c1c030262804000d01c0c0e8903030400344190003902000b40d2000810141c0e54a0400c3d030b03080f4043c080106801a40006001022140100103010000040e0305000d8007040c01e041c04c51503654004e180c0e5400060010504216a15010941680600c1c041c1081510a030802d4020030184c0a40180402096103031000310b0191740380c615100c1c00000f0094440c2e4040441440c248006d6403050346c44c00254408c0b02400501c010a0784503910030303202181d010b070254441480c04114418405044281026010824803010500ca449032 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 875091250 1250 875090000 875090017
    0xe011b0903140a021201050417041d09010b040914060604110301060c11090703090c0b031e070302090607240b06300f04051606090303110f0109080d110412020402070314 74
    0x207c0c0518040c94800410407042c64040c0c00b411042c08144480313080c8003002500c2e0074054190b412659502c000b22409403000b0240150801c2c035082c004001c1c0718a6900100c0c2150184007111015141c00f01840201c420014101ca0a00c80c107200512101c0c1c4100c807400d41c5a03000c0c844604924448000158010a043c1e518a011035038a1003954200000c00c2000c20051100070700043c19440e060b0090740c80c2c40214040380b0b0380f2417500300006407014001d505840054202a02e2035481d00454a811488140d58400c5860014070418034a121141b040c000e082300900041c02c994100400e4042e0011070007015101c0182c1c0301c3c4001c0c450500d2901c40340d40e80303110390300c2518100002e08140c201581003184111034941c4000407940709000054001c1d0400b01100d5044c0307401c1206010114115041490010700324900b0f508016040c0d040c03000500103171848000081c403c2018042d802e4140d0040c0c0309510408407038001002d006400f52a05038007030800d80340a170628041c842c07014070b0502d4083c3d0101c2d00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 875092500 1250 875091250 875091253
    0x204060e01150c050307020d1b1401030b061323130603030e03070f051003020712020c15270a030209190501050904030c1b090608010e011b0903140a0212 67
    0x10411211800e02c2c1d03000364016070400014808040d15010b40701e201d8582c010b030090307100b18900d104100002c21080805100c0c9083d422075a62101884000e0542e1186001c1c0003e041c8004904c00b4a0b1503021503410700306140300740c01000c0c501105c28410104a10311228402c040000307e0401e42c50700080c44160001060300055010b080d4a00901031a680b81007103030003503000c94014800918644446d8040c0c410841d02610012040c0104a01900c503541e4010300c1307403251115201c2c103190006004111200c0071210382049039002e0415258038015032111030745030503401c20141c5400c1200d072641c4040300030117003040803c140c603071300401c500707003006d96152040d020000740319a40c0e02541c4c8039460141c01e08070307400b40090510351002004216101e202820600b01005c0d0104c14001520365070b00104881901400010764a0100074020b01c0341951500840d405c0901100d010751003034041508165254072042242c50460302c88060a02c40da804000140c401e00c02e5070400f60b0f4407001903003004403e480 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 875093750 1250 875092500 875092529
    0x607051914270301061a072004020a030e06010510050a050f0c0609060406110306060406080604151d0a0606091503060f0e0103020f0f01050901030906150e0405061b0409020306030a020406 82
    0x7090500316000ca40c02040c000703c00f00d500c0714140d0001d40032643c40301c1d005800d000e0352001c483c2d0100980312342c20600950044c400a405a021505500420740e503441c260700f6a4826030783c2d2018000c0102060a401000075001c20090300a18000c10143c00bd40c800482043c0c00d18060032002454020255960400c1d0340c040e900f0001000f103030740510380c68450002915070841c10003c0101d4a940107038044c00c410700c1008000140039484a60186a12504c00340718a40300c16512211400044036802440040d0441a40000d01c00c1070603001d030310101e81c0300c0c0e81c0c0c144107180b0300740242d40b100002d00c0c010010941c40740030000b0100ca8481041015100b10044803070f01e03515510402c4a01e03288034640710301840120300141c595a0b041001d5810f0710000f0308011071401d6003860214010940e0110503040070703804890202c1d041401c1d03190180701d184110225042c648034150008c03074940c280000c80c14402000c0105100c0c421031500515008100501100c110b100240e0020381560583d80000541c0e0201d078 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 875095000 1250 875093750 875093827
    0xf070f230a170a0902010203030601031e0507050307030b01080f0601050c0a0b150a05011b110307050915040507170a090c0909030f0206130804030b060109050613080607051914 77
    0x38007940080707900e0070800c4513034201c2d40080d4490000801c4141131665803034003d0740d020300c030210f041c0030308007066001c210340e01e0102800341c8150416210301d0000703490100c480f0101e5000c1d01402c1d01a510f41d0040c1da80c1641d90744011540c56111b94000e600d1070245288402c00192100d0a0354001c0c0f544808001003a02d0446c1400740f54013155020904100302d84080e00001d0074450189110340d60008103444502551002192820f0020b500640c0c200004200304032110140d019554862001140c040c4065198000d0483d43c203280a0340d545c90400c1e4020103e04003000c0d070380c03202e0b80c00c2d4420b08041c45015600ca4511781291141d4030142c0104441400e00f02c425641400400d9101c198808001c6881c4555100e080f41070146020041800340f141d804140607030301885180c4000c0c10002e007a695100d400c44450f28419086101d40f010600c14400030510050191041c1c803007031542106035045006501a00b164414801e007202140403104000c024101411402c030b0b100d00d0010003084140d850200b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 875096250 1250 875095000 875095037
    0x20f060f04090e0c04020a08130318030602031f03020105120717040f020901090e19060b03061008010b010806011e17011205150c070227130b0f070f230a 67
    0x100c108540708a104014000c0401e030808c0821703421000c41e125440f101c960a203803c0c0ca13403d40c1075090f0503104c4d00b100030000401c11103400541c810b50613020342005885004480280d8110b0501000780820420f001c0110084070131008035034008c07580d25010900c40e05150b0020000402646c00342c5425442c110752100303500700310074044e005000c000003c000c150502001a0b8896540c0d040f030300c2c0b800c92620030311703000d22034180c0124402580c02000d407056402c2c42e10403114004003a2145402d80d5081086610042d07009003103140c441c03441038544807072060541c511080c043c2d001503038220900085919400d030301d20303140c928140a002c0349400d643c03c455850a01c2ea01e085c1800d40311004e007002c40b00800c00d010361090141c4004039419030b41c04082c1e0b221208110044480b0809002d0807031510001c1080d02031304401180c0c03100340070b444161001e40b110250645644001c40e4400013082812101065991244a21059188842e0b0507414000cbc42e201594030b00b42d10003084e901c001040c00700e041420418 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 875097500 1250 875096250 875096263
    0x3070302030105271801110d020423130f180506070225050907121e05090a0209011703091c03030b190603020f1b1605120307020f060f04090e 62
    0x1103d00c2c10703000700c1448400c180300c16400031702410710b4503002065406850825001100d00043c401d14107626241d0310704407040250012302c151000e02e00880081542c1440000c00e100c80c101000e0302640d041703942000034201400780016044d0a803540e0320141580b042140d110b800307241c2e10a00c041e00103814281c5001b882c003d00405628014100607641000030055004800b0880b002a145482c0b240e451600c240c8009117000c449a1441d41001d400408202d503410741543c0075100b0100c20480c649031030740001d0340c0c0d40200e01e00940100a400050040f005032109200801040404403490901c00d83c0c040b81d0f0148414070f07a4003031600c000b108001055010301428590590645407154805030503c41c18040c540c06205903003c0c1640040d5018ae4004200b085905044603480000e81c80c6107a0409075540709284602c80b24010304142002c180c0740741c000c0c03803040303140110300085040903466001c0000e040400c09032035601a204121000103002d043c400352008212201000607030350b5205000508160 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 875098750 1250 875097500 875097529
    0xf02090406060f08030f1b011d0a0c090c0e220f05090105060607080d020904140c120601030b010c08030c04270c02190609030c0c14040608010603022d0603070302030105 74
    0x1c2041c8500410b100b81b200a840c0c2d50002c1c4041c030401010f00701c01d15401414450700c4206ca085040315002021440051400c3d683d61051401c0710b51265100e040d4011102c4d8032144600140ca5807400d00c1e031038074001048070410502a01d18800b048581c003083d02c2100c00030340e022000c3c00c0c3c9070400c225402c40d081c07140d164810000e035210b5142242982e0f8034403c0380b05401054014542c089428001c585580c2d108044212410744c82d903d5504241032500083d4002c50040030520f042e00000813240e5120340105558000103844410141145e6580c2c0f00050f00002e0040c1411329050000052003007001000c0c2d08290303601080e152100000d00764400580785580d44540c1590b0240589980c004102144214802c0c2c10180000740d8208500e0304450004042001030b02d801c60000c0b010038240c2e0501e6100c80820f0003150200f084650f2181c1d25401c1e01c0342c0b880081d5004200c4104214480452080940201c1e08100c120342c100e0203401c00202d4640043c0c44110000742e000c4010700441c01d107204010000c0e0b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 875100000 1250 875098750 875098753
    0xf06060309030e1c03141905072303030601140c0328260403020c0d0b0723040e06062218022802032106100906020c06070f02090406060f08 61
    0x5138115a8075240c698000c1100904020054a00b906e04003411800d6504070600118071141e00600500002e1503900040005c1d210303c04003e400482c0810600c00d0306080500580295017181e95000041d1040c2420341600d035050f2408001c09440c1010500041c43c0c03030404250429562009000c81e8201489215803100038031020043c0040e803011510441d44907422440707107110451341c8615080307080c000c2098806811600040c000c0c404c2002d0342d00402c0c8149225610000c00c0100ca04102c114241d018850003841c0e00c040005014a41080340229407020020744040d141080180a80201c21000e80480284482e4403500340482c0302c80380010f0b103018200540c03d5003440080885034200f1f2940741c00c80320703240501c01c0e84d250081d8004e01c155007400c124400c25594003590255281c5402c8400c0350310f64030501404148108140c0031704607803000e94400e035001303120003180740040c0072032548002c801307440720055601c082006960b0100c80c24411841140046211848d0400d4680c4a001079042071105 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 875101250 1250 875100000 875100019
    0xf0b0106020609070302060f040e1003022d090405011e0e010f090809010e03280606061e0f020a020405042604050303071704030c0308070512180f03010f06060309030e 73
    0x1580c3d0006100d400c0e65011108540d6415460800303410610556104003042c04c1e28104100c0d0f48410115204110780c001d0324181038034004c5402002c148942c0c0d800541c1041c00f81080e034070441c00c02070380181d80507101e03200000e407140422410191068840034841141c0b81c44070414049180e080c0103040c83d18003821414450519207684415140c040c4a203001e04000704075007001c03007070b550401c880d0705080020007035582ca40b02c00110504102e250710605607825407c0c014002011482610840d03150380c6500b54031014003a251504031100402d0000203011441950300c2c50015035a82d110702030007640300b2205040d41000b41c5038580290750308850011900034041c00304004a4801000301c40890b0b0b44681c2881110f0041e46050005000d2500064101d030480040401005a540c0003404218018001c4801c40c545a10101c0e840707102d03202c1044050010740324089800e0910310340c10544454010004905c810b2407200100c00c641c83c903840400001d480c1c1840c00c09050300007800805e60a82039a40520 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 875102500 1250 875101250 875101261
    0x90d052a030d0e070506030a0e0c060d0902040b090103020105090d1a070c0303380418050f15010f140103090b101701050c0a05030c0f031006270302040b0a120f0b01060206 75
    0xd50200803c20f81c8e15546603c9100044202400150001d4100910301a02d80054080000003004200c070128061441c18680381a41c0c81c100301c690381220750507550380385001d0b0f03804240148040940001c858400501c40c0c0c080030f51115001e818842d00311a5240d496809050030010180c0300c03121460280c918611074801842284080604036090080a075080350402150200300103120f000002c9100105400c59401040801f141e861000f032481821100c480030071140b518050305081c4502c03425200092400c00000031185042852100d05050010381003c55032105181c81404803989406040c0400c000c1c80600e000c1d107508080003501e400200a9454031002c0c405052152b01900b80900c04040300180c2010356030411110300d06462032009460303040801100381044501c0c0246000f1070196200d1840f0340d01d0b4009020b088172981c0041c1c2d500540b0351340030710009000c00c0039604d40120500c180806d0002d841c1b946d10501605c02c8482e6450f061440c103150385d0851060b007010341150800001d202 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 875103750 1250 875102500 875102509
    0x10309081c152405130b03100e010602370f0f0203011116140a02030703030801150309030519140403030c02030d08010503060c0a030207140303090c01020303090d052a030d0e0705 78
    0x100d815000c0d04041e171740c44150030b40401c100312040c0e00020031401c00004015901001c100014201c5581c19803541c03e50340c81d0102607031120031590418034254010160030700078080c40091500c1c134008121020310246000e80b200001c44d0700c0e405059031f0a0b10100e40356400c500b8244540110080d072550264203151a10030409860f80b08401c000d411904200c20305844500b05015001c3e03080c0d80102100d0b401c1e40e03a482e025144520034072074100d1003076040c410100c01d18001c2c0100c0165580c03580d0b03071a01d008030308090b1400d08480d08241030100700800d02400e101c160280c0042c009140640c03200c802c282030500c10589410b0703160300c030441000070707030001001183c5000903603c0c2c22000540b080c0d0381341c0070428400c40c001c0c001c04d9405016510141120400c556010001394054116034066807516214903005990b030340f09c10f1b0f440388119441007402c2d40c003551003100070300142c00d40c40d090a00c1d400c03200c0b8564220000064298034a40c2c10005490108604910460030799003401c002403e041d42c940b40009 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 875105000 1250 875103750 875103809
    0x11415010516060609020712020c030a0201050a110c0a1404050c130e0702030708130305190305030c0c011e1d0a03120b1801080d030e011109010309081c15 68
    0x1600300b460b4182c216010002d181c1c02420250851405c11900ca0342c4a0401500a1111a400e00d015002d002c1c1b42503000d00f004940c0d1040c10386c042c0c507090b10f44400d0f18001c83d82009500826441401091181080ca95412129400400c608407440d840070840f8403c12003225000307400d803d484a020080d002c1e00c008014003840484901d42e014494030758910500744c1c00e62041e904000c050b2040050790301c10101c52104c0707010990b8061012200c50584500410419002d180c1e801b40c0411001d100040ca0101030380000d001c458240c0c0000300f100c0c0b0080c82010000801800a01000703911448070218803404180c21320800c0401034000c040c0140f0030346010701024038011000c03150940761000c3e10b4030b60b100c402c28911000000c03149001d40b5070b5074119041c2c941c0203c0e0218400a4241290441d03543c0c814046c0b10400c07070580b86014906200c900c0150001d000030303001115403840601c003c485109465915592030140d099000c11130101c0d0140640c80311459403c21200342c045110b2030b045401500d8441d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 875106250 1250 875105000 875105017
    0x605040810150911030a0c050a0e040c09030f05010f0b1f1202190305041202070302301e011107050a0f060b040204140a050306070c1209050a06020114150105 69
    0x2c00c902c42e800c00032414002038001c418410f08184ea26014100c660303004504c038070010602003040b0507103a00b04980c1c520400115000051024014140c10f01e4a94060b4202003111300702440007030f07075030380d81ea2802c009140d80a80f01c50750360300885c08040c50f9034040c6401080c5c6c112005441090b054840380b4441c4a0310080c4001c01c124080404001c05071581210ae04101c26a211014002000130090107070004540c201c4005a2208900c0e0203607000084481c02d0b254001d00e696405041d0f105000019840104c65546c03d51180c4078000007200c06010b51001c454070310900d0b031940001c1d50b03034880c250345403c088180303000c108216040104d180800c4021a07641e200d550301446070241e0400b40040e02d00e035410103500c50b01c0001c00080041190700c0c0081404c000303440c08000d20b59a203040640714401103903100c01140a140c0802c0010f5100b118110070b005a80c101016416296008603040084982000c40940c0d5140010501c000d1340c01e41c07140c0d000e4107086180400e805100c000900f41e001e851103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 875107500 1250 875106250 875106283
    0x81c02030a1103040f090c120608150a02160c0f121106090102070314010f050a0902091906081e250b0d0608150402180114130e0d05030a0606050408 65
    0x2d0165121030034401c442c000c100c3c042d44080360302c2d1078200d0340c00141601020f0201090001c0310150504e0180e005400c210766a0310301400302c52901f00c610b01c078a442c00400428040307500308028040b9820858104c840b05010340c0006c00307507606001401071184416009440340d0050541000300061224002402c101d0055a5081d2180c1c0903400503440c001194000030240f02200081d0001c1200550108000c5c0211400900242d22101c1d00782d022290380d580065000480e004c0003c1c1540f0b940c1c400c1403145401030400080f1134bd92080741c00d01304010f00c0503405937002c4180401100070310400091040c40c132440480354008085502c101d00d08401c3c1d104049401c28040340c81290b041c80c2ea030010740182041d1040c0c841007001e400b0031092020088a0072442803c144404010b07500d080c00c503a90503600c0041d900050714002000300b000518201644849131034485261000025013400380511881958a80c1901c03803e1002105042d12210f8004108201091104114000b800103030140e600b4000076 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 875108750 1250 875107500 875107517
    0x50912030c06181b0117010e09070605070803060f01050408060703020702130506031509030408071205010608070303020604020d060216030c0b1e06131503120e0108450106081c02030a 80
    0x400507a0045d4a01180742c070a2a452400080d08d000802075051184014406640065171150401d4409004981d0080d0100506100213115410714145400d5140341c1410b103181881c0e6641076a82c50403200b140e041001a80210346501182015299001c0780f03495000c040c0f115281120105e40d5503000d240e1618000b640d09000714102c54000c0c8100e4003d007640e502a2040749840301001404c00300c5003007080782d0943c40c140000801b04001310750b4105890741540900f103144c40360307003c001100e10b510b4070650b00f4503800c0000c25008a111008050284d1094541e00c0d107004150800c228110801006011010000c0300c1c4041c0085042c05504c0d0310100442c2c1c80d006c400440b014a2006058030706032040b032459440000300c00d1040c001511003903d890740d0354109080742010011955088280c80d11945552060200d80c1c00c5032115100000c41c80700f540e1100c040d0503074101545051031003c0c2211829940da0341d824000030009100b1002c98a40384184180701065032076009540e8440c0702c100c28108040304 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 875110000 1250 875108750 875108803
    0x50a090f060b06090315091204080d0c030509040614090117030d090f17030a1109010905040209030f030301180501170319030b060703081905060a090903050912030c0618 74
    0x9031388003d0809401c50704010b1254183c01c071a008151420160741c0300704510945a81d02c901c00315000d03105184040c054103010124180e50f0043d02c003804170180002481a400c542e00c3d00d00c6401d00400316855440710b10345510060008107041a001901840c00000b44600c101c2030000c00c0303552005134a0000104141c482c1803030000d0b21350039000140000c0b180030312114a0703085000550b001d19212030040014001500740c0c0c003a54070480700036a001c60003080041019141540c0608a50030025054a8440707600c0d500003030950b0320903045405585100c0c005a910454a0b12032580903292050b0000304211340307500d00340d5690140b0f0041c0c407074641424044038a1a40300390449150202c1c00b820303040e19021a031a010341110400c590410504510001006504126014060107540058a400d41150a03c884507001e803040103401e409201d810040b81d00240c46145c4c014004031880405113880d03400d0386802d039041c0340d0040c0000306160101a003084460703501180c9410041104a0448044100d4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 875111250 1250 875110000 875110009
    0x606010c020d020a0e0610090f0b030a090c080106090c110601090e15040819080412030c090509090709060f0b03010905040f0506090d090b130e07110703050a0501050a090f060b 77
    0x101c0000139000007140070b00040c40d0b010740d100140105400c03288050519a0200304403203c8640d07116175600710005800810251740c10030000c1d6040505103101060328003294440041082190380040082c2c0e6450104010340d80240c85480c000e102c2e5498007000c009603200b0510780e0743e901030080000040d80d40007000208501041070003000b60201c0241ca629160038100603101d074000724141800c101d0178000003114a440383c40d102e8131441d8083c9940c2070980d0800000c5005000d404520030a06c01e0309000402e040d0f40c0d003850f03c1c0c410385858000f40601410048160705480740707607008900301d500901040c0078250081c01a68151180340600090994841c1003034151044c2601002d08140921001d11900300808a04071861111984031103030180d684942e150032a105544040203580180b600502440304102c0f8041d13000b600d146403150751301c189002881d0400c2c40641c000c48031503100403d030b01d0170840e080c040c00f940001c03004130400c100001500c0740b072018400948010020b5035200c003510304a568 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 875112500 1250 875111250 875111269
    0xb03070314010204030b16170a150f0512032814030c120c0405010509190e1617011404050403140409090b1b070308040c05040c0806120a050606010c02 66
    0x1001010768070030a052020030382c002c0d81305000c2a03d8000059000407803078a005002e48510068641e0f0740c150345515451f0303903c0304d24009002000d0395902c90084101c01c81ca05003c00c00035103940e1221610141ca040b040041c0003443c20702402c0550028403a4103d0100e0b855140b05026400310044a21140044412220309501101807503c0031b2011040c45040700700320014090542d0700381009600e9807107507800001d050040c1d01c1000c4c0001c0080007a404241000403007a02290b01c250080705299455400190900d82e0464195131944800445000e00e598030181c0344031740d07146040c41d600d17031941070184156017000110350880c06291200c01007000c0612070417407455000340c1003042d541c9440c0c42d8814034028200110090303850345105800f145003000030700c510000101d09a941c0030b25005496600359145000100305451090380048006495160f9025948000500d030b9540c004918101c800c0001040c401035400450354482c040400020324005600c41e0403440c02d090004080580d0700c0001d0000c031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 875113750 1250 875112500 875112503
    0x130512011a01050d2304020f09010302090114150c03070201091a040504240b0a02010c0e090f0c040b0c031b060f0406020c210309010b01210f021b0a052e0b030703 71
    0x94112443c20300101e1012a030003181f0840741105220300000412480d11401c0c00041c1d800483e00c0010081b40c0640b02d40c4808103200540391214003104080c04105903001002244016040000c9c80350031580d001e030401000c1c0040d481040e070317003c0e50500c201110b4081e0b4010700e8042d503940c40d2801800013015070a900200c0d84000c0031407003141c80302c0ea0b100705e6400080c028805076003480c1001030228003460051802400103402e2144c1d5903036043c2e058068000203003040c8400700c0d00300008038550303110f44002c10442400360020b65488c42680d004182d00040c01c544000150410b0050200003405880b0850700281c2012000d611205000d240d40e0806400d03200c80c1501c401ca034504440b2034840c2c1c3c800b440c4a90f006500810030101c044e030040d00d40a8610b9101440840b8a91181c501c03043d83c0ea00c00940201030550040c10503a8110062004c401e00803a800300b03c1d40080005130070450100401a20648294640d85503070103000381c14070301d0540d221503080601762610104a100d4a003003140c41c0085 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 875115000 1250 875113750 875113781
    0x50d090203010c020f010f0c27050a061d0a14010c050c13060f090c051219020f0325050d09050f0a03081501050a2c06130512011a01050d 60
    0x8505000a5a05c880d403481d0219103500303105400100c80307024800c100c1e0150051b10f84041081c803024222031016191001c840c116011003801003019191000000c0c060101d07500c03040340304d40b00040300e200100c1c4110001c030310480c0c20070414400c0324040104104058420b0030f241030a00940e280107414008503080c41a08980380c6000f40c0c00c544000d411100072510005505242d841d100c0e041501901ea000940d0004a2403c0103120714000c3c60541e0b00ea40081c4003101814404038140c030394000d0340e01549000c0d5070a1000300601c03441059401201489100401e621201004980c2000d4040d002e0b1a4403444031942e1194040c0501c54244030b4621003481c41010f6550b190402c0c40e001d0000784060390300f000311241404280e60694026000c030358000789103490301c00c0c000d2140380044008c5400140030001c0d0202d01100000d4a80394000608003c0080840700980181000244854124400d4002c0d600d41c0c10241900e0010b100a580c0c2c0c1c007000e0007071038003d60b1000304040c07450140c0b24006c54200368 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 875116250 1250 875115000 875115011
    0xa09120302090415030203030405010c11090109020912161502010615080106080c0906030c09032e0b0a051003050903120a1a010c0b072a0c090605031c050d09020301 72
    0x159150740109101d03401224104004824070a603041d0070140c5000c0203401d0f510401003888107600a0030b4503501d091080d151000310026207000704104940a904c00b024854010488a40d540382001d244102e49103013800400098040200a15619940f441044003007440c1c8440030310b04500c01c0d041341e00030344400d000d050b4217165030a074010030850b02445040d002800300400700c2d45a038540006c0300c04000000b450207045446140e012035107644501c0c0203075850722401c05008e07800c2c815026019010059441840200310034641c3d20815034918100c024403680f145801404540c0d1140314441c001d960318030b0000b84942d00c22038928514450b80340d541030110a03d80c03c105020119030080c59601d110940b2000c0410a580300655580c040c8010042a44213840c00081049104020701016400401451100f081c109840100050202d5034280ca620729054000e008410344c030300448005000c260024404030b501004081c0401404039611010002d0010701403c03100c8060f0841741600390000c0c004c101 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 875117500 1250 875116250 875116283
    0x170406020a05120114031504202e02010c020118150605060313020a12050d1d0a080f0f030a0f051606060e0a0b0405011a070602070b01300f06050a09 65
    0x100020062800c61091240d4a10103183c014a1f40c12030780103603448100e0341c043d0328000709881301560005442e10b8121506012103889070322103515440384d490201106050000e144040207013981e1446041e601968106005145503d02c00d109103110140c002e030321000085502c600007005024198040e551000c40803003840011400b1072034001c5503603c219a0300e16150f9607102215a00306004a0103007840d041290300780350580c01030555560300608091041c0100101800041d03c13441190001d00d00d9901240c1e00c100c100c082080740c2c03152820a4001181012441c04009107540c030705542c148108076000c6181100c1e410380d106066102503002c6014802e82e5100c15907560302d08012198908010b0501144442a0420307104190507201d031040410300300010042044025480050100c51140d800c00c0000045211640110b018001ca80c24000ca4280116240345030b040303910540d0340c1c540d020224058001004144142c011692100c4081000d81d1000d07014002080300e8080034020341480c450741d19 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 875118750 1250 875117500 875117519
    0x4020d1b11010515180a0b030f0703030908060108060115020f011e05070305010b1b0a0609030905030f010c170601051e2122020a08012406170406020a051201 69
    0x241d158070070000300155620810060520364142c600c56401400c0381c205080801081c4017120381c00505800040ba087e51880301181c984218042182080d0b080740c40e0600030168011120310003052218020140340d410b040d050380d00d62006100d01d0442e000782d0412144018001e0081d29940c45492000304080f41821400324500a440041340e145a4a040700007244240a8481c0c181642d4180444500f4481c070640201d83e5000c80318501201071241c500d81c1400980c5c580603010b2614070a83d90120924038050906290000382c1044a449904155030104080e5000c1e0800412202019403500d081d00d4903001078070a0b11031039600d01c290310300351000080c001207a80003c1080505504807000210785890680e140a001501c015007200000300307401c2c0303462200d59004903045000820203800c7c155580a40e070700311204e2543c1b2081d40b1a0404800c1005224062050005d00d80d50402c0d603900016011001007407000200000c0410368041086101c0e02c3c131030b2007507841c6006031507004200d0b541c60b2142d01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 875120000 1250 875118750 875118767
    0xe0403030e030309150702010b09160306050d0b060405040314130e010f0806040f240b0906060a02251a07062711040b04020a08040303140105010e04020d1b 68
    0x580100742403018511003044008101d900c00c1074448090021000c6410f94403002c0b0902134480000c56403100c42480179a0340f001c540f540910f0b407c02540d0301e800d0780c480020742560041d50141e0300c110440ca5249022030940311141d68804400ca6001540b5521442d060303a40440341035001901d5003004c503600b542c184140b100d000940e00306e038a4880c030588c2d0340c6900c0742c913041c101e025940c825008030022800088054103510000ca1150742ca090142400c131012081900c150341861011603210002c040c2541012540550010800c3d5031091034013145640195682d500103031441c0e11011303030201410460160f0024100500980701580d40034800d0340268860030f0b040b0800c1030310498a0b20140d0446c05180c04074640d50324850110882c4214440e0b1a0100d1a20720040800e40081e180c0b98002c4140e582d40c402007544114944800501c0d041c14100181204c64040d580d071020501e02c0c0040c0f100d42e81005542020441c21100940c0d100620605440908800d600c4a1407030140e520b0303800079441d0400c010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 875121250 1250 875120000 875120003
    0x90b0c010203060a05091303140702040e0d081e0412030b03190c0801090b06060a09030609081c2007050708120406020f060c090d3f0806100e190e04 65
    0x302c099984032020090303415030544049403503100c87d481540c0000c1c000d01c80d51380608601603c00e4207051f100d401140950350211b4180025402801c0480e0340a5003040703600d0342000b100c00c440f1504e4540b201e501c656242000d00060520a4000b8030224880c2c403d4110183d00000581a41c811414011440c0170414400d00d0450f455803000602060005c0c05104861440d42c000300181da16441e03841c1400b0843d0f000026a00030008502d00100200e02c0b103005400803030344103001d813503030b103008084085094021410b8608000350420b05100e02000400c8074074040c0651070b0725580e5852207030b440c04518201c102d50103840705015051749600300d804500050011507d1940986428100d12182a0f880f4401160740443c1c0113000e000b001c1c1c15040860101c0075846c420034a80d400300e80c0d54000f040075141c910b120b00c0d1041c0c8d0f1842d074002c10440e440070464480e000710b003001041414404005072115080c0c1e5011420018070241e21003040e03660301c140c0180c4409030405030114a4580c00c50380c158000c00c0344c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 875122500 1250 875121250 875121259
    0x40213080f0d05030f040308061f12180201080705220803090111191112011a19080714030c060307030509071410032a020f0616050415090b0c01020306 66
    0x1107400843c02007080fa4810788040800540664907640c05444501000e002d894004142d0410980740d5040108036200d00802a103601d2602c00f51528aa420b4401c0c1c0b455030540e540d16154181c0050360461101d0b0b40240030fa050158443c1140c645010b0500344480304a070400c40b6400c000505500040700034071010400f0f91703900038581104180b40d0742d41d00c1412081e603c1110b1210640c80031030b0160801c0064114014442000d10500060301425185510340300101a2403440e080b0f00c1518125014411034407145e030110790b07a02e2401030600c1c0c81d82507901c1600c0d10b00000407001420303a81c0030700c021402a10010103264503401c0101004000300801c41e03a0011a2203481c1d004103950100c6406000918070042200302820941001207011b803808642034000f0b0105500c0041c5240411500d00c04c80603016070060410404080e02c141c5080b8029001043c0200d44c41d86074200c0c954054100c5055615180c2011100f620340c00e401c4035951800e5001011248010441142124041d001540598401c98 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 875123750 1250 875122500 875122513
    0x9180a060b070b0a020a02121b2109040504080405040c0f260114010309050111120c09030a140c130504060e062503090209270304030507030b06040213080f 68
    0x14003054850904080d20403102070000500309589a0000c5c901b82c3d50300e2050758902454151001041c0c0c004842d1980240726500c6940c80f0140300708041ca100003420300000e004138030042c0030b03445503119200307030940030f01d07240c100180030b0000e000200c40c0244000344c002c1120480022004000b04056a1020b00003210007005070700c21505152843e8207441e2008604078140d1801c9a82c036540412840c10b00c0c141500c8550703010100e5000c0c496503400040300c805441c1e540034009011039002c0c02c000d014503001c090034411500340e51400105190110340c171103460344810f440700c170f501c502d0404470500d407990044200c503100308030480b0350b040140210322071982132182a00340c211850f151002180c54903003482100901c280c048803004103c21a0200d84d050016100d42d00e82c0200c0e18100303003101c203825002c02c455801207180c0d50340c05201002c0310482026500345400c65031502d40f90102484060848040f54001c20215030f2503a04460b402400e100802d032496698100954940c0540d0254903680e002c1d00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 875125000 1250 875123750 875123759
    0x537020606010801080a05060a0506040b030115140d110d02060c060a0c09080a032a06060b121b1606020c01020307020c0f03030403020603010e0717040804031b030b0703050a0209180a06 81
    0x10b074075021b00d9032040c05406680d8440964000521000703080350785c00341e00d41d642d44001d84c80a208050f49201803480680249042c10709030004000c1c8800aa40210010326032030380403858141d60448100c00449000c50280010f000041c120701031803021340c01c580107000a011020200340c0c04600c0594444c0c039542c09090f41c1ea0f4025403204c60200000d004a60140212003907800a00803040c0760140201c0048070200031038aa480880f12207801c0014100e40014038030301c6042d01200003541c000084210829540320f480115682ca001d03914580c001150780c03003040c41c10001c568050301e4805004400071910f030f190004000b0b42c1c03242e41880590150121541d0310700d00c0e08020007158240c2c2c0c1c01038940f502d1a480c1ca4000b01c2010070080c10502007020b01d1001805e0042c138030030540d01542c050020740351102e085040000d4100000600da080c504c6010408000060030005529445056801e0024041da01c80c19044003921a20120542c40901e0f8451242a60000f4034000d014002440c810002d007500c1c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 875126250 1250 875125000 875125003
    0xc0c060807050a030f0f02040e0f0c040302010909020f0d0e10060f0f060c060b06040b12010506030103480e060405010621020904050406020301050906040b01053702060601080108 78
    0x240c9201d000110100180c080480c0a5040085011500a0002494000c00504208a800a81003421004c01420901548804034480b01317170400e90f100e0b00c162800f861135001070700c00c0301c203485080d00140d00800d032440105054020b031808480311071000e01c40310340c103a000745032210347c40340000300349a11308180400d04144022106050340d201d011415107660034103405031102003104a08403100d903210040c100c03032a2a1a005440100103841c2281c1d101c06000800e47e60308181600090300a207010b1004002003207600303206030700c008100d0602404040d00300f5080d44064041c0c01552070680b618084070f80300030180d001c40e003082f141c6100c17a02005459030010031056903021f200d1000090154200b40303100c48000740380c4480944070b05100614110020002c1b8050b03603070454003a625564044010402c030b00b801c10205a100300704440400800c01154000f8065001d8084601c01f18400d2046202c8204401c03000d5100c00201b103920403503580c41842c0025512142119180d00180306403000003403d200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 875127500 1250 875126250 875126267
    0x501110c01080c09190807180527010b03120d0605090c0403171207020c040506010c1a09100e010903140c07031e12080702070b0f030f07020109120c0c06 67
    0x5940b00306080c1ca5442d080f100300d82049681d50303032109910060094098050241400030003603d00a040c2061801e10440c404c1c8204041004599040600b0041003580071209521070030f40c0c119800000e250000070b1071740140751803a040d0b505480b03040d4462207415070050150401010503102485074540310814401c0c40001078400031a140410710042c070000350031144525040144079141420801040d9001c82c810300103803011000760b04100c201000d241001d008903a4002020300b00b03181404403c0d43d030030621082402a8480ca210040041101a80c06010612200e500c50009200921240d00c07c076000b01364415003240400c17003000c000089480c21805a03101070481c100034083c075520710781344d4070091801e841041c0a1055824103c3d03000032003200300d4080307551070b6a403044008d242890f0080d1904603607401c100010700061140f880b840b55240112a4480c3d41600001840e03200e001d401d03409000c01501c01481070710071694104540790700003403020086001d25090002d460750703580140d0304d910 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 875128750 1250 875127500 875127523
    0x8010b01140f0c07031b060e010507030c0302100c050c060609010803120a09021201022205031e1615030b01141204031e0e0103060b0f0406140f030f01050111 69
    0x1819411400401c1c08078401400c0b44060242c215442c181e0309601184c2026007a810445003120028045101440040d6011018104c0c5060031312403103d8420010707003240a2140d00900300441140900300f094401d0109482003105503005118841501e9070181c081d80050003214071038440c91b400281580b0300440720318103c1c0c02c0c0c071002c0d618100042c020540d0b5000c00804800000d51581d5460700161210450070425410704000107840f0b1a1400c6802d820800a003001805c44a124000780b01a0ba404510070a00301785200c445001d41e45484811800c2103030401d50b000c0d1405402e000001c880c140784103407100d0002a50303000c10401c2c140800545031020400c0c02d8298528052003402c2415040203a01c0f40c101e8000e05004080800100301c1d0084103220300c80300310019900740300606d07465816001c0c410181500d1140e071400c3c440c0e84a441041409548500070402500120031074802403010212420307107001c01481a924601103401e45000d034028030036140002c009404503080198041040c1c01681e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 875130000 1250 875128750 875128757
    0x1e0a0f2714010b180d0602030601030c0906020c0424150207060503011206110d1b0e0901350f1b09100302040c0e030613141606140d02121008010b01 65
    0x20b0342001d801c442a5009a00d40350502511040e4003d4180c2c0c2e248a05034903140702e260090394038601503000505841c07881000006200100d401403080300e4000c41d4105403804181c4002400304200b142d084500c0d20011603080c558128514086242e00c4d034601303004140d0959400f2220403d03a184400c4a040c0b20900c203003940c1c481c1410350140041c010350032203c1c0d298a0350100e00e00700140b1460b64011210040c11708488800e004103020141c0d40c1000e8403408240d800c44040c0c44962614154800440c40c68090322010501600f44000304000d28602d2403050043d4022260900d480d14240c59480150120310404400001c0c0700118524104a02c54401d05400344013a541030f2540e03090102031300000601d14188240100e51402070b40b0200f091900c1060101c0072080811054180400340403207a440051041d0040b03200213030440318450904c012a0454508081c03809010f01400d011800740318158040b2600000c0c1420480c1d01132403065019101000e00c82c1035441e5a00000c1d401c803641880400e020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 875131250 1250 875130000 875130041
    0xc120c0e100b2110030c080f0c060a09081507030f060605090d060209060c1006050303090901150c060207110316081203060a0e10030512091e0a0f27 65
    0x848001c44054500310380380c0b068140d9504004820850420021245a082c04c2c108000800500000c0100280140408009040d0000394004101e0f1204846004c180c0281d20001e04c02403400c2c814810301000302404420740d600c030022820b003c11a41c5c42a00c41400107400c2000e09212103a50f03210b414111611034807518500000401805004038903002c1c1560220350a00a48003140c481c14002e14203407000308054201c0b4105582c1039021180280c00c09402039105008500c8262940000c043c150303070003044a0f101d505c80c44001129035001000e4011b000a0011075001d04104400042c910505011070030780704410300508a240c01e1000d50f10582e25281d020f50b010005035581d020047d60007007006042c0242d6107854416541c4121003d8854400f03800c8030780010000c1c01000c1c01604116008030050740e190032500c0002a100c07103034413030321000c0d0001c0c082c60b01b21742c07940c640001200500c0042810794406030340d1001280000041030f034040f41010301303940d0099034040741c3c41030700304c0a040355002440 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 875132500 1250 875131250 875131259
    0xc010315030f260c060c0f03040b0a020c0a0305040302090601020a0203100e0f01020f1312020a0605210103050c0a08070b1803070308031603060e07121104030c120c0e10 74
    0x2419404200b05580000801c107141441c10850380c1800c0f80004035808030380c0e0328402410003518102d001014100d00c140148008040d21013204100c0f074120760400c001010710388034240e0001c002d01c07507000703000620300c1010781a81c00c158000020b0300880c0d000301c9481c0c09542c1d40d0310041e03840740000304000303601d9040071000f0fa20440c00d552180800c0060982100c010310f4103103051030308a80c0080080c2e541e4000100d403d40d65005400c100074090102031009541806084e4041200b40189015034ac040c4800855040003410075001c40740001030215200c2e0030f80c2d50390303402c000361640304204203a806542c00750408601010002484d404507858040c005103440c0d20140c0300354170502891000b40d0b041c0101c0000002140c1c40d080914050b081c955401c1d042c8001c0f13a140a401c0314182d50022500e103900c40c08210255801c03e01140e0400281c040219240881148081e1984220b030001014201040307004114041c0d207a620100d000c0c4140e203c6421181c0307840c2c0561003984121400d0f02c01401c0f100c004e10 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 875133750 1250 875132500 875132513
    0x1a090403031805032a0d050a050a05090607240908091207080312010603050105010f0f0c08090301020a030e12120711121b10110a0327080c0c01031503 66
    0x240d0b000e05040310605242140d541c2c01c0c00d40d44008521402500140c4c01125040810400d10048030524001803880c0f40c003102025007103003e00c00c072034810311601251546030315005c1c00482e401080018046a1b90704068a810090180000358890015003510201e0195042c00d01c240c000c480e400000980c10b241104c001c0010203502981116241e001c4c80b003002400e040200040c000c1c06081a141400541c1007150080032a03405038041ea0410100080c1d5100950b040366404491450742c0c0f416203c9200d071414814501d1040403140da8040d8800505108025450b5009030413940200080d1111a44000714010300d50282100b059030361907060022841480c018020000303134070300c4407054032220102078043c1102c0e6042034000514404521000105140c002d1040d001c0116048808100803812407081600300d003c0c1c0c801e200b081c5950f6815940071003044070460202c607800c030208001e0644043c5451407080c1c200140000003072003010a858820b40c040e020b542c0140c107461400380070036460b544948 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 875135000 1250 875133750 875133761
    0x30a12020906070812010320010503010603200415200d0c0302160f1d0903030a02070303060302030d020102071e050a0303090201200624030307230115091a09040303 72
    0x80b0b900078000c000d050005640f81003d00140032003522034038819031641c10801d400da41c1800880300010007505203900e80c1d07a000b905486c10b56100f0302d000100950700c1000c1024003c02c6001140c0c69072808903000581c1040d4030883c00102009944958030700700c041c120303100ba6043e0300300c1d03085d0b41d5040080001e420612482040088034000c0c0704455174040c0b800300c1c081c0c030b054464204440056207403e06010a840000e074100f8400501c04021301c061410b101d445442c0d000c0500300341c1450340c0000300300007494800d0b0041c002464000b02541c0085001d584080e00035031044e40300712000d401d04030b1031425120384a0030301e0b071901c0e80040c00f6010034103140d030f0f0490060642210480c14450514440d0840c5102c60300c5100e0403503020002008541058100c5c0f84440802d2004600186140640582d07261808400d41c1c200341d510952900d008003d030006610b843c050001b200d045586041075903000d0703840e200181c0b030880b8496101001078903c046200d4807000410380300b40d90407420190104002174801c3e80b00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 875136250 1250 875135000 875135017
    0x3002010501032a092a0503040218060f061206090c04080c10091509060e041503020d21030f0b09090a0b04020a2312060405060705070312050423030a1202 67
    0x1d4444070f074a400e0207004070f40546844ca084403005071442d0059440445d51140c4a00150909906601d099400030302446c1c09201284c00e51014580401e4440c2c13595001100e60500040c240b64036a003010480d200d100742e049601c103215000000215107151b000b8412038080d60036a401070142a200c0901f400820b9240d1042e01c010017106ca40000b0344a2000d40010100c14290354a03600c0151038604000c0c1240c03043c03842184214500742e07248000e00121b08030030081303d9059400c011041c69a092400865102c01c1d01000701c41c2c002c904038912294075502c22090b1500d80c69040100000078824000003200407035048440e540500d0038100070400d0103120700d034401c0c4010300303400f0034681b0b0714554040e5101c00803d07101000d8100c29810000e10304800303d80c0304250721764000d010358503040c0c0340d0660703c94014000c07105221002441c0f105040c030404c0e078002000b2803030200f400340d82090328109400781d8001510358180d81c0c203507135503203488030010007282c4808005603034040c1c4c0d4211a0840a00030b5115881 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 875137500 1250 875136250 875136323
    0x3110d11030421080c0a05060a021614010b0d050706120c080a0207111c0215070203030912010b030a0c03062a03020d020702030a1a0a061a0307020a300201050103 71
    0x142400070380d1080040a60740b41704009445041601d1825034034001010f0080603115006009001c84c811011007800f01c0704c3c1d004003074102d420801e5103419004010052000e80c2180070300164409001b00000e641c01258601da550321860004120903500f219400ca4000000804010108400c500c00303802801085014a02d540320764404080002c5180c08281121b40004a5903e201415450800306d18090b110503908141e2130026250300090f02c03031203402c4032140306072203000045107245004d61240c81440c00c040c045070341070b2000781842968140641300440f6501c0c10a403001301c0ba00d1205400411b14902004400c4d050009200c056019410020075461495800d101201c09039801300005041d403805080200c1049241102104040000034070310303d400c41c10078100300b18545010707030700c5445520350032030b070540742c1c0c40310f8008074181040008003034002011204440390f02c40031564000d450280001144010ac1c0f90303004140c0c240c51091001811101050007e15081e400004903003000044041 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 875138750 1250 875137500 875137559
    0x6070f0e030109030809070518040b18060c0405120d0f11010f050c03090d050703020a021302070b041104061403120a02160f140409112b03110d110304 66
    0x101090845040c000f054001445170f1060101d810300911403000500400d0362a0b40e540d195043c403032040302101510003041c6d002902c0016032440070810840d03801d09140e109544150030f121000315183e8000d030040501c80c503031142e54200310071000508801c1030320460b110304d00082c92601064401100511907040a0354841500e4407026155100d0350f4480c200e140302454490504028103840c0110781c40749102803101c104800c002294001548000165045511110090380d00c803580740a409203070750080c6a20030f0703030342480204110030504e84050001944c0800c9a45c0d503847c0e038180d90752a8514480c0e0190004000350358040801d100030f20700c001190040390b28014980800f501c0e802c8050b400004e08590b025002c4c0320528040c524043e134400102c500f4001315000d1384490704440e4034140110700c5600340010525015044007071030802a10b8680203e00d0310ba0381e600b03002d0031100a040700d1610038015006030302c8402c3e006008138000c0020003001103040a044c0031b644605074000c90701c0070601136201c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 875140000 1250 875138750 875138777
    0x903012703120b0301091b1208160f0b04060b01030506040b15030903120f09010c021507050d0f1104080705180619030b0a0e100b1e04150906051003050906070f 70
    0x1d00481b000d00b4400c081d100c98105c400000146190042e0304049280e00105812030302054924081d81c5500000f0381c1c40c190300141c1440d01c1c1c01c01e02030f28400141040c0740c0d81d04020a010141d84044501202a02c007030141e969500100000c031444024a50341c809418507501d003030404500081d5030311120300c40880380b4240405e51003a201ea00100c6000c00003100040c20400120400e000b00c60b12100303030340010419070310440c00c4000d181c2d100914a00801002242e020102d00720b80d08810701c260b018013010840d140c40410701d150707680d0050045a40c90310075640001140d00b0106002020101c45e00c00070601d40d141c810030056211044010788050480d10600400481c544d0501d050007000d840c13400003198042c00907950708100100200c0f0980c5460045da49002da04d0301d08100103146800b00b02c24480c0d50035000001e005154600d02c1e600c102401b8040412400c40961004090340d0088401c42118030b85903c007203094607012900c695590b0084008035004502a011081c200c5502d400c14003400c9114 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 875141250 1250 875140000 875140003
    0x1030e03120414010207110f1906030b01090b03090304030605090f030c0114090c21010213170609070b090609130c080103020f06070c0315020c0307080903012703120b03 74
    0x14964001c55501c00030501c000c00c0000c00c11983c079150810003d40c10400107459541d40e40304001301c5603005a02021001c180f590311110020298003060b40a1300c0a2078689070028001d040c04a54a4041280108081241e00c5180c0942e4414000480150714240c02c590b03410010f00009410002c551040300c503502c00303513030003440038010031002c0000020780081d40d20785409500001074132201540d04201c00711282d82c2c448074a000031054465a010300c51807800c6c1105802846901401c0c1d1550040200100b9004045004021100102012034100f44c5400308a02d1b200c3c0b604c2c0c40f692050a6003040402c10034102007010b04107110300203001c8054a001509164103a80c0403014010000340c403140140210300d0108420483c4440c1a540141400354658600c0056861800041c10381a00180340c02e0002120350112083c911203081600c1c1c0b074107058a40007201e40c1048000034400d5080203010801d03131807000303600c94101c404166600c02c80d49190300d05423489103803401c440e03101c5500d400319141c89460 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 875142500 1250 875141250 875141257
    0x4021306181706130201020f0d020a0c0608060a14010302040e040813060807020c040905010b030718050a090f0605090a022701050d020109060f020c031501291801030e03 74
    0x10161a16a20403056840024030702080e90016151400c051120341e60100c0000707280d5a01203421075820a1007815400140d00e0300d102d02e01201024402c40d1a5845515804645c48050b0342c8104a494000c5440381c40940d404d803404c440881d0843d0441c0380404c0180410509650544030605005280640704c0c4010000440e04035001d6420b0070b030000d4448507907510110140e008205901e0202880c1c03d24802c001d40761440c52038054404c8d6143e034442011b000081d8002e44802c2d02c018200e580c16903840001011110f03012006d45160f9141100188200003540550071046a2080705455140544e80d01c030001003001800e1500349109200c02c01d0016150030329110b0811031401e101040300340d0200c05441d078510058010901601c001100d120060741c12650a00940c0e4060a19035040f00303000e6412441d01180e00d100070391621600d5007403a0f44590b1220b8240c1622a0f959400c0c0c00c0351001c56540310224400c8000e1090440e00700030080c0401c003689c81950164a05240c08208000150909845c641 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 875143750 1250 875142500 875142509
    0x824061e030106050a0e0d0b0109110409060806091c080a09030516061a1c110324011a07020a140310020c0d02060609100e060d050a05010608070b1215040213 69
    0x4c200044800110340c000d03020969215046070007a61401e6555141d100300c02e0184503400d111521442c03103021142c1d0b88002c0d500a0480c1c000c003001215030300c40100e9a2a00c099038410300c1805000200149c11741c407443c29883c1d07064240c84103d03054407039104d000b0003400747c01e40680030014180801091550090100783d600d0f400b43e140072030f80c4207444468001d0a108034561520841d441c400c0c5c0b401c03c29100325003550450300701941c9926240501c000c60b041003c2c00602410b4007000c02c445074111203142c40c00c0749c181d505500c5003003880e40110340c80c40303054451301c00040d6000103904d004215a0312030603480b00d4802406020354000200001100c001c6c0c2e00164203909a581003031000e06849a81040800d80c011811a50030540f07080620700c072448082c40c0e0151010300d82001c0009030340c0381c41d8600e54001705a8071804444024400d414014000c0400340109403260103824400106075190a003034520704058003021302001d4803001c400314641d41e80c0c40c148542143d0240400d96000090403000c00061 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 875145000 1250 875143750 875143757
    0x2060c0d020f12090f040b010c02030307060608010f1a09180a06020c010c030501120f0203070b072907020706030914071701050718090b010e0604060509010824061e030106 75
    0x1468042d81d41414031101c1c110340901c409050103511619681d441c1d469a00000c10343d00013078041007003001200ca030054650040c4d0503210004440080140d558888070440f4030400080041880049030b003000d0725280d00d03c0c000705040032140404a4a018a1556000a41e1103083c82040c010264440d051900d00c6400703481c803da0100f0380b8029107a003070140c000408001e1800b00583e60414285c2400c0341c030b01232005041003040312000d20444d1002c01c0503002034184810081e440310503a240c0952070b00300100d40b021440c598a5854004180901240c2d800303070034190080c0003060b0030300304101c004046c50b600075905966610110302c0d001c9401d100d201c01504418041404510403000e1203400c3d10009040441004111924201003611000180382903440c03108000c1200a003190048038141c1c00341c036a050b03200754000340005446030408018644500d080c0c1300c80f0f0b0685d88007070302c00c03410500c10b007036400c6052400d0754000c06c14070700a030040401d801040120340d80d51000c010300c0045504241c1140011 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 875146250 1250 875145000 875145013
    0x30c040515031c050412030909090c180c050313021507141e151f090e100e0303010b1c020c0714060703270b03130201030501230d02060c0d02 62
    0x75400d00744540b0680d031001801038554a400000010007900ca0ba00c2900166101203071803000305482651900c00501c0460018440d440312800c1a24211800e03101c0c025680701c1d040f10b03016002c180ea020300d10303140c42191104c1d81540c1e601600d00011042981d41240e20100607200b108456007a44054440e46001c0c0e5800d50340e6502087c882807802032004400940400c1c060282c01c01c01700001001c0f1070201c01c0c00035000c01510b800c110002c20054080d01c8080500080d81e011030300b0b468a61000e0041c4000e1b5049079a005801d10f03022003243c048143c00c01e20b5800410041c00400110310041c040c182480e07041c10b08007032807680d070300c000c98000454021454001034400c01103d003100c1d2941044039411100240f900e20560ba02510004022185c1c410004540360680a409951000c1d24001d0480701d40d000d641785024103181071a2050800c00302d000c28030f07010010403082140041d203c4054198100164080c22003001c001202e0f10500e0100d92050040000c082c1c0c0350070500110070300040315001841c5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 875147500 1250 875146250 875146291
    0x10506100e13140103020f0a180209042d050c0a0e1504051c0b0f090c01110f0a030908010e150c0f04180c1d0a0b030a110307020f10110304030509030c0405 68
    0x554140c7d44c51501d101c1e14800206016180720039a10364410382605d030005950361210307804600508001c201c0102040a803c48060320310009481c0b001d10705a100c03c04103e9555a07074407640a50242402c035200181d412080910141400002c4200c0140840c0c51241420354507800230721030035074000076042410070100707011003046002c140a0760040c4800071070911a103403081c8496034034903007107031001c1c10440d18005030300328503505200384001440c81c40301b0b40e0700d54003617420040c00c3c000103481030340c0703071513203011451408640040307280160314101c078810f03007000d407145910031880750410b4040310046501004000341c01e0500d4148840c02091901d408601c103a4000009018584004140c040342c2206d0040841180d03180c0100c1c40036503805041c2c041c0c507500c403800480024461001c41c0c090903100041801481d40d00000c442411580b014202c03031420005034811026982c40c3e00e40603426040500200e40040d01490190400b8000601110300e6451007074000713030a0315403c0e550004020301c801a49803 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 875148750 1250 875147500 875147509
    0x40c0f080705090a18140102130503060103020607140705040c210603121b020a030c0302240307030924050709050d080a0503070504080714040608010506100e1314010302 74
    0x4028410040034282035481c0102058159100421010816644191460005c0303140344552524a820000581e003c5409900c024000d51014180440644000a0004445c6000110b0034140e0754040e0603581000040d68803400e03505420860300000380508a008965502c0354403450307000012550359450f9940d0b8411907000404010424024160b0500800348081000352540e4030140c0301c94a0103800c800101c1d501c2040030701c1c0044c402540190035141c0082440740450991051b02d000f294410021101d441b03440f0405000d40b09032107901203043c000114041d0007603003d01001801520014501c00c080c401c041e0307020300c0d100c003013000c416566400d100d280c1d0b034488800d0b4050b210545104525035215100d4007050f0103a003608000300140000055603084c03158040c0c1e0001c06800c803c542500d034460780640c803403507901200305000b41d140aa000410080501402d40a00d01c00340c144d01d65800040002c640e444101c1c50030a03045560641c541d00340d0307400340c803449040710700a001c0a08694158070412 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 875150000 1250 875148750 875148779
    0x19141201031101110714040908070803060306070f02070905042109080d0c050604110117040b090c0402030103020906330409060504020f1c1407050c062a030a02040e040c 74
    0xd4100011300c14200b051540000b2100103651a0b200c000d2072049a900006014207030b2804002d014000100e225070401040303402031800391004a05580b0b1559841c10125041100f9184200061f40988000c0104003d26403203641c0250042021a4000202c800c400c3c0e1416241c8040d04002513902c403080044000604c6011591070041c503000156000d83d40701c0b0340e92010051b0000c0c108103a54600303101c41e68059055230604854941325030302d540c43c2505000c8030340881100c3c4114940034040620160f80741501c00c99050703d030300404084140d2540700c04c0c4103502090100300b402c4103101200d058a07222514540d88046040200c03525a03450801030303200c00f5144c544d80500e0003030b401401140e02c40c0c04030b5020350306a01d80000c0c50255120340b2421440c007500805400455180090b418414041c0d0321000a12800c00e144084a6041c1c452080b0903902d11541c5c141500002c11000406c0381c031403846002142c1041083e403015041584079254001034101c10b030b0301190521104a420042541850380e107 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 875151250 1250 875150000 875150033
    0x302010507050c0d12020d0c050c07120f08090f0604260d0e1201020412031d030f100903050403020307060503090d030522020301091a24061914120103 66
    0x2d03410100c101d6162a95030540d03020310424403009100d561040d803142e83c141c480c42c040300c01c4240844201c40d540a400b86c0e106000340041c41c000d4243c0451003044901400c03560580c00001c14404140503196143d151300311044040e4090707100b111008c038130342c0e501d80680080d14031250103a401d07104444d1101106003e2800c040540c1d00310800d40c400051f00804e40c441080b034140d500035000441a00d9042c0244502e4000759009020311405405140c2d0203500200d0203108110f2400844d4051003c140d503611200c21076600d550310110f103031901d10f1015040b600ca4207110341003441c106900c81c1e00007410721406802c00e400040010040016642d0100300d1080780b4400d82c1401c009500708410421030ba003400ca0ba500280c07010010310102151000d608c0199801d41080c443c1920b041e0320300c07051020580980d0107840410082403041140c4280d2201700c00d00d030800500745450140c0e8900002d00030031940da40c40080c04801241000c01a141e140180006507088403408502c2d815440c020303a0350400b0059 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 875152500 1250 875151250 875151257
    0x7032310080a080703030e0a050303160e010e090703180212030c0c0904030207030b131505100501020106050306191d0c3111040b1305090604050c0f0306040b09130302010507 76
    0x1142000f140560040342d2919030185000b045110b4080300c428540200014002e1440c4400402c0100810841d20f0f030071400700450343c1c0c1c101c13909416801100c28401601446900580c1c441c04940628080d600c034090440e1100c0d03c440c0325003280d400144448800c101042c1180e0000162404401e0092000e1060500b046803512058101034130002c0d6551124040100b000c2c002c1004922081140f03024103c02c1903010030b0800001840301c064030058a07066804454a10305204040b130310b5030040c013840c8140c3c0d501a0041c184c0b0f5a5144817400390207514810010f1150780c9456a80f50200341c01010700b61111504000c20f00c0010303003020321540fa6108140220059801046410f0b0b445c0192100a0f00c100e03600c20100c1e00d1f03000c030803130401709102d0790703110b00504e040000d03042101b1400ca020031021250f084070542980c3d59000d041c0402e0314002c036942010683c0c100480203403c403001018541103a0050400242080000c0102d88004025900c5c600c0c00b1003901980405c040d82402059030003841c915 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 875153750 1250 875152500 875152513
    0x1150303020c1516080a031b03143d08150f0a06030b0105011d03160501020f01020310030210031e020d0c170c071118011a0705150703231008 62
    0x4503007000131084100d0041010800041c11040395110790041103110052000c2034444501c1d0b07c0000d40180807080e180c09202038481e0004600c481c80109038464000500005520308038403003c0c920500f41d218500c3c0c000300b03030818030208450000300410580c0c84002214100e181c00c00c0d00305414541c20042412010724145003003400007501c11921941120400e080c039100420044828080907015451100c1e014442e50321441c4408014185006c11a031081c2c0a503200068182d010500307030f11003141d41c4801c544078810204014108520302c01011000303032070002041c801920dc00750b4403843d034100b10140d0540200d0200444162031150703c000010350300704420300c180341c08028038000c0c07801851104000c80120303540c000c0c0180318003800c0100c54002d00540b1403c070100d03118460090f0a00035210104025024500c80d220100125444160408002c0040100070341c5541d028480c003e00c500304060301c6030707140d200c10000c0700c40040e407580c1607428520b4289011540c02006030140e5002405560120 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 875155000 1250 875153750 875153767
    0x5060f15010909110c0115090c05160b0c0d0c2a0b071407020402030108010903091e05040c121506031b050d0213170c030c09240301150303020c15 64
    0xb207204115030000f400407030b07040354422009059004600c03c514a0317508081f84020340117202036640058942d80c00b01000b440201090850740c500a00810340c0139036031340222140101329584a21a40100303d030303800d1890b211421854005a4041d0488200410070550b036a03122841e9502864440c07200111480c000c003000c588941ea43c0342c001529010078816400c00c55490b5001100455101c980c01620030b541d2565031b0301895000700b50983c000e0f40044c0503103d0208405480d0030440c0074415000d85100e84050400381044020201080910184004c00704034160740c41c0c081c01480404500d0514246125241c820041c082e54111229100d09902000d20107404681080c16955003040b40380e0016100c4c001400d2401da020803d0700031803416a05084659500d0300c0001c6c801340709270300907416248500e040350306018804030192003205040000c0c50003070075082100e07684400d64270300050012681080b444100115001190000c0c1c0040e0488014120142001c08240ca9555540ba0304070b85081c186 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 875156250 1250 875155000 875155007
    0x3150412080a0b030706091e03020d060b060702092701020c0709020d0e060f040c0603090f0f0507180603050c0a03210512100612052203050c0a05060f1501 68
    0x110034660305001520021541e400e00036032110491000c068101e503040781c2c0701d05010706024418415000100350003140324041283e0100d41c04103c2e075001c0e0800000002603610100035000302644250805014001c420140e0795035400680601c007450402120040e40609842d407400c000c4000c00001c0e070040090480070140050228201c803008100140c0b00d020501802c00600760760702504041340300b604240102e0021f0400694001c900c101081c207001d541c5e90005809441071644090907048000131080301003103a01d14200b014a02c1002620000b98407940b4201c0680d18030400001416a500003d0007081030400c040091014100c8800071140d01c0d654400c1041c44020403410f90b4079544070a440d4003640201d054440030721003206802010b16008002c0c206c8a8040d1080c10001281201c800700c40e449544643e9000d500942c1d046942c485d81c050617540c00307000304141142000010080741c0c0c4602c00510800c00c0b0507116202500e501d040c041621041030101910211105050b0309100e00c2c613a80 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 875157500 1250 875156250 875156273
    0x5250e0307120203120f0322030504270501090b010e090c0706020717070821060f04020306031e060108010c023c0f060702250905040f0203070305010902031504 70
    0x86403000c08900a071a10110b42030408014005c0d0104001040002000b6041030241d48541403182c4242c041171a14120701050f400c0282001e0042001007005025040340d40b00181071040b10030103540140901d404a0340c088507802d80c020007259549211101c8290707842104c281014000312080f45050400d00500340d1240f00307540c00100801c0c0d0014488007081005c0300e4144d60b40304221200c5460749000c1c01c000c0b01d1079000445003a8502c2c011000c3d8220440b4001549000300704c050322030004511007a09201c025031021b00000e6040c803a4040c20340060b49000070341d01c40c47c007414010304407652409030386c107081da250968014195041844c2141150100200900e040722554040640003020000b603201c11001405091905005072950386000c01c0e40080e455025000036400c4601680074202d114007164404070101e001104141d904004010389500031503001401058410000156640041e14210840e441140c05944071210141986024003c00900340c2107440f0a509a24140e5504040c00c403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 875158750 1250 875157500 875157509
    0x101a030c0307090b040b0a031a0f0f070e0103020d090c0906080c0102030f090f062809060903030305041b120b0c03060d023001020408010608070311061b0105250e0307 73
    0x107555075481c2c101c50b85c46821440c49140007a215441d281d840b800c000050005042c032500c0f02400941c0820426801c680400d80b103064041d806503a2925420401c0741c450413065049030400d60280200c080c1c044451190169941c0f064030f1000720503162200c400305642c0c05501031002e40e0030a007260180c3e039802100b21100c107140d202c5019956802a000620b001c0c0c00c580345242c0003e4082603034211400f90208245208040701e402c8010f580402400310348222503401040c0010f182d011080001138020b411060704140b02c0d900c85618554416407000c4a9441030344020985001e101e03141040c008900716007504880707103011107865403400c0030101c0d4034103210100c001d002d5030310902201c078030030481040304180c803500100c5242c80c6618100310074080d40050051000d42c3d4a045000111140000340c0e8004603584028000395100c106001c11003242c004410f041030f082d00302c000c2c44050b80030a10445101d41100c2c03001a4500040d508440c100a08d107000301c80c00d00245138070010003a50009030900498 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 875160000 1250 875158750 875158769
    0x110303040305062a0f0a1e0e010f02120a020c010f02060609040f02030c030f010f060e04170c241617060f03010f290303030c09150c101a030c0307 64
    0x140441301303807183c000f40c0900d403071416424007042d0701d260f1501e000000d10031200385a40e5204c01004000410a0b911102000ea4001c110344552020055008055481100d1078600507210482144114a402070b880320307040c0c200503002071a00140d1980c02890711208944a48024040d40c540b48001c100c01c1e00d409040500500c014450a100310b550405c2504085840038054609003500f454145e4040d01e03605090f540714a007002e501180700311014a8181c420743c7c00010700d81e406601c4101029407940207041c00d0440e0702841c403005503040308a000104a1000055899031546480c4c840403600312001110704081054030350400b0125a0312861301a004003044814000102c0d0380b1000a0040c030403a1503c04495050014440d4060100c424402ca07980c0c1c203040c40380308442520300f0151288000c0712a10f0000700140300c02e00607800d0046152180d0340486010301d20342003105015503d408180344141d0000b9807980e041d00b0007c0d035144ea12102c08078080e0300902ea20403c060019848140c0e130700490640 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 875161250 1250 875160000 875160031
    0xa05070f123017070302090d0b13080f13092309160902040321170705040909060e0d03021303060510050d080c12091e030106090e01020711030304030506 67
    0x200020312901c08440915050364030b040d03140114042c2160b03220b207100c0314400c44100005503d2900038000c650081c14010303c0000c52040f196150039a01c100a014a565410301c40c69200024140320010581009501321031a118221541c440d40c480c0b000c1d412101c8180d01707003101544070110b0314501d0060303008002c214140365903800c400d072403400c00241e01000311300030041000100a030042c2d000f0070503a4010003c0c0080981c000c2000946070180320a18000104809000400c11103d4105c4640100d607514100740b41554a07622141996000317203080d43c4655845150076900341e0304000070000c15455003000c0d401c10401c004001840a042e01c8040c20b4980c60300001500d015070509940c5c090b00c1c0003007001003014410701b0070b6a1143c004422410407031103412403180a03010160305682c0d140500600c81c041d05c0d402200c079a00030074904144140c240d0748441011600e0b45450080702d001040036000144c6410150600206032603c0600b5a80660801c01c0b0501c04100c000c40c40c1a4405c84444107540c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 875162500 1250 875161250 875161283
    0xb01021606050c1204090204090b03240a06050d210c0203060a1107050102122e0902070809040606020c4f050a050f0109020306100813020a080a05070f12 67
    0x20a000401d002030410310019002c03500034440d90142c026038010000c200311040503403043c943e892483d840b81d33041c90241e034603139070031000443c5074007075031200b2001c3d0302140f20740d51a0301042c0d01b400f09500c202c402d480321000b03034411100040c1d0917072849141803616413038104950b0046601c641e03000e001440c1c182d49a0480e0b03045925102d048450b86030b0b10100865541c2805140300d038480034140c072210300110f0b4110041041400c5210080f4048000340c0204181c1c0e40384c607007114000d50000d41e00f103030406018480f40005a440d486207000910060700036014294240b410002940007007800c01092900310050109402c0903407002c2c0c000001c0440d94000c00300740745084203400c03002112044841608020401c441b4016603000940201c0c92071014143e2039032500c0203082079000482c2e03c0c6030407107810304a103906640305880c0d00d42c2103e0014002c00c0c0c25005074004c114644c0301c40c4c100c1c040c990302c030305039800400404105450003090148680b0f003420303041c001c0c40e003030682d41c900c8040c101c1c04241d40d4185 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 875163750 1250 875162500 875162503
    0x1406120a02030312091203010b1c0605062727040f0b01060e0f04060b0307140c011a09070309170d27031d0307061d04090302030705010b01021606050c 66
    0x1004a50014100d075180c3c681c2201441131441c0c2111001558012050800d56120904090b28180c4103218081c2d4100604040004100c44041c080c862000380c60f49400100d5440d0301000700700da0342d4000303201c4000c40c0c1054000d504815042c0410340c007c01c01d4000c0d0b000800008480d0604980120084003200e890f2410415010707c840b0381c019000c0c40007900005030b1140c01440303104501e00292941000c1051400c104400c42d04107213f1a00000f2040000511140c8902c0c01403010070247c0c0c06103801c19007242c03203503403c44409143c94203044444600040c9180b400005440e4406490b00c1c050083c00d030300350345480c00d110b200030141e1440d100110300004548402d404c07c44c40703400c00c0c100504c002248501280b0203107449140c241c020444010621801100300214910501310103001800000e2804504556a40d29140e440549240d039010081603030b03907a40074805856020350700440d112805800c00c2821500e044401905560011031a504032a40074840f40741103030320905011f62260108403889 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 875165000 1250 875163750 875163763
    0xf0604030809300d0203040b030703023103030210020f04060c0609060504061e0c0e100c0f050304180501030b0a020f0903161a0f0403120c0c240201140612 68
    0x2101c5204030300c0100301440850041c2c0fa2403641c0201c01c48480b660040e00c140d890740328034000d041c1c1ca100c08100040403980260000d1910805d480d00031008460b1880d15003d9001544450b50b1100d001c80e0004c000b8190304102c201e20000340d1310011480c06041c40b500d02c0d0607100381d215040c04e2140060103401071042c0c0ba80000020707a0048000e110a10303144c54240000c3c29440011305942c03008122075a030100040c81442da5504041d2a4040d9080c0b01714100036987c0d00218521302001030040351034001907001c0d16500a00da1040005585032414440740840d05441d4000880400d0725000042011600b480441e64203b050b2030001a40d503149030413800c14a1003151440340d050b210380f0030742c10202c6100f1010b080440e03102450111003252070203683d00701449100c00050702c0480c244414070100e46407607001c010711502820310717225040281d0b0700c01740e140d00c144d403040f07900000170290701e5402650744a0220f030a0003544003c000e0043c114400b45c040b1030016185601444900d10800075400041085 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 875166250 1250 875165000 875165029
    0x90f01021207060f0c110a020f030f0111090a060f050d09170a0807030506060a0819060e010e010305010f02070f060509030c0714040615090312021009030302090f0f0604030809 77
    0x5199a0b1029424908081d0000404e00080b8520313220410382200d2040d40c41020a0a00c0c0000d0041000c0340d808110003d06600010f551501842c8040c450100092040d070712302404a46100391110101d07410842d403600140d005d41c0610919420140720590b100c0101c8034041404074000415090718103005142c242c0843d56640c0120700042c2c5104029002103c2070f120310740c28ac0c0c051086a468400b03001041c020061100003150300b84012414103005441000d600a0781d40d44002603640c7c0c0c5040050b00c00f43e003a405034603500403000050090010038002c0344545410382005510702405942c034203e41d200b85113000740c0019a46c01c04101c2249052041726540001c207001c60b1141c07521241c1c201c030041c0701c10004602c91440c1403130000b8420608a00000c1082803600da02c4d02081c65a05c40b4200c0030081c00103001180240c01c4e6414034420a485910542400b90340e006845071201c10a120040007402115449000d00e581c4140b050380c0c9100c00c40701500c0c1d01c03500c0c043d22400d100010a5280040084 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 875167500 1250 875166250 875166283
    0x1107210903060c0203090306010f0b0f030a0b0d12020c0d170a17070e190803091e040501030c050924041a04090620030c0f0a0c0c090e071703090f0102 66
    0x160722200c2ca134000044c0c000c1c03003c22801c2e200181d076034841c86d078240e140c9845582140101840205400284070029585c4410265030101302c104254000403444600004100c500401d5104920181c90f810400386180c090165403401400c005915020320301c00e01e80e80a00c00c04440000c0d2503801c42e2045001c00e0941e071240300c01e4a680e0034403a0001d002d05260502a0b400b0b04403461004800c003480c0040d040c21500b03000059494220b900302480152281c62020048c41d211089030340345161110321419008501030b0111120140c1088108609901c015142c90100300103030b40103808600140c41c0f02d01c50728000f02c1c0c2c0012a50800e038201221034413061180340e031082c5021040310510855411814450112507203000b0b02c0c90010081e80300c140000e40b4400c0701200300740000c00c40c400c42c0c440145802005801c05c004c00f081030303a0714154a01c42c4d60f0041404241c880401541c807440400650020300f15045a40300c032200d9284101c3c2d0349008100605200d0042c140400781980d0007030026400c402403402 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 875168750 1250 875167500 875167511
    0xa02100908090909061504090c0e07050403120e090603150105060328020a0e0d0b0a0b06091003090c06030e03090925020705010801060e01080a0c02010608031804110721090306 77
    0x403413a5444050407606400305a040205461032441e0130702c51610110386c0810200039072410126201e440280003000042480710030000480072490303154503103111814503580c0d11020f07420181409240c1c030014141c01e0013580700d0341c1c0942c00c500078098500e040d6103050b10350a441e41e0351034400303c0744c040030294080c0003424505141032107811b1030740044c48044800d40700e140d450260202031029219480801500c20200d01c001301d0505240741d001441004401400d0a040c05000000a801030300900720210110b9920144c00c01007040d801d818200814030fa0a013041400420300800380c0360310510452038402c0e01c010700000c60f200801c006502240b45014451b50305141c0341e240107541d496540c05418045800030703000103803081c400c40c84c0c0315410700d06075266031454440810020141030701c02d10200540d5224072012501c2d8004002030300142a50202441a020402c02880102c4400200e204880b0208101c500c0100e00980107034070390300c1212001c095121041a40c226003880664100909950a14 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 875170000 1250 875168750 875168761
    0x2180c07170d3605070e040303020f0a081503060105030a080f0408120a090f05151308030a1206090507020c0d050f1c0e010c0309290c150c0a021009080909 68
    0x140700c0401c200002000400c5604a02d520610f4400780881c0108158442501440000302c15071807250014840c0c00c025080461368038844156410680d0980b0000f40c1c43d50820134442d0b40b800076410340032803c0e0054096941440042601e610151002070b00920000403203444a6a0701c0007240c006166000c1a5814000408084403099002c41c240400003080c026021035078020204140003110f4000384003502d1400300356030002c41c5402a42c003940002262000000e0034400a0009140d03869047da00c0400c0002d10b140030740d04541c80b82d00300b01a110714010400041c2500050170aa50580c11203590319214030f18542180380440b6542c3c040080d008004003240b846900344d5003052460b20720344881c00b5081c2840c1c011514621059000313400142200010030041c00d190b5240f043c04580e01d0340e442452036206440c60250741c00310251300c0386a4070069001075419000c400381a004010644518501040b4480096030f6102614201e40419a40c1c810b0100300319030301003144c05d08840074042c5401032820 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 875171250 1250 875170000 875170031
    0xa0303020f100c0f0c02030a06050702100e070503070326160614060a0e0c04050d0c06020d05181009050d0f060b0a05010518121902180c07170d 63
    0x52508102140b1420700c1018030307a02e542c040d0050640c1d240d9102c0c0381d000800c0070300b12070020760f005c816a014041c0c0044980854035038003840740304221340c3c1c0042c58498200f0340100d04482100c4540506904250380c00d100c29070b00401d1003000c5a41010310140d0200c600c120089100701500f0414100000000d50055010145824110039038041c04080010501e031000d107491f41001190401e43c04000958180700304012003484a4101c4d481c0d20b002070400b919807001c50b84401046c102030340d400d810501c04000c0954100705980b04108a8600182003400010080da07100c0211501503200b07a401d1916125281c0c41540203100600004008104d000c00364203210041a48490b010b5030340c9410300c1c8a50080381006921201141c3c0c06030f58091070304244201c030b000600076158001c0d9220038080300c00200020108001e80c8020b00801d031b0055101014410084515020019000c0c02620300c4108082111888103072402950484030284c03401300f030700b40250024868043c10081c128945129021003c14 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 875172500 1250 875171250 875171263
    0xf07080a021906210e0706080108070b090a0b070f0c0b09090f190902030a0b090d170c040e100506030a0b0306010815220605070503060f0103060e070e0f0a030302 71
    0x1c1c1c42c0c04515986021104500b01c4680c000c00f03000c181130f000f154004504080031010040b10700b40c000030f2144c032064001c80c10000740d64811000114420018858414144916002060701c40f0000e0300d0070007001d001c10040782d010300c10509528004a240824443d80d41848151554804c1042c1c0b507045e250401040319401c6030301c00314041c0c00c8100004098000c004203c9014104045090349040703040403600d0003a10442c00c0480c3c060003160181000101e00c101d020380105590006055000c000100c0100411900810204607112500500403000b1801d003c42c1d06a40007141a001c0654801c0000503440d52517038042900000b0000411038940c6aa07441404102021404e54a060340d80780c2c501c41e926120818410102c4442501040000280710b584100d4102c149800e200d4030740c201d803034071012190102c8a08000c00d000008005561820441c4e0020111090078104400c605100c2c012100302001082d40060015650020000d641c5090301c10f02a804010141c003480c5c0c2e01c0e490b00949805 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 875173750 1250 875172500 875172503
    0x5250210290d030206060d080d1b08070e010f08071106100609090519020903190305070b07080910020a110a0f0c1d1603020c0a0b0610030624020f07080a 67
    0x292031070600e40403490803040840e6038030f400d42d00070103440c1c45540401110820102c5d049803280020012034210503d540101c80300c0702c2d08148400c21490a0000c00740410600030821410440f0002c80391040303a0f0401c85114080380c00b80f8140701c01d951000d00580d001c4031a032802400c0c5100300800c0000e000380030100d4000b0750301123a40e040c00965032004013400741e441c10f8a050341d680081d040c8d104d4a0801d0f0381d0141841910042c100c1c0e0203201c24610300003502c100d004080e000100002000c00a005480728000d400c250346113803d281c82e107801e89416844851154110802a0300006d1218800e4443c0040c070418442800c00c0c0d544540a601c0c04952450489400300c03410b411f1a0000503a5618002c60300c00904003c1544400f0380e0b075001c03220100c40039401c0c486000c1c10740c28003020603514820800000c0d03140c8074101c5004203040c00c4007000103114114880740d003010b0900409000c03080400ca01e801030003600320381654009500041c16802e00501c20084199071050100010741c1c400700040c00804035 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 875175000 1250 875173750 875173811
    0x10080115080f160317120f0402100504030f0b0a1b030f18210c080c01150504020c07140d060c020d0f0f0e090711030301080a030e030105250210 63
    0x61040340000780e280c0420b10340f1040441c402010400c04150700002c3c060038140b054400703518228149030702070700080c0103607a009030892109042001314240800c40f000900040d00780b80341814615542d004001000e140010328107503c50020072601084d0b41c0008002090000f034044c4000d440c0c0750000d0040c035000c181c0c041c885043c03094189040a0040340f0404142d001407100954031210500205442d1102500000304030088a065000c0b41d00038020700001c00b1000c0000c64107880c815030420190b29103400c04c601c51481002260340c00e240014009044034031150882c0110040fa10018070650303a800805071000f402c0040000c034850780821981c54000f02d6440781342c04124800d8007201c00625000c58000441e0800701c50450f6450100c0c2c18179806400c601d403a81d034010907000c00784d08540007039001100030381c001007004040681000c4410030f03e15040d0000c200070b1510b0061900c01800c403009141c07200048400c1000300920038040301c42d10101c00c2c0000e0109034001c00c281400d940000c440c0a409 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 875176250 1250 875175000 875175013
    0xa030c0216030309060c1a041523060d11090c03010e090c0a0e280e0d0c051002090315100509060414072105011d1e0c031008011508 58
    0x203590700d08101d0341a00d805646080381e407401c00300180d80c81c1c122502d05507030310030020b45c110a000070f80500700ca228600c83d80e99010b03004800c0c2122000d54800d10f6021014511180d19400c085144840d1103131300c06422600415451900e041402c00c0c0c804455100703801401e07420402c0390906240009604944034506000c01580c0e40c1b2241c1d548841585514652065005000b00042120044216000300f20110b420200c0c070110328002001001c20159251544d07115800d401103140207002480e407902c2e0310f0409201c003000650780c1d183c9600e411142031038003a6000c2002000c5072010000c950005a429078480710508058490000c0382201c0e1145038441e81e004000103003581402c0c01018090f8056079044446520f0345482501c16010f080c19094140741608158002c460403401500c2c0203061050150043d101110130500303441d6002480c0040f911801c00c6001003d08203403a410b50310120219030705031682c6500e1105540ca1185131b00028140d820010603c05819078200320384215032007403040359071 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 875177500 1250 875176250 875176273
    0x30f03041a071d1809010c0e0d021f03140c0409050a0b0105071101140a05030109150b180f090420030715050c011b320301090911060a030c02 62
    0x102440e04450520010301c1a44074580b080c0c1e01289000322043e00140084402c04c11007841050150f030440ea2220300342e45900b44c0d014216040518045042000e0310700e0700000016070045840c0c026140d070320070124880620810300c081d1003a404407401c08400480204542407000c60144590814082d0200e070341e2410000c100d02d00854400c03200d0154068441a0501c0402c5d1141c17000102200e5025040c42f040d1009511815810001000c000c2d545841c0c01d611395042c0b150303400840e22a0102910140c1e6141424409010f0090503540ca410860340359140258100c03012580f24180079802c5600304007050705000402800000704142d18a8205049012101800030966141034510440d145c0e600410f195000c211b2050340100500c440410002c6202c654022070009542d640450342c41c0020b818503052080440c1490500d0301751626442424181020f10f2521381705440188100d1086076078941600342000741c2204000c44480e002005292034030203100015028080f03150b0310f04014000c0728000d00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 875178750 1250 875177500 875177543
    0x70f110402090a0e090a08031008061f0e0a0f060308040305010f1515020c1206010f0b030906060906030f060c030a060e090c040c110714212a03030f0304 67
    0x1604048000c03d4034a01600d000c06840000001602206190207820302c140e0101c0e2510008501070610f04590382046c1d450280c510b41401000340c04d5000c409924400352400c1600113590700c0c1031f203004041c074880b030b5152203500c00c00400ca00862150b806052510020510880c9000b400480f40180e00078490708507500e0058003103504260104081480300d0400b40b0803069032994140d01c00c2c44a0044505007032006000405000c00c400d4007600c0d5030f11410041c843d10154480b0301000305041301c1507504600b000c04540e46c036201e001701864050340220000908aa41c100103100c0b4404120054908074241500803814030703802151045543c5080540004203180400741d051300c1040c49401a042d02c0c411349040102805030329569004001a42c880012110002e00040c130042944954450f01d01d03508509024030303556100c003400c03070240781c142e005043c200d00840c0031101c041441c00d00c044000700d1001d400b0400100d085c103580e014400440c20b14100c1103514003d5008600840e29403045078202003001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 875179856 1106 875178750 875178757
    0x1c0f0908040e0105150a02071e240f0905180403030b031006081605090711030d020c0609010b0307032006041a0304110108010f06081902070f110402 65
    0x10003591170700b800040843c0341d41107103140c01c0c841d00d03060280d21100e5600ca68170354004840300c5d542e103404401c03885001500e0200b18001c902034000b00c2081c0f08995441006002c0b6003481d03c00c0310014001c80341d00046400c014000408080601c8608520303d4025108600340754480c0100d0819a4060094200046802c0000241240b8200380a481c1c419448000c0c038440031034407001d105035202d07442965440406400c0c08145200c0c4800e01c6c1e455403080b0442980c0d03061001caa18004c482010803581d000b00322500c02881401102c00801d900e5000d14030000341450800b40403403101418061382103011104c006e01c0c29007480d50b1846183c002e1100b06000d031007880c1c00041008204030310001c12211884003840c102c0d91640c1810710030810908240034072000d010707060700024031043c5003c0400700060301e50b80b000d5440e04040d18254103503101c941400c580840c1e03040d1440805060074400c0c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 875000000 875179856 := by
  have h0 := BRFrame.cov_init 875000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 875000000 ≤ n) (h2 : n < 875179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
