-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5451
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:54:45.653582+00:00
-- url     : https://prove2.me/submissions/5e5c0cdc-4939-4c4e-96bb-32d0c417634a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 980215827 ≤ n < 980395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 980217077 1250 980215827 980215843
    0x2131707031217010b0f0711030a0b0925150c02040b090123090c070b040503040e1509061f0518122505010f0509031c080601090906031a09 61
    0x1c500100c0d1003524000d035009a4500e01d902295030303d295a40d8030703840302140030302484035100c040c04410886100480d08540f089103550740001c00715206a0300543c2c5410000c1401d9844030125481070320440308400403110f14400d10740604090410440c902030501c0d80c1c000d001c006880034020388800b20015034482d50000400702e040034051103d2940d64040c50181007a001c00c1d07541c2000020403030801c1500c3d000c2281c5000761025418107007400b40d81c1d280c0960440c0e0107003048546110030080007030201728085c3c80c0d80c481d04050700601c522040400600010200061100784100a03541e416800000c203c5c850b41c0c0000702c5850101c5d2100c0c40c2c0c0c1c0c6411103c1c02c00290895210300600090a51a040083c070f00104030800082040c451010540c800d840820034000d50340402c80a00c06c81d2500d80c0304002420b0101030060803500f030803144031081901048905e10405c00610010308120082d40c1000c0050000e2040f030200b003001c0c0e0303d10b495544502403d03203c03540c1c0011002010559450301008158 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 980218327 1250 980217077 980217083
    0x506010e01030e2b0207060c200a0305100f060e092e02040e01031106030f0105060304210e0a06091a03040302011e090b010902040803030a09031826010213170703 71
    0xb1484114913000c10b910071000104250061013961800309009101d41d0401e002c241d8404549405200241d105102001c1c10b40016070304100b0190000000c1801080303107aa0f050003203080055031752050580203060700d445800207040040f0907018071907064000a002045074818900780040020341c9582402e07144003c0c403000c0c0302c0c3c50000c034010540c5030305581a00e04891140340780348c0e460450791040c8040c9000413180240c09025000041285090000c01164000d218490036080c803032400e1030741c501c02c02d10300401000262690568605030f00701110101d01810309428440b5101e8608200c00034280030000447e4100f40010000c20b0800d4001d410001942c1e031070300308800784000d15a02c1e0364003c0c0182e1606482c100c03088000020051390718400c070b4050340d189002551443d40c45046090181101e48800c5081242400403000c0454500645c08003410784078001c813244500700030381c80741c640d213041d240d040d01648100a41e0340c00712005140030003103410420210079203d180607012400c03c0701c203034406 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 980219577 1250 980218327 980218363
    0x541203042d030f0311120a0f0b0618011407050105070201051b0405040b0303120c18040c0e0603041703090a020310060501080f091606050301170111040b0c030702061803060a0506010e01030e 83
    0x580c1ca144608182031149403520030030004940c209035103234152407207031881e5a08040108100400c0c1c03a80c6140b8158a501e040c18440c44100c51018401000d90008006640b41d0f5500c0d0107000c0c24642c28080c3c01d8010b0000b03904048440c03201c2603080c08611403440fa41d4481c0340c0e1521012500d8030203209854807444144003681292400070704981c0f0036400b10f4510f903440518020f1071b2040e03240c6403040400304c08013070384c622141e010918107104840d400644151540c50b0461b100005490b03509005501c1002070030050a40b2503400d01c145840d11012156441d00107050420a111590b80801e0180d07002e004622105003a4440201c02800d01848281d0030030031018031640440c1051300400258100e8081070007040c00b100007075840034200c2c2c41c54030384221841c900704410003c5515000240820220703402c02d8904c0c082056000841075440a180d501c2c0060310320b50780780c6c641d10741403100942c03003504084141705c140343c1040020150740b0b0b142019414160b41d02084203001c1c0c01045a0141c0380000104 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 980220827 1250 980219577 980219587
    0x1201060b0c0a0311030f0d05250f03110f0d0c11100b0f0102150a0c020313080610080a0b040b040c05040c08541203042d030f0311 57
    0x41c0c0c946881201c1800e03008648074000c4618101000000c48544144a50070581402542d40400b8040c01c400750000f1500c43d040c586c4944810510412041c05546988030800c20040340312000d0b0071342380e81c0e03640e58682040038081d0a00d0811807204440c4484150341002482d940e00e410259500400880000d020f482007030304130000052281d0011182c030008441645103190f1700e000482e560b01803510845520420040480e0075030ba07090700300e54141d40b8180180c03400c02d020b448030341840b0403da40c01410103512080c2030044c5c1e0005000d4040c0035141e043c0140003800c8154175208400780c0003900082000d01031600007000c1c00103446400740074060003441400110300100c801000c0d0b541c02d45040c0d8550358100b4603d48420a0401c10104400761140d92848801e011b0031a40c1c87c0c900c80d643e240248106103074460710140700078018195520700e200382c0592030b81400d046c00e000300369060362003c0b078400f4807003007000340925004507000840c3c0c0d0518140c0c58200e00c0a00440151044080e030410380080031030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 980222077 1250 980220827 980220847
    0xd060f050d020607060506221a0427020a080307030816020c0a141f050a080c09010e090417030f0907091413050a0c1511061308030901021204060b1f0504051201060b 72
    0x1d4109500c01d00c2030307000c100e09c8207040000b201d103440c0045c000610f15a000300c4e020071451449180e0580024541082d0300d5a8419136821940311785011800141c00031b040003a810000c10300040d010b90b06200603c0b4121200c808034480181e01c2c040c552a00780c5084006615a583c4d050f42118003202d002c900b80c80d00f03030450015142c4c1e080f032a01d00002c184480d00140d0910550000d80d04940016034031101d40c03103440b00a014425030007820903556819035810714521410355030000c40c00387d01c0482c94050356161032180241001865040b15140508000d00700110000d84a1540d420103c0b02d58040d107a200d071464510b10b0181c100030010241c0003080d80000789460070101d071000c0e030340e05602d818285001c284841307038071510221040e04181d240d00c0c0c080ea02107401c070b10103982d2001c0100001441c0540c26482c0c00c00c6404100d0701281c0060b1103103a18200ca06040d005003202e4120101d1041e0b00300042c0b407000e4124003030b5028803401820600303c5d01e030039110250000c900a0080c5078803666201c2c4041 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 980223327 1250 980222077 980222081
    0x15052805031509040b0a0c030e07030c1a04060905041d0a06050105041401032105071406040311160b090d06020d020306040e2e0e030d060f050d02060706050622 70
    0xc03007145954040d40c0c04420941007202006200d99030044004071596180420310300280807008000082640da8085060310009c1041603001860241495010303992030314031206205403005d40368414804041c0010054035400c920490b083c0d840071100400e0071416071501c01d919080008802e11036100b65200c0c0c0b002d01801da40b04605886003a50140042400c030201030541c0c5e0f500f172200802a611b145003045d46050301c005502412680d07440e0403440e000c23052710b1311891809180100f800540200050104050308003c02c9007400380c4400281c5820180701c1060302c0c02412911402807808000a40d45096a64880e0000d008a42c86501152510004201600290011120540103d103803903c1346030180800116840d107000d060361818400b0f1901c00c0b08000e01038085080221580d1070391440b03a0401800e00141845000500c00022642d01d04010f80c11041c00c40d500003802101c00018810150701e602c4201c030300070352700448003089944401c4003051181111110358450040d40c83d030b03001d020820715 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 980224577 1250 980223327 980223331
    0x207060b01030e0c0303040b07030e0a0905340c02060f0c010605031027060207020a060e180c0f1e13080d0e06040e0709080d09031b1505280503 63
    0xb81d0701008000c4100901c213981c0c20003400d460f5410b50060108004021489008064291107440c102080c04009070201d025a01640c0040184544940c20801041402000ba84240d942107520101f482052040365070340d408107031030602c10071140d440c0d454155207540080354039040c41075003840d541d00d40000c1039038004e01c054014140701e4000e100e8003041c1b40301700e4025940309400c949400c001e1514480c0c00ca69010416500c115404c0da0207000c00070140e03880e80700e20001801540c94a04107031030240c042101d01c02e00c44010300b00141001d410320914521240a0b24a00c420702510641c0d500c000401d101e0810440e010340c90703000007001480d100e00b55002e00c003110845a01c01c04842c4801c00b082020b039a182801022181c10120920040000e8003c4001c10707a00f00f0018244012860346416006041c50241c512040c04210144402c00030082d114058110540110442c56591401d00340c58105002c0e148614000b045030105841600c3c200000c0080d0a0019964001d111000c8504d4042d00c107400c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 980225827 1250 980224577 980224579
    0x170414060c420f070503150915210c01050d0605090c040503060109060608070c020117010603020309070f0b030412200604150203100509100b040816050d0302030a0e010e040207060b 79
    0x10551400c02d40100c100d281e4014640780944400c25070b129101156070780c10007480241c00c6207120000102a48881c3c034124018040d90003100500c02c1d03088107000c8104062104500c0c0d80344006c0c01d0001c098008525a0f072800d50900e81250740e0403000b200d650107840c8c2900300c26848030701481402134540387c1c0c200030011510143c0589034244e0365010710f60100c421a1080201003034503540055130f50340c800d01c003501681e481410810030b4040180c501912929007604000c011039800000e20504920403c2840000c0440d500f44520050410b1440c00381e500001d040281140d425800050003103000b030038004900950020f2800c82c0400c070650003699a80155001c1c0c0d2180c040300b141c02c2c407010303560007103034070940200200c2c1c2585803a04040c00000c000040c40030b481100c074810003281842c46c03080104024a0200c004084694000c038100142082035803081b4814010070240384002a00401075800d250090f091060341801c0007401a2001441100d206c0d03801031000814000704601039201078500c0c0341c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 980227077 1250 980225827 980225923
    0x911070501021b0d02280c0b030f0604060506070c05040902270a181e030509040906020d05070819113601020303190b1c030804170414060c 61
    0x1d44641c10b0761a904d00c85000d08440901d000100440b2000e4046c0c40e80c0103210700206400995581c010088503002039504425002540c0f013448400d1803c2c0c040c01d0f024103412181d0500d030920b90754031031101a149200d624050741e240d0f1540015540c950b0414580c40a102c25122031130b83c0034200740012a41c3c05c542c000015440c11a004100c8420f52600b0082107900a0301001c0c40d0169166041e0880668881202001010822412252035501034070702858418100540c035000c0a80104052342c1c002007100b0108542d43c01048036040300580e40407401210203100003190740c0c90440d41c0c20075100d4448003134440c40c41e002201d60b500c818221180750b1505d2001c4415152641d10004a8070f034441507a074141000320009412107440d00d0755024400c1c0c590010f10300c0b034030074840800d9803c004046040c26800305032010100000d00120601c0c00c212120343d140900d1405040c0700070207648094821410380110340118004503144010400c4400314103000141c0c88001e10302c0b030603030885000e11400140c40c40c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 980228327 1250 980227077 980227093
    0x403080901050402090f06040902031212180307150603020406180e0a201807030518030c1209060d05010314010b042307020a1407060305061002070911070501021b 71
    0x100c041c45068021a07004004600b541c6961581e208078000140a10b94031544c7c4481003c01a90100680c2460008203000c46488a0300714010320302c00080200440019002c010a40c45064030200403a04200d03405004810015505000800180707250342009400501d04980825007020001505201c465280414415041501c061589401f60594028501c0c070a441500380c50803584160084542d00c003802c0e0404a038520260b03880315203002e40e4aa004603a5840502061410b015200b440448803400110f203016225040b0b15583c408002c8036072a144004500713103900ea5607940845101814514040c01556140d0030050a80c2c41d07040121000c961909408403000d0400e40a8080030b5041c82041c41009100508084110807001b000c481c11405140c600c50001102c00d55000c054905200003016418203000b8040d040f00c201403d028840c0d200800d42001d103560001c1c941c810b07940c42c1007000c80c40003001d04100589000e4088001d209500100302c072001d50207198840290100c49808880c0341d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 980229577 1250 980228327 980228341
    0x10270f150c020d111503040602070b0115120504030509090a0b0f010906170604021605030c07060c0206180f040c02011514031c0c0605090d0e0604080304050904060e15040308 76
    0x50a0301203002900b1000f41d1541401092403814248804140903152284038041e408002d91a51320448080390600c0e40401e0882c00e01c44a80c01c4580034003491101000c04030100030001d0040034905500c00d048c1038440d00082c0805200d402074400c0000064011081c1c0d043c8011748902404031002c800780100036000900c0c81540c0b003070344c4140496005840e001c00521040c060a0784d80d0000429090300103800308226244155180012070031140100c002d503496030741d00c84090b810f04030250301c01810410035815400150b82e92030201c0d1040e07140204841c85110480012801550b4600c0003a41d01a190650b1001c0b02601908507140e0200c5030b45105444d02d8072125400c8400308204549500365020840890aaa90820420120200f01d080c15070344d0038060741d40d131400d0b0380084800084540000e10403004240d007113000407500b1401100c00f1410f0a0411003540c0c0e07280528420140702d407081001240510500341c0c4030344401c0000c4000d6608001f00c0c0780525032605030a075405c40005034244002919 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 980230827 1250 980229577 980229587
    0x9031c0804020301050a15050d0f080a08010e010909110609150c0106080601080304080a080705150a1e05160e010504080d0807120e030405040b060d05010801061706040210270f15 78
    0x1c1c5c946110347e103200641020140000650f800c1021191000d04940c0b001c0402c1207403014101b4480c05036a104040d41c101001003030806070680c02600400c1c1006135220001c0c1000c4176010310400142d400c1511425528001081c08600c49404c1100c4000000c01a80000c010341001080d208d001040307a04c1a41da0f02d008640d02e00c22446200c100d81c002800480001d003100008103003072030047c1d048400c0c180032301c60282040c11007035885141d0560f4510b1700e06220764602c5800101481144010403007498000c0382c10450242400e82d002c00c01c61541d404101c0360307000302e055a0140404108440075000c0c07480c5d026003107007025500c00d0003084620000d040001c880340030700740500b941e00d005503041a00d0202408003428444c0104d40e0f1003d824010400584090f1007524001c003191070000c5403280c540555845075444003d00c210554108030200805030b102d4071504e0500c195145000040b241001042801007081c00150500e50304c011080010703030110160001c0c050f5443c08020f03c1c03040c005e141c010f5030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 980232077 1250 980230827 980230841
    0x40507031104152c010e0604090318150f030c0e090a02040324200f0f040b0a031b110601030b04060b0303070f0b010f03111302091207031506080601030809031c0804020301050a 77
    0x311b01301b0307000000d106042940083c000785e8801c1c00d20503c070000070944441040300e40d8000807251425868401082035000e882c120321240301782401c200010318401c00038864181c800318103015800c41c001245150348164101c800442d044028500c400c3c07204d0412040d91300168403c259244c2c1001c5040c420b10601500c030024507801940824a8000b040c0c1107481ca17070f0801c400040308018140000102500c101c001007202e1903090780d0004a644d000003207001e200300d005a21100f00401c40750b181006070b00015a080c1507a4114003801140e6a840c68018090160540b0003030300340c000841c10100b08680142a450071610070f00c11810306a0321840130174441c10480c80003802a95906208160a04040310314800150b0503803005481c041c0b0032004100c05218618800c0004d03840690104140507a60400d61000082c1e00c0003480f03030301d2806501d079569a0b810f01003d04160f00c0007a02c15446c1d90700300f2260490810080d500410040381c0c4101078041c28080310184e0195081800168180c041445516 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 980233327 1250 980232077 980232089
    0x90a03080405040c0f17060d0b0103210e011202090a1d04110103111b0a020603090708060a11040e07030209030a060507110d0801121a0112030f08040507031104152c01 73
    0x411100e04c028151910840039214940103070b2341032890300100d02c800c007045020758050b01d000c800c52002c01c1002c010074082c0e52101340030000d40c0b00b00606142e920410b070340040307003040d100561101c220000060100c00305511106100290a60f003043c04000d001241e48521302030104030080004942c019015240c41c1080900300d14010030a0001100120600c0754001c00194100c07255828140d0204040343e10503589040b140d807043c1010082e84008215540d84a48007a1040c000e024210547e880a809240500e001c11040300c00050402482a4141d80344c2c85c2c4020100c41c1203c9250401c5d4005084c140c1d11100010008880c410a1b1480000c11003070500300e541c2c4441450b860244051103c00c42c011003100d24103102441041544e000300d183c103003e01851582900c10041340e1402910540000002e5418840c000040001090f808100300c001c0741d4202014030540201c81c4000307801070911064010396684d030720101181585c0031001807060105581d800039018000500c1200604030244113107 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 980234577 1250 980233327 980233337
    0x2100c0828090911120a0914060130030e12030a0e041d0a06050606220e011203080a0c1205150906030307021c06020c071203080703110d0e03090a03080405040c0f 71
    0x18404a055262070a0740201c00e000e000a034200c80d5908c11081000e24a0711000d554045401070061702c080d140401820313200d83c8500300b4030f80c08080c290412591407203409070600461866002d11a2030b0990003401010ba541d060b030707540300000c82c03014004251503010385019900d400f00401100c10a0084c141c41640710500824a02e00290340d4440030744402003035650032000501001c2407004890018400c0c20001860328110a8200b011407001a0016800124103240e01c02007940402d42140480d0380040140728045040030b601340303080c0c80ca180e0051107515100d2408082006903811104010480b40e412a807030f20454a40d01c040560f40d000f00e0501950104001070105082c0210b514241d030b5507442844054100039116075440e042c4505544000d880380e016000703902c101544650315a42c001c0090804011002c1d40c0308902d18540a0300d044600c02c15540d082a0301800420420756032840d100810040000b5140c3c685201c580d0050b1180360300640c203102e40100000c0c06160f15069212450b9a0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 980235827 1250 980234577 980234587
    0xf07020907030f0e1032100b030129040819020f090412081f0303110a060c020a06060e010803070b04060609020d090209100302100c0828090911 63
    0x800c8440040600441c041c540d403202809076901c081e008098520410001811065042060740025216003900c8050140c0c00900c802018800d20040343c00c044003d608510079558503011004845166504224940e4001100010301510782d030b030000b1103803550103c41c03840041151004903818011401083d8068000002145c0b82e440740c0317031980ca000c2e400200562001c50102000c45d04010090b0340c255201c10440340103030318981c2c2003914190402d8104500421550821440d00c0d038103d01400002e003004a9041035000d20b0000304036000480f50040001c101895502901039a1000140c3c0205c0301e413414071500041490251400504a50100020b185825101d503103001142078002e008481030b581d20300000c0f40300815032015124084011b440059494a103004000892400828000e0228020001030005071200036207a0105440d900308241c82c051280350065180c042c900d404030740e440d90b51058001c0c1d800da00d12003075003a01c1961503100b91a0780f40c1100d0001c3d40c26120310381c89040c5041103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 980237077 1250 980235827 980235829
    0x71b06050a1107150c02031509190807140c03070b120601200607050702010e0d0c061b0b04110a0b0310060c06060306020a080906070e1c0512190f050f0702 68
    0xa000c2d4101900d00050b0b42c080341d00d0702d0034120030007480e6040300001769602020b0011420200188000c041d800c1c418040c0c50314291010796920310040c50007000f041400f20340e0108208694050380c19155000c101c0c45a0102210ba41c41c0d9100c5062a851b4800d00c2a001c00055002e15074088440c0c9040810074165513540781401035403a822050003162503c840c16015007144141030008038041d064075920256954002e000042c0404541d040c00b621034184d804050001031450b01d1000200d030158200200082004420074079080716040b03024080c01030348000c102c10850142d1607583c900000300c4513842c4264540003201f00340d0104480745505038010b000b0500ca801e0040440b0410607216000100c3c5850300c95a800080e030304244101408030740000d0a0ac502c101e400d00c41c0d00d5000e02c6900e01225100420000510980c000703414121588903492940001d000c01445808541032035181d410341d03501d4294040006041e1b04940032000100d14004802009109104032425143e00d9020517040403081e070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 980238327 1250 980237077 980237087
    0x5060d150518011202010c020d1203050c04080a060b0114070605010806180d050c011b0c12030c052d0f19080f0103021e0301060b13122a050301090602071b06050a 71
    0x800240d0501070134013010b1f4016520003e502c40d45510621043c10000b02c00c50020342504d0740688903081110040c00141b140c58400552440c06513004200440d07030011043c010703503001b504210340201c1e0210004260041c484c00b6008281225004011100541e4426a00329142c0007086515041130304002003500c1014464070140800c25100d0000007030f22000074011052400c180d021080200c1e6000301840180304803444001d20072806c0781001c1c00b011b83c0c241c20007001e9110341d0610001c0e035040300c152141d032100341441005192003a85c0172103594070031151124009810500304152002c14a1001c1481c182c401c041c058010903100105214036401c540c2044800450010015203020103500500c20642d000d0144600626a0030481a079a100700001c0d0800105030360000381101e040031565600081641d1110201d5064070032001ca01c252984a4988070b800c1690f00c0300341e056003840804020300c5103d500034000c00d4840d8031030750f007202020803d007a00c540084c4038101c04510b00f404043c0f440c83c019 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 980239577 1250 980238327 980238359
    0x405060f0a1115060f10021c090b03070c1407061202071e0c050a080c0d060213030602030f0609070f080705090a031a010f0b070f12050405060d15051801 67
    0x1810604400003082e0307159481e00420200c0110260b50240500030700b4140035080c98203a0300d054800004058035000040e40d9400c007543c1071b0030032a6558521014062240342403001030440400c50a03aa814281001494030345016810b0300d0001112aa440120400091410403150240c4503020140c880d03040d03000003504005020340700e0605202040d0303800110102e903c00c1c4a8411401e000e03641d1300380070500401c0c403e83d8100c202e2551050312201e405a072a80240f4000700d90000c8003603500d01c190501d40d60301007103a03400281005d002106201c112861000200c1c8a80c10035649a14940c1d990403049a010761070060140225032900c002c10092132141000b449010409080d440c4155900c0e69100d14086940c803642c00401ca00c070005006c1d1800241c131b040000d24640042e0b50810030261241000031035050001000118060b40c0c4800b00c1e405041601d00401d0020403581d1504041d407041000b070718528200d900e40d900030080101722490003000084041d079410400e60500e07030911414103640003036 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 980240827 1250 980239577 980239597
    0x603070609121e051507092105160e06041a010f030f02090d030e030c1203030a021315020a03121802040513060c0908120a080f060109080d02160b0405060f 68
    0x640010b801d0b4044881d10f407642aa48950000c040400307140c1e0703141a040303801600a4041000001041100c100b00031040c0034610140d8000030466601803a0052414400d00c808110a03090303a9070000c0d4004d00301040320300c280829241031042c10a181e00b014035811402c10b03410301081060b03240d03040c0d292095000d041105031112005140401110000c0c4031301e0b50185023100080e0303000e00b003ca05410140440005d405068409a0415803055201a143d0100a00d03001d0300d95804120b24040b0031121540c003009040140c10342c01d50803006600292a0f40c1e10321419008500c1d1a101101a10000d00c0b070b40c0098034042800c00304414543e420030004e000040c010030f812038055a8071703501196241c800c0258003005c1d42c40388146503140c00109424610042e0b4200340c040f80902003190600c0d00088a9075100c05003100302c4403903030396060040e5015030030391700a042648140050f180200303400140240c0c0c040b402d0001c841205135907044100c4584154000c2580100c400e204600c1c561301d03000050003000c0d1b6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 980242077 1250 980240827 980240843
    0x1081005190528020717090a0308070317070e04200301120201052104051b0904030302070f0c260705031203040510091b08060609040b0711010e0c0306060307060912 72
    0x400704240f200400c8210540328003d0b940003545d442040b00d8103d01d0554840c0344898142401e10b0b6400107801c51000f88000f4012000019040301014494812000216090008005217003002c090043c8900c0d40c1d088514000c503d04030a9503210341c819682d001410700c40085581c616802c0144600900d5000c11040341804000e00100413441d0b01441c0c010508201140038400f24505420b00a10705451a906c0c0c81d1707005005000d8281603102c0d1044240d1082d0181000b50707039440d25207020308081e040c101c0040e011940607140400c003400385800008080d5014009007440c1088084220f4485119220750359055101c00000810030040b130002c0c0d0761190203507040d1101183c800b01c80c2d005607224802c0c111841c00c0c0d03060a014a01074142800c00140803030300001c20032440c140c0c020507034a140141010704440c001000140250348244420a000305c0c082c0001c0c081508a020001d0341e4420f158041c51180c0600c4001940d903040001c0d004003180d00b25518442c02d149444100685c0c24425002620910 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 980243327 1250 980242077 980242111
    0xa032922030e150418060617070e120d030b01020705010f020304150918020405130b01172d040b060607050307140106030f080d0b0a08101e14010810051905 68
    0x10550020b030009004a200018014105c0039521040f500e0b650801000e02070a4188169544240b0400342d90154a90400e0904c2c03021441c001031010940203c000d105210b03100314007135519850b42002804610030b03000c88545c1743d20f400c015140c3d607180d00075180041c2c1c8103001c200508103e4410300e0902441300d0401c914080d446500c4907408403060741024050f60303000141040b643c10880c0003400306000070f05003081940c96010008044056503020044404c2d041c4001c900d18200c0c5a02141d81200c81001984200e42031a0021900c43c3c001c440655500310741c1000200f183c2008021200f510358048042d520706115641ca9268480e2450b40c14044c640d6181c3c4040006420300c0e0881801c180144d56054840350899090001d641e114a1814040d044102040203001000200c081041680d04008961030b4402c0b182c43d07a24940381e00c07030382c000b0a0074000c204d2000c010380503c5038141c1e4010f806a600344080f512095044c0e031029070300003032543c038174603451202380003e9400140c012200c2c07841e0000791 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 980244577 1250 980243327 980243359
    0xc18010c02040f0507091e0e0403050d32010f0e04020d14240709060210020d020f0310030b1303020a0308090a05060103061a041a09060a032922030e 65
    0x3e035011521500450a100350900080c1d0951f002403102441410808140d5801e00003840c50041020380000d09102c804680b131281c9100300d0f040040c0e501041200f00104020100d42d10800d0f0b0103003100c003140516807d001244c40003403400c0000998100a2903403161351559802e000401c40c0c000b50a94611802403501003801c1c038180f14490340c6800204002041d00c400d04040004848050700d04000e21a170306104104854000c140001c805261900060f2a210f078450315001a1041000592505c070000013044459280c0c4048982902d004850a001c183d03240d003c4010006002d190140c00340c2d000000200000f44203880f503682c0000750600f80ca070300409d00d99506207441d80c203802c00c499140e140d00001c260084400c160554141c401c880c1031021032000c5944411905404041078041c0403c5400140640c40f4024820010f60380500344120321210f11620f81090b4603000009913200208401040380d86100c403140c201d100c405119550a900301039981075412000180015030000406c059401c91 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 980245827 1250 980244577 980244581
    0xa08010203090d170601090e180109060f051f0e04111f0e18360a02040c0816031a0a061d030d14030c0d02030703020d050c18010c02040f 60
    0x107910720030020000c44112038005030241c45018131000c100d450900410000760792005000040310107200c02d5411903124a10005408202031080c1c46035036080901840c01c01510303a11002c080e0540d000200f10035140c40a084040c4a5009a800b4400038028803d01411110021031f5401a105110141d104119140407078a4000d1a03d5014088913550b50882ca600e17400c50310070b032074000701250400c07503440300202002440c0c18060030704140c180d828111807500310b2501885416100192106110308110010042d07039407032202c6800c038000ca04042c11847c03800d0152054030f0007100c0760fa00d40c114030001d082d800c40c003c1c10484142d484c001100f03100741c4001d407500c01c0d00d01e004d0b1845681d1840e404050060396400400c0c0815101d0007603004203000200182e0001c1515055001c150455680340c44542580356503005006141c20810320020a00901070380541c0244a091400300041c230859407900c1a0a03010700800501c0c4c0003400e140c600000303056103d10703010301d00c4c188000c2001410240680480e01 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 980247077 1250 980245827 980245831
    0xa020d0b04110a05060f0c1207080d110f160c09020c0a140c0603060907120204090203070f09051f090e0c040305060f130b07020a0b0f0711030c0a020f0a08010203 71
    0x30342800564203000601000c1c0c549104409070a8444801040c134000100c1c4031882488000d42c00d01d8000300e00c1c074030094400d002c100b41d044200c030512074403a804d6007401c8007a50b020820000741c5900d00140b2500a0940ca01980c0050100d00c20071424520302038401e218600780000121400030612102058507021840640400c1c030f0060010400da4040d0318200e2544900c034a83d03450305134003102d05011556204000c80b98000f00c1a0740003040342c6c0ba0598142d521000c1d040403400340ea4000b0501041c030410a40c090340c0b20310810f0380c982d050808026800d0b6007201c1903005194015603402081c1c02c08516807504000d851402c2d00d80403000c10b65458040035894000d81c0d0411052100203001c20a1000c100411908401c5c1111440c0281c105100501036004041c20002c0400c407040d400107001754000d01c042000c80350440340a0b60940742560704181b500d007045504101148008604900ca40d0001064420a500040c010f0015021035000c121030700d04124801031340023210781004543c03079000b800514 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 980248327 1250 980247077 980247083
    0x21f0e03191d01020309090a0c1101290f090c03070207090e0102070302060c1321050d031d011e050c04050a08060a050c0a02060f0c0415020303010f0f060c03110a020d 73
    0x118007040c10401881d180c2c80000142e0440d40700303200360806507884d01c140c603070020003031880000c42401105003a034041282240807040c55180c03c082d160940c6070144a0517446401380d8805841d06051000c00913034101d40d004640e004569840058910420314009640007074a0b40112010107944040c03100650b080300008455030394000c03c8117000c0580401455401c210141446409c00b03207105641106402030384240c2c1c084074240091844a541968011980d041c0c20038181c9002041d2940c024002e4900c240038242c500020400c8601d210006105030910308076400c2403800c0000150300d00343d0141030094405004404100400603c0356500c1450100415031032005d0141440c0900055040754001030805115820401a45107501e1740441c00e65807107080c620104180380c54640e9402100c0c016030304807100c4441440340480099400002450407104503135000508151200c1000d038618a05100301000301e01c00340c001d00c001900500305821089001c00c05c403495100d0075000100750b500c500d81d0903 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 980249577 1250 980248327 980248337
    0x3022b0e0f030714060403140d1d01020c06072c06040504140714090d0201270b041419060804051507091d0c03240d030519021f0e0319 59
    0x80301049038580c0081c0c1340c511400054203040c600398801820b01c0010010428060b00005184400415540d106a21f10440340c0030829004401c160094001e5010041500c42c0e4454500000c0486109625140f04c8070800009180310318129151101c0c145564008954820300603c0007103103a0b102c4d8030501c20440949405081e450409000207040c00700e00384090a1486802c102042c0030340c8400e44081c9400b5420700c0d080102610240035011035071045603e84800f00700e8200c0c0003070083c8110000e40140c641c0030000f047e1510b410301c00c101d00c01d400e0042c50501040520000c00206009110780c65000380210251441050030180c006080c48040314132070041a411039091107854074203c01240044c0400f4041c0d20380d805d11411031002400010015162014604550480c410f502c018500f080c0c0d1021305540d06080743d5280280068101c2c1c044240001c29014540301c1c442d03c0003e038080760070903080e0301a46980c090345c0320b0000740c2200c0c04c041c40d07a071104002668100f08a83c080f55450b0b16140c1c1c41c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 980250827 1250 980249577 980249587
    0x50601080f0603030304080c0a0f0c090f0e1002030405100c2d090b1305060403080a180605030c1b061602120c1e070e01060903050d03022b0e0f03 64
    0x1504003600038008040c0e59140c0401c005298a00108030307608250000c00d40b640300d07000118074901c0c01d01c0380280202180e0800d503c1c4800c01010070310750b0050f6111400c06107d001031003e900c0007200c00782d0f040e6407155402110030049c01030b40303a40107541242c090016204180201d59210003652130802c0b061001a40c0580c03109074940b0601c8491080c0d240140c140700612044900041c0a0311041c0175444a07400f000500203041d074030102c1088000c1c2009800305032250350702d081014060300f1020014002c5041091034035000c49585068606a1309691141030641d02c42d40e48500c070130b80000d2403094003e50448180e210309042000940d100b840c41c421040b880c6010341c28006c0c201030410051081c20407081c4a5082100c00100c0d410180c4409404036800f510000288a443c066095115101314403460300003040140d406518a01660300078011a42d11010f200b07800c500b20311134154500030300880381c1071300f2540c44410a444181685001070201c0c1d50128030400d2401c00106009030111035000042c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 980252077 1250 980250827 980250829
    0x307031103070e010f211a060a1e0f15090b03130209040b06040e03310915030629010302070c030b070c110f0906060d1b0906110705060415020109080c010506 69
    0x106c248058602c181c01c410029503484040c000d5400201b04001a070780c02c00500e641e290900090010000b40d0244071010449000d2290907542501507410240c0155401050031a0281c0011500c440c481d960070401e18506080c41d00c031604060088100000744d0164000036980d03442a0900840c0074101d5500e03282440c03800c02040350001c510381c1516070000c1c0800b00009034143c100b00d00380c0c03120380400c03440d110122440c0390450000d90403859041d407504241010301512880d4580075644200000c11601d050175001a48586d00c204241056050390700070525503500c80d8025125840c41817030101308003034032075071101806002112503100103010003048405106140e015a01c02c188103850b40005404114045950f11030002c02c014064200022521643ca00d82d5000189007807580c0400c4200b0441a030700182444501c1c40340900203100792441007503c5801299050417a00010314041c54503190500b80d064000000385850191756845507001c2c08a106d1000801c3c590411000025052400354 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 980253327 1250 980252077 980252099
    0x1e030a0e34030503090d02010203120a050403140301030b07050c0109021f18030209010501140d0c0f030501090e0c010e0f0303040b131508040320031b010501060309020307031103070e010f 82
    0x808400d40c241d86902080031503400700480c1c0090f03001b51409007601501d800144c0c0b5500c2907554000036176100c40108454150f103a1301090046100341d99580180081c94000b55142c042804060003800d801400305450b28062001800c1b0030b80c101001182c4160070385c002070303440c0c5024040c8444880c814070503004100d6002c100c00040501440101014a0468000ca200d02005025440c10300501c0059a1102c540107001d80c2e181c0800544140401140c2c203500400300d14a1080b4400820300380400404d00000714000c81440100102c010301088034240011500c4030701c601d6503290002140c010100043d1814001000500034001011f6a2403640700701480c00409641c1c030100c1c8020001440c08403159000d811503800a4040c030307003882107040101c01c40c147c071400300215061034800001c8242070307410340c444807210b0414010002c11003680e80e800140c09503150300390001d600d80c01c40507041c40050550558844040c1002d0100d07001c590b1140ca5044c0e00e85800e030004081e81c00385103000c0007041c140d0307 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 980254577 1250 980253327 980253403
    0x30810081b1005040b1306020c010903050a020f120106060518040b03060106140d0e0d0809061003022803051b030321061216060908031e030a0e 63
    0x40000d0203003090310080022103040410041d80b0840580500c00328481c4160b00b0344001d0030220708450fa039100b8428215040410300d201e9000036010300800c08140e5802521040c04998008018050044480c0d0030021148542400c00e035000f001e070b101c501e03092202485510060700301c41c2c0741e082c0c0d2510031900702881c0c15500d0158034495401c00341c80c0f098a031001f00742c0604403081c506100803810980180000103006100341d203141c076441c00101e54580e98001540300800121034407068840e8071008040c035150b18044402402270442400c0070001400d10260000403c60b5403107540081403a44031400344d000180750b01c00d42e061742c45015900b0002100d9164000856021001103180010789449500b01d0340d100041941c007a039a42d4009440d0352554607145590021920a41d0703a12124a54100c0060382c460180300c1c00640d01640100c2c6c2044000115103062130744a1a103000011740c0c41501882c1e80c401444d0b019180d8a441081803000d50070000d8000b000f0a030310f0b00c00003101c101000c1501000c19 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 980255827 1250 980254577 980254589
    0x606220902210c0901151e03020d02070f020f0906060a11010f060f06021203060a09090602130306062c15030f07090903030c1b020906010c1401022802030301090b1309030810 76
    0x243c2510f114426811100c41c06030102011f040390460f070351160f801d80080c040c1140c2c2070f2420b80000380700c04c10401e00d0389810076680e200300c4e5080d4020010005020002d5021103805800c42410003403244170381d006003205085158680300114101c002401b02c04103848450340104400030307444405004941d01170060010294060184908520742003000440ca2101c7e8071034610403566441600e0148602601210310130461184800001c0c0d5591038244014182442344010360081d2098680c2070301421a443d09031000401c0d200c01311a01c0d840a00c2e0786a000001000b0352500c6255807901c080e90b005c0c40f41d070004140030f507800545981a400c0250036102000d4148017048010800840c44a80140c1e0f141071850301a82c042c031980d42c41a0060701d02040c0310034050300f002c04040070580d440d541500102454017407201405145103d081da0312005018000120740507070000d00041c40440013580c0000a290740052510300c807682005c5074601140e001000c194006070300c40341000a5604150341620040c42 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 980257077 1250 980255827 980255849
    0x180501110328020c010e0a0203241902040f08010c03050109090b181e03180a0b120403022118190303081f060f020606220902210c0901 59
    0x5810441010940b1900702c00d850581000720a41d11404000d90541d2a94041440200000b0132210358803a039507058118101e10a00c10446006d220748943c2210807020442e0029241064840203404510380e07414103029940f0a90900001401c4c0d400d02e8820350040030141d000182e80b45061380010b0648105822592a540c01c00c00060000340350b2415180e4011f810305022000d00f0614064141411180a1040d100103504a440810355201000601d0f00440111078a41c101c08101c0c14080300054902c514100c1c42002c0c0320a002c00701000010941c4039201e481941c3d040f11401c10b120b40e59650924085100c1200805c0114000d4160110094211800c982040350302e101e10303a1903001c12100e400014100700c160004106540008458140c2c8005401081d000c0d69484400081070071229207101030040c858140400d105003401c400f20400041c40c110340940ba94100214040034200c605c0089811a600c6440e01740780d810315019002a0741c41c540c000c0d002440c150810807041c020103801c2010280 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 980258327 1250 980257077 980257081
    0x304080702032a180a05060f0916120e0a17070506040c0e0a05090607050d06080d030905100902010e01052a01150815150a170309090a20090d05011805011103 69
    0x6001840341d507a11984178070300401c0701d0f5140404290100e414428480d0052511418400c4850140410511500c05981c4540468003404c8081d03040d83c0229440c0328030303a0040c1c2d020704081584100c003e203d50015514136494010b240d9111454490101c50903502c0300c0c8500b206109501030f410b400c58000030480802c0c0154185451415290840500701c1010300c100000c0d4107816071910740120f401002c4400540b02455698200a0043c0000c0d0208403024051100550854901849001c0700c40c0c0c0c06a41e00030a03090f2103c01940c00da4080b20b030160000120310141c524844004601c2400d41c520704001003441040c45280042d06403094000c0c519641002c000202003c1246c1c643c59444008101000c01141020011821281b81500900b0f01c409008207201044e06000000382060103040d10355004d9030751504403440c12200c0792100c0894240c032002d00003044400d11405051007100040c00080c180c040c9076281e0342154401400b1103404007030700b44000e09106083c480c07500f503044000c40c0c0391b10b14 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 980259577 1250 980258327 980258359
    0x403050d261608130203060f0a0b0108070c020907121d060606090d020906010314070305090c09010e0a0e010b041a0312040b0d020a02121204020a0603021e0304080702032a 75
    0x480030688000b08006507030000803a0100381c1902e82c54050b8014084d01e0060800021018000404840514426003032641381c0f0551f51003242002e204000030340e903024821031541e00b041410710000d4855010407076031030400c2038070b40d04c680310744080302d036201680b4540d242c0804007050034440000d001c144600c1c400d00200000d23894010000500982c116907810a60b603400c80164020004201003030a01c24170601001101c0390560b01c0240224204001c07501104040400c100280c803003409003c078001084804600f1500c0b442d0041c0440700e10041c004200c11b14421f02080440d4503042c00104800f03103219804195090a100d060400744400b20202d18140c14041c1c2d241c042e105440814001e90f41c0000e400800c4c9100b88840d89540c111118155a0340c2c00c50350400080d54000da0302a44030300600c5000240d000d00a100712a55040104190405003d40d1600c9182e40d0300014003d5601c00c4040001e00b0040c0c0e802d00042d03020b00c6d02c1a490090b48222028840f0503034101507800c90013089488950030305 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 980260827 1250 980259577 980259601
    0x606010807050c030913090b07091a07110120030316030e07030807120212040f0306050a05063d03021909060503060d1e06060503010b0301051006050703050403050d26 73
    0x3604001b42d038581d10a408032071014000344580d0030003074400c2c1d41c40d500f44281c0f603a01c01201c1045501e900c140c1d040a00880760015060300c95848024600ca914114159455001d00c040c1840405e22080858454400303401d103500750781c42126000000e002825611300c0d043d8152088800b01c04080c0024202c4c44d0a65481b80402d10071000045d100c6090612000c1c04988200701c60042000103107606511695590000c000001c2d540c02700711150390030040041c03850f141d64880c0611414004082d00d000c2401ba5004c010050710f094500100e140c5814501d00b1480000f41e540c074046815540c0040c0e0f600f00981060a00c07410501c0301c10108103904404100e92640031003a2900301d941150780540300b14062800429214061910180c0d14074046901d400384043e6600040131900306600034001022450101401c032078045501d4110401e8100c405c3c490301c0e119502a1400500c01c0c10030742e01e010740b6038540500e00080c2655038000110720f18030780b0300b00e03d401000d0601c000900c06030b02c42440c02c0c543c844a00d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 980262077 1250 980260827 980260837
    0xf070305030a1107090f09020f03031305120c060f0901140a080417160b01030c060903172a011b210b01020705040f230105060415120c020606010807050c03 68
    0xc1140c4200c42003283d0009200000060410b46030405c071049440c0401006412040e4090b48100b428012100c03084c00c012044071008100c02441c12412814001081a60040ca005101443c4201c0d16101b4841e280d038001402000310340010161525404000144010a103040b0402c40007414040c1810268014001c540c105902a4860b56881030341060414580100c100d00d16414003446039210500010240c0301d8142c1e40121029004240c80300001d542080c80ca200040c18980f407400d11013a000044806800c0740389404044032102d4040e200401038500c400715034004543d554004400c61800b0940b030f10580e500b05800e2216440d46901340c40c0003800490070034501041d45648042505a209010144c0506401030003000086e103044580320003045102d141c0f140e041e1240807180c030580848581c42d81240ca00400303a034907040c200760744240c01104080d41c54003400f040140003000c0d0003c4e8010b004000043d54020807003443d01000040030b401300901a841401420001e1075507031030010086030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 980263327 1250 980262077 980262097
    0x1c031b0909052d041a01030f12080c04060e040204030807050d02010614010507060e0c060f0901030b0d050a12091203050304020f100206010b070510021b0f030301050a051e031b030f07030503 83
    0x1035082c2d072117081601314101d4981c900c04600ca9440d00100c01c10021448216101d40192030540c0c41c503020a0090321040700503980e03040d0351903040c4010400300d803041803070f00d18003000944003504183c0d40755901305140d004036a040354141c00800d1302c0c00850b40c4c2441a00014000144008200640003001801c144950400030b000b8a440712668801340c1c00030052582145c80241640c1c1e5214100101c4103815000103026a00003030401c00e23044418905005c41c44030b01604030000d0842e0b090305954103204405407094072010300640d039400044021a07000103040ca14040d0700c2c0c00d41c2d64645481000550300d0b030011214401d44074105d107040955400101d1038151881e0300c0059988030f0702820490b03d001d0f09440303001c100030700024100705081c0e1a00c4243c042c402846040f03c407101a9100ca0946a0009018031070300510b00358010402461700c10b0382c1a05044100b200a15005418000310341800041b00c00c4000c40f0324010082c460b0350904001c2080180014405001c2e0300d03003540e441c80c1c0c480c440d28210f1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 980264577 1250 980263327 980263411
    0x90403030b2e0908102a120b042003070c060219020c01170601082e0501080c0406050f1b0f07030b0f091c031b090905 52
    0x501018020307032265107400301c02070501c5544644a1160310400503124401c0214401d0b00ca42d00551070b0082200d0300a40700b1401c0900f00384120120300d08000c15411029040120800003625248504400c100e0503c050b02c1d900d0b038418590720b000800c180d6600d521400e0040385006c50f0039172035540003403441c0c800311003909409581c1e0726011421150440800cbc406451588002024400d11034440841c00140200c1d8081d03038400161100107480c45410f035038011903080c2108001909645c410080c03d035206a1110f0035034020a0110450f400c00d00980168059056900909110540c1c100310440e0740302a20005551606080800081890050740070305644a00c0104884007840e0003c400706819000800459180c2001018595981c288520040d51982002c00100b160700a41c000f01920134280307440100310740c10036a10008404010403070380c44100340d40c911484100e0b28003d88020305020b055038941100d5400e107a86001140d0002d404043e800960901e800c031061016071003040114184145 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 980265827 1250 980264577 980264581
    0x1051f030908090a0810060803070b150a03201207080c06030a14190525050c1509010e1504121b021003050411190504020f0c010e1f0605060909 63
    0xd200c14001c40d5803c2d940300348641d00205032068000351013644a40030355410712400d580d84c05119200c0c0310b100d00152805003148001040600c94840400c580c1c880600460500f5a803511850200191440b201d541d1840d1030041003480d240400c11045900c082101509295141c058056914815501c00c00c6c000c00c0040300141c8003001540c4074080411000c40d0141c280c0c94002c101c00d50062610200c040407514000c081000036040700d01d07110458554686860a140c00c8200070395441d000003c4043d081e10a0441d24054155150201405002d00320008076402a108032214108001a1403480e4040821010000410b80b01104c06503246410304110313140b035449814031003030060000b030003035002004039000850071a410362280b0b10460180b41017198000002d000c1201d8107801d0102d207046045040001d000c1807805a0050007031541d04d04001c0d1400181c01400c50941e12040188415900211501c0402c514401d0386070b1248200b032103007000a1414500014020b00a454440c0d01424103840 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 980267077 1250 980265827 980265833
    0x301061209050109110a0b03060a06032d061d091009030c0503030f04020f10020606060f07050a0c172e0b090a09050106050621070e06030103030504090501051f0309 72
    0xc060701c480d50b00500240701c041c219041c1821840c104280fa14001c0c20800c0d4001040640d2005403402290010300c01c682c442d02d040341c220040c000c03400c44000b80c603401c003400d040361218500c090032300c1071200c140100b00d0610305922240464800d942d013142c20382c0440c081020500c0045180420220a42c400240d4600c00e410202e6409126000c000d10901c000800d000300c0b543c1d0f40c0005803007184201c134060500e06c0c80c002445290109503000b80003692151000c12003a1a00e00003510031445010403132801e0030b041d900c2e16468043d95003001d8a208000080c10701a40682aa17139a40c04020384004040c9221aa4142e1010031034528031200c540740400100ca03801086900096000383c070090810549003440d00b500401000624011a0f080d807030000005610704100c815100d04005015201d0758003002745030840300d00c80c0000c05003c00c1100b880070414440c0d503168041c42c082d50095030340a07155414071825204503030041e00140d20810011b00303040454018001c444200e0401894007080c070400702d203 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 980268327 1250 980267077 980267081
    0x212040c140d0503090405070e0306070e0a06050408030703080a0f0c0804201c06060f1511010c0e010507081209060405070801111b010b060408011a0a030f021905060f0a0e120303010612 81
    0x30710203034ac1402014140442d083d44240005101ea1048942c821101e0303036400140c60b11300c40e6101707094058001b03221800c0417a001c0c0d062030794881e51204001c0b43c0914001440e0080300c603d1054030010a4640c0705000c20300c054680c0d05071400c03c0c41c04401c0750042c3c0300710004012004030a00f40340511a01c1d207502c420400f00c3e4200000900074088181801d9444040340d8040031800034190001603055070140c00743c60414040d03e220303c1096203d101d85030009000440c2c440e40f081c80d0640c1c040c0c00410180401746050b0345824403a40008024200320b0410b45044c0d8207000d100d5000005980c1805a04110b15817002d0458407104400c00148048200d40c0e40554050080c0d00e00c0035500007808200041d0606040d0002c5d0034140c00c0382c03050020a02c8134000c10246907098080600301c140360884c03040050800740d0107400b40b003800010541a0540c0d03040001c406511622100784150008141408059001100c0302c0318941c003100c20700130700301e841100c07103a903400144502c0003080480c0d09981d541c4c450715 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 980269577 1250 980268327 980268347
    0x7030c0804060905131118190807171b0409050a0209190c1e0516120914030102070f021c052b090b040501120212040c140d050309040507 60
    0x200c29101c0c0d503100b2000d0920b214030f1180c0383c01601c407001e01e401d580c4030a00c110f0031413080e0034403480d00701868148440d1003c2001c0c94415000003c100b060038140010101010003401600d0013890090705200c1080441403c200f0081c106a0003810100b9003210460740c0003003085400d440010b212400c500700545441701d828006500120079030705004280b0900c141458440c482d844040c00115407103601110045810480303070358103421400c2100303107203441b0f02d00030b2050b016503050515004489480c0c02c40c2c84400c1c1002c04000c1203030400b04000c0000203403003601400c141107000318280001504e0f4441c00c441c8000c0021700ca202014484418190003002c40380e9a150004200c2c1c180604015186420b8906040c94500c025850590307124054401c0c03010f94190745803032403c00c0c102464070b8010f407110400b681d40100040c0d000d220300300c0360984003480144106e00403002c602460f440c2410361b0020028810034140039100307101003000800c90000840321400310542c0c00184070741e50031344212100040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 980270827 1250 980269577 980269583
    0x150a05070c0e070210050606040303021c090e070c030e0a0302030303150a080a03030b1806150d110d0b09010911071112011b030506030d090314070503100f0501120507050607030c 78
    0x1802c0103020000b0760010340000b03031401d00c00003040b10f52600001c06c84035000300d200040040e4031055003802400e0264410044074820307030401c1c004e480d464a42c1c17000d6450084402e0000266000d4141c418564088105423040e4025504065927606540200c3d86074170000780307120b110030609101c0f104940c484d905030307100a0140d101030f41c00010a91500030f010700403d0345618481d0b4081e42d110100350039034038074042c000e1000908002c0300840406510758150001141d140b605559103040c040b002101d031004004140440100140d4805804104803602d04107070029520b9603c0c06016880004000c011103207025040007030003404070081c00004100b070784002009002c41d4204a841c1c2d04a0311a400518002005070318148010f51352082030550b1440144001300002e10607140820115040540000080d041581070302c101c19200e80c086850010308003a100440c83c0e40705078400740c01d98580700302030150001d514849000c003e15141c460b595190360288501c0350b0b40001c1c1c0502018011001280d550364 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 980272077 1250 980270827 980270849
    0xc160f02030d17010e0c07140a0204110c0f06010602030f091311031603050403053103030f110a020f060c0304170618030702030d030c02070504090c14150a05070c 71
    0x31201c00c00815180280c5000d550707203180c3c1000801c1c0c0340602e00409200b410032020080c2424001c4d11024010710301c0d40c141c4599405090301c40c40143c6c480c0e0003448245050070324969565240b410b001450407020f5042165650080d10050105035400720403034074010410500b403502c4408000009000002500000081d0f03031400b84d84041350b01c10030b000355103c5d4142c01c201a4250361201403d50969008a5000780015010040800001d540c400603503100489201103e424072514400003003c149150010790205650a181403520b562000c203618030040520090180c400382070380810005d205c0f802e101403250074081020065203900300240c400429841055940c000c0301601600c2e1141010341d12103180920b19001210740e05800421a03015907405002412259401c400403801401c0803c0c0990442c042c1440006440c0c2d00c0c1c0c001c81940714042e0003100407007481c02070740c1c44003180380000050088800089004410284400383c4424101d141401c6548188502e001039500c1e41c6a000507243e50 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 980273327 1250 980272077 980272093
    0x2a03082e0503120a0e090a1d0a0204050907030201050306040e01020f0a1806050a230c1006090c0c0c2102060d02071101090503120d0207050d180e0c160f0203 69
    0x81810341030041124020b40554280890b2941400214840c410b500004036410800207941403d1080c0580e511264510000a80404031020f201860f101c00782100042d620034070710398081d8a024400c444d0480b800b5001011400d00d183c2c0003034418000100070a109560340c0f980c140c2d6002083d0111641c0603400e0001d1176482c65034500c09040810b82c03040d410100584c3c0c110100740c80e4007d01c2254004074003920703140c00821a90b00c60182c01d0b03d00e0b00410701500c1003403004699009003000442c4100f403d2800101e10141040d01c80c41c00c4480160902e000c0250101603600420080d01200c000d4a01c0034183d02240e030f10b0310100070749500c98a20025045980044ea40c00c82c0b00c450b60280141500c02d1910300790010307509004652000307480c05401d600da000228400032034060710340240b01c0c2e80000d200c05420441d003a2501400c08018080c40c80200d05528400350500c020b0800800c0900120000ca842c1401c1c038540c0000320303010704d2050130307240340d840302c60780052001e4070700212007847d801000c441d810 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 980274577 1250 980273327 980273401
    0x60209060c1f0c0e01081f030203161d1e04031704060f0b03060402100e0d0807080408123f0411130915091b14012a0308 53
    0x1031045125a000d5092038200b036414030342e101300020511088142c4d030f24800c45e1680c250a00c00c1c8007d09000d003586c2e000d66180000185c4051160503031030f0915084183c01207143c90400ca049408202210382910301c090204002000703500c0c40c5c40007062503805600304650325860150784000b04000c500348124050030400c810460b8a0300503603134808170710209103e000219024503036a000c0a0350000d40c400380c01681d0380d40f8188580543c000d0081c00900204414000f034582c24801e41c0403140c240c1e0020320009090003000810401a17400c0031500040a1900100d128107198212450300c0135a003031000d12014031401d800000400d101c44615aa95849a04003842c3c02071144405019190140400241040e8113840070b00c0741011145d08600e06145c018607010306080180350301e0b101180c00e054500f01184884003616000341c09400c01c44948045040020000342c001c0078802002c0551905112203c3c126084c41100c0304a65035050420201a031581c403040041340112465002c0c074040180c10603051 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 980275827 1250 980274577 980274613
    0xc070f0602090a06020f1f061703070b01050d17282d090b03180307030503090106050d021c21030b0f190b0a1707050a090905060d060209060c 62
    0x140d200700721000390f046592a00c059071280000307205414150042c40d0030242c032045c080180c1901204442c40094200d46501b401042d00a45511170441c0d17620210341c01003008003c40405015003401c0310203541e0041640e4410440b0b10074518003c0c072240010a0300d4036513010300c400c3c000341c6043c20402120401c000d010020300c00d828580b8440300019864400f00b03018079a00fa51140304060544d01e1080741410b2140a40065202509841081400c00b1130500700d400c0a00242c0340051096a03010340d6030401c108200d0940303002e500681e1040c15024510b1006076150b0183d2410541d08032902c41243e0380c14207160782e1500070348503080b2800344995858180c2a5259000c4048a101164240d000800384000d126086d1405156444409020729080c4428542034010700980c40e29407804031024440d403203808140401c1501c908001c14000701d4000007142e001000c01c80909007900c4100305034903060340044e1244150210280c509035000904050781d88400c1c003201e4002b52644102c2d040ca280c04030742900 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 980277077 1250 980275827 980275837
    0x203160305160804020307050a120b070203091c0f140703030201061401080117160b04141008010909080403050601030b06090a05090a02012609010e010b04061a030c070f0602 76
    0x2021458500811040034000d100d10340c091801003000d0030005030010000e640f020006001a640f502c540000022a942c5111440c0040c0041c076100354158021480c01c4445054050200d100350b41042c00181c585854121508030211650822a2481012410804139004e00c42501600b5800802c603042030f00b0303000003a9201141c0c03081c0e00810141342d43d640c4c100401d9080104043c002048030004100c1d059545404140d6441ca04045c5c0b1030f00c01016000b0034010103d075100c60034071f50004c101040b01070601c2c8404003082d0381c103031450a100481440014144141400786c1c200055031014218140540241650082c5a10004458155071a420309110900040314518031440c0c4483c005140d000c924000c4038041c010510080c151600b076580195446803881c0c0f8800d40b60303a400844044110042028140038844850001850080241006007560045401c550042c1d0030720104014001c803034088140900201100039849481d41c07922481207110b50703032000d80800744818082007805042c1c2c0c0142 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 980278327 1250 980277077 980277091
    0x3070602070f08030306090f0c040e040b04212708031b1e071503020c252c070c08030106090603062c0601090f140307090b060412060b0d03030203 64
    0x2c900355541d41901030faa03200440700d20b9001116440404d00d002c045400c030507081a2800251401c0c141c4031840100391020484051300c0c4c9075660010f200a0000328160705030348040c3c24036480851904410060100ea48411440344112032401c800d01080b6000b02c00d04000e0003540c0c0c01d5030394a4601e06400b0310000703090402c0114501503001200c010381041550142d40c614000050912036140c040a03103413001480490505154003003081e10741ca21402d0010320701e0b480450388520f04080c42d003448003100c6da01c141c122019503e04004030011500405100f4a4080c020068510b1241c3d507200c8110351654100f00c00400081c0c1c08400480e1070f641102140c02030f02c4266070200440d565a000608200444110700b4008070300c5481800039100d8580c035a41e9002e00f060422007041592000c04c0910142258000582c10740304840300001031805100c00e034001d14100c68240139904401000940a01c114072650710b065181d1364501040242c01d400260040d0001026900306840c00c1c00c0260196004841039 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 980279577 1250 980278327 980278349
    0x20115090b030d030c022805150c120907031a0108061308160303060b030705040515031605070c031e03030c09140f04090803010b1909032f0307060207 66
    0x20800044501c20350741e680c2801401010740c54070785a8140c009241e0640204110700a6140d10488203185920010325038546000701030b81103955080c070606244842010800440780c00050060a4100384250380c101d8428143c0920380351a01c8928900d13041c065840201989800014002004501d11246040310b505c8000d0320566030721715810081034807603524020803281c01840310f0ba00410182110005a5109040000f900d5840b070400e0446c0c0c0d0000c8504500041000600f48003d091090700071b5210000740a44504504220003410100044240c20004021001c105036050012501d0400700560b001210407090942e01d01c1d10401c040004c0805501190801e882c40500720320071803503101240c0c80702822075441d0a40d0010440c00c5012000269481601c1c0c40604001c00c0311100114001c000350a01c40303689029280c8603401803085020b03446d0500c40c184004002040460031000b441180c0381311400c6640c0c040001480e4041400145650144500b810105051341c0018a12083e18103803030203 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 980280827 1250 980279577 980279579
    0x1e0b03030c0d0c03140705030304081b1f0b04050c0a080c0f12070e010c030e1e130204050f1f142502012a08070f02090a0219050403050a1b0510020115 66
    0x170030322281c402d144005216900800c0028003143c2080c01502d0103002200900baa51104804134a103090740700f21118410010040c040c0ca102a940e04c110303d152442500c0030f018920748142c0e00c260034041c012900d418482000c000844c91000740c1f08507850f90246082d455200c0010200380d000c1150210380c4000801d4220203812060342c050300b5543c03903156042d500c44214045107010310040c2e0072071880041116481c0c0f00c401d139075550b4010540910103a400001030301c5914040802c68800030841109010f440c2059003080c241845090301d100310300203030900034041e81e603519100c0c1d2507114400c00641c00002081454100701e04101e0b50707180c4e45000741d803014004454003140f04120641c17011901140403e40c1a001d00003142d03800900586800b0710340f07038005040c080c0c0220b000a4022550078018943c006101d010000403250502141502860403c0c141390855480640e100010040540100c0140071048400710007126500c000d010064a0110085c1c1480c10283c00780c1072000010100200c000701c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 980282077 1250 980280827 980280857
    0x4200d1b050c250b040b031009090506040813050604320d0f0c03060c020610080307020105040905040f060f020c010518070612021303030c0201020d031e0b03030c0d0c03 74
    0x1552141c100301c50183c00001e100d07181036408205403c0f4004803550300341e8400544c41c0c24a80c0980002e15004007501d55a00c0c04000440e118141a0002407480d490940d0350804914002201540640e001142650b40d000d030340c4a00340c51150325480168084000100802d503031080c0b0342450541c0e55100891516494600c22504d4010100b0241e250041107014060000c9186081d04080403406059041640758403034464400b44c034400c400c0c41001d640303e50188004c41008608a100070b06000021b1030820706643d000910520842c4100c0c031000d074940d40030500788040742540248955124100300076450f0f02040740c034084e42103a0951080e039481c2c0300c000340012800e071401c01180c11a10014005440c1800c4096aa0341005201c00360403650902003c0c06c3c80d810610060b0256010351a5501000c00c0d61000a141c0090300e151501010b0418010494000c988075040200400b00c01c40400c1004103d00400d11714010038004910520600d98030804054001c40e00700300351401b0750b581706900b00500b1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 980283327 1250 980282077 980282087
    0x7140a0606090b011704150f091203051b18090702100c020633010c1a07120f0b010e010e032e05010b0717130b0a031b180504200d1b 58
    0x2100901031958070882c144c040c4503558042232505006410003d0100043c2d190f60070881041c20040000c250703140c007800821a02803502a1201d003525070558502402c0c1c0344d40c000c00c01c05406206003c0c0810401281c0514001d101580c8807100c030040411030600c41400003580d41c84d082e590300b9040b000e5a041c030303c800e014042040101003001c1c2100303143d181642c001102c141c19030581c2503900701415201c2c034000035080340700280148607554400d010080d01a150351f08070f03001504410f18551a210b118401640c2083c400c203440d401c24201004002c1c046e40c0407030b051130440070700307511800c1702c10404040c0144a4400d8002005000e641040b00b40e80380d42c180c000c107104101c0c1c0941102d180b10500c200641071035005101e20070452a425252581d13b44900080e84c000307010002c04292142e0301181c4640b10442a27a0840301a460102018a00808156107400d80e0b4080c0b41e00681e00c80d0107980580141d00724401d00c80c2215040d2995070141201004020000942d04a42070711285081206031440b907 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 980284577 1250 980283327 980283331
    0x10030b2502071e0605071106070b0a0b010e09070f0c03051c2702130203060f0603010b030a0507090524250c0f0b091207150c0209090703030507140a0606090b0117 71
    0x54490310310703014442d121000491080500b0072352000e4100000e20010319a405c0072402400360400c0407640c012488000741c142c7d10115038440c01170140304204100658803100c0070049080d00e040c0100c01d00d02504041304d2314824844075195a0300304203805204003099030301c201c1c50350920342a50442ea0f040d01507101002d01c41c294002e50b00c0501000c0c00c140100b2960300031504800000d0034805c401a130700d000304000d508240e21010740241c0c0401081680f009501440d07a2001c41c0341f1305100c01e24100310006440600149601c0d20071b100e03940c1c00f00400100300d401c682c1010310010350905a00c4040c80c5101c090420448104c07841045503000003010a1001680310964085c4441e240c00d050354182403015101c2011040c560501c509900081c62280003103a4204110003a13031076041c44104c50061100c0400040c0c0402c856034040c90040001c0380d404800d94556a0307000b0b1441440e1707058850101d14001d0a80b0001c1d004a141c0f000008540c240d41d80182800c03c42a2540c0c40301c091100c80c0d0038400c0e902 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 980285827 1250 980284577 980284589
    0x1216020312040303080c21010e2706010603180c0f050a0608070c02040f090c090f0c0e030309043c0e030703120b04020d1802010e0910030b2502071e 65
    0x1400707000c1038032292140b000d4000f009a01e18002290040d100e450307e11490207902941840c991102880101c030004050703d880141090042c0e1440014a00c0995491605229900030950345e00d20704178003003a01a283c2201039800c50801d5244640700c4106d01407048031482010b10803045d10100044e85809100710314421034040d07c03015040b256079000c4c800640b00800d8400400381c0d45031600350004405280302d030090559480005113002100484c138044070903050401c8140501c4a040115556000040743c40609c03003968007140d1981107060b02d60030b01142804524101c100d1011089449010200410001d080e2010a0007626013544801d5100c2c450500c015000502e50380b03880b101030381c250708480302039072000c0c1005142074070201282d811182111206000250503402100035581e021210510006040740c0001190030040190040c0c050207210080c1032071618400240c030311101740181300c0a82c440c0744c688050350850310b00094030f03450103014025100c0c40b03241071101e034420a14441820341d46 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 980287077 1250 980285827 980285837
    0x21030b01080103050a03050325020c1e09040f0501060b0a0809010c2105180f0a02090105010f0c170403080708030a1a03151302190f090908030f091216020312040303 72
    0x2086d10b0441e402d9000425406c001003118899070000f07800050340300300c3c5590540c06020300c00707040000c11103020b910f0b010b00c8510201000c5402a00d944190702c0340d41165001009161810310303440e0442c05850a07501c094980d00000c905550100e0704092100d11410014000b0498810740c2032003070315640036007a20340c401c0111000d109045070255070300031a00711141200b0b0200204003001001d14294191042002c2500560782182c210b003485800c2c180504001d0900640040c007440c4d004200c28800c0002600e100051740c4050350f502d10400c01c13a00030390f8010003500d5480505040a0720164400e80710042880d1800340d418105127011507181c011440028040d1000804903200d00c5420700e0003501941e00c050b51480c4040050391850884103200160442c00e41045140005003198041d041d40040c0400381460507500c0002c014808599100202c858100030903100c0082c041e16101500c501c0d0b13440e900300010340f603105400c07115032032107407c9c4220219581d41d81005460007940c0641c1c0f0004000c11 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 980288327 1250 980287077 980287093
    0x103141227030d02071a03250306030804090e0d030b100f03180309031202070308040b0c1908042d1412010516120c080a0c0c21030b0108010305 63
    0x21039180c00c000646144400d50544259141d00180c1060140044100941c1c4100303c20081041030f18040c0058402c1114103e00314075194040b45250f1a41041c1c040301281d070700703803901d0300e4034002e510401c061078201728802d84503526600400020424100900024805c22449000d114442d00403502c012101a1003000c1c41c81c0d07110001d440c101c0302d029001d420f0581380c1c0780e00c0710400c44442c42c030f00c03e560007581d45659039441c50421015241203d0303080c2085400024090000c10007a03401c4800301c842d0700040c02c1d560040c0040881c24074018400e60b0302003080400c3c10340c2c180209400a0416600500c984d000310035840000c0c55010800c10203540007001403410b0402c000303035151030700920b265805005c61240e100081c07500f5003154011030f000c0554000343d008200b011740e480b0303003410100b14480d18100320000d044680504500b0000b410701e240d8a07125003858540e14031640100b480154013000c50201303000b02e40e42ca11a507d107080d07540c00001b86480b006074087c3d80310b115100c0c1225000b8018000392 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 980289577 1250 980288327 980288347
    0x110114190c020a1b0b07050307121403060607060e01241d0f041e0803090c1c12031508010b150313060b03032505072c1806090601031412 60
    0xa0101380b07101114020110500080080040b0001d000191040010b5a0750f260149403103010101c10a4044082040c03100101c0d060300b00c03001c00c503a04890300321592030325003000c0d291101c0030342030701c4403515080c3d405c12420794180c03030a0000c080002501c990b815002c680c1c880d802155500200d01319001c1d00881140810710141100550f10b4121380201440d04a606a0204c00708180546820407a41081c0000400c0030342d0000b4000550a2001200d090300719196458511103c085604400341c481c41c49005002c00d06800703944070410b81030300c400043c1951566060b410303009164440392180506252414410448032080842c0d105490001c240710954142e034841c2402401840315481d0940700400c950008044011480e040302289103500484110b4586070242c01d1415560210780f2070401c10750040c000f00303104074036039003c0c41924841c440180d507500d1031603c8000308510f1040c0c25007da4024041c8440340441d0040c140e1b8000c1c5050b10380002e89070380007070b0385400407035103507074407400900450f000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 980290827 1250 980289577 980289593
    0x3151234170c0409030c06060b0f0a082e09111e0706090813051309021e03071806060813120509012606040b0405012103110114190c020a 60
    0x110401c060221400060010049400c03100659000c1e404200101504000c100b11402404090112420300c075003000c410084280711030007899400300520911a00003a540108a001c0d00010741d07090b140026502c26415031003410050902400342d100307050440000142048030101c4004103080100c2000d42d122040690406801000048660f581c480f40082d000c2900c80e03018060324a840d1065a042a18180c10454210000403410420500785010340c00035175110921444000c0d2400c80032103100059000090410741c03541c0000d0000640503558481036045684080280c078180c4d12040703441d850f00309c408040380040010003001d400c1001c0c1501c07034181c8980c018150880c81810300a0b40d56043c881046440c50310b10500d980010310340c40030000180b80c203014200d9400390a440400c01e40d4100b801c2d4401c207041030b130035011465103900704043c101481005500d4031800007000801650380d119540c003510303050549a4540c80e0090706484810703e02075120320001d034102030700140031000e02c40d954012 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 980292077 1250 980290827 980290859
    0x2404140f07021002030a02091c0b1603020909100503010b0108010b040303050d06030519020301110f0f03060f060406091505030717061c0b101e060503151234 69
    0x30860041c0801d08000b030f10306001030350040041030380140e103400d80c000c14041c21440255440c44244e10f0b007030001e0040b0b10b06e4004c554001c0b01d40300d24040400508501a00a440380200351900003140c00e0420a05091000100080d00d100310000d00481c51110300450300b100080c001e0704d2064808000402c0000d0050700180b01015510384041a207a940c1d0f1189030801100801041e11940001c495204615080c403511103090b22803c0c87c1410483c0180c0b802c510f9005c0d032060003c042000002280060359200c94183c000707400104019503458503200001c001c140c6034481cbe100c2c0034040440c14103500d0b000d00190b9106400c103548142c8042003449c511002c407240078104030740050008020322007505c90303246882059405000780d151b560614040c2000081c4c607a030b1004400c400d20320400181c0000e29052001125068075040e0703200e44070608c0c2d859400210b140340035445214500f9000620b40041140701c450003907601e110f14100f68288030101100c00d82003089040317070721100060180c49106d101d442 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 980293327 1250 980292077 980292091
    0x712020918010803031006020714120703020d050d0f0305060f091302090106180906030c0b030a0e0304120201080a0605011b031206080105040c08070e07030f142404140f 74
    0x401c1140c0c4210300440311034402e0b08107808603000081000303c0520a60740d03582c01031440c0e00c02031a400d07291080240000202480303c1c0c2c1300701a01c594078800b19900f00540c10147d60000c1850030860030610f8882c2c0d82d401030040d4200441d0b40d280c440180780740a482003510415001d0b22003181d409031202006a1a00001c00c501c84c8920074403070003800b580711002100e0180c2090f489818440d01c240f0a51250540700d40e1200c411036060400500000c1c40b405101000c580708404840e0301c035100c03940c503c1d0152003a07900ea403019120205000441d07404440801c07660038001c1c0c84509064846d00c0d059400c2d030700c15000c0d0701d0101760401d040001e6241d40304402003000e80285411030200c00042417000a49483d58081da035140c0d1960184010b1001210030200108a1407004080007481d00d00381c035590030801098203052591310000407840610942042032660606070f40301d846454100c480b40c105070406202042d40c080100c00780d017105d00b410b101b00b00064424224550403660b41050803504800010706031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 980294577 1250 980293327 980293339
    0x2090609091c1d190306020307021002070b0105040c05160201050f0d06030b180a05060c0f04030f030f0e060f0d0e16060806131a1504120f060c050307120209 69
    0x35209001c201c40c840000c2080c0b5946040da056841c0c911010350304007041c0c220384600da41c8444d00e100b8031070302c9400341c04036540604003580725660700c0b03402d0341000d81c1010b140345071600001d946010800c030115900d0595804950821105811030b00480e00b41c01600c101e02c19103480610b01034007660266014200d9140152000ca10701b12080740a9019101c45901c111101d805800c203012006000c0441110703030891101c0148181100e646a56030384a40141203680031800024002d800c0c111104100c50142d5000441c8070010f0215203002001540759015600000e10000c200e01924034100c3c08448084040c400e04c10300f01031b2440040401014220b281500f10b200388050100d003200c2c031a070b01e8070090039039031a281aa441d011091020300c00091050751056441c101e00305030826418001001c00d03140c00c1c0c400700248840e14a41006d1417080b074000004011951a103001081490717000101254821842407203d4520034000362035a00003a01c843d408107280c60580300c40341c241503001d440080787c01010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 980295827 1250 980294577 980294593
    0xc041818030e0411040e09010c030507090312051b160b090a0e0a06031209080d02060f010e06031608010e0705030c09071103040b0a110d021626010c0903020a0b070209060909 76
    0x1c44e10695010750301405c440aa0707481008801c0d5401c0c07040301e103040c410f414280b000b4a4a0200204201c41070b00005151420703107040c070811540b0038003e17103141c112002e10172120705801c1d4002030340d240a840710610f42c8201c4500d001ca165403000c011798400240140c4200c5085060403116900c0010050159092a0b0395290000c0410b010068402000c0099203840e40028180115941003c50941800c015503100800340040d44c0c03404000541100c13201121030700a0b03200e0b00002401c1001e10000540010300c40080403a4404040d4000e25070b82019074101c1d26a580c0c0c9009240d107540c40803021950211034040000c0c403517401110301400030180d10080d40d24103622500b001407144c021035034400010385454010410703450304101c02c00d8072054030700040807902c4155442526602c10f034080c2400103c000410808292880110206e400c1c4460f802401024005d070001410150140701c140d101d1024104c0c005101c0c2030750012940895000b9040070895508c400902040070400741015071203105004c0c2c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 980297077 1250 980295827 980295851
    0x12060a0b01022109280303030e340e010305070b09030a0b041b05060304201801030b0402010314010602100207031103070c170f0a02090417030c041818030e04 69
    0x4403a10040d420000280d1642d0100003442000f100c0400b041d120f0410511202c03480304481700e407035404caa84c50703d40400d8060845236040d040c651004540e41080e502c1d0010540e0300d00c018000d051004540031042c0903c555501c0b464881c1410a00c0050520f0b007203808144050441540100700041c80a0300300d030300c0ba01a0356070711081c05004803801d032002c0700001c0e540001c03005c4040c15240102030031603031581181855151240940760303250000b0083c018101440425446414081407880942d2141407402e60f580d0900345201101190101d00007031600791000c00b1989444090f5060b5480740e401480744003100c0e05207030001d41c44400c00740c0030721440d42e41c11a1800d04c10001862038510030504020520310b80141800caa00d0888042c84450b00060031003a010701e0001090003d1680403903408200c1d40751401d1030242200304440b219281a030000c200421001d902c0020304c2250f007a0303012006000c01d581d01c1c1c07100b200c0740f0f42000000d001c0901a01000320303105003c0b11200712070082c00054030541d424 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 980298327 1250 980297077 980297113
    0xf0111070b040e010605120f060103110409090b0c163002010911041107030e0f12030c0d020604031403042112061508010b160512031512060a0b0102 65
    0x41d006070001c490000302403240c6402c068000d40103208a062807410600c0d040560b011300100181a800801c04940c0014180c0e8032a80044031580380c44540c16a1740d0b03440b1501034014041c8160156503c1c0b19a00200700306820a0080b500390035440b156268691810341d0721451000c101801e5041e428082408a82c2441c5207070742241c960708107a03000045d4407441c86c0303002030642140c8003180d80b02d285007189981c0303101d01c88421a0485645440e2401217070440000007544690600d200540040c2d40705468428900b00000400503007036070b00211105080c92540032681c0d001c04660050001e0580030101c101c0c1d045140c05103802511403000d8441030840b254840c0c502d01611001e407800940658a00303414013040d48a81c6c0050480240d207103101049510000e061044103101d080d40c0764200040c402d009280c3c084c03000d00307115031040c1961101421200030003d5600140c9910000310880d04411000b0b00e050841e60091194007000b42075140d5403412914010842081d8880c1540100c1e142410500038070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 980299577 1250 980298327 980298329
    0x12030a0b041a1c080f0d020403050d210504120309050102070611130b0c120717030c040911031605031003020d050604050127060522120807050a09050f011107 69
    0xc040d5240b400051502004903004074407100306004110240e09a0220b0b40240440e0005060601c50603529802529540000c0c4156070028010b8004c002d10a1074190703010786990881180040226103030503c0040c048121342d002e880041103040c901031466945d600a0304034041c241e000d0400103043c401039444d1350098030300031055100111000510090003004101c0d822014050286031307541412081c2200c0c41c2c0d54000380c1c603803034422103020610b00c2c10480ca00040540520120300150384909090000d05040d8015000d00a0010308151000c002030b0040416a44150300080310031503008090042a5403d07840503001d420903202060010015880380341207242040e201e41c0040100d0301e0903013003560071144e0300002040107140c15001840b1040c1e5044c030340040c0541007030b00011561103c1d60030001c0c1e07805144a14100b1100740c8500f0301480b84c6042c0f50403d822180d00c8002d000ea0b142002240c8030300c217011740e280218010724014400c40c141004004150755040c1001ca00b00071381c02440c01e14001c1a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 980300827 1250 980299577 980299601
    0x50105040c180c02070e1008071202030d081909050f150a0c09060f050c0115080a0b060102120f0915190f020a02092a04140901051212030a0b04 63
    0x10254040100e140c022502c41d0031074801c1c2904210006201c40c0c001d4641075540f20f0703900c08880c120046002d440c18200928003c0142c0802c80e0a1243c0e500c503016100117182e6005d07803090041842104080e0b0151649501c0788a1480399850b5104000304c00304001c1c6070020042daaa4841c1300d0303228103140c0c2c0402c140403440628600c945401c7c540130070031b901900c1160707881c81d0410100e036000f0092190000d058a088403400c0c1031440d1580e108280d207e0050059200340844982d501000060f41030003c58202c92440c0915030341e080ba40c0d00c3c0001a0fa1340c401c20000e06180703401c100041003011000c5006042e10710303802003114102c00600700d6070042a410046000358501c1304844004c9210b80c01000d44400459980003030005442a0340000e485848000c007883c0c48400c550781103440c590541a803c098014a508610340c0341c41d220800301204a101000e124010303500c1c44008200340c41c1c6a91403048002180e07000381f001024225614500d41c1000e03200c10601d07500ca42d14a262070381c9500842012100c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 980302077 1250 980300827 980300843
    0xb06010c03090305060a1d03131502030d05040c090e0c100f02010b30060c0a030f0e0d091d10140604270f09022b0218071e2a05010504 59
    0x4000040c04070030151030b84000700359401001201444603081c2c10384000c0701e440400c500002a181807040e801c1d4401c84dc036952546240c5410401001005494072060352581c100401c007400300400c0030365581600034041079005840d00124034030144a12510383c40342003d8400440c1c60b10922010030050f440205110f000102c0e078200102824000c0100a6403070700c00c0350011b02e1a800e2004080215125402049003016290b071060500720010b0b0b00700c10b10544c2d031041203942100d02c0300702c0104910307a18050030301140020191003070f41c9074006070614042c072100007450200324074001184084042e016101d136000001400b00091061005a0500100c04180c1e4400c10200e00001408100d400ba1107884172614a0281050096103441004204101c03000034114130695998100e01a00d45000310025440b144030302601d007075100e034807040e00d000307a56585824070020b03103181240c0070002c200711074000003500c404015450301c05910b40840c0d000310009010401c42c155a21a10b09650040b201910054 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 980303327 1250 980302077 980302091
    0xf03010f053c04060314010c0801061d120f0f0f120a0503040f2a031109060306190204150c020102120f040e04020402090a03050d0e04090b06010c03090305060a 70
    0x105001500c02c1c00c030b04510350010800310190300710001e900040c0100c0940a1200b4601d50076036141d56001030061500000310512245c24400c42c140640104e09080c000600c0c01c40001841501803045104084010002013050509003424890810305100118101c0d02c14458054410401800003541e68135140b000b03401941c261800032403404401440c0e031195620100201814294040150382e00582e1100c04802c0380c0442c0c4c2404c4024082541400400080315515024810604d0416104072440358007007000f030b0400d0004000341e2035411a242901038001d1000240b55104292403009096903045c0011b08060301d41c800e035141a80d000c482e0f00c000c6602c103031000c019580c0403c0380700010756040140b0745c60010503d00c00000c0380101e2060b03644d140b00060101d802c541d11901520748458016005880d1565079040140d5074204661600d0045410a10045100d04250007404011504400111446d4407a0001159808008034040d010440307c0380010000600a003c428040c00381000003160702 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 980304577 1250 980303327 980303329
    0x60d050c0d1b0903020f010221090f040603020114070311030d0603051b061b03370309023d03020c1006120809130603080d0b0f031e030f03010f05 64
    0x100c008260b00c9010680080c0a404419407100700e2905a0f981501e105802d0416600140e140c48464201280e0700701c1c0c0000526a1202400b000c0c01d0603900446a070a04440d082c810b12048808500000c1e0015144494500d2000700402c0185a83c9110345000c0202043c0c1c0d9003128255085034041000d91926510f040017400810403002c890f2880c0c000020742444c4150002450a1007a88101c20391052354a542c0c0020b403009100392891401d4813844205641084d500031034400304207125145c010b054448803900c80a11a215200d007080d40500300820380044100031303030f179079407032401d08040d0f10350403070182e80401c4166903000d00700f00c03d09442c0582c40c3e0311406100c604042c680504106410300c0c0c450200458600d40c60f907460640e07000b071044c9503140000d1000c1064481d400400e848260f007882400410000301900400d440104001c0411206a85508010301c01d000240010360541c40a076400c0e003440c40c444421821094144e003142e1500e01042a01c5269400981c4155148416600c080040b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 980305827 1250 980304577 980304581
    0x9060403050627060f061002010f0f0f1b0c080702040608010207030c06060b2a03070206040f0801050a020f0a0807050c101a06040b0d0c0513090c0e04020f07060b060d050c0d 76
    0x85290280c013411035072504200101246400409080c03180c503800d048134450ba0f0003075215132680000c201090144d41d034000c6225000d4050300d822842101c3c44c0408140189840d4000e46020b800f00399200b12561200e52904c4602d604003640580c1d201b5601d860004100001f48001c03c9054403a4031910184840c0b41801c0007110100c0d40030340c11902c020000598109031501d4031000d040c2080300c0403120005000203061460058000094002200140100c0c009030006103c00444205030001d200d0707030b82c80c02252360a90240e1101140d21403800d01c2400c0c0a0760054944940c041110f2a2441c10220103034041c600d0321000f650150382080e035540f20300c102ca81c0b20444080c14041c003964600d240600d0841d41941c1407207102c0c0407400191b80d456141c103905102d2000c84042654031082c8a4002c1d8071460304000070020f450151002c00c03c0001c403048030781803d009864107102d846003c1070401d4001e03200c5401824461203050780c007000400804000741020310070a070040003030a80c2551200104860101 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 980307077 1250 980305827 980305891
    0x9020d09060e0c18090705030307150608030405010e0919180201080114010e0d0804031211010c030908041202010e040e0618060108070b0d150b09130b060708090604030506 75
    0x4603080720300480d2141d15001302c40c1c0210a0103115840659513a401d0403410110b250304296414000040c000c8140b0812003408405120b00c0e42c0200165642d500c1125500e202d5441a6408922840c09004142ca0950411580300580c1d107514014201181408403c44010402194108260300d62000643d644915014054400092003a00c80b440580011746100301d00341034030340302d10780554000c01004611400d643c004e561108128135011201364000d002441000441c0d811036280c1100140850711a00406510542080d001403405040c10000e01e2083e449103170607414080e580012040a03101d91154a11080c2c000025010500b880c51001c1c00504006840c000c542c1d0002005002c0c1034400708401d8122800e185450b9500c030000c42182014189500050040c4007448030001040101d09005083d2031303c0440d40140d590340710603042400c4a07000d40300250040b0081c001c060004850000410701c501d8000c120700d00b090b6496560034540030b01154001e4501035510422000000c80b034050340 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 980308327 1250 980307077 980307101
    0x5090d0c1404110d0221191a0a090b010311040e09060f040803151305040506040c0b0705030405120c0a181109031c0e03070303020a02091006081f09020d0906 69
    0x1001031594401c284189019214540442c1540002c20140c0010110480003c6c030a240c10348450b82c2ca01800c0440c0c88050398400100e19a00701162800d42c909800329100724075400807c09810f441c20b008200c2c5c0188804c440c00c42c1031680d5549900600703043c41c0041c000801a0148408031403070002016410840e0140455850150300c4044c0301c000360044059942c0001501822196064001c000801011010b03142e5600145000305020a100000c0360340b6200ea4003822203040015518180041540304d1440054190b80041c4018071180c5081c0284d451080050412200c00d0100440003844110035a400802e003015042d410305518001c6004120140003003504541c00c04c071031907000ca912025600c0480380261003800054006d540034203008120400c01808460242e078581c90080d50b0b45411020a85c4034900386000070700c141e41c2c1d01c3c0002c800e0b2200c40d6170300600b0381c480d141030f08044c010761600c0201303420120750301040340c09070b52000c0c1c02d0001d0140307404114482281011012194ac4c0c803a00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 980309577 1250 980308327 980308331
    0xe0a03050723030a0f030306030c080a3e0f031c0e0d020f040c030e0106060302120c0301030f030813391a0d0603020301020a0203071e03020d0f05090d0c1404 69
    0x102c0401ea8001c40e003590120340003030078903a003200f07503150031030082c40d0942005003540d210b10700104803c000054200200c601c86c135010f41c06501e906221841154242c2c0ca072401c081c3e9040e9603080c4c02c800e1120a006145005001c42c00c600024400003406d005892001611508140480200c1554000c0748141e00000a42c0c0b0108a02501e0300031481d299404081c0a01030b60300c40c0080e0002c2c5100342d1210f4820441c040c000c01142d51a01030040c06544100b5411000d03481100100b03841452a070b04880c102d0358000d599a4034500da40d5002d0703421880061229401210888010000c00c0b42c206000410b44c01d20155036000a00a903414644c0039000400f0b40e41c2400490400e01036036084116940e204070618035143c0d180e5100c0d886120103171055400003501940040390710110f0540000140210602c0380310a0407881c0c80d00d2040300c0d0f03240c0c03080c90080e0040c1d000d001c805007298007560601005040502d003041c40c0c00840f00c0807e00e20701000c81c080318443e1030036004000000c001c1100a49551080b207003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 980310827 1250 980309577 980309639
    0xd0c090f0608040809271006090e0a09051005010e04031e080619051f1b030f140405090f091605060720031603060605150304120e0a030507 61
    0x82c1465401400200105400100d00070282d444903144803918441d41c00d00084840c2c1e58600b400300c1502030761a60100a54510042142c5014040c44420340e03108013100c0c01e8965035011217001800f42a0302c140c402d070150b001d03040d02e00c0c800e80c0540d44c040d11124503844070318105850014100f0001c0000703000f282c824907042203010782d84032400702e81100d000c0381c0e007080382e004211500310480c01c00d601142d400784008001e103010310800203000040507040d46403000c0d6405035405e00184211b04100080000700740603251000305004811519907420900c1296050a4803500400c03100b0a007034400540c019103500c2049070800c0308004012020804c8450b20410710718160201c0c0e05406041c0000f015540d032081d801c003242111101501c68100c00a044032140b022401c500ba4030004140416034103582800c102040c0c504151003560f0b00c0080000c413441c50b55496031907944111045903100010418103916048555036004005005140a4405802e10a00e420b000c5051518420a841101174400031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 980312077 1250 980310827 980310839
    0x60902010f0516031d10110c0a05060a03020304060b130911030313180e161d01120809030c040e0f010b0a050306040206070302010e030703110d020a02060306060a0309080d0c090f 78
    0x140b0104813503050415070159a480e91074400300681090215070418111810360811561101c081004030101c0420342c0e1055103000c3c28055450180d02500b500000b0804c9640021407090303000b10f5109016160000d4102d0008001400010b046140c0c0c40225448000c01c01c03c2c8511441c0f841000304044008500d4900c0791503080c01c0d001614801d010080c8114210100152402d8000c0c0c20000d200303901742c8032181c510011038007038130140c0d014428081e40400c24501c1d0078a018421141038035565000140e42d00c2c41da42e5813000320f501880005405014019040400e9140d0303008004800c1a0400600402004400e0751421074040e19041d0744580d106440030041c9880120390700c1d40042c4c054580d95550081e500f401d03405413079152041e00345848001105024940d110210060800000007a03c4190804030400c0ba034641420402035408081007010a039980b0f4004000d000900803400e01141e024003946402801d43c00082c4092882364403028900c20309036110300941e000d06140a4910300c0e1605290f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 980313327 1250 980312077 980312107
    0x2070b07091404090212010e01060611070f1502160e070e0405100509090a0b010b030720121c050a0e0115060e0d02120d03060f050d0314030a0204050d060902010f05 72
    0xa0300443d5984010402d54941c50022000050306c440280074103114103510900902887c0708040001c1e44030001402c2c200d00124076103080700c2034042d001041c24141b00c13808100302c41181c030a40561080c04000c0141b40110304c2140000c00607070210940d1072070302c000003030144c0da00c1700641da11451410041048804c5800080c4054030820b41d00d001c0603580c0c00800c1c615041c000d810240078000c620000240303030400c0f02e00461003500107550703140f00d42e61948481800d04800403401c1e00d0315000740c82c0e4481c211920402030084119406c0c40801e184030b081c021a000c4032403c2da02c00c103885440d40500c0e41c01807424000d410700300400b401c4903001185804c2d0000d00e09185184100d1240e545000d03004255500d04171030102c4c801c440c5040e10440325010340068002c105d14407a828007103a10304000602440c10390341035244a5015119040c078100801c008843c2d6601c01852041c60079801d20000c13585840311241a00a00e211740e00000752545607000250101c2d0303205000c481000745c20408292203150f90 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 980314577 1250 980313327 980313359
    0x9070e130e0703150603080304050303060411040e0402090a1b0504140102030712211d01060f0803070305031b0403081b030304080415020106050301020a0507060e030306092202030a030302070b0709 86
    0x1000480c100e01c90400a200085c03d00f070fa1025103205408400d10007480400b000560080c039003180c04000d5041d060082c4002801244100d410128500f8005000b5007807001d03119910254811000406400c103015061000401c0d0b00c07003070b0007e5004102030240c01100c03668805924070900041d81422141e0381e41d008450581180642000400b11410109945a8944c0d01d43d00040d4103090020b41440000c1305040c03615030b0300d04505582440c4001955811221584041d100c411000c6c40c500140b40e18180e403680d001900028400b0103441111029181e640080c1000d10710504c40b00380d40358810403103021301d144541010001ca4000f0800d000c0000c4006048030100e58a055000a000000c11011390041039103a0000780c242d4000146c001d0840e501500401b01a849070314104582c070a091081e981c1c0f80004c0b20040d0300b01c0b010740080303502100c010380310020180c84140981414451907020900f4040907200807404a40c010070014104602c5000060740000e00380f0307124185071300d4030640100310604 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 980315827 1250 980314577 980314583
    0x302161433130306020703050304031806020303011205030c010905060414010c02030d0e01090c06090503011505030a111513030b06090403020a0209060f2d0910030b10030209070e130e0703 82
    0x18140300380340b070070000400046400500440d1034610b20304014185900c100c400b00e000442d03401d00102c0e0702c0416507440091f00c3c0560f00070340c01c3d60b0801048080c072503043d800585103480b0500c4080c14040c000d0040a041602c40d4001d00000e0a15281c40200740441500c5c0c001641d042521800311141c0c000190b030345001c000ba00c04180140d042241ca03005041120019003414140d103004240a07404c17010b1441110010340023003103100f0b0302900007003844003a406a9981900205841c40100311104d90b84041080000d04c400007200720048503180540c0907102e0b01502c42209203081017801210001d95a000b0026101600389140c81d582c002d4a0f03e90b1b0b54002486901050041b40c01c60f01c912032551440d01016000080c1d500400a10900c0300c0c00720180c03250940390b290000001e9041182d40c180c05070240411200e007281c110742e41d20713211080c014140084040074580010140e903404078518041d540d1921034400304040b4a0074404000d000c529018011400d01ca903210241100040001c200c81d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 980317077 1250 980315827 980315929
    0x91a120d08330a080607031e11070b2203181d0f091c021605042913020d140c092103040b070b0916050d020d03021614 52
    0xb8a0030000f02d0200d21500628424030500c420002d8090300b650100301090b14036a900c40c803c0d0608000d14094910490107191082800c1c0001000540c2e8203407a5034216409994201c8001e2a590321030070500b01050099000030380c680091042400b03142c00000141012001d03400403118007410407040c04002400302289400362000080d99000300703000d620036408550706014000d94030384000a585050142d00c00403005004080050207140c148190044011440314070200c4e00721481a9030707440c004200a031900003100c40c0781c0e004550041d100074040031842c15000248070600c0005010001d6000345054034506040000b0402c44d524000340044480380c01d90480c1c0079418880d501411402168000100240082815820407a100c20f24900c00d142d030340100d803007201ca0480e4012a62356544265900106100003d90242c1002c458400c5181d01030300480308103103140c0f40c501e208183c2d070b5803040b1400003005484180c140340c031001540c500042c1200703242d414412880c001000c644d0401c60010140 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 980318327 1250 980317077 980317171
    0xa05041827030e10120e031204080d0905011e18030503160e0a090608100b0109051203120103050606030c030102030618060109030503030f101d01091a120d08 69
    0x16200e40b40d040030200c406000700004c1452014081c09400c0384000001d5414181100309240368000426500c1d040103240303281e540d17905c0f20340752103180c3da20907844030722016202c40500b0040b030001d00524403140300524440c07035041c00070701050084502501c45440150034030070f04031000c42d81c41000d8a4002000703480e06019094903d05c191504152401c0703403900303c4150b02000980d040151300c0001251401c02c280d50400c80301d500c009080b501d40c2551a408104202000d000c6030030000c8100c0d182d01041000c41e0b1511a868899a0070490b0990040300e107070f804402089258101880001e45039001600250f00f1410840c000848807024650720500d0496140c00103040c2e40e10030b20007000195006000d0b03d0341c03814500003070b056249007140ca440d60035005c0c1d00c0001d841c000e0344604c000b00d10384e0307440c44e060542d0814601e60040c1140388942d1243c0f200b1810030001659590400f041603103440030041c00445401007019081020040100062503010360840c03a050240424003114166000c80c800220 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 980319577 1250 980318327 980318333
    0xc0210080f01050f060715050603010e0d050a0f03111b010b0103090c0b0a020304120606080c0f060714030f040e04050c0103140708090a0609060b030c100504060e12030a05041827 78
    0x1a0040d10400350107010440c0e02a0032200c4203500989c003914050b40280461100d4941c5256920f10700c500201c0020420845402038611460024038020960b160101b55408080c0c2090940d4001c4046149543ca0800300503041d00c509100c0d90340b070108282024894981141c0300c0e40c0e4600c8151041403c0b0003000545242a1403007401124054000580508080300a50030007200038880c5003c1e51485220b0702c90902402d24040001e079030300c580014001480c01c55541e4400c0c7c20550f440c9100c48052000344400c0d03155112000c00b03030001d005219001d038058a030604050785000300d1900600c3c1818540900110409041d6038529440780346401c14022503101d80200c20310b40715408001414051900350a482005501d402c4448114800c90889800e010020f0410200c401981521408540f04020030000c85010300c24110b080b0f0030040c0250458950944840d003154000454200005c20000d400e11904050580c000010901c503003040184074000300c917100410001c1403c407100708500400700010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 980320827 1250 980319577 980319589
    0x381515071a0708040b06040b09070e030a02060c030a02010b15040e090c090c07020f01020f1e0a140105060306070212071128090c0c020f0114190c0210080f01050f 71
    0x6151407070303054400180341404004240032000d82c2c0445103c0428004540320749014010b503154080004c01203107440d12601030030703515041140c42d035903050b0003049520000b50f0fa504e000b51409107200b01c00f650303483e2201180242110011341115100c1c0c100b00c640030320754482072016101911810060703504141c50b00c1ca500d034070b425094210b081e407201c0e03480200469000250041c1950038820f5680c4c03420421200016610707900e400e040750105038801103140301070807504000740080009900580b4046203454849403850700c0f03003189000031b03a0b4440e000c4c17000c82d0900700140c907409491031000e44640810301c594001e20744107440c0003418400d0307101a1f0741c0745942c4090b0548400c2d640c201c3e0440c004c8030b2003c22004290114440c89201e246000000305c80340b0702400c0310b407021035401010b0404103801880152035a0110600441c60304505100d840a00b510007001c108440c2c0c466104d580030080a481001000c0c651180381008000e800814401c000d0f03205030344103040d5031007100d4280c0480c0642000c00c0c0c03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 980322077 1250 980320827 980320853
    0xe1005091e060403200a0c03060b06070b04240e0d020613080316141b07051c080a030212070306181109130e03040b18040c021938151507 60
    0xa01c1c2c05005446e0741000b01c10780c0c0e00000c4900c540c030141702c288a10800c201c15402640c2010305184030600c0007074001240d0544801861030702662001746408011026412032740c2d1100098810351001e124014420f404000c62940a585213912001001030341e40c800700540009031014580640744820202054080c1c0b15040281480541c5580c680200c405003117200c83d119014120b0f24002e41c2070104981c10314107480c230b81c80d004554041444091554443d0f601e5407020410204040d42401403100841c4a0211340b8018062960040b461a0400244036140e488030514011010300c0e140512030111090400c1e00e140020844045020003e1501480041c00c1000d070303406c1003070100040c04981c3c0140d10001c0e020f51108066184900c950390018042128003801181c00035a11050b4805401d0f0b2110140c1c04203944105403203042020b0240b43c1c6096a0a424a40d1040c12030500e81100070000f42c1c580c80d540183d40e00040032520a10341c000c1000c021890100200f8080700207188010b10002c0202d8403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 980323327 1250 980322077 980322137
    0x12061710050603071502010c0f112a0a08060a050c1908131b061107080613030c1505070f0306031707020a0e01120507060c081c0e1005091e060403 64
    0x85d44c0d0425210000380202049280b070000b20704100034000b14580324000082030003100500404c42e540c52540b0100c000c42e850b0700c84101c104004202080035840d101c00c0e1000030a01c1000901083c02c0c083c250105607035000b4400028584140300002c172082e264074121144140a04140029484510322528008a68000039264213601c05520394a5825a03041d00300f00e90300717070361004050740005801c01d85440f010301c200c00c0d89620520200d01e00d51281a00c03801c0a5110742001f000503585551142044190040c0e90620142d5a030104441550009a111022100352031f04105031400d40d5211a0100920400364542c4a8003042540c119103a48000c14081e0800009820300c56035100364000c0403510942c01180d441c098100000340c0c441c0100400c8100d00c0c0c3c044103042c2171400c40c0768114030040c15100c04440b4140c888a036808000740610414050a0540e1408241d81c50b0181b82c0e580380003d8004880d0078444600d108600200d404074070684c000741d25140854034600380c3c00200c1c07a520303030303000c000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 980324577 1250 980323327 980323349
    0xc0f06090d1b051912060e0f16090507170118020c0f06040507050105031b371d1c051606090e01060503070f0e031207031206171005060307 61
    0x508808410b42548011280c0841c0d4512201c112000e44c10031100b22071040d00c0c0088001582180094075a03044500200704800c1103131060340c2c3c9003200074509410014081034a2030310380d105110855003401215030180c01c1d403c0c0500c40f031700070b42c0f858400290140300d880c6103400e201f1402e40a100d4207404855240000700700b1140c0e0240d1041e202500c4039425601152036100c0c6500c0014154000c0081d2440b4a00e4140c0711040c0401c607035000142a407000113149805203204501803415000d01c5842c00590010f40c9406542004104029061030303140028400707402111080005540c0c0c940c042c4140070b4521886511003103209240081c42c00010715240c0d024041884c42c08913000d075000b80150200e44121a1000c10f69036125000d40d080c0c44151440c0c00018124040c2600580c00303442402d103058405030071200e401e0300e0605c000c4040d0300032550440008428540d060151000b90040d500030b000c031440141552803564a03096501d000d030188103000240c9070000265255070902024000f81070a28031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 980325827 1250 980324577 980324603
    0x12061508090709110918040507061409041a0f22020d150602060f0a0218010503090703060204140109050402090603060d08041a0918011802070804050607050d110c0f06090d 75
    0x5442c640c014a540b240161403601c000c0724486506640c3c41e00864200020300109401e02b04125448082040700500d400010031601002c1c0c0c84134450f04200e41445004607100744410000c00c0403013070740c080e00207229a0800ca1016186000401541d000b404240310050341c0b8024a903440c0090256202d00c100000c26410000400b41d40109500e48070303c0e82c2d1205485c0c2c0741c3c2c6044482c0124001c0c4540c9075084401c041e0f40c1c0c000b650041c030046400c54907190448003029070301d0b40d6403802c0e41c0c4a6004490764410a074500e01e05560020f4442000d040c040342c081d03041c0030b10b200124005020041490384030745182c1500c0340c240490072040b90082c100700a4880501c0318000841100c0d036020700c406038041c014801c52018005900c01903507069803100c007440c940941480c031071403022750810841a25801d404010007d1342e9550b0a00030180c1ca48200043c0c0707000c400280000c1c24016820320110306907044031440200640d241607034011041000c4502e981c460300c039070380850000c80105500400c403c80d0100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 980327077 1250 980325827 980325851
    0x5041e0302150703200705040c1b060c11031c0203071704050313091404020f13090507090e03030c030103120c0f23030a020a1e020a060c0312061508090709 68
    0x40100551070103922461411002c0b8240040c51100090040b84170f60480c010520951404c2d40010040300010700c2c0c0480210321007000070081100501d01251070300d41da680e01034001600140c03407424102400d07000d5801c092903200c0e000084015840d10740d540680c0000020407860050300c002d1000795111070000810b250601e407041e9698400310314001c040c1c01100000030010380d240240781e21a900320300c8040c43d41d2515401e000c0040c1d040100558002c26071003900710324503000c1c0705400090340241c004000c420f1420480400322220101c080c00075070010002c000c80c2081d18811641101c1c1c1c08102c401081890450481c0d9000611030024440c440071001c900a2103250b49250348001d40c0c03820700c1c820400c001140c0b40d503684035000f0340c0c40144c0c202034442e1300441c21084400d50b040c0741416100d801c814641d0300241d05c2920300d4001001040303140c03a500e824585c3c043d104000484440c20208807103401d245e005200d007840b0030b1403034007000000c0300002c00c2140c0910156004081440061000340d440300707 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 980328327 1250 980327077 980327119
    0x70602031e0702181b1c0b030109050d0507050a06181a13030c020a12080d0f05040f020607060e060a060e0f070c17190f110c0105041e0302 61
    0x2a107400071004016005401d11a40046a101c654000d2443d14004103500741808070000084c40c04100402c00400e00c441601048001d203c0f604010399926032a415001c2c50b40c0490300240002070003031385024120320020f580000c580e2404460340c01c08980314641c07490210301c0d020700070500401f2141040f4042182211050100c1c1d40c5903c505c5064031440c00c0140030009440088801003511842803111034046070048060030312403400500441c100c15160342c03840e021945000304c01c543c200000030302c0200000d070520581200c20712010003400710303003459103407004040b40452010340300303010001d5240b0403c051039114000e1214400700f03445117490700d108014002d00c201c0c49070307885404031640001c5150703450b00d580c140324050702c5e25100b4202c40541c45484402c00c0d1002504d40d010420460403100340100c11612054800039554900c00c04500b1800401c00c1c080c000001206a10102911400b42c2c0c1080a640c2550709030502030901026841c40c103155452103900c065004007044551900c04c0c0703e41 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 980329577 1250 980328327 980328337
    0x70f080730080601111c030615050a11160302010302030703090212070807141003020912011e0c1e180302062107020703030504120606090e0a0c080d200f07060203 71
    0x640ca07008210764400d001521761076208000110650800065029a584580c20100074150145000110961203001882014031450450000310b0f4000c500001c0c0d05610440008100d01c1c0c181c007401c0b040c440c05081c0d200c59081e0740402810b242d00800041c51b05072090f403000030025001803004030604414081c00782c03581c0d11801800c64601402d0f50110b101405c11102050001018004840d40003000030110000d41100b007100d6809010840d000342035040034003d008201c10b500c540ca5106c004105107003011622000784a80501c00c84c1401200b4032108640b0300c51004030344d41403e0b03000102c2c05401e1000311000e42c1000f503104001080c48a8a041052080440c0b640844131050054481140507a69038034544002400910204000d0100350004030b00c0000051007080040360054803025081d00703540320076505414030b600c040504004d0204181ca41802410510003603e21a410032500900417452403101c0c5041c01101d002d4102841c4040003280000d134440e00c183c59020f03464ac00025120b41c41 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 980330827 1250 980329577 980329673
    0x60a0506010e030d0c0f020102070308180103060f0602030a031d030a27030f0f080d0606120501090204050a050913080a080a0632010c1b05010212070f0807 68
    0xd2080518018100040c8000c1c0f10034040c0c642e020005c00d251b84903150f040b03c3d92000c0303046000d800c82c0000042d0300c1ca0041c090842211141d443e05410080004003240c0c1940c1c014920620181c50400c10380b1780100c101d980824591030041007104082c2149545030510091800c81c5e8400014610302c41c5034010b40031420305059402a003d0803807076000303000c44003682d0701010b003c2065440c141030010f045801740410b0940301c1c90045052010144940c0d04175600f82d4001c0c4040b030034500300c500517810140704150141030b4140c02142440e00f03080c08507103014021302507a402034ac2c1d48004124619144ca00000095034880d110a50343d4195500081c081002035411900031800d102000ca41c1e1107640a103030540e4051003511005d2110305034038501d5148540d02d911410b2044510103e40818054601e2000032a83c0b0070803107403090715100c00280782c010640008115030340e060109400082d110140092f0103074112110940718041c80c20b094400c81440603510140180c8018400c030034a60100003c004104 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 980332077 1250 980330827 980330837
    0x801051918060f0e0606090909010621030206160e010309030c061a13141314250501030506030c0f150d0504060506030606031c020708031b011112041101030e060a050601 74
    0x1a0324098104c08840681d0240d61248007401503102d170f030403d041c000d94444043c100200e0038640d28490f9012140000d0388103c03801c84108191014180c0411000c0e400c102c084c41000000b1040080041901180f0702800e410540c54000b600c0070315200c0d0300748100f05a0055000c00c4807500105810546800c11030055010f408020786901001a05205a00c90304015200f22022076803800c401e0803c2d5042c0441c100c903202040c079044110b505080010103c0445007240140c083d02c036206002e408036600c0d0780018100340c00c2004002c007a0b180030600500c902e50582d00c0110f0070b4040e07000602e50700c84900080c1c2c0512400f0840b56106079030381e00964040c50043c82c00300300c240c69070f1042c50788860045034441d03010780c0414000c0c03042e503503290120400100f451046c1c40220740c03500302285c21540100c4e90000407820382405c04020b00703000e20468110482c4007090714603007a040642c100c180600103002415035440b40c030902d0110303406a084070343c0c1d41e11b070103094400d1490900c05200040c14103613040b0340055 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 980333327 1250 980332077 980332079
    0x10b04030203280204110d090f150b010504090c03020421031805090f06010e040f0b2e1d0d060e010f18110d02030d021c02010c0801051918060f 63
    0x1140c100940c00700381604001e81c2d100f080b0303000c2c8070290990000008140c481042454041081485800400c0e0710589154010746e10b2814420f120080c0303000411899440c00201d00010fa070002c08590443e0340c03003407021a01c44128a8207400a0040340d00c100d18038112903030446c200e01403030081400c2843c403d803504400088030604404400c1e80901805411610800105061303a006c0c00c05160f001805250420100c0c0c8031201203415650340c0d9001c0031940303403110513051307452505c280d5072207640c1194000c2c0549220003030b441c6103070210b0900390380040c0000c00c0e40c01a0480c0e0b4107414000d94440142603c00c03841a42e00d002c800405600030a425617520f001c02e800d031014003d0103109000300192032000030881007a112503600040c44084907070321480075600140181c50503c0300d080e00c0e100e60740103020a03071282135000404e5a080c02c900004c6900d00107079580030a8001e0f20701340c1568816a6881c8400085a1141008142c1500640400701594042003510300d00350300503900b0b480b03c0e4203900e6619 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 980334577 1250 980333327 980333353
    0x50f0f0706030f02040b030117121b010b030a02011b0314040b0c060a09030e040b0307090504140601060807122705030c0f01150909020a0f1404050906131118010b04030203 75
    0x85c02280110030040d00c0800c010400110080302540c1411014030585d80d601824012081680d4840c081003540500c09410703c4400c22000e06c196041e001e070507009040402890f500081010118180d013034928802d6003142070a161040709101070501c0d803030b400541d50300d0721412950f04540007194056407030300ca0800010542c500364025650001d03072589503000204100400c110141c10381c440610380601c10054002000e06680c041d03140650b02031428441814001c03c2c0399414810160020001d01a01074180400c1e130b85c5c407641c0b11108903d48500007449440710204020801598501407420b4810050f140702030002c044010841001d4a10485401980c042a56400d039176020912160601000d942017101210903003149111500c000c1590160a07110040b80d07030020b0f41a003001142901e000d001d4240d50801b407041e10b401800700030090086241c540d460103e034101c00720008104030031558518225407640e058840201c078441c007002016685860070010700e500648400c0e8428802c41310700b0700031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 980335827 1250 980334577 980334581
    0xf08090c210609060f16140319020f0702030d09030804050603070e0301050f0a18020d060b030c030a11040f0911010e0f0a090912090f0e06030c060309061b0f16050f0f0706030f 77
    0x240404a444080c0306030f0305160200203d400080808010500c004210715a440540c0700601114010701214cc0d210841801071600d8500b044560500780301d240c150602c04902da02c81075800300c6000715401581c1c1e0359050780498441e00c1d0944500e8156080409000c21150b024410b503104520b01e0360100801400c205107614044549100690400361801d111004105a5000409400009800c1300c40b00841200480c4c940700c0d84010546004040e8058420716140501800c41518400d49050203038294648500034400307400d2003540d0601242c59103520039a01c40d06190001140c00414481c065a9103400d19805000c40141c11a0b1010713980d0325030402c0b5070041d225201649c0310703111089591810003c403183c40300b001400c0103a0501c20001f0f024034555070740004521413001c00000d0050741c1480c034020000f03000400d0340345070440e50910100c03000a08000546100c1420282e481040301c1207804d2450030082c00c0180840079025443d00c16501c0040040d000c012038805a400700115410b040342c01003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 980337077 1250 980335827 980335861
    0x4050d0f17130210050d0e03031017011401170f0a08031b04030f0c051306050306190f060e2401021504060e100605010f08090c210609060f 61
    0x8a666020320107a81c1605445980d4464950407000700011819000200050500590600040c900040202034941c05008200503490810004c60450407e0401d5003009001e60142202041d6541502c540e102d00035082652040c3d1146407480c0a541c44002e03050360000041102c02c603c2c40344126509030006d0000d5180051a007105029055031921010010912610b5004d42c0b0300000500001c0003264100180610041c0700c2c01e0400101d502e044203000c0b0b40c000d500e89004c1c410346040801c008030b031400310344c02d60b021a24038003502030300480640c2c0c00001d107068040400c903545024004984003502c2c6c03843e0f42c0103601c0940701108640c201110039040182505400740140c201c48000c1510900071014a900f1910030440801d00078a6140c401c0d24080c0806281c0f00d001e51564420001c0e941c02128200d0007032218a4070b101a49031800000340e640d0781080115005411404d1413404440c2f00c7d210100480b41000700782d5a10781021250b5954030361068901138802218a00418600010380000e48 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 980338327 1250 980337077 980337107
    0x31207120c08060f0f0d1202010209040c0203120a0c02070b0706050108011d1507120f090c0f0f0b0c0304050a0608060109050d02030d0f12090f0c080c060d020c10110304050d 76
    0x4004c1c200f154060001c00e0042da50460307001025400c0f0400020454101040701400960005071070303150080400042c1e59000105005541080080d144d52409004400754003000404000c07541d0a4115000c80c03a00800d50300c1201021004210001007160b070742c20040c100d5031400001d108001100b2050201c002203d040b0300b586034013403084a01c400c5044c11001c0d40c0100c1d00d060a00c01504003900820555500c0c00c00d80d8010341c0da40480780100410000010054101100d99000260512803141d03215800f43c01811601003000c0b1b008201c81c0010021580034010250001414554480002c1d000315401d84482d804a500003002084500308060b59010305030f0020020102c03044030b442d081c0c400100350b50501040194080c4c0401b47e0084600500340e18038840c101240c005099410b2081d46400079802c6108140c000110345078240d03403076000395514101580801030742d500d030f01211640740480c00f0284c0418641048130300040406500040c40c401c030b01650a0350103540c40d0401c1266460141c4410f0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 980339577 1250 980338327 980338339
    0x603060905013f060908091513030b060f040c0906030f020906090103020d0f110c010b030606100807020a0501050c04060e0a05010f120b03010212040c150203070303090302031207120c0806 82
    0x241d0351080f40280c2110705182c0203801d00e03400b480c26494040903038003602000d49031200002520034071810100d9030b40100b50380c1c07000380501b03240f12401660380b40d031590711000e0004000c1101040c0c00f9924200c00c1008400000e20030802c40c045110050491803040c0300d240f0101e49032440401d465112402100c90361a00180380301e152802d03240041d402508950701c00303c3c1c1169110b60004000120340705002051090b441c006482d0010108020300307641400011a0281c0c014400f0b0220032f80342c3e9041c0c10100d1806080070903155407952000c03071a00510344c102806540c281410300c00e1501c0c082000b002900c0e91541c0c0d4040d818003040070300800315158071a046c0010768040c0d841c10641c0c400e60640382d000c100c5044c0410b0703640100001a099803c0382d80e50708076400b000c00a110405c0204228040182164041414084ca0800c0003946030300807808017070180340e26400310100b050320034004c80e14075203500641c0056170b0410b00b1004100500c111812448245011640701d00b050140310b400d84650001413034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 980340827 1250 980339577 980339639
    0x31920060406050a02030d060e0115030216020d021909060e13030f081f03110406051e100c0f0308040c0807050f060a050c030318060f1e090c0604060306090501 70
    0x201d0740f82c0d0081a2400860000303102200821501d40141002000740e00f42d0b40301ca5504154009070102603a507102801d2502c1000002c800c6200703a01c642260756012600b801a4848500104041c0e206030f030410382c86031404103400309881020340c0c4880e00390b1f2001c4092810070b507514861080c80c0c90b1108005808a070901e1582c0d41c0c1203100d412503541c08031256007204011842078111481407992038108a8140b10555400c4899080c24801e60303000f020b04482100c50003070311004280c00d40341c41490701d42c01003c00b4000b44210030700824005441c0d0b82d1050020b1250001c0d03080041c40140251022600481c80c2340c800241c07540000b074010180c8000820140380c5496140811084d98068203030ac070140300080c019415441400d0000e14451444281c110140c1080b84a180f400c15500500c0030442e2821081440b1501c0b60340c40c4205541904081154010389130000e1503440c1c20945400c2d640c5c40700000601003001c0b42c0c5508140c0807112440d00610140e6280c11810700c80d41d0740810b410100e0914019 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 980342077 1250 980340827 980340839
    0x1202070c1e0806010b03041e11030a1a0c073518090a2702030106150801080c041a011206030c0603020a120501081903050405090a140702070f091a0319200604 69
    0x1004c900340701d00c60b809501827030701c55001080c24003902c5030042d01c20780034100381c5520700907414403291743c0300280c040349034a41020344e601c46081c0300382034022010b414002206040c4a03804100350a10400b00c4401098035825140c1680c0b03504070f07210714024040c030b160a001c201108824007a500d00394903240c5030740c01c0004440300000541b1603000010381c1d141d0349a43c4005070090340c8410424454000b5590340720b9941c14510a04e24118100c81501e00031403504440745401c040c1581241205002460000b82c4041480f042001529450704081c2c12107014401c002003144d0075034000c015090343c40d00d8a0643d01404503140c01110400d10a00405d604800318911044084421f00380b5694407074104103040c151120007180c000401118604401965901d98094960410f4245540b26025100814185080a000d0754010310684a03211803203407505096581310880c180f40c81d5031031030090708a58070404040c2c881c045040c0c244005541d03c1a50042590083d10481070110b00c44c0350240200e460145031030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 980343327 1250 980342077 980342123
    0x3011508100c1e02070501020609060f0106051c0c08150901050609060a1107080303040606151202210c070b0105060c1902150c0717010207031202070c1e0806010b0304 73
    0x1107000c504101102608480700360000560340002d0034030764005c0c5551410000003929003c0c3c081c00b40d1310b0b00d900503810024145410000c440c1580d07503914259480d011250301c0606c083c0c00b0041100c1d0610304000d2202c0c401584409504e02c04d284002080c030702000c0300028416601020702490786c0007902041681510309080d00204105521460070019200401c3c1686d401d00c007094110200f15007000060206111941c091100070300300000c440d800d20030030b00c08050312650328180800c202c45c3e0003240704c1d4481c40000301400b4010403c041584568907200703100520603485146c044802801c1403002141b2410440d040d00e0f045092940105a4200b6204251580c58030034681281d01c81d540100300083c2941c103502070000744441100411120303040000b080030080e21003d010380184e206201c03010210360b0180c8030104c0c55041400040ea03410f65824110035800702a0004c030302081d0f0514150b801c404034200c1c0c03201100c3c0c00720140d03807a0b642c031880000500d01c8150350203801a41ca000351121542034103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 980344577 1250 980343327 980343341
    0xc090b12030a030911040203071e120606091701050405030d1505100503090c01021c27060c0501060623030a0f050c0702030f12030121200301150810 65
    0x30400c900081000000a145a000300c0700080002e07112040c0100b00a240341e1842d001c000c080f20154110302d043c1000503d4030742c2078444000080041098280c086000e148000e051141e03010050201540300c15002d45a9801c91146074001c0c03a2010b40c075810040c040c8106401550b0081c003035460100309114510223007181c40c01c20480d62031460170004096031100ca1030030030840d050f00d4203500d9181040c2054100f400300341d046c0d03056410540c2c0c1003000c0b0b0b4034101c0d87d410380d1a6038140394003032101c0c1491040701101490501e40b02c184c0342d208c3c00300c0d829070081880648036200d00000d0025070307203d102c111071100e004221001012981e0b0703c0c545140009001035648030649100c0052481c480c0e1151505844050341d0803461310704001185000d42c00d080c00411b100d0900ca000034a1003142c224440e000900c814401c800d5640000030900030141014800c2080c43c07030304201081480c5450350510b20a59000c1c80d2901c1c400c1d0701e00081c4440100c0310003c12000c03107415030041e0503001c140800580c090210 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 980345827 1250 980344577 980344579
    0x90a0501060f14041809140f0606100302160c0e07050903030412020f09100801060905060d0b100308041d011202150a0201060f140102190f02040c0504090e16050d0c090b 74
    0x814407000c105c48040607040c0a50705407482010624200d80d05003110080240030544401c1d410541050324180d000040d440e40200d0199030300c040090310300364200e0085c01703800800c09070101440c42e018140100c6002001c1610520308000070f030717a1030b503200a4500344104030031950035401c24001040485640e000c00084180040d200302a0306c2c07042c00004042c0e990840b0300d103200b021058818040d100091140a014081c480000c0145040003800654130b040414801002c03010f41d071001440074a01c2501d0b00700111340c030500f40c9445079100c4404141b5131076900c0099100d0303140840001003070310484030f100f1700140e00602107507400501001001c40d40e90059043c2d009540d2a0007000565034a031a100f00000d184901c0300b80d614810300e42c0020b0410140b114500e514204034020031000c101283c10711824190304507000605044102401c1d169401140d003e489a10b19081642e401020701080c81d01085141d4450301e689140c0f40c0003041100403a03481c001c4c1c482c1740a04028807440030951301c001040c01c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 980347077 1250 980345827 980345867
    0x70c022101050a06140105040302060d0b0a08070806070f0806010813140a06020c0105010b0307091206110a02060405010606020619020c01090501110d152301111b090a0501060f 77
    0x1a2069801e0941d07078140c40c8810304580e511010005c0e0144404c484200340400d280103450141b07103030005041d6000e0420852443c583c0d842c44200a40d0b40e480080b0018080c41081d64011030b502d0a0345a103900044030b80402092480c410300302c2e024860306c0f240b80b041005031682c0710740c0c2d126030840030303c00c1d000b42d9003c0361544145103040c1c1c031404c0e0803c242940345100c0e88000d60303103040e03640d441c5082d0f41c0180d1201c0c080c0c010510900c070009802c842c414080c0d9170741c0240034440040908116020f41518048010301250006200508070b602080a5204a01560082c8229583d5180490b038480007103074046044000010a1001e05c03116400400e1200030400001c9845061511014216000c0e81801c0350310300700001d003610740140d80e402050300101f035050001d507286240c0240c04021003240c1c4903001015116903151072080c0c0c0a0700b91100d40d83c4507030044074505200364401c000401d000200440c030030200e000002e465250075014240c140c8590760784100c06414010001d49101600740502c0130000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 980348327 1250 980347077 980347129
    0x606040f090f0f152402120a020c1522030b0612010902100503250e06090d0609080a020c0306161b12020c040e010b012f0708010b01020c09070c02 64
    0x900f14020706041c0550b210b000040c072858066801500c0018240308030300803142c1c01d40d21074559008a000444a0745078001e807640e84400304000c07401c008614045a910081511074800e911200038040c1c8a040c0030150f481045901e01940481e20718101d00c802015000b6a5000070102c0c02c1040c0c101a04507022800400e0072411903001034071051240c54490001107020041156806200241c00186135190307140c40f0502d002c43c4030060501041014170b90188000091054454075281c030a100d4168021000f0484040f192070a0b01c001e6001c0c002590052003820340d82546d514011524501850b542c00303d62081c07003101001924018036180d0b60041d01e9064111920101e400c0581030142c6141e581d000e00340758010381c410001120300c03071700c2e440102e0303854030040100507600b00314028410f403010780740b0500700080000c8060b2100c0790f0205140d42401281d6001851960540280002c1c2c0e200360291171108951800f444000d031401c440c2400002c0d040d0f0314840140c1004d201c51800c44500030f0f5a86280 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 980349577 1250 980348327 980348351
    0x290c0c0604030b060a05011103160320010903140a0512040303020c0a0f0303051015030506041d010e06011d0c07030c0804080a0c0605190e0a0801060b0706050606040f090f 75
    0x20780c2040d4402e5800c0464201000350700d00d040c415980c040c1400f400c0140c02d1205885940d540c80c010a2561181d4800280515007414020013a810101501100355224102683c410f64060304d413801c0210301060105082c10100c5841506440c145c801a03031310141042c0009400c8182c0f01310180040d024950708100c0b50b00040402d0104800650061050203001503103850010101c45004021340742d10300c80780405002e80f050904500030030760b25500e404102511a2400100180408440d04c1b4156405aa56200303245064010400d1140f40d00e094030600c3e80c1e00d49100e69010450024840750302001c1000624142d0180c1c050203145002e40b408c040c0314681691845415407140e00680d02c4c1d54007200c001d00070803c00d01d079410702504151600d1814000001510b0000a03444a000801e02030005020001515601600e0380108203010080c0b2880c0c0e43c0d40e5142450b0341c0160020b072046810b0030001401e85c28400100c0302100d815518064800d0f290107900802025001141c03581103854801c10040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 980350827 1250 980349577 980349589
    0x2161a0123060d1413050d140307080402031213081b031c0203041a09030f0c09010521070b031807030b040b150307061e020106150f09090e0c0109290c0c 67
    0x104005041c610240c251781030070440e292544644c001000c00068030010010712203400180d0340c05c9021810040c0300b5895903c00a42420b4080d4801c0c003105501003107010302d00c103a8900350011501007078182c2c0c0d28122080b640751103100022102940680c01034030101c01600003003414050040680c419030f4142500d410390b4a040d4280c81407007205490300410024080e00d0180320714103200c54280010301d12400d4200c003180c8817180500c03032280300320300c140c2d000e5101c69104400c954000e020034080d6a17040c2e860f00d07290301c1150015a8150648001e040001c01c00d070800042040503a41c22840202490742d070f0340e640002c200001812800c040c4d1102708405035907202009403c0103000030380c80d0201c0031031210f90307800c3c0d0b0824040716207130442e03041c070008101e030620340443c0000065075440c140d4911a0520307425030b03e4414076407000107001c1ca01070400c1e018070740220b1381d0f040303c0d24241e0312244c0144d55510395640ca04103521003282038903015408080c550f60725000901c1142042000d568680e07401d0400908 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 980352077 1250 980350827 980350831
    0xf050f0304090605090a021c0f0b030618010c081b0f07060207061e092111070e04020a090c0f0e0f040608010504060b0402040803030708040602161a0123060d14 70
    0x108603203d01042c0214074003000380f00c0e172010715502d0440c14001c10001e0254040e54480c0400801c0ba501d010080700c402d1f40d0341002001040140466803d41007140074005802c2c40c0d5544901d0551800c00b0000c40e684c42004183e00500030004940e00041d4101c40c40074032030340548240c0d8140c420420807400004e220b4005000341ca03001e600c0014001341901d0140f5103032002500c8000c5c0d02031400c1062070003c0c103114010000c0c0c0c0321245248103000c403286030075605228004881d256900c11942d0000d030005d03007103000034031a41c425070b108814155180d0441c800d81e0000301880010992400d801c120f80c91050242c0d00000744001d00a01d034003203803400032404890300e58102e00701607516038007080140100c0e801390462140c0143d4046103014034102c00340d522800040e000c0b9007040181c0c1c002c20148000d680640d480c1d42c00b8203801050409841c1f52030601ea01580614010036401840000f030700448842c0362446070b0000f001c2404a01d940076007000701e564040c141e02c8a540355a100501d80400380e03405040c0c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 980353327 1250 980352077 980352089
    0x60c030a0617060a0509120a03090503040509010b04030c0801020a0f0c05101e0510060c02130b0405070e010f030b03060c07050f0f010204260a060b0301090b090d030b030c030a0f050f0304 82
    0xe03d42c10301c682140181c850044c0700c82e00c683c0c0f003c40000c101300c2d0b003c01110b6411703100e4900062400c2142c9091421480b90f039002691014a01c40007080801120000b40205c83c0b04000205d2038a0303407900e07510f00740e01074001040085204506008800340c02441c2c031203a61840750003541e401501c00d04c094011940c0d818000350280460b4400d02625100900c10203070000601d2000b0021030386006c0b0010484814814000c0c01014250180500c112710f40e0020890f1810040c4244440d1030f103180c00610032100400f00c2400105510f206e0543e90740030344604002c0c1c81014014001b10780da0034090505660180c0400c0360b0900c20300c4100e001d0300c0d07400d020581c07200c8035520000d40c0c0c4600d0803c0400c0c110010f4408211040c0310602051030420307002514100e0980d0090001c14204001d2001900500601801034100e0449208004185001044103000d06941d07840c200845a001c00506030f60381190304450360164049107008011070810120380441d244503004840680c511000702c5400c540240d8445 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 980354577 1250 980353327 980353333
    0xb220501020903120c1018080c0c0120070302150c0f010e06010f0807060f051216032004231809010515030318060f04060c060c11060c030a0617 63
    0x4007485142c180032528030360b80804c0840b4100307064100925181c00034203010b100180d07a10344920415144180440c403c0513044a52640c80d0201a02003540b40c04482020301d000400c5d0000c801060420040d11a440c2c00700e070f000506c1081e0555007402051a1641d001c854055024002c840d041c45040080c551007040040010556035a5071404030714040040c3c015044200504405104510340001c2101c121001c1c0c0c5048500843c03804401d41d2a03100d401011009032444400700080d86480540130b400d08881070f0b50030400786085459410420189116100c0042d00c20481082a40c0000c40e071040ea00804140c4881c806180c0d200050352a80461607420b00d81c103000d420404c20b0102071050369809013a801403000a80c85a10000c1d841c2c0c461046140680b104041410203aa220242a5070302044814074450b56241c950402605600c40400100d40303290078000c3d504402031040b089405100c44040040005449040d10720f62107400080240383e2456032580c0003d192940600c050824154000107 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 980355827 1250 980354577 980354587
    0x605091e0a020a090c1209020d02040c051201060f020304050d06060e0117011406010f050307021006170c0d020604062d0f0305070206220809090a0617190b22050102 72
    0x5104002039154461071000d403800d8001700406402403a5100341807401c060015180d2540d100080e44182540b001035001850420f400000d150420300920204040c545801c640d07a9907510304030390040f80641ca040c010380080c00b00b04100d081074091404114894600451160785440074540c55010990100c1c000c0f50801402005400080c49400500c280e40c42800d1540d03d04003001810251510444a007080000400181960701c00e000d1030810210210003030040c180e8950b901c4c804000c085d03901c0515809040d4562141d4a480c0800301d00046d40541498242850300c06c040c0e0302e440d41c0c404400340e4000944003201070000e82c039005080b031070b0391501c1c1c9003160700441c00000c0480b50004c1c040010b66012a090040700150000c440c0e6200b20003885144000d04076191082035402031550244c0c002101409019201d1129004242034401c82c900c420f41104062102c580e940a0101400014401c00414200428000d014085d8072907108111040b03215018040150300a100e003c0c1542c0710b0b5400b2036 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 980357077 1250 980355827 980355829
    0x403020d0602091e061b0f25050904110906030a060905150a051014130501081011030c03130f02030a030909061d06060717030406020a030b1c0605091e0a02 68
    0xa0b02642a04d03445146000c5400d240d00484e955104040380c1c1c1304c0d40401c0203003a90300200300b0008034030600310410a8030103503221540030114071a070700012140c180d002d480c004940c904101d03500501c120b41150358000160b00000901c0042d0b107019040540500940036603d001c5682c2c0c1c0112102d9500c5032009002046100311301040340540034248014141c181300034411202020040c0e5020340307440c0290071107940c09150024088240c00342c40d12640c07605000c0000f034492000b1841d24907003003da600500c004249264803e18a110480300203007112002d001103002130844510186110f40701c1e130752207800c89183d41c00091900c000594120001090090248546280b030b00a080080c00c0448107146416401200b12341c840c40700800d03080c01142c0100d100c07400e00c5500007080c000b509042c01076940d00d003841e09005020703610101c0d060700800c3c03c02074024010708002d04524908031602002c0d50071803005130f80d078601510001e00f407041284500150307603805092051142c682140048020040e92801c0e00c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 980358327 1250 980357077 980357089
    0x17090102010b1c0204050a0b0429030d02060723220602010e0d0809031b0f160e0106031e051602010f0b0906060313050d111524060403020d060209 64
    0x2464260203641d5001c0c00400340c415821004040c40e134111008501e66450789580801810000c4a650780181040c0c9241070300d81760400e070700300e59184041540704608203040c04c0c10350700e50702c0d107207040c0c0103a002d44d00007507040388241500302100da40301c802001c24020144507003407660003602058800d00b0850079440c00b112840111140209010b0001303001e900e07188880c0c2c03901c880e17482c0c41c46424003000e02d00050041c0c00c140102c4480c82c0c1050f0310911541410b60381d0b1540c6542001c0d0302c0c20b0a1188101102c0c03903800260401080b6211402c0e46d5810340e007003110440142507840e407000340501c130304900404c0d40c803028022640705104604c104403c012103210000c2c251402d4808600e416403030100203540b03503203e030344800d6440203042d00ca41f0b41d01d45500c2c90010707212a02820150a41c00b03000451440d80c0d0740315201503140402501101c1180030a49600819040300383ca4001612044042c020205444180e404503901401490315003060365036004141c9040100c0e004813080c640c0000c4032441c0c0c1c5064 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 980359577 1250 980358327 980358341
    0x90c030f1b1314092202041107050a0b0a0e0d0f020c0d030f021209060d11040b0f1b2b031806051e0106321b0606060c0a021c1709010201 60
    0x4c0720300e038015003484031200c8a0700c00300c1e825400f050f2081d0210207007552a581c2114102e201c001c001c059842030a418840d4803643d07000e5045030122100000714218250a00074481c0444100001d05450015284199440d4094000380c0341540034200f00c20540f5072b0f0f0082860041d901036102c24044040c0c507a002410b00605a0912600340b40070f01c400c0d0040c0d2900c41c1542c11a20b00710300c0004480d46090076826190040340d10582c0400b000207166052a00c064000e841c0f10401da801c2a1a80d101100c6110703220040c00b60007140b426003011100300410702c441405010741896080010741e00b602c0d0070303850141d0318070a0000e407a0a900c0d1400d00c821210a2141e05000352503460500481c3d504210380240702d200189510034020360305540d4213404015010010701c892218909035583c40034500c65400350340032035520001c0c40340078843c00118207040071012039413080e841c8006080741040507820810200c0b1b4000401200140403010f0780c001400e00000394000348000005151100303103141c002401e41d014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 980360827 1250 980359577 980359579
    0x1180e070e010e0d0b1308070b0114030d08010312031a03011d1018060c0212070f12081003060e010603170d110f030106031805030a05040602010506090c030f1b1314 72
    0x305404601107100e4203017541c1c00804441c8142500442414800b109004110303011b0000d401000000a6501d403100070484801400e50584084aa0b042c00039145604248805000c0010081100208901c81c0d400884c480a40500caa0011000c02d0003080c03c6421003034060710703003500788c21552050307010030031100000313400514007407051030700f81c1182c1814a10b00b004000c081680701e0b5219627405001307014210100000706079494503013003281070551090380300450958a00000c0000081c030b06216089641c81000a01c016080881c0f442e5100c600400151f100350205d03550312940800043d0f0b40c0460705c207851610895680d2200259005141100c101c814070f108032180c100000c0441c00c0011058a045881500300025903101c403041c00e010080440b40d00915a02000ac0c0b043c1d201600400504180e408660080015507112030510200e01c109943d000b54611007800015085071100d050303164880307104210102416612046c08106400030341c00180c4401c00c0311400c1c05550354484000450b164 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 980362077 1250 980360827 980360839
    0x80304090b0f120a030c03020a020301050c0d05102102030c09100e011d15041b0315061b02040903050f03190513033509030910110c01180e070e010e 65
    0x4544890385a84298006008042c01031b80c4907454281402030107050011030b000342c0284502c0c60f0858480d403580d4810550110035601e007001080a541c02d0075140001d9a040000a90182c420118004101c5003a204120385c94402c2e01e92071400c0d5140c4803000742c00b80f0200d00b410384040d410030850816201c4140c1254401c5200114000202e2042607030054020031440a141400030080b40841d015003c911158200d201b034860b101c10a6a50540c010400c03110034030000f048241c2c65141c00c9841d00b000481c41c480014104c1c00301c0c0302600d01584080f4144d482030a140c0e20300030403031841c40d1254108842d8070300d01d0134a04000c00c101c50301c50b005030b59000840d400030400d03690459601504480c5050070008111380039a00140c16008204551a05e010480404051600e000c0040f56075130342c00100042c1c0503221a082d41d20781140120300c004950340003480549101c501800044404101c201c51600c040c0c881305100041d4281600b81e0540907000c11354542900000a000140545c0c03401c0c5001c50082d6 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 980363327 1250 980362077 980362099
    0x6150705030406080a020c031b01050a0c0c14010209130e12030c120405070b130305070501090b070308060f04090b040c0f1503020d021207081503030a051909080304090b0f 75
    0x2500401180c0c1982c05900f010401c981703030001c0c100003c0c050f032608010b00344400a04030140e05d130060380da40026441a0003c1c00340765110a1954107850200080c0303408561500340c0f01000500c42030a004403900c92100050400500c2c000240c00d03402d02c0d0fa542004a41c1e100000070001c00d043c001450070010652005155003041c00090a007407151865100e170050080b80458100f0606008c001d006240b50950b1319280d48080701c0004900d40390384070445052080781c1002640b540116400011504096489824402a51410b1f030300c081c002030503294800e640d1004c600e9140d0705c43c81410001c1380030700d00d24401d501d03151500040030180ca070418003483c004900104494480102c0c000d013003e0140c03a0140c0c81c4c18240d81c00d100a03000c0d41c5002c4c03400e4441e070000c00054950000c050b9214110150341c0701c00700004d80c0c082c140c880c401d01080700b00042082100e02007400761840030b5503220050746030100e401c590f1011a00d055401c01e40000071030540314080404030345811020800a0002100c074800d0358 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 980364577 1250 980363327 980363333
    0x7080318010c020d0206030703020c01151d0a0b0901030606031112070506070614010b0901020d0c08030a0504050313150e0315070e06120703020d110a090e0a020d14061507 75
    0x389029094241000745110002c42152903040b09040d40c0e907405003d40d03483c2d003440113000c1e0180d0002c4095541e25840d00001c0148046001d1030071048403c51800002c0161600858080c41c041c001d01c451a0340f034603079201607040e072209070710140214040d11000035103174114500625000612142a0301c9400203041d0040744602c080364950032100c040754060b50740c031668a801c20160a56605c440c081c1c2c100c0070000076010045800608500c0700c241c0c00d84142d6100c10005413200c54243c84090318007c820b10009051016a40c061500b15005000305c1b401c0550f01c962074215214150011690026000c1d1048106030b0440c5102025000450142518150035140404010700c000e10302e004001c0c1d1010781540a48801d003c40d03a40c044241807106d42032070140c8018002e94003144034200090f24004035180c2040b81e20303054031107840c2280d880c18101c0d860044c070380100c410007400d0b285015608125517610203507a8402c1c42840c0040303142d0304049140540401c440202804034a2064001c100141000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 980365827 1250 980364577 980364607
    0x1e03070314090c150a0207050d0f03020601081906020711030a0c03060b03030a020a0b0619090606080a0b0f0f03032512032f090d06052e060302070816080408070803 72
    0x8141d4038040c1c1282c841d8141d05d030491400440b0740c0402d0700441c05294047c01c1c0821400d50443d118029021122541d0f652842c0c43d1b680c101240440214034020784060001a038150024009180594a001304002c411030009051a5180c81e044400b220036010410410109000300c200b1100c007200511b0400d030041d50301035268003100100802c2030304160006441691b40900454044404072492200350f51240c1c5a1001000140100780c0400c2001c4002000d1021034041e072550401c02030101c030081c280700014804081c0c0e0380c903226035040c0000e000e100e8045a00c00305522b0394450440842180d50441d04102045030b008a0001f003c250406c4030040c2c00224820080151886503503480340c101e0849041130016026807004a0307403000e090320101d02402626042540500c8800418036161003507051000b0703010440c1c01e0071020001800c0c20400210340242d01030007000c1e0180a00c0c514020300e8585066008040d400c04603038a00c0003003000c0c04504410420703030303014003070110044d49042407100103141 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 980367077 1250 980365827 980365849
    0x181c0509040509010e06040503070b011a070b0a090204020310090b12060f130b180613050d0e0a1d1b0a1d040e1506040b0108060a05061e03070314090c 66
    0x400365442e2004140da18030254055500001200240c03080f90501d85006900c9901442e4166041d40f0b801c00081a1300c2d00c483c402c4504100a0743c10a494420f06a58180c17480c5002414008800d60f0344031400f0141e1aa030005620480d0865000c20400d070074401110300720303000c4030102070107a0081101c2c280a031800140542d001903030a1118000c40d6a041c510180f40400c1200081c4030301c0146091049039181a20211913410120342500c0341036031090707034541d20340e01412005019039204c0d400814500f4041e02806004407000b61401d0040c50325803084811304040f0303035071802a05170637404001041c2d01c0305011381c1c806031800803114905203401c100141000742e03007444199101c0100005800a035a268848000c0410074801d03214512100c3c91400003a00d0304a0340c00780074034240240100151300c6200c10074810700b0000e122a58a03030800f000d00c200783d0840000c882c0d402c510203102064101c1d2400241d07209115654000c2280b440250b101c07021481d0107411400142c1c00400c0410741640c0c0d40350010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 980368327 1250 980367077 980367079
    0x80301050d170a030c110a030917010b0a080f010b090c0304080a1110050103030908010603081902030f030108072c240406030b011e2402030f03181c0509 67
    0x1d007000285007001c205107a00c40c040708618580014000381210b4258001c150840e19685950054408012505440b440c200070010000f80c26240e050004849000b18242502c2c0000c000049450041022803a80f000d02d0704440302581c01f41404820141090081d008007040c2a034031800581414a400f18050001406c002c00c2040040350a15a9520070514407091344521811070301c4240358420384200400c020300082d800101c20103004074815005008074811a80c0c0001168a022a21525180a24030b031400710b0045003c00c1001c0e200211071800994080c003002800b920405141c10700300c1c0500e80c00b0303820900120011030303002200d65007081c0c2210f500210300b201c1040c4440d020401e103290545603040445c0e11500e400404030a0007180c0f83c02c4c5044c2e400e586850001c50102c0400007800720030320310174266500d20741c1700d42e074a40d1a0034802980454140340116800d01861600404094000706e86045000104042e4000561780401400000d1040c4031078a4a04a08a40b401410380c400c0c0641c003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 980369577 1250 980368327 980368339
    0x5090c030708032a071802120c0901030609020f041e0308120708090a08070303020702010e0301150305240718030b0106080901150b033105010504050d0e030705130e0703140111040308030105 83
    0x1b803e042154040740e2000c240b114410305145007001d803504035a01300a5002e40002d02d0198040740103085882164008116a0105400c0a14082d43d13a00d00304581001046082c442220010009038040c0260000038001e1400c88850700e840040200031020040ca944001d80c40030103110003040340b0400326180581c0514003d41d5442c101c8c0016200c01c40410041a013541c645200c1403814400307a500441902c3c0300714255841c403007030310141e580f4a86540e0948013900c821000810b180d503000d10191840d49008c511029015562525103008c03c06090b44240045204102000b09641c0700780700e41e50900041240510120f42405581c0c0d0890000410400e0030769842032528026890854011304100099020300d0815510313840d15a018001c21f0341c0840341813150b40142442c0c540104540c4103017010150041c84070600d05010004030781e1400400e411800d80d1003441e0300c0c3c000400d020400103940241b0703110303182c154014400c070308441c01036070b00740400101404107000280340081180c2c1110011604 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 980370827 1250 980369577 980369609
    0x6080117010e0f030310060e0604060c0201020a0f0f030f0c0b060405061801231c1b0503160e07020d080c0901030b0307090b0301050601030603030c0605090c030708032a07 75
    0x1015004210341c21010b001031150043c0340c080454000001c5100300e0421742c803022910b60b154420342e4000c0b00711901a600640500c000c3c02064481c030940c40007280148111a101a4aa100c43c10321a0014805445c1e204441014409041c3c00c40c0f6080003400c803501d094035802080340c07203103206440081c104521440d12400856000d40da900058001d102c040d2400240d5940e5170356100c0b802d10f000006480291440c0c420700502c9103860451803a116078100f4515440080d6079441c0130010f4034008003500024055100410170b901e0800c041c00c0105040d501c410f503001c0c185501002c000800900000c2103500000c7c0c040c0310075501c03503046608001940346041c1c0390050b02c001070f00500304000c4120f80504c600c2000141c1c0a03519000004a01c6c1d05400030403094850b01d0044040d00c10600025004c9980308040070300190050740001c0d440380d001030980308000c104000081c00c1a0007a400b51811340d00c0421048000442d14481040c6000d4400e280c041841082503643e45a106a110f00311481c208609 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 980372077 1250 980370827 980370869
    0x20108041403040512070e070908030f2811010e06060d03210c0c06150608130c03050f0102180d0c0b0a050409021b0607020d050f070c0b030a06030b070801060801 71
    0x30980d4003400c0c0080c803a6a076410171214440c5d80b080c20b0f10550100342d01f2080072820aa000f14003102c1640e0350303400510324102216035890030320b5018151052800d079407240c01e46451002d0b110301d40c02c12250303583e440000d0501001c2d050b095492840601c1105d0304110140a442d41d034103540c00e0702c8951715040040b02c0003505c003510712020281c10300d4000c066003048020003849a10105c1007240c544140c1c070070420a4443d803003101d000c000d18010035010680000104100300b0f0300305001804103120303035041201d5680381d40c0ea941c14003807444100e01e860382d00441c100c1c0c1714440340300500c19500c07810b075030100070207102e62120440400248120159660001082c00b2154490300031500034084083c070a540d1900409101c0551006c02d6465061074010000440c0500b4401710341c07407130040300035600c1508054207140c581480d9800080300700e52250700c5c0d80c0c0016201940c607010314410341601800065903841c2d401e1009104e54000d00034802c0007141401803080c540c1004402e41991f0711202c91341e00c0d0010b192 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 980373327 1250 980372077 980372083
    0x51e0309011d06071406010f1404020d150803041a091e1c11010f0f0e040e0a0c14030609120706090215160c0f0305150606120405060105090708040201080414 69
    0x42c8050704100c00240440c14040340c100d14281301110a4201c80c90790303903520b1601020180038001e110b01d2006002c3d113a83d4504d01500074201e00f1003844400940d240c030101c0c088051100903480702240e5000494108a100d10840352428881606000035107011802e100003108417110018104400c00440072110722922803400071102000c4614841c4000f5415007054040d5449904d1482c0c0060840c1203082d810522480340c1c00c1074070145031520049142c1c807008002c06008a0300b118a4107100c0d4103a000d02082100000b10300a14884550704000c42400d424582400b0004103c0c1032107070301c440c5030201070890b00f204944180781c1002001518034040e00c00940d441d9040b1302c03070000386e038030125840e01100c200020304c4030042d1243c1c0080070410742d280106904a1810320015000c2c1e0058481018074070b400c80240c0f98403920003003005203040c04448248040042c142c0f016241540141d0040c081e80c10f140c02c189800070400c1c1040c01e13051500364002031004c40018802001404101020700c9a207a0230 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 980374577 1250 980373327 980373377
    0x7060908030c180a030f0f0203011112090d020106031a04060609090b0604060501030509191a040312110f0712020a12020a02041d0304060f02070503010f0603051e030901 74
    0xc05946a030328104281c01c4a11500940d030810000d45034a010140c3c3d5181c0310782000200c0f5070100144020000a07180c2c24040825510b050760155207800941d40490307e103030010311400c04c0070024030040d410b20100072494464405805019685010000c0c40454231108072402e01c003000c2c0b6031250007540c8624064020700303030f264811200f95052500303c104010b50101c13124841c480035241040340d540e0b144011800e9900907101090380da00941011900585400300d5a88100e02418040442c2c2d070889a411040c00e40484041d03002914107400d401b0202c00d507003d1003922a40541101c1d003885d040c1c042c4900d5030310913000010503000c0c803040040256070080c401c6205594003c80800c070408246c03d0044d450300d0016204078420381c03810343d140c000303a0b990a001c070000d12190343c02142000e040080940381c0c41c4075860a882544070300140050716607001d014601280c0d10340480420480d2540c0741c011310b001c00c1407003c1020303410180c0545200c007200105032401d20900340780c600c1c807402c02074000c1803901c149 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 980375827 1250 980374577 980374583
    0xa020705031c1b0906080603010b060d0b06071a0118050c0f48070b0a0f020a0827010201020306010e091902041712030f130c051008060f0102030c06040602070609 71
    0x4030b00f84800c0c094100001c0c034121006a00ca001d62580c1c1c01c42098220f540403a5441ea011405024045800b1600d0f40030f04095540506680e2500ca0b068a45503000c00b41b2003120100d02d040803005211540541207840480c0110500c248441d04050f16010014080e0b5142d403061392001180b28070140c2d00d2130240c03000300420720800c07003003440d14407813000042c1002d1070407880f0081e14000c00d2025401c0000307036081114004801036040c040301080803140d0012000d0341c0c17000c40c03045801280200e12444000c007001d116a080750551001c0620342d0310f64510400b201d590659205004008042c2d80003802203081d05c20403540190769030b55203c170b5202b2035445010314a00e40703480484c01040b10b282000040462010250441d2048071049401c20118801114080d040c042410081400402169071200c0c41a110b0783e500b80d20b860312000400c40b8060320307040100c00522214240200d5080500c0c80e2007507824284055807800103260308003a0b031084054802030801e41d000501070309100d41d540c802c10f041a8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 980377077 1250 980375827 980375861
    0xa1e032105071404031104151701050a0b0d0b040204050a15060c0b090601230f0d030203071721090f0708030a0f052b09150c02060a020705031c 63
    0xc52980d200004040032074800010482818580c200801c82200f5501205d074440e400c02050911403091202078104000d110140100034900841c408400c10407030510303040842c000141615203050341405551521503894010b0302000b05000128001400c07071a40715405032070100c0e89840310007030038008141c04042c00000c0050401c000c168035a03c45100d9680500901c5840c0300fa071109103940d0380700d08081c03040c901c4c1000311200f8001007510701001c5082580f002081100d00d43d40c139101084000000b440104c0041e00000703046400c00008001d40b100304c1403825042c03400d0a946001505414220b07035101c0140b8001000014407059041112500710038112042d038ac1d40355a21a2420341c6d0f03400c08039001d80803560b1f05a025001a200b2400c1d1104e009090f258030300035069030b0800e21643e64040a0b00002d5070345840440c00130075082039030100b13020392480c00020680c0e10182c0080c14081c01401501881d8010002603001c00d0340041600e0007281d285209a00010701070f50400c008100190f81140c42c1d00c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 980378327 1250 980377077 980377127
    0xc070305010e07050103050a0203131202010e01020d0f0e0616030e25152d020a0b0c0a090b0c0705010f05190302040e09030a090b160206040e0105030f0a1e03 69
    0x70b040452250f04031002a02c0601c0242c50b5039803a501a0f0000311180441160041d0400b0003140304c0035902d8100c40424000040d040c480c00780b026099034440c860101816490b00b80c2d407070200240d0b10401400c91032200182015003041402d1100200541000d00b0406880f607415000c4500c00b40010362510402c044110141511703511320041204041c0306800001500e2014000756501603000c032505c40c01c07040b4641009100c44c2d031607108004035400d0003604522500241d5070000303000d80d1a5500800a00c00041c4d20b9101c410b0000b0400904d9420000800c02c00740032542032081b00241e01c0054480074204000402e0480302d04a90720b0003142d600750803481c18042044032644d0107038001c05c02e992000210300c09030740c1e48a00c216580d220b245455000a0000c1c103003006016032207006001d0411352180c044c2804150741e00021504c0d0400c1e0001860030960b84010002450304000d05442174a01c90080c2929081c0c0f901c5040e404411414100c40215070482c000c1e040620802018801c0184800149149 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 980379577 1250 980378327 980378351
    0x60e01140406050604050709060c0219090203041b080d0c020f01030b54151206011514030106050c0a02090703470d0203010e030703031103040b06060c07030501 70
    0x80c08040c4c03150341c0038500e03000104a9440c411141482a81d17111340320805010007507800d0011201c0d064a1a2940b03c100d04000b00703c43c00b29000560203180102600d100c2003034444100c81a80c4c01f43c1e4400c0c8070551108100c0c040207034100880e10050f5404076220188000180016005031046441c0d00b9813200710240e10064200e9203400d650031440c031300600600400029002100c6034014404410039406503411070001c42d40440107130740d5020100090500a801100001c601140c09416120380d13690031132001400013049142510070039031035a180274419000e000c20101414841070207130b2010041c000940140600d000c102c008041170b03019080c40c1d034500c0c0602d4004c004147c0008503c00ea144942002c0a04840c406410089900b0001c01c80300c500c007200a508103507014400540b07800204803043c1002680d42071140717009030411f040103903585c0c82c42460014102c407922011414100ca083c81848040340d2900250360740181e065510503600c000321220249044120390005001e5030801030b43c4251 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 980380827 1250 980379577 980379581
    0x170d050d0b27010b0715091406181011070f0618060209040b1f0f11010603060203011e06090509130210031b0302070b040b04081b060402100e030604060e01140406 71
    0x508502c4200600c0c00e03600c0c2c4440255501c60003001130000d0100034030b05980c040c00c40c1c1c04001501d100740c654564030000b0008950408404954002c81c040c088003460262500501140c8062088450304200c00d070b107490302c540018004c2d000d0240c608842c0c0c440280c1049a598059486518804060b0f0740141c854505140658850001180178030f040ca1201681c134101240f190044000c1140d03011a61240e48400300c6d070108174010164100904480d0078034980310280b26902c0039500502002d0f070f482d07050070200c2c3c500c1c400029071041c00e94005039040040079030014000003611011a6000162380765003000c040c1c500308821000c0e500207404c0704000051905603020900300a4030b00741d140d110803207101040d022800b502e04064a40380c442000100090002800c1070781c00b0b80308140035030a0040010070200121351107170800881e6407000092006601d8908a803000f41d61091a254003100000c0e804251919000340005007503d486440714007520200790043e580034500510400e1182c030303003400d003040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 980382077 1250 980380827 980380879
    0xb1b0307060c0e0108060a090c090504050c0306010905150d11071a01060e0a0e01031101170f09060109090302030a030b13090809130204030c03030534020a170d050d0b 73
    0x3010074694590310f48694050b050700c51041c0320041842d4419482c040402d00500301c1c02580368108101e82102040c1c80d40ca5102e0580a008207100440d00d03880c0c6040050082913a94005910580010490181c000b40103400ca4000181408012820803244001c0e60040d00903001c0c028030001c0c0721003c6803000945a9000d50407544c0641e41c100c0310b0003040e41401100ca0750b90084500011051005001084050030340f8200290306241c04001c1c442e028000302c0140302d0694005d9088484070041c400c0404040200b035000d019418020003075014182c1d000f80d0350b03100d1402800107054842010b402e0780d5844032202d4003c012092801c2c401c4010a2510704142e038000c0030f4a0707104242641078901c1104952090b5000d90750b020001c0341c0c010b810360304d060310075070015040c1d105a6203103400c0700d40d401c40350400581e51804081038410f6000c4900d01c1044610540380d0070410811561580140c1d000900041c52204c00d081820b2844d580c00010900c2009001d40b001815005115603110488441204c49928 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 980383327 1250 980382077 980382101
    0x603010b0f0a09030b2509050f01051804180b06030309010504060f0207080706052d03040201120f06090209270106051c15081905121b06070e040e070e010b1b030706 72
    0x10b507202e03101c04030035104016036028094100027508088140c035409200140740d042c040900030b107030008510000a0070b81d03ca030343c04c00d6054102040c1c0c0d0410080008015500990218091342c2080d4101c00000c0803801140b003a40100142000c0300c02c0040d00a000440c05486a1426503841c60b45480014203a035102c400307006405c24000941d01c0981505c4000c150300407418124030703461601e840c0c00442d001e1000c542516000c913a40d509009059205100d220004c00c444e10000d80c550140c0c0c0100302e803504011402c1c2040034003408032003140702d900041071419a907050901d140c450380c00411050b5401c3c0c904031543c03011490803500440c00241d20030700ba0101c0e140142140e8032182c01c07030002d0b440521100402400e50380a4419000040499406050582014042880b284007010103441c98040151032900c0401c00340d00e0b4949003410303d4014107000d142d03290000c000b943d00e070541c00172a601d814400e1807521580880d00d0448501050900d14100f0007030011240c40b41d10908105000b0080740d0105 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 980384577 1250 980383327 980383381
    0xb0109020306061e0702121b0906092a0a020706030b040509070314030904050f1b040308041503180b010f080a0b04020d03021c0906080a0c0f0f052a0c0603010b0f0a09030b 75
    0x208d03a0384c941013442d68410039001d4032400035500c0301400f00440c0c1e1110049202080a00300044101450510140c01e080f0303801d40c014160245040c40c0030b41104d40031454280682d0822007004ad01450010b0f80100312548220030748940c40d00381d00214290700540081c40c2d4403906003030a0201802c0f82d0090350340a540d16251241491808500b4a40d80c2d01c103910000301941b84c2400f04002d0341401d1228244010840c2c01e02180b048503a29002c41c4881201c10200c1d80e4072203400052040c41d0b1102c40700340141410f0001040030030002d440340d2141c01001800207124082020b20f0343e04040c824407504001c2410908003070000144801c0c040c093381d0041c05480000741310100003c400343e41d540174141c60100c0a8540c100e0741459404122a000b802e2030955051007820045403503c8868200145089480c0140c00e81c10703e110102c1d05401c01e08200b0342c0900c01c90301400148241a601012114400d40c0340b2015176031507550b11001d540c50506a80040d001c01040001c01000c94040814805042c5400b145c0b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 980385827 1250 980384577 980384623
    0x1e141215100219020a0b0d021b01060f090f0e0115030303050708061e04060e0c0406110f03091908070e0a0c020d05030a090c0509130b0109020306061e070212 69
    0x90000200180d035400c001070b4801e031284011120440c0294040e00d002906103a0015183c1c46da10030164080b910503180d0b01d500040811044000b0f240070301410040c07030000c1c00007a18114800e604400c880c055989610f550300c090781c901c444954800200204150001c1c407178240c07410407446801d1440d100c10b40c0800e050100050105114854003446680d0040c0064902c8124a5004000d11106142c15402907a9108003040703c2040c02c0e62544a0118040126500e6042c1440103014440c007980d903052640c0030714860140040044265010303044103541001c480000a400014080550b51045102d400344c180003041070121000e149200702d001a0007440260800380d07040b60384400d0700091400060040c40403616408207500a4504c0c0d502480005000540305c000084c0c44a000792020f016000c1c0300712030700c0204099030610f51b00500131900d0840c250f00d014804603440344150b1800304030000e40203140d200182e9800c0290b0741b00da1f8002d0000398031544040c03070169840d907460100c2d0204604010b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 980387077 1250 980385827 980385829
    0x6140408070e043507050307020406030b1b072a030b040501290109030809030703050f03121b04060f0504080d080f01050409050a020f0d080a03150b07031e141215 71
    0x86a80603031010303480310101e40c14440d0130260450708040003c46e00c5000401c4448050ba4803401380c2409140601101000c6041903024616011601240101400002e101000105003541120303403c0650503c0051050505002c026240705032a400040c071000559082c003045c04070542c000c4005015400b6001c032007031000f400b041c3c45500840147c50018a00742010300000b03803800090440141e010301103a1b030981c0c803556850304040c40410249032580c40419804015021070b0a5907410002d039a502c60f00c13010b00490443c00c50b202d14014036090000440c204c01800b03105030102c0300107200314819141c0317003007214100404407a010f45415280c2e45046001062a107403034826984000d038450000c1104c0107181c0d081c480c0c11100000340e140d004500b4460100441c80c81401071021400542c0c00044201560081c40259000c1750499200300c2e90600c8030b500080e4108000944850310848200540800e050044504000503102814200300c042691850888440e0885c0d0180f04804000702071110780d44 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 980388327 1250 980387077 980387123
    0x33c0504140609030303190f090302150a0c14070503190c0302101a0904020a030602120f151809011d0c0117270102090603150319030906140408070e04 66
    0x3d44059068004002044403150409400180a00150000319048541d0050503044540144054000d608050ba081919185002c080c0c0e0b40028400c20400c00b041507000002c25412540c540f0b65942d000c0040c1502c1442820025145401032995103202126041d500040544a014400700d015100e1240020164840e07809004120300d844641c1c42e40d000d040500b0801c1c0008040c1060740c0000c5880c1000c0701241c100d0005140c02310452450030f111741020641e0030714a0170000d100494146074055240e4556444050900100c1c400d45200c030f83d140c0b500c8600600400040304a410394060f8444111070b0b0102c00300303207052109402d0f00c4000c15542c440811040510048a508d140e200c0e5a1413002241c03100014034140036088600010304191101020416680c419180540c081c0b035520b040300028581080114040e41c0c1e0014101d030351a201d5179018021015a00510007485039045803c1c00303c0341001c0a4400034020001264425503446000282048058900341c4042e1015485494030b03d2100c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 980389577 1250 980388327 980388337
    0xb030f07031101050702011b0b04020a0806060105030105040504080d1a0a090b0901050d0c1d040c060f0819182003030a0c1b0b0d14090a033c05041406 66
    0x881604141090400b0044942c0c0c0c2c03102504078140843d4402d1404140e124041202e0014412a0141d40d6410b0600401161b000316070320085031a4031607020445145da100b8156411180103071408580c580702d0346819002c40c00f605594031011850440e44020351100c1c0307a440d9811100648002442986a480d540280e55000c1ca01ca80c2020311000100710506000b0700e10fa5009020780380c60411992200c0700d20410314180300d02c030b600c0c0540103000d1000344440c0403e20402002e250030048112032400030013800c8550b0052074a00d00620314140300c0e100f4000340e08070203d10108620740400c020014500010070501c0603442d9881d20010ac0200e030102c1c103001045441c1c0f40c1890304d403100d40040540c0c9500d000f0103080b90480c0d4210340300c1381c0050003003400000b400404580140124000319507034242094404010906111580700041000c0403c1d00326600d05040207400721010302c2040340d021080758000300290002c030180d40030305003a284658040c02400581c1d807a405a100c1001000d401c000c0c0b039020b0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 980390827 1250 980389577 980389583
    0x140c07060305090a0b0117070314030703020c0a230a080a1406100302010210110d0207140f03160b090109050a050d3203072102180603040b070c140607030b030f0703 72
    0x706030050040080c100d47c00c00e00c058580007110411a00d80e5a041103080d80001751050726800401c0c3d031400c0540512010381620801e440011340b80c3d117451940820742c43c02d044081c040030002c2441580070744420305124003501c52802124040d8004c0d140c0402580740500142165000360400b1403004194a44c281007200d40590080910010003207a00001b0404042c0000700302004101000c1c4c141d003540090071429010b130000e0a0207201301d0640302d04103083c0e9080e41500e070b0804c2191b0000b50745503040440b0b5464100926814550750308201074014030403188041e1482c071034289018200b040008043d0a002d103142c0d80c0c1d1848050222140c1225007040d41d8060035850120280800008100d0183d03602000b245004010021030032202e681c481a103115400c0c0f8070b5000541442010303c1505048003e85098410510314981a242d19041b01c00241c00f5404005a211111091000c9040e000301e00c000301400344d03846402d00100144c0146515510f6600a004a80c2c5032200f500c00072075104210b0360 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 980392077 1250 980390827 980390843
    0x1003081209010212071710080706180302041a2b110103090f0c210c060807051c09060c0309050a0311100f060608062d01140c07060305090a 61
    0x3014400044500340208164500d6500b0320000401680d2440f019000b040552030740f03114590143c0240700d4141004040d0702003000ba01d4410000580700040c500c00301c941528002800f030b1a03c140c055440061070748040c1d0b00c141007103140d0180d140c070408103681d210003c407101c04100108110040703040698560301040c13200da1610460200d000005041020f80c414900090040f400b40c5e1007130200c0d079070175005840c00404940244020301040780c1001100c45904404032181003a9911903010780d4050165074200300040020481c050b000b03a0540d100040c50065200002d80c5800c090802029034803404e68015040c207145400c4c0d0342c0284124010300341c025010b0210b9146e152403d0f00c0c11320600758021414414000c00c00035410301e038807410142183e140004031304240340101c020034442d0040c0c00d45115040140480303100c01020b100b94510800250319940944040d0801a114083c0f44440124081e9000a03000211440031a825083c0c44094404218640b40c00185d40d82d140500b140c000c0600c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 980393327 1250 980392077 980392087
    0xc08040b010308090604080f1e0a0b060d03232d120c0d0905060610020321221407060e0607020402090607020613030c050102011a012d17100308 63
    0x28103004010031340070101801c010310b17241d80c0d40b44451807c1452143c8a00a40200c28181944603c0c01d00303441c0b85810030802000b00351b003691900300a0311400b404040c0b2801080074400101030140a2401c6900b034110520409500461081c550b540e0201c10450200158544003d24001c8040174544a84056007009402c18500c104022a880701c00f400101409005018010000f6458094815034601c644050202c6060031010711076818801804503080d0341003800300072280e00320100d846104400180025a050711000f80803500581c2520340d448182203440c00e40d07000d00200c9109614249124000c83d10241e41d550b00440b8040d01c0e0584003a0700c50f40c100000d00140c80c2c41d802800c0380e010000c04003882c02c800b660005007150b004401040001c0f15212040003801095001c41d401072400380001c0c04410441d0f000c1da41c03800540030000d41408028910300180c241c503060415016401c220b0303c0c9024000110018002f0444c02d25035012140303072440010600f0045080b20760490303a11142d610704103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 980394577 1250 980393327 980393333
    0x121204060e0109170c010f02120708130f0c03151a0613090906060602060a09050a02042f040503070911030403030c110604030918200c10050a060503010c08040b0103 72
    0x2408400c50500c0a540d00c2e50b0095002c50a0010040c100815200d0000d5417050020401e81c255014110000c0e20640305000510807040301c12107507030f84003504d813802443e155070380c180e41ca1000c090040085d000041e501020703030401440e20381d03038403c0d02c2c040e100f4480d41190404102056a58100300d2500c100f071140c40c80c00c002d09103200507000c0011111a140f00380707510783c500f00c0100c6841030000e940d4241c4914041010743c1e014400181c1145413910203209505054868540d00d01c0c06500c020f001d995282d001d90620484148854802103034100388142d4254070900c02051904640140c900ca4024000d00041c4100705204084e0803907040d8841c10308540c0d0ba40c505a0080400584c04400d0012003602d0300754001d030a1161034862131003511508450341c1030000311020b00c03441d6105404154504030100c82501d407500103001c0103402c848010383d1f460925a148074146041908030500e881c2c1007005024011040360040c400f81d41c0150000c000400580c04112401da42c10707500501010003900c014404 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 980395683 1106 980394577 980394581
    0x10f090b16110901030308190b090906010e1e0f0c041203090f0b0306181b13051201140c0309010908030c0a0905090108030d09051c08040512120406 65
    0xb0f01d6055950142204001400e401a1024031080c0712a200e603080e0011005654080c10400e03c600301808036540d500428003903c035551058038006084000c4441201100c041e4a11002e0f01a484802c1c1240560303501030701042450008200c0840c0c05001d08818100b054800e50341e902c80c1900e45618076208494580206480007406c005002641e90780d000b4502c420707a8140210251600c800413500e41032029015003180306000407032060082504602e41070101c07175003a0340581c11080311a840350f0803911070304e000200740c244500204038080811070285600014040000a040301a61503880c060381013104c1007405000d0029401c810298802a0b00300100000e840940895041a41064980c002d26000d10f01c501d40da59003420074000200701003c803100408800010810210000a010710300c100c0301520103118290705003503000c1c0c0e4101100d5a1200f41000e03418603844a40d03513080 = true := by decide +kernel

theorem cover : BRFrame.Cov 980215827 980395683 := by
  have h0 := BRFrame.cov_init 980215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 980215827 ≤ n) (h2 : n < 980395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
