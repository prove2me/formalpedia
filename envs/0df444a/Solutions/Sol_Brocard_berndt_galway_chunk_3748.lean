-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3748
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:33:52.745443+00:00
-- url     : https://prove2.me/submissions/2b07540e-5a0f-4a95-83ff-e049212d7532

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 673920863 ≤ n < 674100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 673922113 1250 673920863 673920883
    0x41a04020f042d0c0c080c0109060c05030f0f0c1605070512010e07080c060901262403030316081008100f0c050903060a021606020f0a020609030c0705010e0406080f0a05 74
    0x840c1003088280001d035000024010342900120300703c7c0e45410b086036030360041818500c000d210904204500b2621900b107401b030b51040340448054121951004140c503505202116800707191071090202d025040c022803103010b0610320900c201c0d1111a16100002c1c420300340c20070151a00c0e0744641e0b9030300c0414824801e4400800000c4002c0280308046000a0441c0c000e408403503040001b440307001c90a251404895188562507550745078500d042042840c046034907000f4146d409400604200841c908000044030311440304041007100300440e1400c201c414440140040c60003803540030002c26094002e100c401030a6003441c20002e451444030040c24142e90b4030100300c5003800024060109151800304074258000180f02d4016070758032031028441d0031060019400f4022a2001c50540c1001554100070981c0600d99000c852850761303405101381d40da00c2000c0403c80c2e01d4104140c00c02040d40504030042c520321004001160722a1509a8146000d403025015460755000304003030824000c6c14445403c030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 673923363 1250 673922113 673922201
    0x3100608011a0a0302040b0307020106140a06080103060c050910090f0b0301050d0b0613090b060f060c1b041b020a1a1e19090c031a041a04020f04 64
    0xc03035031526040e4040e4400d40c001c00c004000e000901807010034443e83c111030141480204250b128180050300034000c041034040c202e104208030610310355910f4401489801c642c40c0d030341d810708282c1c00c543d03680700546202100141805014020505250390700140b107034030400d580d51281c029516081c1100320742c0650391700600c01c2e11010030040c840703921380c0150301c1d0341076800096242d070f20f0325040c020130b0b1030080054420045510b8a5480401c00070f0105040b4010744044964080350b0007080100b02403440b80c4000e40384640d001888080a02000881e66a1246d500800026003d0440d140b403105035501d041130200141c010740d40c1c5400b04201c0300c1c484045a01141e18030015803508100031010407513408000300560155200240b00701c07510701110964010401ca05000090252800c0c1d000e05006020844854401d00b900e55490f000c0300481d94070654200410303980c0301d02c01000c00314840f04050400d90704a030030007406c0001c546890162001c0030b0400140100c02d0341e22500d2106410143e0b51821030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 673924613 1250 673923363 673923377
    0x150612020108090708070602030a020115150c06110301090617060705030a091e080301061b150209010e0406170d0c050d050c10060e0103020f040216030806030102070803040503031006 80
    0x8000011002a44055420b00700b152031070300c031040752901d130000319804a403c910586502140240e800b00c05000169141e03002444607c020412903125910203003c4d20109900b40791000800c9031103010503008241c0541c0001038440000c1c0200e2080c0d40c0f0980000d10f0b5991a01d10400000038201c013209580040c5c500601094244100000d01c1c510000d032130302c8946601c0704680c0050004d02c03000a100c13800141241102c031115481e001700c15400134801c00e00072880821160703114003600090303038125079403200400c00f030036aaa85011000390454000d40d81040803d4000c0c14907a29903210705d0010700306440380c00e4103d00001c0401c40ca07282ca030170380700c0e01001503100c0902d0000708009845c1042d00d442d81081d54885825a0006140440c03c0c083e08010030300f030a10016690f440d04000e01c1c143c034002d48844020031030443c180400d0303110b07080b0104808140c1d080010b01103403080080c00d03081000240090302d82900c3c2e456040ca103400645040d1500d800c004140000e040021005500515190400b08 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 673925863 1250 673924613 673924619
    0x303021018050c010807050d2d1e05090c3d020604080f04271107050c0d060b03060a090b0a09050c01030504050c0a2303070503030d0203062d091506090d020301271506 73
    0x200c8001041703c04900ac050b20f81d0f011580e0480c0074012102c5402d0081d041c50903200d031380003800e00d100c0110203190b00c0c45080560807000108035044003079032008441e00202031503112a541c45078540c0c8005951590708800b4840460240035800018940c101e80c3c02c0c40c0c20440401c0b0008504848d020912440300003410440c1d17000188002c11040c00c03240080b00d01d02e42848490410101904000442c2c80d894010582002440519903100309442c3c1d00441001c80c00d6038031441064115401068094500e902140118a0315031198104503030040c0314200340c50f072482d2102c0200ea5110129004030000694042c3c510301180d1112002c0d2401c41c00480c0140a600c2c80c02000c80e41300e02c10a8001c2000540020001c1d0750764598400001948580106a08481ca1802e4840c80b041d201d1450703d03841900041c000c2400d244003441040300080300106068034002c5488200070040080d4142282c165480c0c01c030007015080300401c1e0f00c4110322080c1403656101e03250f00c0d2903002c00035081801c954651904c01d041c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 673927113 1250 673925863 673925891
    0x60309030e01020c0a0e090115030c03050607080f06220e01020d110f0f1608070c060f0306030203061305070312050307020d0206070512040f0c0303021018050c010807050d2d 76
    0xea000c5400c1b184e42403806072030744103115002d0702540781200030705144040c0000c10030441c1c81511003201d010b074003a140d903511500e4046408440550701c00600e0554540429001c0c0351480520064041907440e6100030a0094218020b1300c2e0302100c50412139602055010418141e4010b500b101010580ca1901c2c8c800700d540700a80798041d07100c8142e0070243c04a000401e00c845068070141e03283d08200199100e00083c640500000b14500a080000d00500c9880c0981070107405084d05495004019198aa407900616212142c42103800c0d2020b2080f22400004600450800d07440c0c4901c035a80c3caa40c9203000903010380791000710480681158400820410b41c00e620100ba5400f80c8005103000c42651510f0803c0f04c0340c41c0748604040c040c0c190720309000080540021704800806215202400901c07900e4030b02419410307102e10041c2030768004640400c010340c400c3e03c5c210361000846c00c2c410b050401c0f41c50324508a451001080403046801c00004000c500c0700b8011150b100c0c0300640501807200d5000301 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 673928363 1250 673927113 673927129
    0x30702121606020f0a110636061603030507180807031e05100203130506090106030c12031b020105070f03020f1e250815060f0303040305121e04060309030e01020c 71
    0x1001d01034842000752110f4a5441200700c81c0c080030010000a4601040d180210b14142c2c840c2c1d401303151140008d030421340c42c00c0c81001d4a0724003442d00141c0400c40d400c1d031400c0e070103042c00420f0750b400c002c607259101c100c40765608040ba01400381400201101c900303516140301c00d00305000c07801081d150742041900c0042e10000b0001c0030f03114071840240c2c0725119100da00340c0709a41b120005105000d4182008100c0d0815804502140d0056a6050780c1a40e940e82145444d04006005030010f40c501011904044211007030b00c40c0c030b0b8810700d4903624080154075200c603400f1000b2000c0380160025011a54160020010780d030b8001150071688849801510159944032900200340c0003c02e0b40d1079188180042074990100100140710030b0f10788500802d071108800d014204c501d503124000c0d803c000d40c80341c100041900c0541e9480801041c20809900c640c8220f07400c080d4449a80c80d251403101050446060090f000604803528040382d20520781c43e020740002907000e86603045600c00d0b01c3c5d081c010f0303551002d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 673929613 1250 673928363 673928383
    0x2f0432030610091e05070503090d030b0f09060d05030f07120e0d020f040608030f0d06080c10080405010f18021315050103090c0504020307050c060f06090c0c030702121606020f 77
    0x30002030002403141412600084c450342580094030341030400c5080e0340c1050046100344901d500761a4401080101601110726144120b40c0009508170300c1159400d02226803500481c0080030310f4a02d040c2c40e518185581c0c443c80b2904101000403415404202d880d41c1020080c4016081081c000d48110002c2248811101ca0184c800c550880c1307222841e89840e4009805000444180c030795488440e1103070110385c0d0000307210003040303460058002a504808600d11211910042044460350418003040f10001405072054505d035580b0180f21000c4030842c0700e011950000e01030400e4018402e4010130260b00740c150301c0d10401a04050466601e0003003a02400291002401e000440381d0550034251101c60150b00080c1d0010f100000b03005130941c00c60060281400380404651880e81c070024000054902961095041310996000c14441c00c3d0310000350103201943e800300c0b8240340d02600000c01d001220010111250442c00c40d203044891030800010142c4a10700041000c1c03c8444c0354555500343d811 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 673930863 1250 673929613 673929629
    0xc0408030315040b0909010501140102070b0d0c02100c02070501120911060c070e0405160f0b03010315020904020703110d03090b0c031506040b0307030b042f0432030610 74
    0x1020100b550303901d0741d2020002c1d00000c1e1000da414600203034070710700925082c044c4071102e94019240a600d50b00c002184400d80758400360345400c103c140f0207400050b01008821170194062881c101803144214460301c8100320155000b81881803034480054041c004c02044880001d040c80c01c02000708025003e40313072005a0541e80c0c01d6549002680513420103102d600818050080401417000b40030000441080202c0801480048559a00385004a84003244240c2941c41000d00c01040400c3d013414504140541c4803201529003002c1500080c1207034030030401113010039204404032140b440b007002003d00c0380400e418104003014041e2282d40b13200c003004190854100300000002d064400380c2400b512885009400c1c182c0707460300d80b0020900e9400460340c0c07900092520700d07542c8035480c0034003d101800e0402c00210180341d6000240c106e100c400002c1d0101c0480c0f0411000480310607e884001003c2c0b041d01d5002441d00c4891940040c004401c012240310741d226409000b5942d80c9d10358405c086032201 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 673932113 1250 673930863 673930891
    0x10170712151508101d0a050901090f0b0a06090c0503180705130e0c04060b1209070e010605030a0e030a09031a1509100504090b0403020c0a0b030a1509230c04080303 72
    0x6003045184c1048142c208901d440c07201d6002e20640c20710140c0762401421001c40c18882c0da900c01005508903000c4040141c1450503000e00c00c070114010750b540d00d0300b0521b02e92000c10515140c404180c1a1401d80901c20001003001040204031003403481c81c00380c1d2141580241c0304140c0f4103400903850306da2100345201401d981d8520300f04411001c01400e000d06101500c10b00100e41d54010b2030b64580c01c20301307880b9144075040303000aa0100d408500720040c0c070f071001103030302a69007010402c40702c5801c001c2c002c0e02881d03a10400396600400c10800303001e8140c6a565503088442c19480d1100c0143d00f1161064040d072441002d1241005218000603101ea9040e580d02489984107800031701200a1948070b1078100380f43c9809102404213011510348524080d4003102c9507000e80d20144451548140b2840903202c0e41070020661100c065004100f0304402c11800390b540c1511035502800b00e4201240e070b150140c1201d820180310b94080000c1e40d034000e103092030241c14285400320060712403100038105d654001c00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 673933363 1250 673932113 673932121
    0x1110021b2e021c0504080418020901090e040809090f010603061a0919120b150319060c020109021512010e01120204090c0e10031e020f10170712151508 66
    0xf00044115259208441403019003880d0520700c0042c0e0080c00b81c2c0500828a940c81640d04505000319004058180e460042583c40e005c0c104a81000c0600100e071075841c2001710700440d55501003945c0c0140d13001c09142000354907102c1c01800701c2d55954000380c0300c40e000003070800fa19003411059941c00403081c1c40001c601c0540036200e0201007510740085c0807111551721410284031442d03148030321030710300c1c8080c1d03016550702c1604156444490809000b0303040e0388601c00e900000c01603041208180000e0001041c6490160300183c203500b0701201521050b200030514045400d24030715290300402001240b644254146548100780d03541c2e0b204064080c5450f9041c01042205107080c0000a0400c00c40500d20f0b400d140032103070b120103550701c0151491202041440304080d0b01040001c5140da000300201040d0f8083c03024000030403040f0080c0d02c2408034a00e0b1019a0304400e4801921900c02a071780d10f4009503509050402321481c40d4101000001314403c04c0c406070341d501c441c0303840c00006428840b007180c0d2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 673934613 1250 673933363 673933387
    0x1b0102160509130b0a0204061205010302030606010c05032106030d170f101205030a1e0c11030a12090f0608010b121f0611101505011110021b2e02 64
    0x2001c40001015081361004101907180d450340500142c1d4056680e144d010180940801c095076400c0c000654940c101d280483d505602035009500780a21502c10b0f6420582c0c0114883c02071843c0e45002c0b00c00141c400c08018007841c040c0840200d41c0040d0804610100300901100705141b4002c001910014110012072024801d03038600b14002c2c1b0214919007038242c49032800c191260098180c40d008075031419060f0402d1200e00210751000e010aa6801e010205c1c180c17203072104081711400d05501400780b1201040414255400141424803a455044505140045003091182036a129108000d011001030107402e07c078104607020000c801c03096207010f441d40c140001c02c0c00d00f504400d0008041c070180000d201500080c10142e20065201a2203001824039a14000c0e039540c01005030440c41d00c44024400e56009200c24070707901d010041240d090520b00c8184038103c1e80045001300040d21041f10340c101d840320402c508103203404881440001e170b0128510040859000b8034002401c079401049271810a4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 673935863 1250 673934613 673934641
    0x180f140601060504180501210819090e010b0a17091507031e0501080705090c1b06060f060a0c1101020309060d060e1e060f0d020d03021b0102160509 65
    0x1455040558440d540c1d5050080d2481d400b900c10404074003050068400844814426241203400d038001c51b0030400c04c488410006000d82003411103050000380072540e20507030715002d015100c00490315160031250400e008912a01e40c1648034107000041003000411680d0720001246900c13412281e51001626940c158070700780842c00c000b090120f040d0b082000a05541a00a03690b200c4c0001d4000000500403c0544103030764090080000d640d214010401541c01d009104a80c80440300031041d0034608501c0c151100b1404200003e4410360090003404403a11f800242011818803ca42007854920301c6c140c040c04280c1c0d413000280c9141941a80410564000d02c120303051001c00420107555116054507940c0204054061064005007040000390011303c29031010041296000011055a9441e81085241c40041603520740041488902d080140c40780b40124100030300c207401074a540c41c1081042d402402041d00700604660000401611100c1104261020381d082030b50344001c42e903107110442e0741741c1c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 673937113 1250 673935863 673935893
    0xa17060d080705100c260709180209040b0d2111011401031b0302090a1a1e040b1e15070b011d010e01030c0510031b21180f 54
    0x20366002800340100070b008104c180d0000d1201d90104050440401c00b1116401c0d1002503c1c020320103029442d641420840840743e01c01c44925049a00d2921001c000391000a150080d14038140c02203001ea14602d40307030103034100c04131007030701e00c2080100c00c1c0c0c0710300c50b245400f010300c4030082c40d48083c1d4180c103a00ca9040f44480e00e20b000001d0000c640d0711803c1d0354400c02e00348001d03100c03a0a0111015040d81c50816003c08903900184014125142c6034420401400050341d407000704108181100c103d0788a64802c48411a884c0c03068400c0360210106101c00e43c4e0641a41c00d10840d801c01031480b08004514401072586c000750740f40100603d9801400070035120321200070b02000d140100001d50700c840002c02300c40c101e525884421a07a6078510b1081d80c809006e00004020801e60711090089040641c4041c0c01c500e518a80801c450075079490400591080559460001f0005980860003d101c0707014200c00000f603940c200042055040c030000044003414006215842c1e0030b980302c051006404d280918 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 673938363 1250 673937113 673937123
    0xf11040b0717220815060913020a03030801090c03092406030206040e010303140a020307030f050d0905010c020c1e010e2d10050304020915130f020904060b0a17060d 72
    0x140341c480744a01c0e4904902d40d83e03100640604a0008101408042a080d109843c0f28003420155243c0b0001c01c03160f0807008000008110492030f801015039945202c8600070740c043d44440c842941020009402c3d101058080024942445806800585019260003440680d01070703c02450410701307a404017074007440d8000396004202080c04945500350840030f038126072082c0c40d0f1005510b00c0d801550002e014402c03030403015820612078a4040b034091440107002030000e00e8050700d443d940c0010346003100c080c80c0050305c86a41d11105044042d80401c070544412104642c8103c5401005640c4440c948541c0c413800d040111034154a44030340c9441480c5121141c0030701e100c2015480039442c0d041c1412400ca1203901c03900d142c4103281201401103049a00a90f0050031007021030b5a030309102d84410007904400ca412a41c401181da0003600f440c403900c40d003654400400740e80c40700c1070350030082070343c0013900601e540000801132a00404c1d0040c400d140a10f00f02c0c0342500b010360707504000800c22400240003030700c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 673939613 1250 673938363 673938367
    0x1060509101401020a081602010c12110606121b03070305070303020c0315040b041205130306050f250c0305090604080d03060b0306010e01030504110d080c010f11040b0717 75
    0x1500d081154814000d44002c41c002d058000346007001240d4a4070381400240607040d00704513a40740001b040c00d41d0160b40b401810a03c3c113404890f40d681d81c400f2881440d190000b03001d542d01080c101c40610006422080c02c452032042c2451010398a0744509160450100c407001400e0046110748007489a48000d5402c081035034a01680ca0030065107418003103103030314460700034030350030f40b0000d290303a90b03028011500540381180c16644c4d030380c4105408007004406000e2050900c030078100e0350211203981c0c014611980d400310705c07402c1400100b81c80c000702616944041c401b504680310351410b80c01610a10044524000c0301c2c1080c1401c054482d4495403141540001d03000a02003850040040c01c4c400b204041c0e40c040100035903824040c1103601041d00e04278001390300c0c441144c8083d8403e4001135005802036001d04075000b094000103041c0c0150f51800c44d4141800710301242c0c051404c2c4100182d81c103520300c0c2401000821950344000740701d10302900d2203480c40401c81000b03010310004003d80550510400304c1e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 673940863 1250 673939613 673939621
    0xb3303070e01240201020301030c060509040b0901080312090a080304171207030c02160f06031a0612010312030b01210905160527040807141002180d0b0402040e01060509 74
    0x140c03100b00300e21080f600510080c610285010710510869040301c1e0000101040f65003054400c407165480b0500907a0f03c243c85103081c8001da41c61800880c000c1244400a550740d00e00c3c0480b00807424030090001c24a038011403c1c0c0000714500343d00b207a074069071201082c44621040c2c28061158001d00082007041e60b051820402c82c42c0d059400880022582e40842c1d120724030202d0500700004681c000d41c80c6107015800c081007130900a0700010b096280301c1320301d040300c4208400400c071140c202103040080381d01140010010b002003024040302c44061480d00b40280030065001900c444a030351008040c100c500903002600740120790140260903131000c1070759114011001203040d800303418005d040c41104c03c443c9607034080d28808450814000010322400041d9556200c3c26440e411079881a034144a108d00300b6a9200000c0c040c1118500207a00c0050329184400e0080103004003160401c3c0c02180d82c05003807400704036102c4690754000c8c1d040301d02050140401349428090403080c0e10040e0407800f103070148 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 673942113 1250 673940863 673940879
    0x7022112180f0d0c06030e0c03150f06011e050702061908151219170301080706090b0a0206151306030f0203060a1103070c05070506040905040b3303070e01 68
    0x607800e400811101d00c03100080d141c0403c0000000001c00800d0101d6091080103c18025003003141c07515940010b80c0e20800325032000c0f03130403c50042c5150501c0740181040044201c001035a040d000402840c00c4000c1107c0c0040e0f100381c01c0d068002c1d90052100208040d400c540e41c08040302c181d0f80410030000040f076640c0307001070500402501c0383d540310480c0084045807810a081100c421050020003002c00400c0c2c45d4040d404550030301c0003500e6001c1c409084400254035680154000e25040c0c004142d10382c90500004c00e40c03c841d4008108140c400c005550005500060309a04104540029148001d00e14000f8050b112881d0240c032001341840b10000900c0300c44000014414002d4041d56440d66488280d001192144100e04c00e4226003400440c03101841901c1981d1482e02c01c07400c8907207a40d110340020300c0980040c0d11451081d03841c1d00422040100e90005550040306c40302c160224a84a9145e5201c203180006904a2001c03003607828007801c2c1c0e010404000100b2120454111550f100c640c0703 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 673943363 1250 673942113 673942147
    0x4091803050a1b23060601030b0604031e05011d0c22150e0108030a03050f06010c030813050613050f060705090103150b07030512010e040515091e0d02011107022112 72
    0xb5031a0b03015490001c1c03a95400703270280c003444150050486113054159a502c4001861007080c4410040b1170380a0720001450910030080001d407240c2032440c60700c0081d80500e1400308003204250184850a120305a01400c00c0c080b0214030a051390041040200b4040601c00b5080640c001c080040b180800090271800c00300050a800030036a909000355910344e046901300720400c3d101c4900042d0b800b166100442e02c948a03464200082c21410b02c101100764803000d280210a940c40314150014000c54410402c0811551105d044a0f50151005103040f110280c1940500b518643c18180c5a542ca0640c11031307440446000307424904405074950f81c46040040c05508503100f0a08074442d140008102c034811401080c1c4034591003002003816490f6000310160030100036106a48a1081c1074001c2800d4031403030a00c4451050a900400850203407840003402d452402805102c1d601e0708018070409a180e8522040548600000e8141c0c81e00402034083e02c1c142e8201c7c4070104010002c1240c502810f40212 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 673944613 1250 673943363 673943423
    0x10c031a04020301030f08070f0f1a07020a0b0609190f0f060e0c0301030807030c2a140a0915080312040c05040b03060f040204110c0304091803050a1b 66
    0x20040d040051040900c41240b02c01e000203041c070103036440d503240021128401048854800d45a101080c041076550002c194845141140c070140c40040031301d0741200f0314500795030210540c402403000d1800382d1165008604041c1c512402058403400042c8041c0e04203209481446441908100d4010301a00c2c00c2d00410043c2d441105440c1006000640c0320345500c0340a000d02c1d40094410b145900c0c1d0380d1040c02983c02094101c051080051070000440c45401c0d500a641e480c0b10b40482031032440d15861004010742d608a09001c540e4441c0700100c1c1e40341c0d44868020f8070040c84000440b0204210742e030310808607a40c09201103110010383c2e2182e41e404c02c20502c0c0654860b00003900302980f11002c000c180c074114035030550194024000501103106258209801a0002e4800607040300420b6140e41c00c0d61080708082ca503a4000a810080414684503003103000c1a08141c8540d80c070b1080c3d8000341140300303045659040200c020200804601c54a0111155036807200c1e854030910350f140881000343c00484c0c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 673945863 1250 673944613 673944641
    0x70b18040c0f1b0f0b0a0507020609032a030c010e0a062003040206130f15020f01090c29130e060a0308030a0c12050408030907080735010c03 62
    0x103030400c5405000340110407510210703445400340748280f070320805a6603560b2201500c0c441d2501d0180004a08990480c5010b0750304e030b90b8045810303d81020041e00d07041014002c21030329441003100c05400800780d620341165042c02e0740110040d0241c00c080328503500903c0d940b1103195103004146ca92903e4006148101184a07050601000071b035000e0740500c6e1030f111002c0306800c8500f003001400510300040100f440351640035801110903105c0b1741d10103da80312500030003085200010380b0801d8940401100074405000b6000f80940403050791030548044603031240d174051810140c0c19502000d0b656190312030648001000d030391110306031400541035400900c07540c140985c200f00859a981041080d10702580d8001c50264074540764035207200b004054042c2110b080084400008850003624000c0a02803405150102d49030f0a18400003420186503920100c130590240328100030a60302560618045110f030f42c1c001840b0000c5250325811044040341640329540b8080c1c14120043d0554000c0c07541200b00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 673947113 1250 673945863 673945871
    0x308070207030305041401021e06010f0f0308070b041e0507030201090602011a0f030708330f04060c032406030b06070f0b0702010603020d06050f070e130e070b1804 72
    0x9a10160786860490101400040d001c202c1882500c1403404980394134001881255420381d200701c41000200c0c8120840c04154118500420450300102c1242016110115421751101d10b0350395021104d1060001c001c00024008001905014007001000d02010122060342c4102d601860525140d02203400201d0100c1c070003500c045034bc140b05105403000c0c040ca20240c40a080c0342035040154401c0888005a41440341e49000f10b0400000e20009010b540808011074400e070f80000c5600740ba1410280e1881c4030001401004461070326064a01d400c1a081100001d0303100d038042048002c0c2140403415800f141e15543e000c1c1141183c2c007410000c8075665036041140700351050400217140714402c0041c00d4030388031741c2d03110000c00e02d00749590b0740001d103900000684039070303e50108a400720300701c07005d407282c0d90756004011110f01c000c40e1082e40a0074924000d41001c150300c3c005490689520400c4805581e81c440034a03022000b000503030058003980000381e403541410300301c9001600d20050310a000f0f90034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 673948363 1250 673947113 673947121
    0x2270a15020106180501030506060909011b0e0a0e040209180304030b01030b07120506031e0705040c0c0618080706020a1215081608120309120a08010e07111f090602040e040308 77
    0x117114260603240d0000142ca59521090200b200c82140500541095580d820a02004c2c40300031040c0c048000039034540001c030010410421199400340d50040480c10101000c02c001648c4405005501032002c100315811020300e0180d00e8614082c5130001822820340400210604c1150081c26100392030320380c0c072801130038aa03c815000740c1c2d4007a960582c15500241c0e694018851244016466a00b40f80841c0c19040d82c0f14002020344e1400c220600224030581d449005200403070061682c0d0110503488414081400c0d5201000c0b03100c6c00d8000380080394003041803043c1c0c1c0e116507000140314190101c02d029010350210000411400340c07080c100d181c42a1448410b1030b6031b04540c064202d400001c00b44c040e140c0c40301c49480e01548014040d11445c0560281d20f40d44001034000b0b41040300c22540c1e113411540c1086c0c480182c011010b00881c0600800c80f070400101e1700700003070422110080d00304215045c01d031240000043d080c030b040001c040e07c0c0017080110b01031542d40300d110721540c005d55426520340c807 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 673949613 1250 673948363 673948409
    0x5030d030506190501021b0f0a060c0c1d1902070c03060506120705090c1303151a0102010e07061b060e0109030225051509100207050108070302270a15020106 69
    0x43c070340c0b04050260304484130b501031102440401c0c0018070070151086040c11100c2c070000b081c50300d4507004000454502680d110601610171540005408103d462102c0210803124503c09548000c007071451007610510303221006020798050303a4013a94885240340c5084d481e840c110025040880c0d0b40e0780036650400116002d06d4001618401b00c685c05041403606071582c5c03600c0000e03503105105418075032148002c0040001d1411044066052881c0c10014100304c5440f10184030017640d00e00c030790442e81011802506880301143c60f5007221183d02b0410101d00310b08003a41081d050500303014000350f1a150301c1030f02d90311043d0480c40e0f00910a90170f841c0c0c03c840d4240c422441c070058103440030450f0404c44c0140024104072048064003440200ca4070b0801803801c00162000304c1c0b1850860040c0c010070030401c46035030801c44a68000340141402d508241031070980c046000c02c0307044101da040b01d0408021915881e0104008044e00c01e000284005080c40200030380079104510610506045100709090020 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 673950863 1250 673949613 673949659
    0x12030c0b27120306090a0b150d0c0e010509010f030f021b070b070803041511031807050906061e040801090327050901062618070503012304080405030d030506 69
    0x361848940600310780700c1c4e4080c0100690001d0407205034a54030b400c0c9820700d81c1e17458403482050b2500c3d04215660f000125a4906441c001c20100742803008036011044182c2e00706007075401d010001e18094417000340101e0110041c0c5444000709071100d20014820304081d21001d1010000c001c01011521110b030760b03120505817031044100c0984140c000f480802d002032a4540700080c088110100422044081848614250b009540b2007440040c11400a45000810701c02c2d000140800c491085d41e0740380c5000411520b10034859000f1082c00040c0813043c0b0303101131500780c4002d0040030000b000001c04e0382c50040c0c00004c040008900405081d6550210128500a1038043d40e1000d44583c90b1759280000968024110a050500ca50f2101043c20142d0403c420410b20505042450035020f170210350041e810410b2076040306000340d041a00d540c2c4603140010382d0610342c00584c1e0420540c0c0d60742d0b061145603802182c1086515004002e6440741c0940c0c5504114002c01d0101c03942481803142c003015440308 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 673952113 1250 673950863 673950883
    0x9170a031b020319090e0f01080d0306140d1b0618090501060c060c0509040f150b160f211706032a010302120f012c0112030c0b27 57
    0x140d00410039100843c011040d0213401034030303504242c90f501d03468a1b40034041c18030890307040440b010b211004100540041010070f1942090f410100312080c1082544007110110205985c0204400c5240a00701b0010300d1061150364070000034a04180c1e21040f00501440c9500c0042002440e00c28002c514100540f180c54102c44058440120044442c0d450001800b09081d0b0320301071020074086017041d5107a030301404480d11100a00060f401031480ba1090344541b658008416082d81440801e0002d00741c0b200c00d0545c560000d03a02002202e262814010038001800500710440d20079000c144a90f230807041c101d105d0100300101d2038013591800141070348c0c1c8030002c0e02490552411401003100790007030001100c3c002e1043c90003510308922007640300c2c40d003401514030703030080598034004000840d40d442c4942200c0b4250711900720034202c484042e0710003580600130b41441407030303802c41c61003090b00030228a11030700d0b40000c00800314544486008000310618440d040211490101c0d80300039034021401c2914 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 673953363 1250 673952113 673952117
    0x140f031206032a0103050a0b0904060e010c183506060907172e0305150f04020d110f0a030302010905070f060f110c120a030e03030a0801030f020409170a031b 69
    0xa0102a0011030103000701170301c03081241e6036400171500f827511442c02c0d40b40708a00400e004154025042c0c2c505086681540c820020414400340304060584d017096404201c4a8010566803455030409007540c074207258a0185004000510081000b01b001040c11886070700d04440c2c2202c2e13643c8504050722a08480b00c6d1007001c0b0b41e118000940c001d45801001d41e0500d03103140511070f075845010206e822058598000f40d48981c4100242c0360810300200f800c50b400000d0241c1342d1903504059001c41c54541050100070440b02c034000d4407a4807620b0b100c155005e601c000400d00b80c0c0456917400c006e4020310215406840d240210400803401310b144001d14411601c0e907554031080d076008207204942c2c03200307100c002c0045800b4048070b80c4610755030645103e105601707190151660309440c1c40d01030300d00010452200d000b5041481902c81058000000c903045942020b5010043d196500c00200101510140100b5500e20035205009403034410002d8903c03003140742c80401814a0350f5507034507030135418501c020340 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 673954613 1250 673953363 673953433
    0xc020d14031201091b0f080a0b091e060f180705070b040f02010f02060601050405041805010f1506020f100504030507050624060c0a1b0902030c1e090904140f03120603 73
    0x6c280c42c4501c00351540b01018000c00101e4128140c00035a0001086d24041901c035920003080803510511003490b41c008008030b13240300400034248080b558200425485080c0300641c840041c518038001c00440d0041944078521070400d2509281038110420052010390001d0301001c00d6100c007500010303095005003016166181054a41410000a410f6601c65010040d015104100020708240100300e000e0a07000b0300818004000c0c142008480180d13403140d000c40d8409081800c8810b030201d0010704020b802c410205040c0d0741e0b41401d13660342c415000c0007003080c458041000303460001008003120b01c01c51003052094a040315010400d503401150001013564004a0000000403008a510502102c040d4658100c03a035407074000c030003283c2007162007003d0258005035184240c10010f031807444030b080d4590280d04010303c2c800851100c610050005003080d40e500c1a2500f2050b082100403407500001f01220360300c020303000014440241c15a4250300a00ca20071504030010328802000c0c42075034442440389 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 673955863 1250 673954613 673954637
    0x20a030f02180f21010603060e070303080a1503080d05010e07141b19060501140604080322080a03020c090f1308070606051c0b0f070c020d14031201091b 67
    0x8114030304441c1001e50300c2201d4405404c2281c078040b00d0300e032400500c1e01c000034049185003081c0055441c902050206c90704925002c0c0700080c1c0043c0001d40040e200b000000e051a00c0142c404035900c1d994101505181000c20003004074010794201d141603030020f212824040d00c4406080d1402090040c540800f201c0903c145034a03072140381100340c5c450105c4006ca8041d10341360807a00301344070320301c440a4800d01d858000500c18000134074810380303404000355000391134940f610300c285031079010342140f107540c0c10703440c07606166510440d5180074003400e500015540030107880d181c003035516081c6a4907140511902c00001d810f800e18102201c0c0700c0c0c440d2690f114505485a540c45c00d00382e000c22001c8650a41d43c84004c582c60311070100c10852030100d2541206280c1040c2040015072400401188003840300c2c00402c1034441d0300030940100b1507030503140c200d001266841c1c8000075082100c2c00100754800400e1100341b4840e00c005040c101d4000d00820841d100ca25600d00071088512403841022500400400c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 673957113 1250 673955863 673955869
    0xc1b010c0305090307030b0103050607140a1725120f0c14030a0e06010905010e060306010f120812162d080903130608150103140612031903020a030f0218 67
    0x101120007005055440e011b40b40e69640c03c0c0003400ba0416070300399025500b04000310b43c20841d41c18030448801909800c0c4114684018090360041c10302c62403003040000804c2c9140729054400e56100000404119103901110005140141c503e041050a40c01d248564100400c3e51241c211126000c1c0c0d07034a01c5840442c040c0c00e00c01e60015100b080e010340d0302e4203035202c1c007181840700c180685004100480c2c5545440380d0301600035006811148a5000407004004c1d00c806a205c5c0000c03100c070801990504d40c00c6043c031320890f000d9181a03108030000501044110150944a021034800548444a046001c003082443d510041c3c003022040b8039081c42900103007801884880d900002007802c0385d20f02104e0a250320503440da9913106d032012403008d10030311604a03960140958211710170300c0c0802c0a0324080d6614001030b40c0140009000d42490741204c0c503030072000d0041b2007420340c001d5808401074008040c001d009500c1318500200080c40d04070081040c1072540211178004820b0181d80c083d0103000010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 673958363 1250 673957113 673957117
    0x9010b0c0c04110316080603250815160e090a050702030d06030c080706110d030b0f0301230903090105030c0c1c0c1a010e0a0b0a090c0801030506010512030f07020109030f080c1b010c0305 82
    0x10b1803100b00b500704000034038542d00300701540042c03440c1440c0e18000e0074400a80202c0100710733401d000520582600e01490b0b5100c554102d40e00c050312000c04552601c4100382a4198441c1ca1242c21200d401c0a002000380040301c07811000b1034000070101c0e1400e6664000407641079041a040c90381c1c0b904200c0c030720500280b10f138201d450100750040410204a6054000030b00310b4044000b411800545030094040046008404550183e4010059071074410f541000030309038440100f02d141000404205454040001c0000c51080100084080300b146048000600440710118045640310030300218200d2802085801a0403698040c0000210380c507107c43c05030140c1345089205410ad0310300000042c20100707600072805100b2060321001a02d5055090250070150b05801060091aa80c4126801808000205c0d40c90000d0001007585800d020704c0100c0c0d0120031130b480500040d6500b9250018810350900a0005a5216044036015548414907400b01b03117100800602003981001420042030107640 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 673959613 1250 673958363 673958413
    0x60f180516030c02150103030f030e011109060304060207140a060e0304050a050913060609061403070608040201080405030c01090828080c07050129190509010b0c0c04110316080603 79
    0x65501100e5500030517184003000340e1081d000581c1d03000c001b4030385640610460440c054044002d00c2041c030903000004661113650b148a018080c000000b90038403c0e036606072041d030b9501201ca08446900b14201c0d030756400d090302c1c094422030301d0b009140310b5070cc1000080b078040f98030107020750710380074540410010750500050590f0090741e880c0d64100c0004180d0710880d030203441401c80c001500750810650f0200c580065070542d01944c4607102c24428107410049056115a0900c2e05600c90759851800f00d0840c01210301180386582030002e88003c03c00c0041c080c0a445503241d0307000c029031206046541906400c20360060104038200040b0788041030344401400c03d24000c41c008100a80b01080d2442c4120703961040105045810002ea0440d02e07001006500001c0048814140d10342481d0014110398018443c0c06940500000c02d1540d14005014880640c1e030020010401441d601c1100030b01075000325092030300e011304000344404c0a8010341005001750b1001e00104041d140d40000048001b2802c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 673960863 1250 673959613 673959617
    0x11040e0c09070f09091401090203040f0503040608150d02010e0f030a05070b0409290d1106030411120a0f1202120403140c06070206090906060904060f180516030c 71
    0x4584803035107416000324007440280e40c0300026904551801062101650401041941441c5c0c108289403140641d8a05440301703d040144c3c1c980b44c0f031505000d480d0f07034002e00a042d400702190004910303800200c818070136201c0700b4502c1c800240c540104041541e803420020b0100d182245c0310441400c3c041c900480350b01c0c019007142d0000741c481e101e040c03a00110340d02c2061508030004003400010f000c4d02560503410380e034400d01e2801900c80c07010b02c550441d40390340c41802402d0884d4a10280b0260545800e12400094106503481c1480e043c600541380c40c141e80140900243c40c2140d04420000070207401032a0030411201914001303589103411603041c0c250f00300c11441035500c0482d0340c81c0e50741d00510045202c0d0301c0100c2c4014142103040c5c180307403510b001c0c107100f00b0043c0b0444015880c3c030021034189160032aa4604160b0724400020854056045e40345c0e00035180280c041040304912004070283c1700c8a8000803a440540444072069410072220031034554084464400c102e40250020b1040640758 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 673962113 1250 673960863 673960873
    0x30919051e0f06040311100315030b1f06080403030606021609020f04090c050703090e0c16060e060c04031104152306210f01230a0305030c0703030f03060311040e 71
    0x20030000f480358010703410540d100100b1055000c07107840d281c02031506d00c84841c2004e21061611703042c0841481c04c144000b824607005079000901444280401039000c50b80c221000c4c280c56101d00005201403401c40c1d0031408640740c0710700403810900009100d0080c03110400d5401c0064181070396400030790417414050384200801c0c8404142c1541c00c0c05041c02d010915a0b40c2038035800f260400034034615440c1e220502d000e0881040c0a6000c0c015400c90394141d500305039402d4141018074110000300165010b038102030207248180040c8103002d800a004485c0a144002081035000c02000100d0700c07860300c1c0f4a070800451b1f5041020b0340030710094074041c0513682c0b035064000c03414401190050740300c0c454400421036032104001c1b0419003091615000080c0041040c5c45605150301100c0712820701d1503030103501709400700c0341102d941c0f66603008000d1540101529124507112090640d01c9050b07000440214034648070503014240b02c1d00c00c0e101160342041240c84100812800d210050680f41e072100b04030302030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 673963363 1250 673962113 673962139
    0x903023a05040b04090b130504050a030e010e03070e07120204050901050f03030d05070306170a02091503070b0706050114010f0215100308130305011112010317130305030919051e 78
    0x20388030180c0000c289501c8080780740007015081007030803034901f60b06c0703001e10345403109110101d00c000551058555160a000b9402c8040f4001030712180354660005605101d811804101c410b000603c3c140907520f203490700e4100e0141c4602c05000d900590142c2074000a2400c01040303540b80c024600311020b00c000e010381e45005c840c00182802d691003102c182c004643c80d240e007040f120200390000030f00600c00c0e80182112910356800a0369040f000b8000713040b40f500302a00444e0660303003804154010040e00d51425a9100a460701d600904024850101d01001503400c5144950058218030302d44441c0364090080041050340c403102c0040301400344213910504000210000e0f04100c020300c201d0100380d01c40401c440c0341d0300d04242503e1100b4a4140e2808081c171a0a0003850f112150302e040d039074813440c00c0364001c84101c0900018090101014444040d81100200b40100440100200201580c4400b19580d82c034081040e0301c41d1900c1116088440c4c48008080505036100706401064014071407a41d00312 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 673964613 1250 673963363 673963379
    0xe12100b06071e02241c1e0f0609020703030e011407020601060f05090d060f05010603110f0304051c0507050705190b1b12090a0f030f03050c0c0901090903023a0504 72
    0x140b13006070341840c2001071206c9000a001c200030700d2200e00b2480611180702140e2401036180101540081001d4541c8035038500380300c4581011000d4500e040b8119215140350900501500010341c20140b5940782a44000c2200c0f4002030441c17107507500c0d400410480c1d192003030071542103002c22000c00c2000814040c40c29955120741c580e6400902404020801d030798480003c0c4219141030307001406062a10240300c448094407415241e40c503920b03885c0952683c0e11400c25a080c20140008407038640c140361444c041040d0041d015090131402102207030101d980351400c3c440a41316039850484041d1591000700241e5244400501e5690b4402d201030740100204508585003801c82c64250300e44000104880b09a414107481d0f4000030048807909890403461034641c407050610402d070180402c20700081c1c50071342c58000c1000154440026043d01c4030f41d070307480558400609840c030341103006001e4026050b402c0542046c20004100c1c5c220031285041c034020801441401081c1c1019092200034000040ca0302 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 673965863 1250 673964613 673964659
    0x20d080a051303150e0c0306070f17070c0b010b040303120209040b130e0d14040614160803010509070804120f0c0b011409010f060905100e12100b06071e02 68
    0x54460403d040e0415a480004016254200c0d1482d42e00e0b8800b442000b0346da60700088180c0c20003064100040e050031002001c0b201000c041c9800c00c1c00e2200c10080c4815a64042071010410f07005040000c03040c1d0f2540242e00c0240f1641c40007a000031550040b20b01640c001c3d600030f0903000e9004000003194406080401c0820032000040c0442903651404580203a0042c00b03180b401c1ea54a10b815050f803d00001024881d0182d40628020170403503240304d1102508607000c4440c0c41c4580c0c000e40131109054605a049503009000703582c064980d4501254085000e00002070046501c202d1070082542410401c582c07680790854283c0800a00f8602c1d00040f914045409018144082c05440e040d007848052080b11441a841f20b10404044401041003d500c0802c413400d0f104100c41d1840e6940310b0120899070000d803500025444002d0700c0c94003081201c000340240041840c03000034803070790407180308000c0c09004211303000e0f1040740c0701c9003501c407860b64080e50164201c0c40100300e40e0022082c5d6503000e00c58 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 673967113 1250 673965863 673965869
    0x120216020d050a11030111030109020a090b04090f0b10050d090c090c0806030c0609091f1d0702010c030b0d060f1407020703050f06100b0912030a05091507020d080a0513 74
    0x250090302c079410620040078207460b40b40c02e06170000d100009440080780c249100500c12540829070109806031910320404000c0020112080890340790303034a9202140040c044003101d640c90a150069011036400c0803040c0c145004c0c00d90b2580d07400d004c0c01c0004680645010b5004981910700c4500100314103203d8890961f551426075150030140c5016028503180010079108284980b00901c034100c070941c0e8110001b68003012458900500a07041d00c0c0d546508a81d50b003108942c8180c00340e0002c3e14040d6030400381c2c402d00055000384400c3d24011410b5044072008001160001503140c006004a001500151441c0042c0130000500c641440361040d140d84042d1855801070b04551010010b10108000001226103424060407840c100010341240c1c60540f8443c1060300d50010854014039a1014441d5042118140075655600341403440100705900000042d03104154194840d072008010b40b09440b500d80d800b40c4412a090f02c00e446401044d04108495010041c2c100b25112651428030919401 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 673968363 1250 673967113 673967123
    0xc0301060603060306051b07020d1e080703030f0603050316080f0c0d02060a020f07110d020a0e010f0611190206220311030616210510030203010b01050a120216020d 72
    0xb403030f400c40c0380180c283d030000b1f02550388803000081204248000340003100e06059040350303005540c6005103480400c9031460b02c1034160088068a0700070502001c0401001c00c548203a604120704000000708900b1140107000282c00c503802400300038400f080b4a0a1201864021165142400d060740d010801c59031100746001c569802400140c2e04842e01080b103d6080300c0306001c00d40c103203100084030307030058081d00101410007480c1626410719601d40b041c100d6003a41c0c0282043c0001d40e110760200c801d03030700d0a224000301c0c4065040001000d17403041603500204802c0501403d40c0c0d40800c80303406d403140d0a6510a0f40d0003001004281c0c0e00503003003500ca960f40800c1c4491030304440d1031410540d1f061458541d20601036005002040a00410303141c420107035500e1414046440e050603158104c071004101d0350280182c1c40d000520403c06800f1440204481c400ca00034006c83d40f600c401100c490080c5400c070401f05040c0800d028111440742c001c0c10030011400c02445041035a0b400081940c41c401000795a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 673969613 1250 673968363 673968371
    0x207050909030d050f13060b0604050301020a080f090d0518010306180e100e0a02240c0a020310020a0f081909110901080615010509031e0d0906090b0a050c0c0301060603 74
    0xf1103c0c2c014020640d00440c120b5a0600d207192a100024600c0c520010081500f0340d12000080d86170344030b0050b1405000007a00864450517014070103070010702c0035911203280c4004040060030f070184c0040d880000c00f005650b1142040c032107800c1041c0008442805a0515844480102e40041001c0c1d48000c04001c542c1c020414140e0410241c1c2059003819502d0070150070084ca8034104200060780f2880c2c2641941c1d1008203e401500803030550a0305445000c410303100040702e80742c00c080001d0f19264140210140c035017a010541b000000c82c441c8054031030201e00e0040003203001e140510302e816030249002054006450740d000140c412200001000c0300d03444110010b54100d410042015409041c943c0000c0419040031822610000c204034402810040002010102928103102410f0301030040350300c0801e045201409141c8a8603202e13801000038200281c00500d49102d1224801122059480d1914160401c0b00454442e0302c1580301010b01d01c00d00716a4546610b09100c1c5c400180301903a4002 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 673970863 1250 673969613 673969627
    0xe010c06200a1d0a050d230a1a060f1c0807030302032505041505130b04030203150f01030206220801050919050705010e0d0503031518090703060c020705090903 70
    0x140a2688500c42030540c43c4440500c0c0b04192140700d105070655008807800c68070b00125151422502015514036000c0740910400a1855080020311581151283c04031999100a80d9000181c62000b103404692012a0500b4010f940c1003002d94a64146000c0707074124420a09c80d100c42045034040c40c01240000e5000040003880d207861140038284810040d0b000300b00041166008102d03000d180980c0307900b0000300ba446a14180a00110340c0c45901d00280c1540301c0d655111001074541040c03206900a00031050303015481c2071000036541c8a006011020a0a6404c0d902845403d400c4074601588510503c034106d8002d01e1341c130040400501c1003800209151030850780650500c1501c05606c00f1b080f2104000c40c000070404580e56095550a20780070308a0082c0c1d10010b9000c80b20000003801a00001041c03028441845042d10345580741901d9a1004604006281b8200b28049440c00c6064000220030b1001561a80042d514808103104130390f40c0c02c0c0c40d04002000d108043e03628018582c80000d140c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 673972113 1250 673970863 673970867
    0x3030e010e0904080a020102091203030906071704110402070506090c0f0a0e0c070501091709040b0909190c05030708070e0721150f0e0405060c04060e010c06200a 71
    0x4211021000e00e02010810a0200031512980002d000144840b80202d40340308440d200b541034850001c002030000c02e42840501420351684e005880c003c88030700455000890341806010038000f0880f0048421141d075841d511200c203550080c1d4101584160204085000f041041150a025403401d10240180030070310810803000181e454180c13809074502c0a01001254101d40c24194021602c0700003655031452850114010001804000c10090400440303c075400388503c080d00e940705c0240c40400c414103034402000034650080750f0003000356100d04080c019040800b04041e5996120341e65406201d03480e58006818103030280c012a6056001c03250401110742d003180c4054002103d420021800300004000c031800100c02280001c0d143c0c0c0300e505400250512640880c018000c0050038002c0319118046950f003010b0a80e41900da40c814440030400349175000045800300d41054440c581e844100d4001900c40844107401a11019035134141c0507604240c15105600b481c10124441e0ba4502c04c3c1040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 673973363 1250 673972113 673972127
    0x3070b042606060f01031a18010906060e100c0309050a1404051003032a0c060c020f0405010e2e060804020109090c081b3c250503070803100303 63
    0x80d000c07103079010710280211503c070b0001e2001007190a207000300301d0700c4803000303490030031980e00700340d1030300708115148614100c0c10170702007281600c100c0b090500072507030342d440119403031148924601d0348405101c0c1c84804c500c1c01401c88030207440c400d00301000c043d40e07982c00048000100c4c0c3e2050038901441c401e65400d40c0b4051281a40c020450a00350410a0458070010500c2400c03160114110700140e0441c0c0c02c01e5043c0e2401950b03130754041000c10460b911201e0040c040c4c1b110740c03000c0b40500c024107030b40c007940c1c82d00d8061340d4182e0b584610840c0d02076aa50005e0320a4401d0601600e0066400300c1c240589c159031041000090901510b52842c1d07030030107100040802c2d100b82d009550395460003411005032644100e00c580c020710600c0d109850325170900700704000d130700c51440100012003818002026002c52220041040d81241d01203040c0d15003079980040052042d06061907043c0b8010791420f009400c0c9440b00310000e40076404036410807186558030456a403056600300480b02e9103c004104041e40100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 673974613 1250 673973363 673973429
    0x2070605091c14250e180f241b160b0903090901050607030816030204050d031701060207060801050d032a02040b010c05030d0e160605070b1f0b0903070b04 68
    0x10440c0211300001207402c070144082e0152080d100c01060109100400e104010b5159007000701c1a9100d2400000105942d00c05000401280400c801141c0c403252660300081d5110b844c144050440d2031685410a04691b808486d07194064031410200b180442c01d200082442060108019980c500e107000c100715680405900051180e1010823611300007030b80c0701c8140341e08000303010403800c810f0383d803038400b50040d0165400c2550003240113010401455400304420141c007405041c82082641caa10080ba101c2e0402e0180c003010482001c0100300c18180b500018404600030310b40f014044200044141d00107014030044415000400c0c82c030415841c0c2446940405c1100342042e0031004c0c125036455449004c0c41603560425940c40308502c4909070103106a030554003050700e1801c80b407500c462002c0e281d9001030806969901201000802c24120342c10b2003056030035608800c1c0342c2c46240000004003035211080070358044c0500080090f00c054003c01400c05055203402c9510513428106241036441e100303031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 673975863 1250 673974613 673974643
    0x105010f0506160804090f0203070e03012d2c1029040b03011e0e12071502040b190f09061d010903050d020109050f0303060102070605091c14 62
    0x41000c00c540d680c1d51084800d80300d00303c04030200a07201ea05201c5510302545c1e0228a00c03d0811503c1e010941140e80218400c00a540700c0c101401890002c8c50300303c0c0d8054400c103401c0718064040140300e907070302003100d480405403403004200c202411840c049201040d00706c010310004640c0014980300001d0003070703144580d1800800c21505040c1017070381d040c809010408040b8810480207650103501c1d150010744407110064001e0040c101c0d42c07244d14440c10b8030000c0c00c494140c500448203407450000329041c1880c11400c0c90f01400c00c0d20303984611210744a1403501b20501c981c02c010028002500c0701c0030746091750440038000342121a144024204015000d104400c03c80c00007000c1c0700950304030060342c03064580c0350780000c54042c1070070040e2892003458201805c14841c078041c2d101115030540203180c0e6540f02d00c1c2964174451200060580e00e000984155000d41c1141c5000d200c5540f0071000f034001d16100401d0850702c00c1d55040020f00c1c00125046c2991201c14004074080810010030a01e0f4a42850b8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 673977113 1250 673975863 673975889
    0x22060f030309121203020307030e010911120a0b010b090d0c0602030306180f070f090801051f060914010503060a0e090f0d090b1206060f0f0702010e0d020f0907020f0a080903010501 79
    0x580d131182c0d0b00044180d521014554044045800c0c20f129500003525908000020014890907080400810b041d9555a520414079850150018040030840d40803265003d40030107401d0b42032114806031900442000c541003080100e004012803503100151000b0400e60b00917550760b040c40003d20070100810031403004031040b544148090941d103410160381c0160285050a00000070300002c4404802c16441508035600340014401c0708420021030302e6000f54800b441c03018580c0c2d500410b031403100e440d108061000c42c40d07105504465000c1c100450740103000a201d1206540ca56110320307078508090311804043e0b4030512501c5d2030218104224162607606040c0741890a00d010358242c03035442021160f9099000c1d090101d00147c03030301c2040c0c49010804103d401e40380d522000b003255458100100617030018145829190b10b5061031220120b80c641c000c0c161002020b000e405022114401500c02401c5101d0f001c034008010006002c0310091a100703401190303807001d501040609503041038001c10b00d4050b01d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 673978363 1250 673977113 673977149
    0x10510031a0907230414150708030a0b1302031023060c010e0a1212020a1205090f0f01060603060803160311070515040810090c0522060f030309 63
    0x200319100c89040008803910112070340c403240c044030005200d400a1400848149049681c500c00300050705c1915101d812038040b0003205000c100042000c03504062201c0c00420650012544910080d64011010180800d41142100102d2814100340c0b41d045011303580401880503900c190300c06000145044510f05d070312092a80c8000a95101c5c0d07810042c800c034000681040102820740025890301044401e0322008910b40c20540c900b0300126044200207100b5080f50b1214031924803d681d1540360550780d22140301e000c61070a100030140540404010300c10450030341c0c03444204001c0050a15040360001c00c007107103400000360036038130240c00c08100c5810601603528003020100b282510070341c0502d0810905040140c5060400301d150f00299005026654007850320300c0300300020700840d43c901003102e04104000042c60f0849003200c0c1c005005d41039104040100b4a4040385088240c02001003c28910868855050888409a100352148899a1010020305400041c1d0000502002402000c4031030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 673979613 1250 673978363 673978391
    0x15071e020303160c020a0f0e16021b040b151306020c031015081005180f0c1e040e0706141c050403270906140913020d02030d0801051003 60
    0x2c00803d0107201c0d403140003007050b1085440396009a0050400d00038203454168043c02c010050054941340700844001c20030440d80080003a5003600c0316405000c20506110f1440d4084844c1c81145501940381c071100d400c2c40d44c904c2103208190b030906241c20f50340d0340307a0000c00300c81c4a0780c0d60014082d900074501d035504646000c91200c10301c0f000001c000a10303041c80d030042800d0300c206402918142c4940c54901a100415601003400344c00503401c410064000c00c90402c0c0c0d40d4408020306540da4211060000d9a4149a02c140030b00c0d000c100d040d50681d403c2c8501040c222000845c00c0003d95025001c1009820b400085141d960324a00040324034005c04c1d01205d2442e0003d04010502085d070300d00c006028544a14150105226101c040c1e0741c0c40d000c003d000c0d4800401078015414944d180c00303800112034154000203588840050b080c0e0419544a80c0383e40d2040404200c00d0341c100b800701002e00016507060094840340d9006440700e55095040206120043c28a4049001130514000e00d00d00c15603 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 673980863 1250 673979613 673979617
    0x120c03040512011b0201020c011512171902010603111801030f110607110a1517130602040605030a0f060f0308071a070314090114012615071e0203 64
    0x86081e102045a40078440c103480c0101040750700101131116034001d11111541c10b400600c00c03125181c0007840104203040c03c0c5510a00b0522504001d4403141c40c0e08000500309903448007200007446c4900f400c00c00411840c0549203e018010740060b5035a070300500800c0500c02400241040550329051200d03411100304000000c1808060000d02075240f9402c100702c0c81056400f40120003612403921030805107440b01801c0800110391307104940007000802c40201070480404144003d91303481c00c070100a0500d880e00c50303502a0010a28030641e01e401004901c40d80000d00040c407103542e80d2a940c0c908142c4080444040303d1045c80c0c290b00306103040180074140c40079542969048240715030340e0310040c50b00d0845403024605c44140d0071150710800c2900c5425600141360826031030642003031aa24032400034221940b803640c084180c00114010b001411110140415124442204013503980029030302624200380c15441c5141c0419101c100300842d94041c0143c51070b80300d000742d128510000000c4c042e440b4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 673982113 1250 673980863 673980869
    0x31204140f0a0311010b1e1e09070504080f0a0c0308031504150602070b0c1b1504090b0a0b1801140904110a1701080715051c0e120c0304 60
    0x444408280200303800e5091203071404200c41201115511881440c0142044812041440f9594642080818503041200021892844045407960410198003c010b07503202c1030000c100f049041040001c9268640d090400e004814a81b1340e1038580e07180029040c60100001000c09458020002030f100003400b4000c0b0505403030f88810180d0b00ea42d580c00e01c0c1d034901c03100300b40b02d5644182020907440000f00c401035900103603086903094a24082d2038103004130042c0300e283c18500f0150f000c1000d81448d07807000c40d100150b4200c02040505030b1944441c0c250b40395003098100c100300d15a42c001710313045850306141d804000d20300a0821418840c9103200c1c1140400461003007414007a200c0324400900c4104070032a02c81401c02002041541000c0f498400715802180d2140e0102e0480c04103445100f0280b0b130300034100c4074a000148052800d044055500d0150003510038284403050209510041c10150303111090b0440c004002006c03039000194907d000e20942144601340c41c1044802c2e02d801d804002c840607 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 673983363 1250 673982113 673982123
    0x50f0304031b0c0f06020706050418110a020d02011b02031804020417030310050108060603191116030e0a0f12020f04020a05070606050411030a0b0111010606120e031204 74
    0x16991a800c040d14001900915030104010380800030042140c4083c40c0303410382e13442c420100c01d042c0c0c442070166511203440c0601d102080f02440200070540c401c038000410301c0202a4040391800030285071800030380001b006140580c0085290314801503091144c0d0020240d1101030005d8224201c001a48a01c50900100d000d0f030f0f500c0c0c10384c000b10780715a011140105040340c10301e070782c000b418a02035441350001d40f062802810104000105980725104a07402284000c0c4194510786407152003100800c8200c042d40521500c4680701e00e042c510380c07405451044490390f04060b104129140c010403205500048502c04c80800c14244995071091290009a4070480c046c05003034485400003c60810301d018600c0d601900000f01007003074550041c0a004158031640040c448903803184100010340728010036880195034140700080e40a10550008450040c0604040101c1d0500070407450075034036a50403510116008000352800c00360980701340750704440c00201942c18082e071541015070040010b840540 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 673984613 1250 673983363 673983367
    0x408070f050c030610030506130201021906060b04031208252109120909060501171f0b09031b0906060307051209010f1404050a03110109020405040b06030c01020a03050f 74
    0x10070044200107101652100400702c8426140c240c800b240c1d80016804212000d00401c004550300c5103e08104440c0307184e0507000f800c150f0408103a440442188140f06a501c5601e80400081c3c001300c0c02c00602c042c50203000040320740a0800780242920001416000380c001d455600c40f5a201180c1c0749030208a055894206140c0f82c80490a07540c3d500321035040010217161000035030802800160f0343c5100090b40e01c0d6142015555117075030080351291f1007824081100403041148107a01c407500c0a40c003040215465000c0440c1e4191801001d505400604081000007817408292030104102d6441c43c210765042071410046070041401d07070300041c03c0039005181c00b101059200d8010340581d580e02c1c40030302080181d480d0031101d06000e04140048032000074905070b03150340c41008042180d48520b4004004040041d0176a4085440c0ca04d01226026603540e6140c00070010303516406894062405072000e07902500f003a00415040000c2422050f055511454409000030303000740c150f90001150500d401c2d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 673985863 1250 673984613 673984643
    0x3080a050c100c0e0306130605131a0a05240607050f1009023c01030e0f0114100608070c08090d080d050c040506180a0306141b03040807 60
    0x65814001d00c0800a01406044000002e509160b03100d400c0c070001c55074840000c2014501495110102a1b03105020040741d210a138000c02c0d05034000a8005a188400c1040114142c94000c1107540541840703152032403000500c83d80e03980d00d0080e02d402c007074040320500e14858401d0092030365000e0310107010300402c000304201060041c10b001c0043c80003002c00039203a903d8082c10980008202d941c604030b21442d151140011a0120021200142c841900556150b4507030008141071901000c3c01180c1011345a804140804031f0501003d4860112900041154144620780f5011010300400086a01481450030031001d0742c000b0105800c1401810141e10000f03141c100240e241c4144124203400291501f04403040029040081c5104515a00200401c4d2201940c0c0d820324400c5108241d40550140483c052501020b84100c1454a0041c004440d43e0f580e41d45070300590300e00030001c401803d1800c1c2004603108841c0c2c4220b40c4c1c0610f841c01c1a2030741c501a80d0701c00550103000c0000c0d050307180b131b90009 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 673987113 1250 673985863 673985867
    0x703020f03120c0604030f03090305251401020d111e1309050403080603011b0f050a020f010f2a050a05090402131707140d06050903041203050904050c1303080a 70
    0x1a8000125009485a0f140320780344040c0d554207810354080b000101e040c081d031702100d4840c1c0f007140c2c1c0c42545680d0f21071030f1400903140003141250150010141d10305005040703001030791101035140722403108000540ca880010348204105c1d081141500f010600c00c00c02e078011070082d500b000030100c03c1d0000d46074a9040b5801d03400074503001038100819442c54101484141a0845100381c880d0038210000c0c0007018a040c039140000d0391111106021500400301e061289001d00007600c3d0580281c8119003a484000c00000c1c2990084182c0004043c0e4602000c1540c0307044840009000d00703501c40340703020782140240003032552150600d820100239000c40c82601617a41c0f50100d5080005c0c10204400c82a100c2d000c0d43c40030780d0559107402e860b101e00c41d00041c10a6a012600c0074160000b402d0460441c0740d912500007400c001851034005000402c004035403800c0c1941805151402991241d40312807d010500c01215001f5207212003030001400340300c044280812189007625480303814680c6500c0e055070300f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 673988363 1250 673987113 673987123
    0x30c1b120f0d0b040207050703060507020a060614190b04120c0e150901081501180e160806010f05100309020f0402040e1501030504080708070203190b100e07020703020f03 75
    0x5031100316540001d0710a000403030741c400342c01c482650754010001491000b040104911600300000c00642000a0800c0130032451b0303002941c8001c07140150740d03046484d640d54200300c4000b40c210400030400b001801e181e500b000300510b100c096008041e128060300300301d404ca00b50300071841505441c0580c0141d070020089080f180c640141810001c0d00e40504100d01c0e096005004481001c0c010448500001284400014051900c3c0c50f034820203c03460b42055980000200006402c2105c1d50f2110400400b0040801407451a10507400e000a029400d001c904c90400f02c041e400003240b101e82220611055641010f40b00302d0074030b01d00340000e02d0f030340600c0420209152141d6080d0f000340301041c00940c940340e0042c400d00c54014580981c0cc40c0000000560840c1c0003a200600f85800610482e8000b9000e10300078416580020210307002a48404413107285104481000c440d4034282c8002e20240000394441c43c000b038140403170061510b161560700295100b900d440041d201e82441c42d40e20000d83c0382484 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 673989613 1250 673988363 673988383
    0x1091703070b040506182113081c02060c091f030e030a020c01030f091a041103010f091401271401050103110102070b070201080f04050c030115050f06030c1b 69
    0x70503882e540c43c1500b855611200200d03034603000415007944000d44240040b801c15101c8900d905002076200c49484444225004801c407403000c004031000100b00e81e0030411034180c03004144a41000300c01700e0840001e003481005002001c00030002e11500c00181c4d1401482a0880e280711a09201d40750404002c030b016220750850307480203000002d4142141c80d404902261020000c0c0ca0520410261a00754401c8500d624006408500b40d0480c00300494001c55880390000e020b40120f8a07000481c00c000f0b42115003107a014014981d59210480c1000060103115044001c6e0b1402000140b80c104003200c40a400031010640c1c00a00c200007908012180411300020481d4000820ac00e42e180d280404906030b401c041140940300b10180000c240030004101c41e41d42d603040e500c0c41c030b5944480d40300c410a000050421a00b90007120540305140d1407d210390380001c2a440f944a0580f0b20341001c0c0184003018000c4140260800c108119464580108a4031001000036001c0e01d031f840840c81d010b013010a129 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 673990863 1250 673989613 673989623
    0x405102a05070b0f01080d0512130507080304060c0c051c0204020a0909050c0c120309030a0c0c0b160b010603090812100f0f0603050c0412200a0f030501050a0207020109170307 77
    0x2500f0320080071322401c2114107072514a41254074400c100502641d03507009042c0e00500300a14840000d0044010141200500c0d00c42d000300c9800c9a141d0326101c0c1543c1054200000046500140009012684000308024207080d52034030415805001040711828070480041e01564000079210038051095021400034032412004200c070741441155000164400b10f8a50325078418040c024103003440c2e000c02c130b0340508922401149000c111300070545203100c0380a01030f1000e60202500007891006a0010300c440041c2084e40f0f0141d100a103003900e803901060f04403004240c502802040001c1d60712084407000440c9200404141c1c2e9508610b0b40c0c4400c6035041244203440b90b540015981e000e5040c2c09065501584090103c0ea0b0b60b0004012280103d2162446511101501c1004204200035200c19002055415085c140159003c2440341080781e0010500300400e03d410010f11000303104060b0801e546110945c94244141c0000301042d030305004035408050b0b58205035014103000c00c00c9885032540b00d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 673992113 1250 673990863 673990883
    0x3501060605071505010e041403040f08060406060e01080a06090c081f0f0507050d09051606050702010206100605091302073002070305030a031e060306050405102a0507 73
    0x115030042032900042803c54801c12110301400f114039960280754181c0300c0015090609980320745645040e005902248859030004000100b10022180c0c01d0314041e00b940c000030f2803076050602e001030440340b4036400390340203406200c0140003110f40461659a00d03034111101003204040c90401105402d09640201102d21802010301c0820604000030603500d582c6010801000c580260b00c0f000369101103900c400080c0f0308006420707801c03900b80e2082c041759000c1c0040310b180c40303045c0820041c40b03003090b00004007103000071540c2c0341190384c1080119405000c1c0c441c654150341c600000a0003d00401005070b2081051181000c440071040c0d040d40e0700f10780c01031168a00340d030f81945200e4106043e40e04074200d0702518003504561078000240002100c1d03200c0011841e2009800c0300324001c1c008001a40d65800418030ad070200803e403400750801840c024100010030303051610300b0600e0031002c01d0b150102c0604100d6a202e0424a4040c0080e10a01c161802d409050b201c80c02200c040c49840310050181782a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 673993363 1250 673992113 673992119
    0x30d0e01062c010905070e0909060a0c031802220501030606051215070f092c07021906200d0b010e06090a12050c090903091504350106 59
    0x10541110045914810048410b01240a840001c284010400036004404900100706000040e8442684440d59181c20341100c40070b440003a54840b4107503441e074010f62154052060098070341c841c00704454018182001079030003200206c4000507044a01901c42c4400c1d20320319540540c80902440e00400510f42004a5030310707442c102c1d004085900410b0300484514440f081010300c0056084507400d5071502448260f0f9030701d0811942d0507101c5210b1400c0010296002810354400c02d0310484400500d030143d00c032190b1000322190350742c03401043e860440d0700c0400f0394202819001c0c03160f001542c105070041004080441d440341701c1d0307100300b0030945c00400c00160800328070f480307600070420305e1400d995181c8103440700c60400805000c1c414410b5409002101c00704543c0240c0140404c540b44180e046c2d8034042004400590000000c483e0007003a50800103070482c0c03524040d0042c181c101840080301d030509060107151030280004000c072880300340c40103d01d021a0100c2c800c5800c1841c0300040280501d03a1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 673994613 1250 673993363 673993391
    0x110d080c01061401030c080a1e0c02060a050a0b10121811040b060405010509040b04180b102913031704050f0402040b0708030403120f0b27070e03030d 66
    0x2a5030710480410f0030540d05008020340c81390140314600c21040c2ea4505503901d40c056a88010003a003113400319890100c0c9000200c40e034540c020741d16100d0032500540068541215100b05a0740c006003c3c44086107054030001c055600c1d281d00004001041c0350034002c0c02040300b543c00042403126080180244100385220401000183c4100f804000380c0e014440040200f062000c503010328052140403500601c02a040c80c01e003503204890300c80c4000c01c040317044c088464605025600f040810745103036840324100521381c41d08000100091803005081c00c42100004c0e5000010f80340003403e9991580e00284034488820030400070ba014540010300380f204ca580a0003441c1d000d500c50711580b8015400010700c0880b51605100313032400c4406400c0c2491a000003596500400c2e4001002103051086444580968484901c604500a42c1491001922404942c20081c031290b0404075150b900760400c51a0070440e0b0034409a0b60403041904007c0c0e11740305800d0010f42940a545c04602c5403d01c1c007021004140 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 673995863 1250 673994613 673994621
    0x14060a0c0809090c0a03152306070602030705031e040f020402070f0218010f1e0e070203040e0901050a1a030d18030f05010b010f14091c050a030804050c030a02030703110d080c01 78
    0x11980c40801c01541002840415007c0720702c26440c0b442943c5400700318021940001d4900c050009080c645000f5160351004100d8000780c1700d820002d403001c02003040101038214000c41c9a145441d0101a03131809640d00c0d81d8a0504a600902543d004541402044040703a6200c10103603004000d0707040c640c05225411801c24007486207800003810440c0020303112808040e8140a9980803000c510154180b0a1400c1980d8001c0d0500301148820000040c005520089040c0500c00c141c00101d5181003680405003924040110101c6241102000203656500003420082220050074a07407285981c01e100d40c3c03039007403440d880503115001045182c810402c1c19404140c41010980316440860b54a038012104025041c80c0b143c40380c102001800b24920b0f045030720300c42255054010368402c9003640e45082c140b0f548280c003103010a110400340420041c003400744007280842540106000e01840c2c00103a56100f6500c000f0700703d44103901081e600e54841e103c000c80415041140e9603035410b40946407500030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 673997113 1250 673995863 673995877
    0xf030d061220060403151b03090203100e030c030408030a02060a0209090604090303021903020310140a030327140f0f0328050a0507080c0915100215070c020a14060a0c0809090c 77
    0x7c007444c0f8503007010b004e01901c980c800c0650040c6c014070203c540481d1600080400f401910650301c03060125000c200c400300000c02c080c29040d00a1a00c510720004068070b020000303400c100c80d250062005020a886003107007144c0c807035411600441c050a181c1000c0c1e00900c960401c5c101e80c4c0e03048803014005140c00d90025406003007503011950006aa48400304a440c8003000000d500c12210141040802e104018140908404119100501c5a2940f2002100243c0d5100301e9803c00c608041e00c80c1072909904045140005441401d03400c0041e60000b40c03120bd84101804140107945d003000d80102c0d00341c00c9072a141d0781c042c0445144440234140190744003400d10444000d031007000c208180f40d0800e6084580503103100014004044010001c0101c211f043d0800d5108602c1012110300141d61504004e40c090307081d40d112220080440c1c018002480c00c9a0404441d00c0546410168940c480004498101c0340610f40b400392620545010082c2d0300c0341503d204d52110f022018044542c0c07040000700702c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 673998363 1250 673997113 673997141
    0xa15032009100b0703050a090f03030c0605070306180c020a060204091d03090f0906031f0507030e07030519030507050609010617060907170304080f030d06122006040315 74
    0x5030b9452070006041c440881c0142e080d0308609110520010740100040c1c01d6008107030500d48151500d410344040c00d44401d45c003d900140920340d008041c4002d500c01e054008444e0310b0f0520a41e801c2c0600e0f40116100f44070603501e819a20030003d4122442480340c403650a078028020741d0f51720f83d1144078401515195665468101802aa50380c00020000803584120000392007100f2440350b41c400c0041d2000b0040040d50140a4102c07000c104500928041003000ca0703c05000400b801c245200904803107103400b40340c003998000396040c408110002190b00443c0c074030200c3c4045594041c0380403182401001c8000f04107200780381c140182080b040d0440c0701615030482c5500d140c50486000c07950781d1007060702e00c0112604000f0051004033305082106200c010190200d034940340c0c0d901801e40c0740c011806110310390360b0408104441008501c1c052040102540c1c07044406000858030354220600040303a008003000c1c46800306d828180c840c082510002c1d504040c00251030000c404000016104107400b42c07036 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 673999613 1250 673998363 673998379
    0x30409061502010b03072417101a0a080415090218010e0a05010b070b07030b0d0605090c01021f0c12051e0c04080c0f0609120a03140f030a150320 64
    0x180c0b0b03080021b00031003207a0905401214000f0700055108640910030548810007109100500c10491100c620328002d000ca00010007005140004084800d014075030b03d0072424004001e0310002d00d901205080e003143c0c010b030f030030408084002c0d0b044000b000b902c42c009400c40c1203502c05071641c80488c28503504a402c2c0e4010f280d0a40c0d2106e41b200100e850034010215031080c2402103401040400c19010340c03116041c00c0001e0448901ca0014642103040181101d40c0307611141044a1b5a1007805090700780c0800b80002c200520912030701d40c01000b45140805500c55680e500e00319030901c694400b0100c54540a0100f18034249401d1240003000b0344500e140e21505100c000c25210b01c44c4104840880d481e0b0406014030140d90410800314032000400321350310640c103014845a0780e0350301e40056400e0301844010152303070f0828034000c0e1245917041350005100340309012410713100030701c64201c90340429110310006e175282c41c0c102c04100c25a080c0d00082c1c0005042000d4034600a00b15507a80c200d0f8104640f180 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 674000863 1250 673999613 673999631
    0x14010605030304210201091703090a0b1216090902030a02030114220902061c061e05180402010309120f030e12120c0c030c010902040e0a05060103120203040906150201 73
    0x981c0e02d02c214444c0c510403040a40c002d80012508900b520912413051400038582a910031596132140000908254281c100007108005840c00c811204000c1c1041031000381400f140d9508044001d400801418904012100c1d081e0b8040c803a483c0c04000c0c08045c00110f46030304000b07422200a4209000324501082e846101100c2407400b0003144c9803001c00c008880c042c130030b5400c4e4030502a01c0307118403c83c1c0100c1c00f844500c000b00d00c58900d424240d1200343c000605c00d860001d400307044540070018072840a0044800388555102c604071447c0000c850f610002c180c0d01c0d5440128001c00c26010040c03c03985d10805181d01080e84401c00d118152100e83d42401141c1c44000b52035201c00d1828128070074201c081021140008094011950000b02d0f0385d442409c02c01f00311005800e5910000e4000000d9648500840851415100e80e08079170118000400e80c6800660320300d555500103010140c62654145041c42d003a9108008441c083e001600741840b40355511003a0b20040c400c031045510265007000840 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 674002113 1250 674000863 674000869
    0x80f2505030403060e031c020913020403050102030f01230904151d0d051c0908070b0f07080a020c030715180f0b0a200906090406030813090606051b0f070314010605 72
    0x6150720300e0902c524121040051003541c1f000f0b50111101d160800701903060164a0b420030710140c80154000d200159803864140c01e4500c981e10141c0240030714010702041400703940c0c3d90b0060407042c05016500f1b109551114205480c150300c10051100240c2e003002c02c42e00c1208501c500b04007513018040100c03600103000c40300a81755170050030350601140c003c28410480074180c942001220354002d118051618280b40c840d00c0714a40304892740302c00110644203100805070301448a6a004222460460070207038180061b603140d20a01001610a84880660074070b40129075204610150050010179a0014039140c5908070041c0020300f80c82c00c88038200010f040550900130481103411591a40c1c02141c031444038a1500d03040580f032550810804d2004aa090f1210310807140510300504c0c00e540ca600d18000308a035810000d07000f0180e5182014400c100c8140c000c8159403c9048414150304071148a18085207030029082d10624284074540300001031104080382d803d28488541e0090018940340d00c14 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 674003363 1250 674002113 674002117
    0x150908030f12061f080f130c06030506040621020319210c0b0c03090c03070e01060507060b030a0f03021606050307051b0f0d02100603080f2505030403060e03 69
    0x70091500108001ea1950710614003021540a1001881c401400c4402c00a80c4801920b6446060116150a0502000b800b070460b11030f521000810b00d1582c1100c460340e0b807210401640c802c3d001419114000f00301301344d41325002035000e094102d054048010024000c0040290303414000d0307005c0d000e54280094840000c02e0307007882c0b86801c40d440704042508200b81e03010307115549034034008029080c254000001c0c130400949000310003a001a079201c0c04e19840e0182000a43e5081c603100c8d520413502040049008500303c0c0c11501141811030315100d0a05200001d00300c0e2070340542c0d06000700d06030103017007045101004079400c0c029801c96010104118280c90849120f0040c000814030a10001d07507110b100f800200701e0641c0d080c43d50b442c1e4540324400540b401ca010504039819401050003e45c002d81c0c100311545010f0200201400300a00c1c1d61203803046403140a024020301d07440003805808070215158400c2c030b450303079800010440b1080d0b41400c0e502c81e0400d010481c3e21a003403410509455000000b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 674004613 1250 674003363 674003377
    0x2010b040f02070206040627120b070503042a0503030d0614100504090c030e060f192a0905030a0c03230c0d0501060503100e060a2c070506030115090803 67
    0x48400d14050801f00c040d92411905400644110349207060044494001465580242100c1007200d52801d0039240c05034032644022b01410030850b00340b0811012035402c201c0d6001c2102008410034000d1400d821200c6100b002c1c1c0c024940501c00000c4022005907141c0c40b020440d00d0fa4030341002e80c20212000c000805100c8083c50300068003c1c0018060182140d0000b0880921410b001409407070340b11007181031200c204c40300942c7d04900d000300403820100d400c01a00c20740b52190104960300041d139000492440c0820500c0119003050f0f0005440c50040d1810720140c8401400c440300514903140107412004103000444400c0303500d070ba641c0d40c3c52448021560603401604050b004c0036640e1810700042d8985420103907003564891000107003d45082c041d4040003000d80e03001145440c000d101d0b007032601c0c0c0098290100fa602d055a90740c0c1d400848002464643d034804004c80c200d4a0907070b0003030314010315604000d501c103000000024002800343e402c142400d01d681ca81c413034100c0e03481c001c00781c07640140c2c9 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 674005863 1250 674004613 674004619
    0x121103190215030606120c031b0a02070e0903070605091612030c0818040f090b18030304150b041d0d021605060c010905060c07021f021c030209030d02010b040f020702 73
    0x2041d1001c100c800e04010f0343e48100c01800d41c0303007800a040014000b146040e00c0c000c054090000c01d22450540c46000b54800c0a030a0161920700310390028000d41d01c80c210f10035650001d050202040502c2000d004480003241c0290040c400c605184000d940c4459000074050201d502441c000074504401c00545007140303405407901083e40405031203c1020354005205455805030400b80b1002c240c1e03580c0309604440d8a00c0340c0c001a8003401d46061111031802402e07003101d4046400c060940400000b04403944291310038114180c650540700440301030010302580c1a481820b1600640c0c620034010002861801c80744203c491045980b00107a0700c3d0380c0ca424801800c0c1101c800c003400603042c000018150180e8480c00040c000c0c00c0e0340c6804ac20020103a85064000d5000500c0070250f14080c0e51a248281c07a030100341c0700362422140003a66070b03446c4401007040708000403603d0640c82d0107907041c0c51100d0b1025081c0c801a50035001c000f40200f041f9208a03200380d10340202036900744664401e541c0500d90107 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 674007113 1250 674005863 674005879
    0x30708071a09040b030604200303030903070215040e01030308040b34050f031009140f0403030902010c33020703050409050c1327020a05031b041211031902 68
    0x781024265202c64000c1e41c1054450b00201a1614100310203032082d40905c4080c59290041c20402008500200d544da00c00e80c0144180900c0a40c04022280110b5040314480c80c50052403400c2401e502481e401030110004003000001450b4100ea280d0b403040d4030803c00341e801031b5904040840460030303152544580380e500c601d042031404013003034414100e10305c0d45c285142041115404c9042541c422580102200d4035035008202c010403c0c01401d0900c284007001241e00c0c0f80c82240610340a0000b40060300b0107490707141075000d590183c0c8d40f17010070030341000c400383c00360040007140302441c00440324400c0108842d1a840140741c032641300391a10183c0c5131342c0e076030315203850003031600d02070300c0054020301c100442008801c3c014010400c8850082c01c10008140c4500360310525a180c3c4071500280d0014180100021907241c0d5000f01201d50001086840300145504030000216030f014a410030b8481000760344003032041c0100d0040003062803400f00c0885000c0781112407240c005420048000f5009604 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 674008363 1250 674007113 674007149
    0xc0907020a0b0604201b06040222090609050d09080601060507140c030a1a0907030c031b05090a02040e090f0303040308091002180306070c120c03020a150b03070807 72
    0x1605030b81c2c0390440c030010300100d440d0000854041d0000c1c0016015400300708009505041464415107400b18088100007038503281c50a43c000c50351103900d02d00c241c0c5c01242c0300825000c02005681c0480c401da0f4001c80104402440d40c81c015548000102680c0c001c00c82214000800000c0084d1086c162986641c03041c0c00d01000b980c1d4a0018148d8001d020201d020b4100c0d000001d4400308030700406580913000300740c1c10115142442c80700d0400541010095082a1000d00118800351803a00849902103400c0c54035034038100c00d880130107840e500000d07403200c000400d004d4402840e03000f40058540781100104252030321082c2580e141d145680a08541d00140001800f2030f025136100c41e4007020110a541e60146045909000ca80c060a01b00c80341c0b843d00b1980c444207040400410360701c03401c07a0804105d03400250b00c0302c0b007042c00050709603420001040c1d403910405100340001c0f110140d102c030085c0d1404403004c2400d4042c1c984059454024410024001440240003600601701d0707031190309407600881 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 674009613 1250 674008363 674008373
    0xb030708030a031104030f0f02011107120f0602120c0301080c0409050d05250308190e10022113050c0d030f0f05040e0711011b0512070c1e050c0907020a 67
    0x8140040300012884c00c2c40700201003a1090036440c1d034103100c1c07400c090002100e8800504422004514200c295100680070b2014200d04550150241d401140c007402c4a410351520101038802c682c0349910003c520400c1c040c0044000780594180e0713505000350703401d8074404400d005c1140d8003000d000c0d01ca5480003130100401030091004000c0d02c0d00030000c000b001414140340b0580150b50110403030000d814601044080500c500b0341201205440d40b0070720040c0c0680f0340940d0355416101020180640c0041e50699060b0006055016100c29000c81022850440d164600c000f0b00117009480500600580d1307042490f100c1441c2042a5160312800d80001d44072a048454089401d088024080200404a51034802c0303036030948a40415920800f5000d040c0c0c10440c2510f110b80c2e401d002d0a19048004241341c5d030410259450f00e003010304c0700c00345641c40c3c85d01210814140c10001c0c01c100d810418070b603060143c06110b000c03824002e4045881e090600303414441c00c0f0508071528001608a2000311000135 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 674010863 1250 674009613 674009621
    0x30c031510050a06021c0e030a060c020124050f0906180714030c09010f080702121e0f04060207050105130b030a15090b010e0406030c0501050a1803030801090b030708030a03 76
    0x30103500208059125030105603c031090341c00103000759001c9040d004510071442c0742c16002160503c0c02459004441b0f0111380c2d183c0144070020140c5403a00406d11603d4800d60000c849161844074540800c0d034112079030588054140103145c014840c0c0007514003241042d0b21414010319000d0200c440140e0700808130244042c0c082c0c0322904111600303102ca0240c10044010714000d880d07040341c840c2e907842c4101c00940100c090111000500c40c2030400c1040c00341e0049401c1c8410f04c15407001c580c2c0c1d8501200b0f180c2007003000c0003080380c0d031070390118196050500c03890182003519101e4003200d42141e190070064030780c3e00525000301e10040303803c4014403030820004040c40d0042100700b00880c41c0148010004071941c01504004a40d0395a000352854030f69228002c40c540000a440c1080554116159100020954041c03181030100004142510510030740e81c0303030440001e01c0300c440d204603100e00d4020b00783d000a1140304c2ea11800c4c00e00b0362407a031401140c144100c0e003003900150b181454070407095000e0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 674012113 1250 674010863 674010871
    0x105090303060121181109060925030b030a0503030108190c050112090b0f10060c1a101815080d08011a0f03190c0c0c1e180c0e030c0315 60
    0xa503c2d251106603170094042c400c41070610499140842103004020f2107502c11004210354070a0000700c00740030801064082440c550014140e0265a1134115441034000c0d202e00c0e070170035030144140c01003002403060110255040c1d803022001e4030000304000302c10080020402c80301a01c0341841039800c000c1e42d0b0040b0b9044030f00200100001c210001079131110030980c036088404000e03181c81841004180700b1158000f5018080030308040c088000d060301d0b82c0101d000c8000200312009030601c00701c1c924a500203880002400b16041307101030030f04c10344000e00c0904041e030404e81c002c060b5004007140035207001c035801040c950310784c0d1415001c0e860801c0683c1e0a24003005000922039041000c1c5d107400705060020f520404202003c0c422086070048480c044541e80290102003004406007800011510b01681046800315043c0c620612219076222040145662040303c0920300c0c08601c3c181101190051030055546840f0500003080710030070700d03441d9009203100c103506401900007181a80035030b041603904 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 674013363 1250 674012113 674012177
    0x409150b0a0c050705180c1305130c02010c110307110f1306080c010c082b0501120c050301050709120602160503042111060304020d02190801050903030601 68
    0x281655a01262400d030340840c18010000381d600c0300c0c4000b0720904004a00013000c00762410740495050041101002401030718100c1e0380540055616100a03501c1c018902034800104000d0031018614076620081010780003c07030165007040c082c0781140e4003c440f44519031880202440c80d2101aa49600703242d840118600d0380010803141c6200c0f280c07900038135040214484040016064140480140342200d01c04690b030410036200b940400042202c4d0a40700c039820751808020a4040d80780a40c0c0300958101621180d00e444c000c000215058001d6107079406600602d50000b40c00d0303d605c01e050a0ba04200c0b004004103850f094104640341e81c00301c10b200300d2800340c4c0e80141020703403500c2c03081d901d1a8114001c0d00c480e84081024010201e0301da070b003201800503107030745240707800b03d103540c0d40c00107c0702d540c0c00f01e20070400880001c0a54403944400308800383e00500040644010800076030302c1c00e5250040468541c601000281012400000c0700c2c0200c60503110344041b00e101180345520f00b0301105400c40 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 674014613 1250 674013363 674013401
    0x60f0703080a0603080d0e01140903040e090a020d0c0501120b06031305240108190309140d05011103010617010f050d03050c1002071a04030801030809061e0c060f0103080409 76
    0x40803400307860103010782a85405000c200c0201c091495809c1d51013901220800308208401d100010400208803001c40f00c07102d94030f01a9646010100b400e0840041c4042d4004c1101c0000800708161010414140c0782c00f44c84112580d070000b9030403011101400e44c10707600300c07604001142c0f602c666640c00864a6108038121440510b580340c100414203d0207015007811410031005000c0100b080c818424090030704810400120416200201403204911a8400c03810900074030103031716240c60005400468100d0300070b0103140343c4481c010005078401d1160304001810303091100070b5500c2c0b540a04d8100d034802c8914000460500f010056241c40300c0c00c0842c02c1c00b201700502c1140c0348062103c903030000e826040041e2200a1420506044180c206092011075481410080001c4d081822141980c2e044807c01c0d0300c03016204003140252141240350844100321180300d2080d0304a0300c3c004c1c00c0e1040340c002a11b0711a265041c001400400c00e010041c0440010b020a03c00240c15030310a5900403d1281804 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 674015863 1250 674014613 674014619
    0x50f1b0f041703040501020d020f060c0315060a0e09330d0c0e09070e0403051b07120b060406080619020c07171c020705101b02100c11060f0703080a06 66
    0x2035004000e40380b80d4a580c02c04541001550303018007100d0f6160010780083c0100b81021030110b503d030301008080200507080800401d007003480c002c0307915414034806000d6558654a84001038004030085001d50f21032400800003070015007203501b100c0c5a0100442c001b840da00041d40ca000303406200703018959004201c00c0003800115160100400040880507030316900f0741002d9041c182014802d41041d12440008014807002952020442d00540707a01580038031681200b5420505000e9a544081c00c103581c091401c5050042c00301507107000b0355080b9010052150344840e07070341d110101150700500c1c5040d00d40701d920340312241d500100f100010f80025142480d031621112001440d80c0700c40d424080c0c0c00840c400c00034100c0c403a840d4103007541c1d5000a1034000d02d0000015081e0781d140981d4070400c00d003444000e9014030750003030030b00715260300606c2c800442130034820040090b4103840080e20152903d242504203410100100c500003580000d403540383c81581d1718207460b007100203000c1501c4103903581000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 674017113 1250 674015863 674015879
    0x3070317070c0f08060903090d060b010207082a04061d100302090c030906060a0f06140708030f071d06030105041d07031b080f192a0504050f1b0f04 65
    0x300b0103030075058040c4903600d0521454900c2c0110003001d0008907801080313040540c0e560b0b80d1070100c0040d44901c0114250310b0b02c100403410590181d00491251242d2159840349250240100c1d20440c0c1c7c110b00c1e03480c0e00008500300416142284690240c5503001d42020703c0080c2507501e1154031807003440000340c81b150b6940c04502c100c5011919404520808814400e50705004d006194000c0000c899401006007803003110301c0050000e2041c3c03010f101d00c5844800000ea4010709665407241c000c2001900c3e450034076500080d4140032221080010040104215a1802c0c0700100301c11042c00b40c40e90341183e003850309020051094000f45280440001c18101b0404070420450700036511a80c00c15060300000c8200703400c0c000041d084002190040d500c00215007000055a848104100c4a50a03a1015504044041c81109102c040300c0115100d84400355240080c04a021188241d404110740d96510a50101d070071000d890940125408141141411030150042c0c402803604002c010b00d407965440203 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 674018363 1250 674017113 674017133
    0x140f0d0309030f030515012003070b010e010f0e0a0b12010e0c0f03010b150d020c0d0e03070603020c030a032a08010e0a09030c030f0201150303030e06010605090307031707 75
    0x5400001d03161a020410180d20a80c000c0e41041c803804c05100030304104080f60401008080d1090401400b5005105c8044200c4603c4848420300c0342035a694521500380000403880c00d0040c90003c1c040d0744000240c90308051041e500721b60003054011115100e07044514050040a00380683c48211020b9030185c8180a103e0f41880c5107503540140720f00703c00c2c0c50500a0035581541c0c40c80c426407401e00344040f603885c0d00305201102059160700d5a66854400ca41d07000078007940c80420305511824451044598000382c0d00000d16200701c0803106055507522080b07050744110704420031542c109008034203c0c1802a0040c0482855452100340b84901214180348000900c00c0c90720000b5444c0801000784622a1140681101c54070000b030140300415140a808950b003140c00034100b0502144d29001e1070b100398000000340000c107070340c244215502d0a00501904005020b442c15008240000a59600950442d8503840014010702112481d580b9107000c01e0710201000102c110007000540006051000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 674019613 1250 674018363 674018383
    0x71406030f0603120a030b030601210f02040603080a11060c18010809071502032805220902040e060f01080f010605070804091d060106080402010c02040b3111040b07140f 74
    0x1400187d1910b150040614142042c0d00c80c8040c4500180926001401000082c411a4020138120508080340c80400c008041e01d50010342054808180100040d500003200300c8103103d24000c031800e42d150500e0520343d074420f49003400c0b000d44809203010301e00e5010741000350303020031090260385101e55601c0705807030050500b54084006800c00641e05411142c6d650308135141c0c80b2034000b1109422812203018105100c3d040741001446481e0340e01507510f24094010201070000805c0554a43c0d60390034082e540984160748841c442e050b84912030045507c2907146600c100841c80500519901c1e051003540d0b5580000c2d0300f078401c40c804110103e141086030260480c440050000c45102c44132400c00c042c209007040c0c004008101c504018030025070ba000c201000050780407200000c6c050310180c001000c000c0c7c80100c000074480c0503901420141c5080c68501000490708000740004410005c41c1d60413846203000c0e110380d0080501003e00424000003107240944900d104440083c00c079440341500d0310b200c40e1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 674020863 1250 674019613 674019617
    0x411040905071e081009020d1218050616020108130218010e07020d0c020f220e010c0309200f28050a1401080a110d0905071406030f0603120a 62
    0x201c810015041000040000300c02d02003e100300307140c100580d4a40b201121540621810b40304d01c004401e660381c042e80ca2002c80c6e441268400803465030b0401074801000c64040c010740d03140200300014a803c0442c21101c80380c06260310040113034415401560031540c00f418034540e00c0c1500800308010380f15260900034059610f000c200e400d624020800c080405c0040500c1c0c00c6400c003440d005442508201d820b80403a504488400d1100b203101c010805028014400040551fa880c0e018030500300d16510801d803015681c0020b01c8441100441603040d00d8172810001c0c134034503289280b000381112048100000c0b0000170000101c54140d8400259900039440d00102d1484a00070b900d94a04039062920f0300400c0142d4143c0b0650b03241c84c1241c10182d11480549046c45071103000510711600f01d40c492024140840702003900c0b2030100d21010014440d65000710780300c1c4140040803a04a043c0e2041109141008046602e0341d9070324031000302d4001e000342280343c262184810040c6800f44001c05003c8150481e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 674022113 1250 674020863 674020873
    0x3110408150603010605030a0f1506060f0e0a080706080c070b07050a030506010305040b0c070c0b03150306010f051f02011404151406151308032b0e10050411040905 72
    0x1161444105440907000500c2070389024400c100584000c504a003100350802c0d4020115205e5050ad503c007100c4940c80d02000d0b0f8031300800403e00c580c0204195016001c103956030718007101000e040c0541a500d41c06812443d03440814100003480c89850b026900ac40c9200311a0b040c60070381d6460007110242500c10801041d07000c220002c1840c1c0c140304565110800b4a0148a2410701e602c85051182c400ba01c1c0080311240098000300740080101100028044802070555030319040307400005096100400901c01d00911b000003405002c040c09920556900070b1080440c403035a040085c0048100318001c03403d654a0300002c0c481c0c400c40d5000140b2550081508052a42c100d0946c0030403100c481c0c0428102c50303814000d006e0b060310342c0625a0441d03034450300c8403992284100045061080306621000301031000141004c903144111000091410040c0c5503001d41c0082c0c00301d000280c40700030940d0f20282d13001c0d4010f2564510306411a03078100740640d00661820b03152001103815508403420503120396001c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 674023363 1250 674022113 674022133
    0x230c0f030304170106030311071d090c030601060207052d060c0a0506011805070f0f0806011803050a060b09010311060306060d020d0501061409012f2a060418090303110408 75
    0x1c210703003821080c00340002c0c1446e27904042c1080c03400e691200d48040048815000280f178490200308400d43c1140090031070b0b001d9030b52000300a60300c482c64059a07010740c1104d44891003840d002c4000300c074002c2d055000c00103071400e80c005001c8290400101c10240e0310414000b000030800c14400d1b240600a9440b64a851019552149080d00c0b00540704000b00001070541d140300503484841402d070034259261030320540e1a04001224561101d640304180c66413110000010403600003903c40405203c0c0d0350a02c0b81e0fa041900704181c4c170ba805d102c00351860161303440c940c1343c5192140003140c0c4010014644c81c202620340c40c400342242c1217002c00c046181d54031b034010303c401d5070004410598601c80302e2116240041440000b011a0303050f00c4990900c030b00362814401003c0d030382c0d54088031250b09041111241d140d62040d01d06580c1d00f00740b000034050704a450594030390406500700d90644018100783d00c00c1a80c5030101d0300042001107401e90030035503911035014003415100010002001c40e0310051038103000e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 674024613 1250 674023363 674023367
    0x30a03201f0b04060b0703050909091014100501020c09010605030a0f060305010b1f0c0f0602090d05031e0a0804030503100315020a26240a12230c0f0303041701060303 73
    0x44c0c0394100100508060040f280026480304c116079014000b9698070381075407079454444d4a081d43c40c515040d602800c00900d040003400010089120306800d40307d92a46c59524001642c8031101540303615002520100144081c1d4069802160003685641c000160b95901000501c00c50f01660003c46184c0d4503901c15448510381001c460004456006284c190380801e410040c1c502203941c54010409010000716409101e001d41c10340303800003000303808450b6840c4540303441030f101d50160008003d2008a19600008540c100f015285144450f40f02c3c55409e1303c5607141901c180d00b00030654400708034000c10100002d80701029040450030340b1080561110344502c0c000d802550021100c07c600c1180a1410340f50b079071000303846600804a480b5000717400703c96035034540c0350740006501c5542002c00e02000050b010742d816482003440f401101038101003259444107c1e00100384010a1109600040240d601850580c01100361044010212480c00c1d58500d90325000e241843c0414207265990305c0b00b00309042e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 674025863 1250 674024613 674024621
    0x40602060f1512010204080303040f0c06020106050904030528030e101109010c03141c05010518160903060f1407051309111c0504020102010b030a03201f0b04 69
    0x7100c996504040c544928114075115090a1461103852408402c0c0c00440c2d080d0f0440d4051f10300b880941e941c82c44d09050484045d00d82c00030449440d8841c040000b0040e1041c8030710401c2c0e440c0100072220541361910111a260041d020b18907210811384244d086c038202d5a082100080e400741c50104110501691050a014628400e0407800c0e00381034000c914440804101d072141d81090030b24800001c0c030ba003011240d8050080c1c0742581131100144000840c05484422908029040310901c060b89c1c0355401c0c07184a00006204182080d00c02e004141c03054450300c0d54004103100d9180811400b86d4035203c240a0744c403944a02040e00e9074801804044030700c80c03002a6403009003400c14030b14010a1595081400d1468450840307a507a4071a5102408503002c400c81e40c80c1300340c01007454280342c0c4c054050801840190b904a02541c0703881e0301ea104906020810031101905030300c540c42204072050046a0005e0720708816480c1d40181e42c3c0901d54440b0b800b1207a82d07a104054000a03100184805102c101c03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 674027113 1250 674025863 674025871
    0xc09040f050f091006060c02240c0a0203190b1302030f0316050705010c03080c0901260712051605030402040b030604120806060301030c1418010b130906031a090a061104060206 77
    0x140c00c1071411b0058940080180c1001360741956040d5120036640080101914802000510788500140888624900140c403049450088080d521100c9060882d0305580188030401480d958811001800b00e00d100031246601900160940b900b43e440c40d110346007140d02000f0307407200342c8070034030380341400d0000800155010308001e003011001601c082d04d0203480064002c0c050050700100080000e800d0740f0642034000c00c40c481c01c016000a580c0000c8030034180400f00c03480d100050140c41015195038641c00b800340202161084000d50f040c0240013141d082d40010802d0740c1003511483c08540396201000820310480c0074524000848401c084001c001c1c04010b0320340c0e44140d0707040c001400804e031301608080449004112200c0c0b500368010200701941001c00e44000340d007140c3e000000e050910b4200910f440180398030070300340c0c540c0c858082c0310444001c0e000180020a59030300e4100e01c0c0790107a00b09070300820003804607840420140d49184c29100c00b81404616100c2c0820104550390f0100700441d00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 674028363 1250 674027113 674027143
    0x1f06080c03030c1203040609170c21040512120301030609120206090715110f01061a040b09150d0213031a0714031905090109170f030c09040f050f09 65
    0xb0f03040140641c15034540039403040000424000010070f040203180e40c450b008581c9c1c0480e0452070345003040c3d84030f05140c04c202c603a41640d001d401c4070940c0040109a90304801200140b0050406080c013040c481c241c1d55404480007248078500700900704250800c0a1402107110340c02c00318442c42e052800c4c1c40d91455040d580d80565100c0010b00c0030740940402c84030180d50140d1075441d03a10799150f07011220100440d881d1300300c9021740040e05032009419004081684c0d148041c21500c0058010115040e10451080b041e070280305001240b03844c42d1081224004d2084414002c0c180500a44154102d90106410044010a2180400400c1182511041c1c0b00780c0b0312203240b83e00c1c0f13807461014101c1c0c5c0813903040d02c00010000001a030b501c002c107076150301400c4d4529010441850111500c5009001c020410b4032040446006842c05130020405c032410a00c54900242c15030303d54400300344064101102543c0d00c40d0b01c400f07135110705450900c0358511034960340705101c030242011010541016040c10040e80 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 674029613 1250 674028363 674028367
    0x1a28150512041e0c0609080703170d020f04120b0112050c040903050d060e0417190e0109030f2301020405030304060c0203030403050601180f022a1f06080c0303 70
    0x50160342140540d402030800241d10040d40d55a0320741100c0ca2444681e010000f1901030f00c41406108030706500380c09032040780c0c460241c03060301c55192a03500d0000307100c0280350100c51040041c03900ba0764006041c1d0035015603405414140210481075213500541c02450a07216500c040e1004d0000900080d070041c18006000da0085c4a5511010340302c1113204c000f2402262202e04220825100d44125240050000010022180c031000c101480c040282c0e026500c07214100a00c0e2183c0c0036030b4007200d447d075882c1d4103808605500404d00790707921001205194180042c9480c0000414203101024a4041c403581001c0700030080c14042031119998840390068036803041c070090103170752400405c4070103541840c10906c0600c40381f8400a440c500c919000104540100800050540c0240c016000001d91420f1305100d0080c1c286c5c011412400743c6140c00304410004001104c10a03005443c2414902c103490650f14248030801a2149a044030216044c0c440d944500801c0340001c2441000c40c03280b03003200558 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 674030863 1250 674029613 674029649
    0x2180411010819240906030c1a0316051303060222211401091a2203120905060c040602070608040206040b03180a0302010c110a02131a28 60
    0x46400400b801d4032100055071544400c0d0400780603074003040300d4144d4041a2070820b45580c3c012020789420700c02194a01d500c01000304030109190910200032a4010f085421a50348000c00d22110320b04107158018010308002c042400d56861100c4400f45000740c00140e6500350040180c16001042c0e0188051151000d40510040b1441440190032750b04450300b42c5030f000b401c2d040111151020180400856103004605020445540c1d210802d51307140d0402210b6607610a182d0400c509a42140410714840c0707801d0010011b4059050740c1007800c500700b0001184950b91f130310145000c500303a07100502c071100032404001066040112201504130303031401c8040d50400d540821160301a078099240a100b002c070028020403046a20200b10f030f40803104480c0400d1490501a0080100c142800002508140041c090401c0011008881c5a01900d40c96240c5d040c0c400c500002c01c00c04404101c82c8500c018003005aa488011040d46108a00d486c03080c08410020307403451740c1c0c03c0c1d58003e4480b824082461 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 674032113 1250 674030863 674030881
    0x711100513061101020c030c010b10050c030306040c03020f160c09060b040509060103020f040b180f010e040c1b030203220f1401020106030c030f0210050f09041503021804110108 78
    0x2001c01ca901600b002d10403c0103241d06240039000e1202e40d81001e10000c50700904414054201c040050410b036201001e030076808004507070900c210801e4034070541c030820205000342000d40c03003090b00c6081882c0042c00c00682c080b5101941d4003003103111100c20b45124510f818400c403821740c1402070800260030007105144c9610303403506000d1481094800c18500c0d00140180e40a601110100d440c03841e4410307036682d01c590b00760b0b03500e4204505900788402000d20464081c1084165080440701c16100ca20f402c442620412010f0050b040803a0100891903504144180d40c07a64903070f01c1c0ea4420740180d41c0316041c8001070580181c4190200e400c10600740810014641a0384084099038a005403812510116200503030141402ea0f0006203403102c81d00d000010b001c4c0580482d180e4601c01c9505e1300012103108011a0b080c00b4010ba201c581d900108420855498140d2044203c100610314080c0c031582e480d00055216100b01d4010414a00c1000070001045200c0090100d45402428040c000e0704001080b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 674033363 1250 674032113 674032147
    0x402090109052e02031b010b0108010e07110f03040501021002070308041506031527020102120c070509010602010e0f01090b040308281d030f070f0f060207111005 71
    0x74580c02402d0740b00890000c8103083c10212414422000b2192200400c210000d43da075016924207036074890303100e4050b011080103000d101808141692800c00c00c0c0d0918901c00613900019005000303001d601c048101244800f403104540128096001e1034a485c42c00c000a03040c4241c1c8000210854410810320300041d4001c030314290816004003a000d0001c000b40704d84c000403c040e0704042d0103005161840000d040c80e54000101e00a403002d0850482030944070280c203006042040280540c02040e4100045401c50002d0651074441071b04031900b0b01d40d218085001d031803081c0c0010f001070351a0500c089010ba010005113003842c4103c8003c1100c070384561a0202d00c0030300580004c04110b005804206803941200e403002c01782c020001c16500f10802c1125800c000c10080103207000144801c0d894180c020b20210660319a2803025021921b841c104c0c0e0782e4100c00b4801e025045802d071440e201c50f1008a807141c400381c80017600c41c1e42d0100704280386100b004000305140c1d4281c401c00c903040081c006080f8501d17507 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 674034613 1250 674033363 674033369
    0xc0915031a090a050609011d010e120313140c041b020a0213061e060f1404030f020a0812130506270f06070803011a0c0d0e0109121b050402090109 64
    0x1900101c152140d07a070b11070505507000c4016103a0301c5040140840600190710888400f202452542c80200f0f02101150a0ba070041d003190b071303c0703410030a070300200c1044810081da40250f5042000030080641c1e03407080075600c115000e0341b50641c00030541055a0606200d25240c0c0f600501040a9000c6d980c0e1000f55200ea1820000b4003030451281102038405649d00448040c2000c158140b50146071100d801307003403040520035040082d401c90302800003180102c0440d80031b902c4840300280307001d0031501c4001c0c80010044040740c100f0121baa00140e900310600c680d121000741c052001e030f540c050041c558030300071a45401192150380c041000c1c0c10300084114200e07000c0404003510042c01c485000c0054654140303d00d0301504a4000510300c4100004c05c00150f05980e0320008900fa4003c420541e4800e60088081400c41c682c0309030b200c240c3da01d01030048009041c005160105000e5201e004401c002400100221035078402c400990040e1100300c48450040c0100b55411410240040002401d11003684 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 674035863 1250 674034613 674034653
    0x50913140a0f02070c090c032a0c0206040e0f04060c02190f0f06050a020c01051003050d0c06061503020c06070f09180207060507090501080c09090103110607050a0c091503 75
    0x149802c10b4841c442d0b01030f900102e40041841d10115036400a04014040c03010154002902d0015184c0c5e0502502d26003000a884511600200c0100100103940c03101c140c2c0c000b80c0e400481408001240c1032040c20861054107100c15418450802e40f4240095070803420100381950403464002d03011014904c100e84480703030003031601d041c5d103030f1a0b0a01c84500083d01c01c000c0d009034240301c20402042c1d01a0018814600000001c100f281c1d207858000c00850100c1c0070081c15608075450f6036a82034403c107590070a1a024102c0041c00c00d94400903040c066426810800110b0740105a028050009100040e4040030038188030b2040314011500030600f0150740a510448120900c917031701c0d103100d194142d07100d440c0e00400c00c01850030070b071001a001030400c2c42000e002038a150001422520340d031064540d055000b4202044503425580c4118451130342d007038161b8201506003c0540492401c011001001d0700031922002a81d04060b105400d0395204801c01d9503444803580100000b5030601d07103000410b611a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 674037113 1250 674035863 674035871
    0x7020307170702040e010609020901110111040510120e0705120c241e0705060c07110603060103140a05011a070203100e03092106180c0d21050913140a 66
    0xf880000d0080400803c048980c0d0710b007900105000005500034403020109884404003031170784498290a1702c0307140707034202c0d4001c0091108004a080000d68860314480740d0400d404003580030b1101000b00c0d540481c0442040e4020502001141058500203480a01c1d002c0540001107030580811200742503610150101c1d100021841d46800c3c0071001c2c6c0b074802c0603200c40201c60703444850780c941254012140036101402420041810940035104a59002d40c1c412070000c0c003500410100080c80d0001880207060503158600d0910703030603c0a83d114440e501151000030b035941030040e041117400604d181044425020400803016a500049078540500c0140740441d001c1116200c203070a6006206459805c0603054150700d0b440100340d01c3c1412001e14500c11030311307903644926800c404606d030468013100720f401550501c121030600e000200181c42c0514074902d0071190602c8180010b15908c004040001d0740461130045503d402080396503021002d20040c1710030007011544000c00c54000d81004d4440341e075 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 674038363 1250 674037113 674037127
    0x733080601120c0905130903170c12010b1c1109040515040204030c0810060315020d0908180102190308180f0d03091a0c0915090a0303090e0702030717 66
    0x7040c4140e014101c14401d09014043c2e002d80040d10040f007078020381c1e01c129042e900c0c503450742d8140d02c0744005183d055920340198540301e82e45111403032001340481d50351a4081011100c0100d940010724020000105c00300c0d52181041543d8080c40892001440c81508021203800000d090714103481c40c8450171030700060f403030711226000746c0c08c5000003100b16041400820004207004000344050100c03000907007034a07018400c01c006202140c007503000040c0038119241e408480702072242d0103000e4411034040c3c0003500e4a490344411106401000f001c1e0522000c0c1541081c0c256414001400c2c03e4243c402d00403401c800351f0354040d0080100401600b0400c10110b140c1261190030003805500152030820780d4005c14001900401038881000c080d52170050315011500741d900c0314800c441c0309041c205080750034200e170002081410038400c1e414481d2140301740010035995550141401c025407080d04e0351828a450b12030503014007400242650700f5500140000004a55142c105901c0207503c40c1840340e417808 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 674039613 1250 674038363 674038367
    0x708040803033d26060903070311010e060c0c010b0a090b040605041415011404080a060b091504020d02040302130912020d020c19150207091506020a1712090733080601 73
    0x1c060b400500c0c0ba48505c01c203009205402000401d2991300a44c1c444580b45a6000c00500b40d1b102d038000c04100d940a00d00080509840001410301e65400400102d000c103000400240c41d03e03000c2c1c210b6010350782c1d206090795040c0b0f050322030180204000c2c0c034140001c0005604000d0101002896940c0f24502c400b0340f200c3e03684c49180081e0610079030300959901c503510b42075601e50f44d225003141160030900e044a006514502000200e10800358600000d540380300120610002c3c3d00401c00304070000345c00744000700059550383c000084400baa40b1002841c1150703410060201c4041410710020354002030850245c03035901207400c0c100c0100517030b01483c00c0c000407002040000b07219404a902c482e074007405c0c1440c00c0d130b0204140084991458040c0280312880345001103800d0b8900c00c40002d684011140000a100815100d8040c3c0f0300712041070400004410b840d4024000f203a2a0100313810050707040c800c42d0302c204802604044001d00c035805860412020f000c200b0055403590003402001d01c00299682c1c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 674040863 1250 674039613 674039669
    0x42004050d050f100f0c030614120717240f0406091a0f04031d06041701060302060a0c1a011202010e031f060f08060403020c01050708040803033d 64
    0x4081d09044800c000548015000140015804c081559003000c1d0901b19083c800c2c0110029100c40c40b203012051180f40c6c00b04161202c0b2609440942d028000000030344410f40d02409822500950142c907810502c00c1400000c040e00c0c10941c130601e03078140309000078051000440c5c3d07800f0b50b0201000441d0307811407d0003440150205100d4040156881c20070001100681103640224800d48031a03466083c00382d99a59107081d10115a0b0300a02c00780f10410800c8901e46200c2c0c0301402d44000020465201c0d00440c4460340010001008076003100744030410000d07603600b0360821904a2000500f15410000108620010004041d04000c80d0640c1d0b41900e40c0c00307000c0341140100c1a009580d100410301803c20240c86030741300300c441e001240d40000a0b031800204006124680c0b50b409004e030800e0950040d9100c1e04450010355072a0018000840c030200c04100071800744034a1707415a078022105480000e81e15100424140486007107046c8264480c8801d0300c40c07000d54034188010725940b0403c1c899600d101e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 674042113 1250 674040863 674040883
    0x801150e010f0f03080703140313021e090a021b07030605010e070801030317040206090d060c02120708030f460209010c1218030f02010f0f09030803190c0806042004050d05 75
    0x151000006100b4603200080180c0001880cc0c0c1c0c045104c043d40084001e8986941030b4001d4001c25801d00154102c5807941c014101081c0c0d1140c594034803040454114038001c03051304100d42d07a075a00d40050004259401c6603903030000d081e00d0250601d41c11a90001c007103220303114000383c0740191a00801d04559440d410340c1c4110700041c00c0500d80000901f000e070301a00c10303407203984050301418940862006100781103444803900300340d1491940c0c5170071400c100510401880204511002402d0110039252941c410415021001c0c2160140307007840d43e52000c148400f4400e0b0005031041203600200d903044a8010741d003a41000c807144a85000d103100365121551600c0d21a401c0c05050710100c00c018030901e100314994002c2e6950300c055200d2000503a004d0119400150108144c00020000100a00e0003194000c05044104003002c000f007040400361580852034101041c2c0c41c800304105810184101302c1d4210f15240c2c0d140c248130712030710850007901c1a801140e00445001d48002c0c00d12070700308420030031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 674043363 1250 674042113 674042147
    0xb09160c0320010f05010807240c022218320304060c05060612060c220e0403231210050303160c05040c09120204060801150e010f0f03080703 62
    0x1410142c64209008107101d03102c91138050714060000c0b441c11400a101d0313042e0f6501451007101049801c01c12500c0708443c403200c00802c9480b020f40c4006071100c501d007811001c40090125801907014101c4c60a0742c0f811080001c885c00916026404200b594150b17019502d400302c40004220082c1c10400420040c1b80c00c54603440c40001400a640e43e0b0003603119502c5409070b0242c903001e032145020441d1500200745420003c0d400540841d912008010092403000e0358603200c0b25401146400854510036141e00c20213069440001300700034103400003401c2458000f800130b00c0051464058000c4514000d410300b05541c84039040008040200001610700640710050850340c131407040901c91200584000d6040b108601c0c0447c00082a040c50300600a0032207694480d43e410904006e00511320015003101030368401e031224400600c2541c203110784220a0403512001c401030341004564171140c18103a2151401884001c020808116041d0400046d83d901400c040d9581c1000d0808030303501d0fa200c190b0080 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 674044613 1250 674043363 674043407
    0xb09060d23030c12040302100f02010f06170f010908041e1703090a0602010902031f0f0614011b0506070507030504030503130f0503010b0907200715030b09160c03 71
    0xe078040080a0070310700c1000307000c803a00168043d00c00883d600880c40f000750420a4aa0301a140724080c10300703400f0584507840006001c15944d540c88007510000c0c0d02403081444401d04010000e03200380100e101c2d541c0ca00e802801a1045941c800c201f9208500c20502440000318200b40f501c84407285e2a002002c0510140d0707104940c0b015002d803686c1c4100d078407034031540d0710f50400140310340180921303180550010003900e0b85440c0b004103040780b00010075800e206117075181c403c00d4200034140b01d510040c5c450241c02020000c0003400142801c1502443c54070710214980720440001d2000070030a6000340c85180c402c1d1240c5a130700d000da500740a240c1004080e4080880d0801d29200341e0403a84045030b620000c00d0200c00e40c2d400500d402c031901c03208010340040d07440c40005d00e0140514128641403c6d015152080110600542400d160498116200e01e144428606410325818091841c49140c12202e084040c104442a114000e240320720100c2408200040c0c2024180541201c43c601030342290f01003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 674045863 1250 674044613 674044673
    0x1d06030403140c0309031c02160305070b03070309120c0c1409011202030a200a050d030206061e030d050301090b091e04021305130c0602031e1630030b09060d 69
    0x444110f030b18200f0001880303003114850080727801c0c00c114030803250008040c0002d40d0800011080c2c60f1710044c00304003815282c40003000041c91403a04e01c200110180d882040c8800a49000500d00380c60390b0088200b101c1c0840c0848041d980e0709082c42c11039410800055000040d031004c01d0600c54900070241858680c61501c0d00d03503601c0780e140d801c4261002c8803a5681710b9120403c00c0000224543c010300140d120074001850b42c20280340d4416564440c50b0103030540c3d140c000000e845c10800c000300d5400030303d0203c010170550960340038441701c8a408550130080752400d07900c207480701c200c0210a0300502d00020003240c190340315045c0780368200d5002d210902282c40c0140c24051440c0c0b500600701c8004410200c001452032001c001c2c0c41003091303450f0f0364840c1c101840c07068200c00d0b000303206d464000d414504058400a41c000100d03d4007252951840d0440c5a51040c0040c0050405900c4500b41401c02100c0c000a03034400e69429409007003103d801c0f151100b1410151407903245e02c0c02054641c05103640c10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 674047113 1250 674045863 674045893
    0x90415060b040e0a290a090c0306080c0406050108040b13060507050406020f0c030c0d020a0e01060906120605060418090b09010509010b01170f0705191d06030403140c030903 76
    0x40040d5420043c1103002e50711551a0f06040b607444100c0030b02000381c24007407035003040441400c00c000b051000303180341e0a00e40c88070418801c581860740403101180e0340e91130400041105000c0304800a000b11000c00600d841d2400203801d50300700500040c14001020300056403000403540000107140c100c0820002450300c80c002030302c00d40c0603028020140c455402944403c0c240000c2130341c1100d1025014041244150042c010070040003d8100e03800344010b10041140440000c1090091110395500034040345807035405891500c0d0301b540c410b051400c01c01e082c4a2900c50030304440c11140d440d605294080c3c205800940203152034080203041d02034602c14466111015008140070b00c51039802000030415034401520008008440b1401c0d07011311000064a00c1d00c0c210a003076101c42181019480c00140040b0180388201e80404100407410940e9551406204015000d412070015110f040c6141003070b03200039103251400445134041200005810341c89600038010b841603a030303010b070480d001c080200e116 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 674048363 1250 674047113 674047117
    0x3050c0a050a0302160e090c0915330a0e130219030c031a01020a080c16080a0606140603040611090303040f090c0e01080c03151008091218090415060b 66
    0x12030141170703403060040384172040c0b8403405006010ba240140130840580051000d02880140381d500c208102490180b40f03611040d401ea140114540442180400d1000d41d404a4104008040300c05100a02241b07140a8102c0451440054215191a90800c0103160b4901a114142000300001d55907a4641c0d0a150035412a5400200f10789084c48034030079101c48050068450703e8183e0040e80850400c10208458000611032003050b403050322104043c2e14010061480b4580c011542a40311019001c14081c007440303400d003d0101050714203011045000010500e0002802c05400959669034200255241c01c044079000380300170f030940c2e803940e540e20140024900c1c640301d603880b8241454918a401c903c114001c0d012054141c4840009458007000d115041e0001055115200e1180007140b509980701640130302c40e024103035943c0342c032480c243c1e203601e0801c80c1041b020741310004284101c44603404149240d10040800366001c02e000c7da00c609000024400c28030040c014a4903291010505e03c80805c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 674049613 1250 674048363 674048383
    0x1112070803150f0d081312052401121101031b0c060e03130605180406120201180602030d09031803080c191502090f131a0d0b0403050c0a050a0302 64
    0x8140e44050b0110302442074014a55071403d500041c050341e07440c00560000003800a4104184000003116100c02c4c1100d0009881003041c0d4581e8400d01c583c0352440020094aa8941200528807100c1d524144c0e02c0c4e154000303024401460070360140400d242da6403282e4004081c09002440140d5281c0c904130003c0c005070012041907070090f06240f110781c0140c9001017142d213010040907040c1c40503403400d80e044a00350403400c0042c5082600c1c411080290342c1e5802214041c107412000c8603540380d01c610000d405140102c9204d08048580001008100c3d004400e44456625004d804141c038212454102e0f4640c910144685107a20440c00200c1807080800203400c8040710401201e502045c040702c024002807226400400700b8100403075081520102d038000d4000c00b0800b0384490302c9020424001042401160f0f00c1035003065681d10300c80d9803140400e24144103179400380d5010801d00d40396186c18401190091000c5e061042c0000d03404440d407003c00c9142003d0350000b05440e0344890b1860001d40340e14940ca = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 674050863 1250 674049613 674049631
    0x109030e1003020f09010503060a030606030501150e04030804021e03010510030c0e10061206030638060906090a08070b0a1404061b030311040801270507061112070803 73
    0x18040781150080c8200c40c0446166403085041039030b45001101e40e5800207003d0350300503001103800400514580940405940b04200116110311104064008484540d1080440300c08041c24040405d40004081e504560142c551502100e0000c2c030660281241040d030940540c40c180c1041080803900103d02d0507a071141c0d6502c1103190b500c4d41140400c6006035141c1c010311181000c04c00c0554041c05070f03400c18038040740010818564a031160b00882d102140d9035103450242c0c00703074040701f600c074804003003000c1050b440342003600d10445021aa1502588540714083c0e4400100c0010ba66109000385000300006822100c5032601c41e8241056a00040054408555070318161204044040203035402e403403071507540001d80200740c4d480e6034070704000c4041601072559032160407801c081e6160003400980601c4001007400d158064003103a50321f958205880311845207003907400c000389004c14194215400b078070740014103040c1482e003103051152601140a00000004443d402c211048000d0351160a0716 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 674052113 1250 674050863 674050879
    0x70501020d0b03070518060d060e010b011e120e0f0a0305190c0b06010f03140711060901090b0f0709151d090108060127090c030c060518090c09030109030e 68
    0x31003410744d16041406034541c04207160b24101c0c0074569a5241c0d0390300c020010700c02c03c03208481c1e40780d8604840d040412000765075100c1c0500202940c0105654090b1403c00f0804213800d040450001c15002010761101540c64451076925016071040007449003101a21041d198035900501d40581320b5440300303401004800080c1d4200b450349000b00c1002080a8000c07460001c9652403100458510300300c01c0040040c9551341503000c0c416030510605a205007071a4403200502240020007915200c0300505140c2568184004a40001c3c03a20403060703000169980c0c800c03141e40f50b00d0f6050b9030704501500726001c22290f031340a8401c2075520050b01980303030140c60100e0724100c11074014450041c00c02d020304c50156120000401c070320034213010011070007441449502c101c407081c0c002550680e4514482914001741d009814010b00c0f4081d0866001041181003d48c604290312140c055042c0000c449035200380c0423840010302d8a0203010481c1c070910401002045140c00c1454042d018400010700103000d0440 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 674053363 1250 674052113 674052131
    0x303031f080a050a03050d18080a1d0307030f021f030902040c0f08040212010e120d0605030d0e01030c030b0409050d08090313030b040c03120905090a0c05071104060b070501020d 78
    0x114020b00c02035008405041041e005440030744107507001e0300c8042601c5688021180341c0d4070801c1c045801951181040f5a40e55600307090040000d400500c00c4c03a0364900701010040c099400003581c1c0101e0b680140c9626480000e030000420f00c504008011001051022641680a502d603120860f460700c2150104030240c9171001c00c491084160884c0707008946800c1c0400c0c09841d0207040322040140140c000302d90031200304052800c0c004007000c9010040401b0610105000485c000c400107418290000d145905000d0740051901c020407210f01d0505664403014001603101f034001406083c0081c10a00000320702d854010703503851401040c000013512000100c0c40410002c02102e0083c25a440c1051405003107888804544002600840e0000d24241d0008005080c417201c14142894984074840307a40e203844c5c1031141d680402031044080728074108200c101d01d030300501a02c01d09034103c40c040c59242046404030b00249029000107034038002c0456280f08102d4150010320a14500450601590780 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 674054613 1250 674053363 674053379
    0x708070215040203100f0608011a03010c020d0c0803071704050a02040606030b060d1d0d1205060109030309170c061308010b0402040e1612020310030b06012d0c020303031f 75
    0x103440c02903040d005040042074485141d00500c01070b00c43d0506c00070b111660b1f09800e40c2120380c86e0580c0030a0b00d100b005681110301e4207105070b088044a5002400b2400d601c144020310a41220400a2080002002044178107214a024210340c201c950343e0849103041034100075581d54601d5104904c10303410300c200881d1191007130003952040107000c0c2c28241445445501b80c1c01404c1505000031040a411a600074650010460101524015125000f449810f00c0c4004269400141828103001408908000281d0f02a82c4902128030075040c0d250103010707845226051060541381a5400040030800c0d003030201407041c041086541c198002c11004030708405000690040d0b00c10115001030301c4002660101d8004d01030880d406480c41d121000300c00c040c3c9600103d03002a280449805c412103c1072042207803041d2032642084c02400e2403884040368035106010085028480c0f84000700c1150741c940c0103400b4040d4401c1d06907005003629180d03e803402c801408150b01d0450240403148000e40003d40030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 674055863 1250 674054613 674054653
    0xe01060602070902160218100b0906030c0313050f010e0f0105150d05121c05070305092109030102041404380f030d020a060c022b05040e07080702 64
    0x80c01a006024a185010b1000009400601c0300d800c11007440d48000c00180d45240c1404001810403408103024140303c0d040c00002d503010f42044100701020010030345141c1da100103996015030100d1034280d4a503180c00d850f036407400f28464014420320443c031103880400c07010341000a40030308400c1200e4024284600850980da82644c208228524103000203080b400c0800002c1810340c000c5003103c0080d11460316445642e40600c00180b0518840a002c0458030f50724001e60303800c400186003d01c000d00303000310350f40d4440c1d0650101e801000c800c4201b55840070740c00030030703200c041c1e074000c00854880e5950344655103011082076045200320700d0078910b20b40f182c200001c0d0303e9411140c00082445400c00d11110500c48007a841440d501c41018866160b01c0ea5082000c40d4010f062580500101522458010141e4100342170500564019010041010043c075042d42000c4103c0f8807103030700d40ca503d200146d500744560340046003200200310070049029085980b5070300810f010b60031100b445a03481d075a10b02d02 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 674057113 1250 674055863 674055869
    0x1412040219171c0e1f05040b0706140c030420042903060106090f06030f020412060b0102060709150e0f0301140108070905220c05040e010b130e03040e130c1202040e0106 74
    0x80000c01724041c0c4980d8180700c04d28544500703410810f14240e240c0b0b54090a54220302400c442c1c1c0d507101c18040daa84090145003940001c03100400034110304260703542d1110504ca00045802c10300c007007142c410349961070b80c11441100400f0078420101e400c0583c2d40e0200195005000d07400380c400c0800001e119482071845508840d401400d0990550801800302c011701038002900c00d000c0d40900003c00e00f5581d40c0708980910b44507900000e82500b0000000e82880001820301d0305008010404110b04071242d202c200440380c5900e00b140890240301d001a03031001031110441d030158604440252207511031004035040c5d458039800c0350a41d5941700480010f07140103c1d40d0065085040100f005940001100b02601c60301c200700e01030325117483d50040341c100c88030185144826911400350b0b48241c113089040b0745402000200a0000e02040d4020907074034803c2d0b1185074070129001e00018541c000d240000e8040d140e1016146428a40d03482c400403c0010641040e803007607151544000c402041403041c0411 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 674058363 1250 674057113 674057119
    0x13080f03030c1b0613030f080c0406050d090f08120c09010e0f0d060e031306030e07050f010c0510090b0612301204031412040219171c0e 60
    0x690750350406841642e0f00030b108841d00d409a0486416001d020a02140d0b00c031380701d0f240b00c0040c80032250900030100c4041c81d50604c1403090010034041040001000c035015110181802e0f9901c47d051903c031001030203400005000343c103455074801e003009490001485510407000510b5410740b00c104460310031303101d0b2071782c5540803d94135a4441018100030443d425291402080a894042c05886000c203460151115609940001030000402070080d030704800074103064501082061b888820050740c5600c54001c9a08c24000c44200b50203e0b03204190b603000341c59100040d2441280f05000d031402070200c038002105d500400200050f25810682e080d9115001004000e1460240d4200c1201c110750b86400d420b0400300380b02200c00740c0700000c14024450842c3c10702245407207181c01c0c1030041050340c0380b500c02c0400e02710030000043c0454641072100d411030340441d01400c6451048114109001881d44180c80a89055011408419011402040e400700300c00500e4000e144420040300c00900824000c0d038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 674059613 1250 674058363 674058367
    0x10e101703071106030c0403110d020405090a030f020d050d02090406050d060c02120f0910121d0706030e030d0513060f050415020906040e151f020d05090616032313080f03 75
    0x40030402c00502d100110074041c0c8030441307020ae650041010f440702180c503504c0e160b00c150110410158040d00034201c8900d9407000c3c000c0c440502d04001c0ca94400c00c010100304c240c000c85d44241d20350303856000300024480101584100394803032030b0600180090003041000f50203002d60790004081d043c0100c604c040382d041d602500d400a5a0100100c00d01141c0304803007000801c03440094040010300c6600c1d95811646900c0b0112140943c09a03e0007125410a0f0200340c1000e4407c0d024000000c1654804500e606012640340d030741494160401c00c00300710143c0710904010255001b20300c540e0080f030040303005000995a0000c550640c20903442001c040b60380000040004100d842c0c000c00880d070700151541250703200051a44002051020306a240ba0b800c4185031201081c181d40402c08554040280e05146040054060010b000c078002d0102500d0150748511880c3c081501c01c110928220000e40c00690a1101c0c40711314101c5600709074034101044000c00b0021400802c00944240c1c5403034003c000b18 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 674060863 1250 674059613 674059619
    0x810030605041b09020405040b03010b090f130c0e0708070c030f14070614071106040f02010e13060801060801060609050a1221021b18010e101703071106030c04 70
    0xc0140300040c015608007288144070345000c1030301200300004241001c03015840303030f00f0041084104c40420055522985c58140a04007a488a00440d5407203211004447c1440d99078804030302881000800c0180b6102d40145c000c01c050a4468400b8000c280c3c0d65a0402556165003080d205400d8107980507021496076009580094803456007050000090000c00d800e200c400c2e508d41c002c3e1205481d000038420361005c200106141e0000e182d08680b0300c110020300d0f940c2000e441d0300d18454030000000e4100069120b40003a0354a4109902c21440070240040062036629003110307009007040d000b440019400e18800140c0e651094200009861004180c0c20442c2d18203000c60340b120501d9501143c210116011080340e0304140315003803103e112160040c0480702c40d03000d000c1c0d130b1500c080e24a41d4480d092100005000603a0240c5035410740706040082c2c025070300e50703100d25074001c49960310040504040c415504821080170003d0420303a842241171444042208082104601040b03d500740c0d1200107100070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 674062113 1250 674060863 674060873
    0xc070201080414010f0908220f2907060501080f0a0b010506030403020f030703080604230703052a07021906020a03050d020d02030a200309150411030d020706020706081003 75
    0xf4038400c00302000040036505403415038103640d46a8401d8031480c1d004240840c0c40114642069040e5803501c07404014982071482064911215010343c00382501c0f0341140750755070408040590201501006229100c810b80d00c0c040c0041c1c002400fa00713840303000760700000c10100d200060303d24200740c4c402612103490b0300b454180041c07504014016000c61240703802082c5030300703002d100501085002e940c5600f2507180507030500060310f103085404000c13100d201d10798822401c11660f201c1d4111050749004501030b00c07602d00d1190103100121052103601e80d0082680c2c404500d00d030042c12084c0c800c0e1041e0342650610350400381e40143e14811800503030402c180080003e8031610040c10305008424005060100d03c15482089800031203034000d801e40d47c0c00d54400d040f40c030111441101c05c02110000e00c1d52620414840d22400440d409102c1900c000c0081810440340b20704032044240090200d0b510703105128002559008a841504058010308101051191003004420b100c0d210300035141d9041d5195640d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 674063363 1250 674062113 674062133
    0xf0f21150910090c200d09030b130501060609090b040203060d15020708130810060312030e0a054602090a0e0a11100801051509120a060f050c0702010804 67
    0x1d048407452041c40d010812103080d104440010180317503203125802c120541d51140360050300081c626142d0003004401d451a5000c1454000c0d00e40c0460301020a0322401800c030380502d543c12004049509089000c5030007503101c072041c403c407400c42e4018880990380c64188070483c80183d40464000103a00d101e0300c0404c0301c05c545a41c02d045801401881c1c40d02c9500c61981580001003000c84020b00260204002c28041040d500307011f248403020001d00f032540e62102804450078600000b410b4503404106401c1101b801100e10080d00b00065600c2348000401070461000003038103581c0b50440d0800d40703000c1d003040e55116404d46506240d40c1d000c890041c1d000c105554400420300ba1005845d1440750840303074014440d0407800b0340f050303d1820509481000b04103005003220300200401c0120401042140d03500328000c07466040f5065110b503070305980c0d40800c580303501880300351082d4403848805804014669019600d002d2181100b00715946900381c4d0344c1801c3c40350143c060f0004d02c000d00403401140c02025 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 674064613 1250 674063363 674063371
    0x111070503090d05191a010503060f010614120108030405011103040e040605180d1206090b030709090501020c03070c0509061c030f030605122d0715050f0f211509 71
    0x200311403170f4405a4030b03d540700041c2e0000c126590b01c0da80c1946481c20780d00c60055405005c041700134200d0780c68401108900380b0070501c00c1008005034100424510380b0680104d83d24048051805840c0791b0b19105003650340d602c28441c150000b070a004030400c2c5440f001c01030324190707008070399284601c1d101c0d034807208064640904900d810008440306e400c40024200300c0035540c070a0b95203504021080007403102003166070740d80c0f10b00340690a085107009260313400324954040d500712074030010718900d150034903e00900035480c030415035100000c0c0319024490340c08044030480300c0072500d070711540e50740e02c0510032200c50822107002514031140039800041d001ea4940020f03182c00d4500040c00741c0d51440018140442c4245080715074101d5540000c100f89884080380c180844010391210768540541643e5031a040c81c8510b0308003007651905440c4941c450000c44051038049003005807150891030381c644640d448401e04220b4403d100c240708481400c1c02081522a400d500e08801420802000340104810300078 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 674065863 1250 674064613 674064623
    0x3020f0c0a1a0a0924020d020735011d010609020f04090b150a030209130506030c010c0503160c09180206030604110c0f0307260301090c050d0e06090111070503090d 72
    0x45011a0b01842050f05030b07110545090340702d0f105c60940300040e003044181c00010046400004003800680e20286d200013801d100e000c041805140c1503088c080c1058404070581c4465401e1040008201c103803642c610385040c01d104000c0003155038070b0115004922801e800c0c0000c00400380001c100138901544028a00e0760701410001e0303c1c0c801c1c10b4070481540e12804040010030707804144182142000841c0c100030301e040300390401c418140b00e400039070341e4181812050b040080078140d0008000c0c1c10300c01d4030f621026000340c40750a48400d190019400d0003d01981c04140d00c0d000c0f0302065082c14692201d0300343c1d000791a451451702c451301840040c040041c40c50b808503e04111582c00e01604004007100d442000303010b5a1940021314000e48200740e421207140c503032f19642c11f080b05030b50415070851b41100c807981400580d2068035941900d0fa8020383d8405040c0034a4000c2650143c0f01c041041885804420002c005401180f1346d070140900588401500b40e41c010305c405507030381c03c1404136101075074091 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 674067113 1250 674065863 674065877
    0x507020303090a030b010f08060c070209101203090314031207050f070b0a060e0606040b120417160302010e030408030d050a1d0a1101080601020a0b070909060303020f0c0a1a0a 77
    0x5022070040400c1340e008442a100820040014603150b640000180000c20044d0030141442c1c0300024942c026000068410107441000c1026003010f1500240104000b55034466004804d04000d0041001d030f110642c0c000c83c00300e414606990f0044112403400800414000b4152542281103880f9001035000540800c0100011004078000c800420b100320141d800214120b8142103c1c0e006500003d07002c00d000f41001c0c00140180b408010641d0445080204095501d54881c101801d030752030650300b40c0c04601c030b0000c2e040311070f01005139507081c28034003d400a1005a450000c0e540da07030301ca284038040d5107810034890074120130b129407c60384c0c000b4030300310010030070f10b1025011250410000b4490380c640d03071080f0f401c04100014401c1c0da800713451003400d0074502ca107010300000c0c0d181c100040d00241203550b090000340c08140154240000707016615800c015180c4c0381d207030180d034515100b08110f040b8800c000d0030000c0da02d0100d05080603070b0904401025020714042c2c000100b6000320f01c40005010030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 674068363 1250 674067113 674067127
    0x30703031404021c052515080f0714040302220c090f0521010c05180609010909020304051e01150e280f15090b0409120c080d05160801080604120507020303 68
    0x1000f80103030600002070400e00340703c5140c41510407c841c40515240c0a0004c988100306001c1c56200c41260b00c03107942d0509010307a0100020107452032240d034000079807007a580d80c0482881480c0e4a80d10a82d1035003500e080202003d480b0064502840f18410603000e03540c803d9050085040800380c510f0808100e00705040c6d031401502d0031a09480504000f400010310200d0a443c003040010122130080805455a81c40c20781004002405038080d402117856607034000003c54100030080010200f07500c80300300b15500c50600da462140c040d04d80000c0d80802880d181401041024200d89080d0003480c3d40a4104101b0f00c030b0076014401c4e0442c000c3d146d60340542d158010341d95a43d142c0107d07000c060100d5105007082e030906c1309041c12103000e000ea04e80107a00e040201800603c100500c400100a01d003031020318100c1500c0c0c090003030f1107040d04440c002c50605081c00703042d00c2d00080c5481c420507a512824056038984086070fa03160812200607091058101001c045640104010501140083c060341d141a038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 674069613 1250 674068363 674068393
    0x7030f060909032c03070902070203031201090f06080106050d121713140309012102070f080301030201031409060a1104050d1113110306100302070212030703031404021c05 75
    0x1581d40d00070b40201d8200340c42c504480c3c103420000c240800a40c042228414401300c0402e43c2c46045026600c440c941c00030341c02003950740400c140e9400000028040100b5a1160b0a02020b01082d18020030380506010000c603028006000c0c45003070740d50250030354150403540d4440000c003181c06d4613200103210f0000c0d85001e2600201e01c42d03504c80d00c54100e80140312071281c90004929040211000d01075082800703c00d81c180ea12504135004601030200c2c90f81012245542107000303110350080207000c1106c10002d00200502030000c3e40c1268000d80301081515843c052211801d9812550041580c102c0000682d0407442c0b030703000c042080d200c0e20a55007070580300d0003c10000e0521120984898810180206a501d00390700724000c10030310b0321800e10104880d00000101800081d0010744036460182100d0b544502c20b1741940c024540061054901c80c2010303c803141c49502c00f81041c1c00103410124915100da000c0d00059020345d6000d405032540c400281c3d0301e40d440c2c0706070010450b032a018262a84e500310b5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 674070863 1250 674069613 674069621
    0xf1404030c032d030c03020c0a03030f0501080c0d150b0d0305030a060b0a171503011b12020301030206030606070219060f09150917010227180f07030f0609 68
    0x40c403036212a018107007107042c003a16203810082100564440100d000c121280c03030030030081c10400326080c08a80802c0d4401e065029000390328076201c00b03204d8002c420050680c140c120203070300520b03000b007081142d0300d440490f074a40c041c0039262600600002e4552000492100700404450f42042d0005002082e41c0c0010b12041400762064000410104c14031003850803500c100d60040000d80c041c549000f8100d4400b80180e0f41d00c203081400002080300050028100d5400540c00d00c074020300801203e41601703440c0c2d01480700e8140d000300041034407441704940043d0f0700c202da058035001444e003429540c030302d02000b405ea03200301800c903000030f9030340c0203041c40220a154140c060304854540d180d034a51621001080c40559602c004140c490401340c0d51602a00810b602c0d06859400c02d00c00c1c040e140c0382000c1390191003a68245c0000c0d48442460b000454413140700e98003041c1c2c040b03800501d01d171084201800c4046017940c0049106c29210013040c08a8002d0b4050158054028404034a09644500071002c46d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 674072113 1250 674070863 674070871
    0x160f1409040818040501090615020105040b13060e160612060303170901140a1a03010902060301030f1b060e13290f0616021c050606150c010c0903061512060f14 70
    0x3034523000c00340484110f24000c40d0480300288000c01c6189010f440b440007a04015010700380c0c01100c1c1ca802c10a000c00ca400182c82c10300381108580902d4484920161644d01c6845024001094080d800303400581c42d00650080301d0301507136800807146074000481030740d580103044004907650b50000d00d03204220b40d203e00c51098410b0240007480d00b03500c0c040000c084400e0b5200d2486a49031011b00001070750740c5402e9a041d80e0304191600c1c25000e4900d071030b2403e401241e8105900b407400c10400901c01364080c0d0100401c2070151540c1d60b0300407900c0c0022080e6078500c84480c101800c0f011418000300c59020410840c440002c026540854901000c0744a650044214031075092480d1005401c0d414210702d0074000745040350302403060034035540704c2039210503029100f0751084044204a00e41441e901c41a01c10044280008102c1e155041038041c00c140d4251100301d50b51410a89024035075202d0019510450700b0740f800c0c081030701645644d40070040014010500c0150341d1303094404040900f8925851103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 674073363 1250 674072113 674072129
    0x80f0601300c0302030c0a060503130302210433140d0608061b0304020a0e0405120d0b0306060a060e0603061f050318030a1209060608160f1409040818040501 69
    0x310f04600500d41841c0c400790505003d04441c000802000d40d10178120381e032006e509540c400d007c00c184d242c01c90425400038044d1980c28045140c01004400010080c004c0741d810154207003204407030604040f0565014004540c01d880c0e140f410390346040c0910501c210f2028025400c615044107005881c0481e030705030308007001c0340e84580c0401c04000011408403c524920508980c198680783c0d0000700702401d903014000d81d0b904808007040400c201002405482203841c5401512085c020141e03000918111092903c40c2c030880f40440e0a50820b90326000c1595070540c1c80651036014070007840825403014014941004540c800d810400310b814140e0040312003156038603036890426146180d410980c0c0711020005402c104060340160fa0403040c0818140003410f008508800b242c10000700420041e8840c0c0b4660050192240004440314a69000c1e10000302c0540d004030f4883c404580031140400d80581c0188040c400318010a48182c06000f5156944181d5041c0400303100100d03042d130740c0030380c09280 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 674074613 1250 674073363 674073383
    0x209150603180f031e0c0c040603080309010b2b1e1b0f050a0501031d0106060806040e03031b070516091b0507110f191202030601080f060130 62
    0x4002e005001580300304141400950814102d02c00c3e0240904c80a184043c060708002000c1c940848240001c42038550700070800c01005a80782480a401da004030380054680d4640b41842c491450440b0304410305444d2600c50448040ba203071407462440250190590b040482c602c0c80c0d90040c0261525200c26510803160444403685010002d001c00702160001c41d09122010018001601d4500c02c28040b034030b003481c020032107603e0000b0405080d00c1440500b20035500308000811400e0b0444507090103503e05640801401c030800000e140c40740000d071202e2140540110405e141422032901400c12030340074109641c2c40600c5603c01c080544a15800801c00c42d440384c520045000c8a42c2d0315160441d09810464600082a81c035100d030744036842041e0303129880d0240c01d6422030710395001400c58200e503c0d1013080095180d0b1f8110705003982080040740700f4032401c4000b161154003c2050fa010068030002094240d007465012811800510b002150051190003141d1902150628000740603000d18440d071 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 674075863 1250 674074613 674074651
    0x506090d0f0c030f030507050c1506090109060810020a051c050907060807080a05070e1206040b090f031206011b29070f110102090603011715060d0209150603 69
    0x81c0014070009840014032040b5100351021940104250b841c141e92031038006581d94910034191340500420500140e02d00c40c010100c80c40040850034a40510700072111403409070b9940c001c210640f03316014010558004480c1c40c6510003258005c0e000800140c107040d03040160011600c41801c1505401034031094460080c0140e2050610609014050a2609074401d00e800c9201900d8080301400c0602000d80c1d4400198005214495440080300001c10701c588021459044513682c0b00140da040d541001044c001c520060130010710010032804d1341e8043c41c1801e04445040355140401480745040c8000d90701080e01000304248602a43c500c181c0422950800703500b4544401080b1030203014003000b1000c00d0040c055040301d203007281450945090110200c9130100c20303000e40110848180c01410220011500c1d0050340d0400c04850300341c8040b162030060070100c450b170b2144252130858020308409115805403e144440365403161102e034101d01040500d902007103140d80110360342d06048403a02195 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 674077113 1250 674075863 674075867
    0x6160c030b06061305220e030a3c210e060709051f0215010905071b0b07112a130b061204150603030f11370506090d 51
    0x100c0d0300316409a8001d070419440a1418040704107074043c06101e84008055140c0c0c41440e1240c1ba0340c440c01c2c8400a01071840f040345000c0d030f6a045940c0440105070b2440c00c1c1200101400d0460400c1000040c80340080000150100204203140110703600b08144809070154100c8002c0000741c0741c51304c001c0000345450034400c3d840e0808401610404c10400480c00800007a83c0c2c54079081d030681035402d0440201100032b00140d10740789004042040c002c11140000600303080c558403241c4280110384410720b00e08548829002c9606102170010480098900442e8040d407040ca01c043c04a51424100e070f880d281428414681b4a00b010101603010301c0710342c1025070509001c102d107100d10608580c140000b11240000801c0c81c02180c003e00720380440000041e00740404c1a051004000d130700f8108200d5603460f400d00070124050341041c800407422002083e9001d00d1b0000303182c0c0d21a900c5c2c014a0692100c10898201c0a11039601074a14002a80f4240d0000c110203101241c05018808010142403403c0400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 674078363 1250 674077113 674077133
    0x7050a050402031003030509132a090b1606060b070c03021507031209060207120807140405090601140c010c03020903071a0307030b0a030c0b072a030f0206160c03 71
    0x3607018500610900103000d21201d110700540354142070043c4c4842003d00030070461280c290003c000182460100450442040155540004042d1100d03045007145074041da03034079605105411045804002c0d02041d00650764550503031500c40c5801003038440e81d401d0b5584680d000403c003511a001d000c1740c02c10031403a043c07610071502d0041c11002d50400e9800d80380070f007c41c0440440c000781e1a0b169200d00c8100b01d5640c2c100e0744400c0e07104441c1000b07502c48200080000200b26405804034501841482a81c02d291042e201110402021600c4a544003001121204499004000c070b03070303900b8410180d926400780a8140c000d810742c2d0300103849494080406242030b009500144906801040f40200400c07610f0441e544040700f41008074400c189100464440c1206501c042c10445c4109030104203451030300000d0603664010b800104002d80b113040e150005994800d00240a103d082100b000020004040c010707156000070400b5042060394181c6400500c524101150708000045050080040e5504 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 674079613 1250 674078363 674078369
    0x50903010b1207061202130b0c0f060f070f200c150301080c190302180a0e010b101416050d020d05070c030204050a1d0d030c0503190b060c0f07050a 65
    0x5034034603840c550541c0881d1940c00d0f90042c0000c01290301d080303642e03881c2c07642c04840c4284505c00409200d00e0f42e546c1a10804c4d001644a00103034090002095412000054118010f4a2041007120180c84c0c200c2c0a64190114440003010300000c090f640c42802000e8909000760baa10320003810040c10203804205c2c403604115682400d821081c030042c0310f0f000780060700840c424801c4d50a5a14090b100040030000c03036a80e0310003540003501a035002180740350212500d020383c1000e0028407050071800c1e4110300742c41c2109000c5421284007003e01c100383e886002e4000300e40c032290704500d1820070010407000e00b01410044c00c0d0b0300d5038040c42c09283c42e268100030681c4942e15515206003086081d9880000002d441d100c0688120303180c0c00815040503565110704681d00354004107503e4089902074682c1ca4420030f28004020914045c20300701143c0c052002c43e4403503164140b105400d400b011415078018040449101e81150061000340c080640400c125411408002c00074040c0500c2c05040020520043d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 674080863 1250 674079613 674079619
    0x7061103031603050912041412011e020307090e1509220303020708040503100902030709060e06040e0f0304030501062102011b03021609020706060801090807061515050903010b 77
    0x420010740500c80c00003404854000c1c540411252600d0006600d004042c4620406c0e0300c00c0000c001950390080c2145103004031040e2580c0c28403455000c1c41500301d801d1020164003002d2515005c90714190580e0003180e02480f0b070f00742190126120750301e5401c40d0804458496030301c0300d030000b100d03018640081d026038421400c10390944401e01e01c1c20000d815600c03040c402018950085510340c1000241000c1da005002c02400b00c03091074000c5000f12000d0107621034164080d0003610b00102c0d260490740228010780e986001d408a0580701c09003880010050b21640c500075000b00c0c407489914641c03d1000708021401840007145042c200401d400c0014040361080c240c5861681c145c00050740c0282c1c0c0481c121150800c04030b04244242800d138103011951407500441280e081300843c4141c06603001e00b4800d0301a00c01040f03055101d55000d422564200d6000c0c05c074480070b00c40c07400090b280f03420120982645500000740030b50f503030b805030240181000251000c03c0c0d000c89c0c901081e0809114801c0003d0f411 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 674082113 1250 674080863 674080867
    0x30e0c13064b17011116140c0312090a0306061701050109060302010903030c0c05091e010e071e0203070503070606092d27030905010206071107090c0c0b01060207061103 74
    0x1052080340c00000d0301c2900310b1090300b881d00d201e400100391722502d480350f480b030080ea503200c50b030404400800200350801ca038111403c2d40b40b1001d0100010f0b29202c0e54201500900e00050120318010260308030941150303204a240001000184080c01110010441005808451411a040c95003035400c16003001c85101e1400e02d00f040940c1c3d000200d641200e4040c2480314450046007880d490500040d0809900803811005000210507004c48520f480b590f08000054580d88039000d02903100e41c00d0351100c000400341c42410b4404c440e48441d070302000441e40100e034a08203c41d99101d0560300100800c1d40d5140d59560100a1b5040d41d0040500c1c48456030304101c406000d1045285e90907d004c100f00c10120f5440c20264480c9811440000135004100c0800a00342c101d440c00510003152401014014095000400d92103070040740002d000e03414101c081c00e041400d150340c003030081c41c00b052254200401c01c00c4401c041070002075a41d000c0c298a60181c48207030f00b0a10054211414800303102015441 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 674083363 1250 674082113 674082239
    0x3161a090307080f070b0405070524041a07060501060503010311100f260405011b180308090a240807110a0b06060f031015030e0c1306 59
    0xc0882220a900d90100f0000d4894600119070001809440d070014110780d000c209000910a00040d90701c100c91044a81d031104810404640c0940412503916a204010509c814084040418061844044e484070030b24140400354450740b064032400e078041404150000018070910082e0844042a44000d0b900c0344116000084e0042c10308100326111000c111400c5400e4142c651204201410805e280c4180342044c245418840c2c000d001d1084400d0b108410200d80e4403225020b19008510700003070b030801c1d54103680b4684034000140d00090480d641302c4120301010071004900040c1d8680c204082400c2800d2200c0c0c080301030200c4001078810021320a030400000a01040061551402035211416110540314040030641902072200c0c02090844040f04001d651182c2c509000c0c12210240000300001c2c2543d0f03030590440d1480b40c41c81c00d094000030004180b07410444c20b142c0210400182c0003d8260341c4103070103480340c0e580403031449800b11011b800038461949103211200c040e44409145540182c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 674084613 1250 674083363 674083381
    0xd09050c01031a0d02030c10021c0c020603040b090309060d02070c0803040b040519080d17060d080301030308060111011a09100b0307081e0a1407080c04051c0503161a 73
    0x1e0482d41c40f81c4109481161882191820f025002050a000c1d00c0008101c14425005e03498803100680050a851580d20703c07a200c511a011000280c3d4001e8001403450316113072202c1500f608000e0440c0c4040c8000c00c041d07001500e515000b4240050500001030320703500b080c03820608600f000c2d8002c20702d682c0240828056107442408130760448408a0300900300401f0001c04440c0e44806511103200345c051480740742c0c64907800207801d10340c0c2c14007168207010742d40d24a010400d0381450010003610780c1030b0500040c80020300907203105400042c1410810049480c650803c0c0c2508c8100e4031004501802d01a5003003c0d061640030300d40c020b0070002c012808030703082035200c2040b404010103800400a4080114007005049203604102500301c80d4001050700e08000c4440c003134088000100080d202000001d9510f03449031580c64000e403180c200e114076003490081002200d554030180704407200a00c913403c90018134200020611086004409000c0c1c80c0103050040b031071a003083d4100c003114ad55071f04101500c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 674085863 1250 674084613 674084651
    0x2040e07270b042406080f04080a030e06160207080102031614041a1c0c0e1908010603060b090c1e1612080901050a14011202010201020705030d09050c0103 68
    0x80d0701c0c10401d000c0c1410005040080c20300b03688510703081843c251401610300d5140f01c0c00f1065950050740320920a1303441c50100c49150040b12440100c01090010400090321003009018103403003442d010501660040d100390034070005444e051000ca0b0381e0b00125160326018841c0300c000741072480085045180015020000030543c1c004142002034001020940501200941c1c01030f00301403200b810640b0a46940d121a580600c42e1240303031000c0d12196038482c594034012004901c86640c1c80640c004082020b00040801070101550f00341007001010501c01003d02c84c01000f5409840040384500030181840084c10b009000108280d8080180c0302c01d1031400e00c01c0103003540204140c9651050455001c004e4000c5625000b4107040001c0702c6607450645c0401010b00590b1503030002c21031611031554903400c940f005160000d940401d00e004001138800c007081d08038035034018000985407601c1d5507039080c03c1d42d10080c1c00d03d00d115075525071481031000404c0840940b14007070804006411604036074071800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 674087113 1250 674085863 674085899
    0x30803040b07021e011a0a030201051c020d0207061d071a030c091f031505030a060b0d0204090c030311010203010b090f040b040507020d170708041203021207050702040e07 75
    0x1110644011500d00307407003085420034800d00510305130354540080c44450f01074001c040c84e540d200381c840350541e440c0e482c001d0035200c12a98141c540c41e20f8412a0030b001001840c540c6124039149500f0f200c1071070011614001003408611426002646000e000c00021014600c68030071180e9a000040500142507400660b86000c640078908607120b6903540381d010240d110311a420f43d000308001800e010340808113130450840c03005c00c0e1010321904152054804103640c80d032156580c0b503440215030384045000d80d409114207100140460010b440207401080984407170303520444040592580070410b143d0700c000c2d00c0541e1210740c0d0003945994540340001e051170041d1003ca0b8400c01c040254051a0754550b84840741004c4041d20921052401c0c400103525440c40038082c201148501c034052040113142c1010324494807250f150140b807038541c1d481301c50b110101c2100200905900700014003001100d04412846250140e070b94503521501c51040c4019a10369001140c025801101e060025800b258404954 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 674088363 1250 674087113 674087123
    0xa0b0c0f0304050f010c170a09180e0c041a0405041109090604151e1e0f0e0d0807170c0a170f040308061315090c081303140d0c0e0a06020703080304 65
    0x11b42c05092640075806441a8020001000070700e81c0c0c00c1941181600c8119064591440326140074068507001b40c6298041103d15030b0445540c0c40c1480c50300da4030408888412080d10401c8085100114080701d206980655a2204183e00f04610380703411203280c0d034050310f4100074107014185070f6034035031795515441015801e590f02d80c5507020001d003010700c200180c03046101050010070115401d503e2401c0140e949121080d0030203180c0800020f2030f0042c0b00b0442440c50040a1307a030707844e5508440c0391002604000400221104d07040c0d501cae0400c1400350064104601040d915205c00764058125640340c1c2d000ca502d5408030701000006c40c4075a400582c0035806003400c2c8855603c01e0001801420840200701d4890300d01403d140e50f00104c0055041130328800d070010000030080000540c1c0e42c940458444815951180388840060f204060620448450950305800c042c80041c20070140e400c660141c00000d10844400d914a04d0701901040040c0114009000c44505549440b01c0500c0000c1010746 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 674089613 1250 674088363 674088377
    0x180f0c050403210e06120a060527061909060609050a0b191b06050105030f030715020d0207170306041b0509010c1a01080601090501061d120c0a0b0c0f0304050f01 71
    0x14042e0403101c011180042c500d40c0d0b1b41201c0302d60500d186805440440785a49481804501e0f03003007854620b001c5e603581135032060039488202258600103000521131900241d140140381c80040320141d641010b02403040d0007288107810001c00401c102c2140c0e1055202d003401c1842006170240d18811a200341003103050b903540c84482600207580000d000c041840c10240d6943c00300707042c003100d6840141641c5045003070760110760105070903a50f24000e8400182011001081e400c000f60015802010341da01035040150626003d07850b1f2004105014a541607900000001c203c0e0a02e000e00c1084a00c4507008450200c0310b2409500038990b00410300304905005d00e9000030300901201c50741d00f986091899040ac2800d6840d2000652244030030700c174182c1ea440c00d040c000301c1d90901901c240300d00c0d2403464081d020001c1300c01003006911090500e034084c0794021903aa03400d40b0740b60301c100280030341900d062003960348290304043da141103900154000300f81c0090006000950341c0050000c0c0790102403a10340 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 674090863 1250 674089613 674089673
    0x181c02011209142a0f09040c030b01030b220b160c02060a0c030f0806030c0108040f1205041a0306030a080705101b08090a02030a0204020a09180f0c050403 68
    0x20060190860151009841a0720f03034884110004050055443c0032030341101440024419001041c100e0810507440b000009182d1520b0a000403a2580680608042800e0030394070b880d1000340391000e800a40d0b5242d5840100310040060841402c0c0011185000603000b1900e41ca40401c1580e001d4440301248408128500f020340c40707000c070604465001412103070707607504a42015150700c01d20b690890100f41c01c40c105080482c0149459441080041d0160034613240190044455500082c001c840c12460f081070781c80410424441b40440f0703800c0351503441c1d8550920107081c2880e50742d0705164034148000c004100c0e0315100403481050b00703136100e1209525525503180080c00c1205c4d21524140040c501242c201c8a5407040e0481d0b003004c0c4003515850980d0f210132550301c0d00d0740303c00880070f03425602c24490780c4014203165008251801c42d901c0d28030b84068464100d20241da08030141001a941c45810b030f6030301d4001d144503125002c4100c2c18500d21702880c50b540c15150b0240805506000c9a0780c90b001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 674092113 1250 674090863 674090897
    0x103020a1508150f030f03071b0f050f0d12030504021201090c090207031707091d13020d0c050a0b03060310061215062d05030706020a0809040e030a05181c0201 70
    0x500c6113400805070b6500c11016825039542c2c0d00280c10550b286075100c6505c1940364488002030090364a03d5060090a9050409000d04030301c02c0501c0c0c6421107501100c41000c1540b1420f640008900b80e46e0200da40e090600400040642e011000c2103940d04d001c14020000c1c03080c1480c1c2c011989d400e1805030311013420b420103580c5c40360011036a900c0320101200b08a101d40d80900c090082d14109124000080c0b1501002d980c0c1b80c0040b110707010503040c080c24104c0035182090030407014038480c0c0ba014a28546540c01301c6c040829075071201c0e41d0714501100340208c6140c00e000303100da07400d112030b4100209464141203041699014034062320f80640c0445001c40000e1700c0e080076001e40aa0610700e001944207101c640700c10888000c000340762004481021400e8500171410b6412241c642c0d000300b00d440c8242c0c0742c98146034861501c032603110340c0d41d840700000900c090010b00f1103101d0b00d4507100e840f881c2c054a82207084541010407881580c2c040d43c00c0070b50340d01d03083c43d117158030b5028a40140202018815 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 674093363 1250 674092113 674092129
    0x150e21040302120607110a0c0324020a05180f0916090b0310170d0f14040f030605091c080106030c03021608090117010b0724050c030103020a150815 65
    0x10f500301011500100c00c9400c00075169000340501d82d6258a0048010b441c0781c0c070760390401301c010086000c8902c100007040c903030120700381e0342c1c020700341c031034210300c014900403803c07a44601c68500100c0c40c082402d92544200c011900c041040585515485100110024001d2100145010551032040400d80c501d41d2080318040040c29005c2c3c00c0c40e54904008280b411158607600c680d20940040d0660744680007400f10b24918040c01076241d008503143d084800740c444a11045d07140368162420b20001501c240702a010100460141c00006104e00f8060310031410801c1c40d00f01e001036946014620442c4a5000c82d0403411036555160004603404038590803006841034200c06400c1c1c000c25000602400300b0381004004120090301e806081540d0142100300003242442801c0c0c541209025000101e650042000040880303400800c500c000050800d4007100c00580340207611304c801100500850030300707000e4600075081501909441e2804018014a2500e008040c01c3d040d4581b060080041e0301d5850b4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 674094613 1250 674093363 674093369
    0x613150b1c0c0c0b0c0c0706050f07060f021b0312150d050a110a0f0602060103080a03060e0103080705120906090d112d040b010210020a02070b040b07150e2104 70
    0x7030910071030403940070003800200900d000307607440030b01c0d0303000300e0b040e1004402103411040c1e030701c0041e2624528080042d54590081100201c102d41c040241c0000100d1510070030100c0501c0c17840c01031b03c9044910aa00d28400140c0c1442d500f070740100030900c0e911260390b02042e80021081807545214a135030012036a849000040101580300d04071011080100d4400c807078810316002c2d140c2030140c0d55201700905003070131584500005030708000014000b00e1000001048442d0241c2000728000c0c0d07607500c0c40c440c070510990080d030380d544010540c502049010303c120f4084008901500c0d082052290015410b4882c00000718410040d1494030303001c100d0110303840705481360004c01808901c0490741503411b02c0001411004416140403031a0b0f200c628013407040d06440c1d201a401081c250140381c0c50340300254005200ca5042d4480e5100000b118000100204050030142c160079440760ed0170b00d044440381c0c42020100480301d013010041c9108820016468018140d1880e86000000c0140e0744082c45100c2c0d50 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 674095863 1250 674094613 674094667
    0xb210c0a120b3d08270f0313091a090f0a060306020d140108060708070c0302070509180606041116020402040b03040302030304210c080901021e060613150b 68
    0x40c0310340030507030320b643c09120009422500c0002d00c80f5040342c02c450111085034580780d07215081d03004825080e110b2180450030b0841000316045800751000191868004000542c042181884107000e45005409a0307001811200e10406210b00008002450720300000c2099040c4410710002541a00168000d48001c6130024011542d54461066040c0503004a10b004d070110340703201000140c44140014080d100345080c0e03480e5451030302c40c2c0404580000800c202a4114818024049000e944030065140501c51008150f01c0390b040c00d05070b06041080c0140824840c2c0c7c41c02c540c040a0509200854001c2c0c1722000380504080c40342e1002a00a004d00c1d00018030749040401080200758001000307501541c061301e120a0b40340e0304016480710424a030719100000805203083d000005e00c00c2e001912030403005005a030b40008580c449401000f00c0400b4210041d44024240825414601c0a02c516070322107000c24840318241c00c0c58030b00550814801c0442d41c540003e4a1280180545e01000c8442d02c26 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 674097113 1250 674095863 674095909
    0x11103042301210f060b091020060907090e0f0d11010e1923120d1803021510050d0b0702151305120304050a02090c040b210c0a120b 58
    0xc0b00140c0020071034084e0b409051071400401240c0c0000c040b0079105405401000c58281d0b401c41001209d48903080c841d00f030410440751000901c940790600c05244100480001018160720f021403442c26100c28583c5602c103900031400107205940c010806000c03404050420804601d0400d04c020300510103120b00c1480c0c0e0081c44809001a8058984601040e01407280c9550080c0b24222500b100381806c00c480c0c1c0c49a000000402140030f240019080071460300000181d803c007007441604c04421011400c40040c0c0010b00b07206401482c040c1d269030801a40306420b01a20705000c04940794140034280640303607422203000660114400c03c0a060000e2604111641508020514a0742c078404a00d048516014180c0011080300c420000e0f40c1c4115084401420340c030341217400f401180400035000088503101008003080c1d000c0c0c4400180310325091105800b0300088144143c8a694002420104030a02c1c100700d2048540d42c01800c800385010740726000907050211703000042c0703c02604004040040d400c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 674098363 1250 674097113 674097167
    0x30f180c0f1f020f0c0a0807031103071a031e09070509100f080d17061c060f0e030a090e0f010b0307030209040c030606030c0e03100903050d09050a02011103042301 72
    0x800300f10071004031301450456003c01001400c204082000380a11034291344640740800c0802d6130b02d0310f05800c0c11405000e84282c0ca40720f1400401e40d1000122011421400206028410003400e0924080d0078080c40030388504e007403918550707403a9640391050b80d110740a02004645100c556441c40401008804105003105980c4c4c9841c076100c444000a01000c00c2c4030b404158210010a20050310039207008200030600c1c0c0400c5040d00c0361103402501a602c1981c0c852203903031040c055114400380007420000850f115582c4140003040d40500750011b407005410101800f0f10f94840c121450706503491030001a8403a86c80300801c400034000e40107410380c0a818031b80f01c1c0101b9070b096408001078840e103a40c188842d0b0310780c00d07007a03542d104003c00c1e031034040d8480c140e01841c114942c0c0c81101014800d04d40146002d04840c03421050700d400703000641d83d030742041c1c0780038045680102502880d83d100002031410a441c02c5040e0442c021840039030a1b007180c80c1645092180e1181c0c55900441012030705c40e00c12010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 674099613 1250 674098363 674098367
    0x105040c021615080f160f02030d05150a050a08060402091f0603201303030516080d0b0405090d050a032a0806010e0d020f04020702041b05030f180c0f1f 67
    0x3e141d040c1801300b40784030080341c5015081e0003120300c1015402d040340105041d4078000c40e401110f0030b960f002180030900c001030300c108190080502861924501801c4400d00c002000703440085c681c40644506140700041103504070200b80b4070752007601102d1900170f650faaa0120322100c007810140070126100b10601040d403503010b5204124000350b0501050010b1880d1028088521580180b0b81c141c4a600e4801c2000911581c010440203100b6070146040e10411350b20030005400034011000340c5921424080781c42c0c2014070501c2d03400640040207004076401d098019200b403042d10741c20000c054a680d19407241400503100007400001301046070301034103180c81e4002c0082c3c0003a1a0303507002502c01c0e501c441507464200300148001d900105100200d08040007004000c1d40311180890300185c442034140808000c01600b4002c44565072900c1d03030741c2d191a00070441c2d0404020a100c0003103083c8104c480b10f400d07000a40f104107060580700c05141c2003440000410f2a03801c004030b4030807140d500e01e94540d42d907 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 674100719 1106 674099613 674099639
    0x90c090c0c030409020d0b010e061602030304032411190e150f03070f031a010e030c03010c0e030717061306020f04030f030806180105040c0216 63
    0x84000d2070141990080e070f00010500b6800310310f0450403031242c0210b001c0707103109103041c1101800400c0000c10b070380900748421002e403501007032890440d201001260080c68001c000843c08040d00c9031032082d0309a4101c01885e4007402c200a4460280510041d41c0c40c00c0c50501d800d00200d4030f02001119459180090254490005000c4d03841d41034074540100b80f20010305a029680b031402000242c0040700e040c10b00001c05182c142c0301060710f1b042540c4c141c1c0c070741400d21300044803807161400245001c480904155040d444c281b14100d80980000000c140174400741d050300c190b603945090f6000c0103194442e03002c0c6113401880000f0210314250f010300420503c92000141001d18007801c003507490b08141c0040f2486110341d07062109264000302074950040c81102c0d1900c83c09070300d86000031607a07018403400b8040c1da1a41c820708407050080c407010b603114921000840482d590b40080c0d03c409 = true := by decide +kernel

theorem cover : BRFrame.Cov 673920863 674100719 := by
  have h0 := BRFrame.cov_init 673920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 673920863 ≤ n) (h2 : n < 674100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
