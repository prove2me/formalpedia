-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2070
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:35:31.456929+00:00
-- url     : https://prove2.me/submissions/16aa0664-e368-479a-b7bb-5557653ed7c5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 372122302 ≤ n < 372302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 372123552 1250 372122302 372122341
    0x5150301090c031509020117100512210a1407050f0105040b1503011a060309070e070c06050c04060e090901180c15080c0313020a09023402130f020909010905 69
    0x250f185c101c0420150340c01204101c2025040c00340b0000903525403030080218080c5400c0660010300c801d40015082c4000111140c0107040e028a00c24100c10848882e202132081d200c0810019400121500030b1440003406401c01030300c03980c207480d00480c3ea00203040c2152400c46054410b41501818001e01d20342c0c071a0540c884890580080c0800705404006400781d841da0403e903030042a000000424022007441008050102c94000c1c0c45141000304000f010b8182100061310030918201c00718007403050351002c0b5421540952500441514a541040700995004020b01403d54a800001000304a4038600510f55072040c140381800c1070908500490b801c21443c00041400b006e4000e0007c0f4070360040560380d2040000001d00e04544051010484d80b41c00c40c2e0240c0c0e85035001040344000185480d940c0c1c52856880c5044007507000c120b48000d0545110340d00040d40144210691510712015034000701c26200c64407401510344036500002c151085000d0748062600f40e9a4410f00c49003402d00c0c041403044 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 372124802 1250 372123552 372123593
    0x31b0302070201050403110609041109010905040b030a0b090312100f050306100306020a0203070b090f15040b07050306060415091505181311040303030e06010b031905150301090c03 79
    0x74190a42d00284c00b9116501000e40040c00c0c0c442c00880702ea4a400c112041c0e254040e0050001407101c6000c0c1a42c0c0d0003504110340400c840341f8022880382041d02c1041455040200240701c85546a00c03000d803080310290101000b400100b01e0a071100043c0c0030740f14043c042c1c150440307411600d4110092070060140d0041440b07a00140c05000c40c0e190740d00c0c2b4190603030b600200010b03a0b0303030f40b10301013a0320f1849070b00c1e801804003401c982046481a0041142043d81640c2c409641401002c0000720000300030403500100041e4170200400c12031031040b0043c5903c81e5029080d5441d040c0c450300240e10348607049425500013141c081040c8401c2c0d00c0301c0035920384600745040c0542410800b14050748207010440f4054095004480084400d0b8070b1600501c481003055005ca0707039519103a080040140c80c2441d040d032810f209030350000481109000c00c40748a03040c48050308403001c4a60b1075580c040c0201030203036040c80c242540d0340b07042a6421b01c1801c1e03144d48540b9078880b645246191001c10f07400c00300706040701c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 372126052 1250 372124802 372124807
    0x90b0a0e280b0303030a0b010905040c081b0c1203060d08040b030414030a0203040b1e130f06020d1715031b03010b0406060503070522030609030e0d05210415031b0302 73
    0x10151000800c0e00c1c6c015816900c045040b01c804801201c02803000d6010341d5201d0704103008080480d030082506ca0103506240b100c2c1e4501403440c40c41940910a81c942132a55903c1103040640c228080404ae640090009000781d002c403200d52201c03801900300f07030014000c94000009220800c200300928504003a09503000c1c41c10300071404406503d03402540304142a54100207081048c800b000e4104102c650120540c09444a102d44032441c00c0c011203004040c50310320a49408a2400c0c000501e500145407540d4030340003c1c1211000d46021503001810904840407401c90641a43d9014000b5040c5071920455035000255544100341c25100034800c018003942c9004000d000f13055006c001c580c1d004826042180e40c68865151a00b685204501403001e03640542c030011081004e5908000d10150017603a0b5007010048500c00c215440c564079000030100da00018800101c10b0300030342540086040d08141c6414030b95070301484191a40540e041000080e96541603030b50b44504004c0b600c48a0312545800c50 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 372127302 1250 372126052 372126071
    0x80a231509090d030905030c10060303090801060b04030809030c030d02060901111c1805011104090c0e0a090e01021b06090d020d0806041e1b0801090e07090b0a0e28 72
    0x5865a03d94101d900802d0b032518076483c2404410000c0b40c0c002041101210506003814099000614107030108800143c108040010500c00500428050b55580301c0414642451550360103085d5109500e05505405001380c0001e440d0b1342401000300740b581c00e4000d440380340780000202c2d08490420354011034842051040d4a5143c900301c03151103d1200f540d5001442098151038a1603070340c03641170000d0181d070070541d143c55181d001c58060b00450f43c0201c028010288640c4003591048085692a50000001e0400b0000344c0d8864009845020307604000501d420f036003640c075a92010300320702c800e0343c0c6921207000c0c41485c180800001e12401d4407840545910440e90800601e040806410f5620454440c0303807801030442d03407c030404c10562003107008001d54101c2c0d8003103d40708501e1031401408548010000508403410b0700520516902207409000da281c240700d0100c2c0203100541046411802d04400032924080c0c1c4120351707018422131072400301400c45c0e00c042c0800312151007007104074907418510b846 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 372128552 1250 372127302 372127321
    0x310050103022d04020d06050603090715030605030c011404051503040b092a030c090115030e070f33170c090f0105090301150f0302011e020706080a231509 68
    0x10f03091490100e84c056510040908600060101500a2540305c40c0000074400e540c40300150780070485000c5002c00880340342c0c2d04820341c101c41c0c40f8802d00e40c06420000c00c44c84998400c8594101c143c3c00040d13413505083d100e0b000303d40300c140c40000250032940000180810b00000c680b40f541c0c03020300c0f9001840c0500c0f0f02c0002191a078850b910341d200145d80c20395102031964003401080b11380c08004d405030f40c5942e03440c4807184501001c030340390310082498101d0700440090003103020416220f034130340340c0f8424030302d0401022003030749440000c28107030078440a41c5c0025003800c8084d00d00660459442c0111056401e80da0f0b0000304c00070386070a98001c3c0c1001810020346400c0300204400e10242071903507d81001c20042409400034410486032000d81c0da4010640904210308401500c3c005c0c4d032409c210208410880941e41190026000580e0203008201300103481a1101588031104450208a5001d043d8022103072465165200184060358010090b04988807023646000d82d40446050300701d42072850b4003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 372129802 1250 372128552 372128629
    0xa02010b01080f150904034b140c0307021206100b0717031f06031a0312042105010c0e010e030114061504030c0f0f1a090d020d02031005010302 63
    0x11305024110700b03400902850b0007012100723440292905050203003080c102c00b40800b124885481740440c0714001028610300003e122584a020050700ca2800c900008031800b000f6812240300456103101c00c2004500585600885005240241005194508051104c6010142c1e2608200009a402c0c41518045555038002216107180462401e9881c0c542100309525880030a4030081c03900f01201c00000d88a40c90780c00800780700e400e440c001c0e00c0103040c03000b019129102c4003108400c9207000e0200b886204170f08081c001e00f00303c00c035091541380030650f40e441382980d02503801000400c0000d44030710303d41d50b00f0603002ca5004d83c00710300070482c0050141e507400c05200f000d000c140c0242098200d82d544548244112000703142c02841031564aa51000017220101c100c0c00303508641c02c1022030015201180c058080b011207991103429040101000c18040c0202c4980c006983c000b00c5903603800c0158405101450303c0c951031201c0415598154010705c00001441841a180305082420606207810052403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 372131052 1250 372129802 372129841
    0x110a020312060f0904050706020606010e030a060507202505090f0403030b030a0b09010b060c190302071508070f020c01090b0c0a081603030f06030b0106180b0a02010b01080f 76
    0x60701a203031100c00100b1041400040095001000807050000b8040005824402c4404aa00712241c6507910300045403c0f0b4805102540c06501000c2a00d0000748540c11050780311105107022030301c9491520700340e0032103003007101c10340e509400071603409001c013104070403c100400030049035410f03680c80c01c1d01040c180c00c40208600b81540d03842e0003040c105031180d0060203a100d402012588a80d2150922030201e00d41921104002d40c030344110f01401e41800303001c0c0d030a9815400701405002d41c401e2303441032150b50800da044045002d00000441d07240d1600c0090312854045581d12803552600000c0a01351100c500d440b6400d5502c004a0360009131380c40044c035010b440c4482689034540b612650302510301810580014950040400c010106052a5502c1008a4080d56060102041095017401150458000900203800000c014000c0c1d40c0292804110030400245021005684000500c6141c008141e0b0b45c006075102d402c0e0000395079100084941003031810051704d910703040449260542492214 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 372132302 1250 372131052 372131077
    0x71e1505090f010f140a050105240712030606120515120f1b15160818030d11010f15031205070c0909061802090408031803160303110a0203 61
    0x891181d41401a80c1c100101d0303000a0000302050611034000d060401c40d0440013085220000d041c9001c68040c06040700ea0180640083c1c07a09001c04030758415461074410b030785810403c1070301d002440000b41809500615500007802c1e80c00c1c0364004090300d090082e1504507038141011302c40307036a2440840104d440400c4544090440c40540014209101e0601040180c001c0da065115000c00c03202e102c0c4500f000840e08581241c00c2c4850603c41070140d607628024000d2030b80001c40002c5c02c0000244213016110300c0c250500084e21000a14024403150b1900028081d030310324600590090203164241c14003440d052000b001100f028401c1041d0610025104240702c0030007203e054001d002b1140e039160031542041c02c03103845100c040c019104003042101c0c0203107004055a00c0302d813a0420140701d01d500605020b003a031140d0300c43d4101500702400d8030aa6504601000c40c40d0132040000f452070010038540c034007001400382000303001c50700e0244d045c0860210821038060480d602000f295401005007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 372133552 1250 372132302 372132311
    0xa020c1c020a0f05060105190e060f0112050a14060f09061009030c06020f12030105010203120603010b0604080a02032428050c07140c1302070501020915071e15 70
    0xa44101d00c2c02c000c04001401c0c040d011180d02c0144400031800d070341030320703070039a400744031404c4150f003d241482c3d861040503400d41c0542d01084981c034004900395901e1a05240000c089000e94058a00312802902c1105015948042e5105074000e82c2d400b0650040048651060700300745900801c014080061a2900c90b074114004a083d0900407034100c00030f5504004034815070707038459801075614540e056001000b441681c00c4545030b042c0207406c0300e042e10010b90141d0f09042d0340f0442c000d0103001c09805c46515548542411166840c0caa02070310086c01d511005003000101d078010b044c104018040710b100c2108052004107282d00100f42c9103a00840200c40f450512400440382041d148040c40002a841e03003005c040c08003c80c84a00034211150150144800110340076403010750342c10f889040e090300240713201c141841c0d049495001e014006e001c0c0001624003810307100000c82c014081850516500380c003044407824002c082191415070030142405451700038090700c407200d00c1150011385c0c00190341c84 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 372134802 1250 372133552 372133603
    0x902190c021906080403080a0501030305091e040e011a09060a26070b0304060e0705010f0c0503070c0e190207030203030a0b190b0a02011107021c02150c060403080a020c 74
    0xc00e044003585100c0345100d10900b9031216402000c600c815076040e80051041030214038804814882d4904030307541a201c00e8a40071183e002d106010f002d0b181c038828402d02c0d610040348140c4850107541c211103242000005c24510502801100c2c00c5000384850003035400008009103030326000c2c01c180544190f12009807003001e0f080c80031880c4051080580d11607001c1c0e074030005041c0f980e80b400f4501561103918103101403812844110381d204c89034485c0c0c07800603074045108049140150310480b08140a030007500c0c5841903d48a8007000c1000780e110b02451755a003000c0284244255201c411092580c0030150719250080c1c130000d549000261040220955441d00c0d00c001d5030392101481e064a903c11507140b8450340c2c400312408280c000004860240d401e2100150060045034222442654020110240b180280c0700c0300c0b800c50210b407401c0303130040c501060b410a0185120701400c4000c0300900204030070300d0240340040c640c000150200480f0340c0141b140228080e004a01c1d040b0101d80d8100d510902d654 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 372136052 1250 372134802 372134809
    0x30d0503040f060e0c040c052119021611030703080d0b0409150f050907030b16051621090b09120705060d0204051806090c1e120402030105010902190c02 67
    0x50480000c1149140144d044407194020800048550088900701318072071038402e042d5458442c0d031740b0f004c80e2003004010640b400381030715010036040300e541c06914824601045620080344c0c000f080c010700124045980ba401c100c0b4211100141880070360240600a01c0c50341c82801c5400b5400203064002d841c0ca080c0c0710b00d52525070142c400380c0c2d000780c22200b14030104003070380004012032046203000600307101c00a01ea41a00080d40001c50703030700a04802a964840703c0c1404503000200450040250801110000c085005030040e03ea034010f2040d01c10700011b150700d0103a08980400300c181440f80b08002005950f0440e01a285062001e64004503440c42002046003810642e410440d4801000b1481c6245031a0030307170162080e0b4000343d5154001040741c200d030800c6a0800c89081e82d01c081c1e18400504003401c1200901003140070a1803c100d03540103d0400000c0360030150315030211008002c104815031400f400340c0f42c01002c80403802c610705880405a041c42d114a072008800f40310362158104119203 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 372137302 1250 372136052 372136073
    0xc050a140706090615050411040303180f0305030301150801060905011d13060e060f0616030c0206030c0a080a150b0a09030803130213050c07061d070f0512010b030d050304 75
    0x20360240c2e00b000000c0844c40d00310b0051000030b840002407100c0c3d0340041054140351040d01040d1100051540c1004e10b140e03000c0ba01c030030584514001c420142c0380c0003c0c00e080c1d0402c41d40c0246200740083d40d181d60514102d158807400d040d00c0c040800c103480c00100111a00004130707070180c6100f840c08035074504401449524441c80550140d401200360141400780ca14150b100c00292010181401050b413214410402141c03d0b0741c0d8159400b0320100504240c20b100d4035060401c40b48281406054040d1030303000a0741540048408070500e54000842c40341301c581c4484034070390200b01148100b00d00c50046521401c60079050244a10456000a98000041c080c241000045078003070a020f40e00e290080005c644200d80c01001c030301810004885243c81032035230040364452403810200c9030070025a0b440c3c01e005040a02124010282d450710110710581c000c1c007003040900002c01d80150060b160905001080208052806030359140c002c1d0051320f9038010402198400c01c501e0510f489031a541041403405 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 372138552 1250 372137302 372137317
    0x5010804080705031c0b0112021801081008061e0603060403020709020f0f070c030b060603041124160b16210608070f05041125050c04060e0105090601030c050a14 71
    0x1044000c01890780f03900c840d0006d400d0300c1420f03030b1488500d14100b00c2c048141d001e1041502c00715140001c180186520604045502c000d1581550014540d2036804506002c01034441519800721104108012002c00440c541c1003401176000300083d180c561002920744003140280d100d4140c00140001d40c01c0ca4a4044e240e042c404038000564131019460503c6c451b950324403048416007403c500040d1145403038412f880c400c5c3d0700307c001c440404412400308a956102d202c4028040380c0700401649040d8204405000b0305040386403840040201c504241c91a50001800e0022144000c1c0c400144540c1c085002c140080b16040d8000d60110031945290240a003504544020300c903e0400050a4071103003504001c1380c6007a1000c00818a080950200a20600d030307054020911403520f2074601254a854aa0524021020b440010920600043c1520b019500034200c80180000600007032a01902180c2c100307109007010481c100d04514043d00030302402c0005410321000e0901e804c0c40b0712880c000c40e0000e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 372139802 1250 372138552 372138577
    0x10504030905100828060806041b0501120c03182406080d0810030203030c030d050f13110a0b0c01060303030b030c0102060402240307050c0d03090803150a03050706020d12060501080408070503 84
    0x10b0352247c11543e80d070f8204540170b0310014424070711100116080c000c1c0c101070300c606070340e03102165200c40407500151074407008135401c0680d690303058404440c1008600c42c90620451000020300e5002c0342141c44814984102918146000d100300700310f420018151809058074101912103540c0c044900400744540d510107501404002245000001c012000b0802c07000c0040c001c00040e203421126107a020070407a1140e8041044e0300c401e1000c5242d0001c17440484074001c0940500981321407145803170b5042f03440c1e030f15416910b44c0400d00c1055010300400142041c11b80091542c020001c0000f5036800f80940081c1c015400d00c00241101103031402c030b42d03c0340707c4003c038115505d01303186400420985c800801d011140c0201c90400080901ca401605542a0170013000d5003140c41d0740c810180182002c100d040c0c2d0000c4500070001c0000d100384681e00080c8140e0300a040c074030030003d201a00400070110f04000c103c0c5492024441d0340e8120010f117401036006000b0b2030710b4400c94640b040c591b01c91500200780 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 372141052 1250 372139802 372139811
    0x305010507020a050d110d030e1f332112020303040b150108010315020927070503041505060d05030d1b020111031521010504030905100828 61
    0xa5142d00010340c84001d0b807040c01200c1614030524000ca410144078142c120a9400100c032205426209420484060000c0402e65044c004913000040040c054091004005510f850b58003190f00c040301d5106814401003116500c040380a4070b96984144405e008400b0b4040191900950307620b001c20b400002c0d00e911410304100b0000d42c58010350b80303810440d0125114000b22001580c3d14404801c00310811074180c442c0801039003107a41d4901044454100c0508107642441411902d03034402d110030784c40b1f07030240ba685040c5600c01d401c80300700d01c0c1008000c030b014460100180301c0040c201103281440040c45501c0041c42d61504030003d04040b035802070203049440b020035032410800060f481044107000645035030400007840c0300142d0990f480000b405080308010f200151000c0e142004124541e04010508410015a94920f4040542071051520f65a6582080008054114640c1000f5000c1152504004103122400800d08030f0000c0040d81c0303004140094041d40b01180120304001d07204c0304814403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 372142302 1250 372141052 372141061
    0x2070303110d0f050c0406080f061c06140901091212060f14030c040b010c030e0a050a032d020901060507021203031602061006090b0304050703060606030525050405040e0703050105 79
    0x80c058080d410382543c2c0d1925000103d15240340308001c40f4116203564071440e005942d118902c41e1210002880260440c2c1480d854604041c8108403c3d010030f84240800144a9000b0304120020f40b002840410240e2400c1408400b05070341400c41001e4003828a80201d04148a00f84079024195035401159030700000c0c1400b00f0f081c0c201518407810120103400f1600010314800800060343c504505c41c1e408280764000300d0001c02d200e4541030100001c090a49030b50b8690b00c0020071641a00f071b500a59a1a50a4104182d000725403003014000f103000c0c05010308986d10b80e40000701038120611502083c8000000c07560704548030846986080343c000c4090302d40740c0ca010400c82c1c074004490040d440060107800b000451241281420b0f605640c81031ba500c8d504541000c95618042c1d00c09041528240b140301da0000000b0803138002c0902400080ea00800c1600700100708040102d100b28607041120a008210344480780d10200f603c044420440380030843e0003451003201e0500304540c00c05001c0394200001c00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 372143552 1250 372142302 372142327
    0x602252409050a27050c0313060b060a03060f0f0b120703200a0e041a101106040c1805040512090607061104140a0e010e040303241806080703060207030311 68
    0x540305414075181401000708130306442d02107801c101d07001d04d41c1c10020700102c0d06518181d107160500c90b1040c0c60000b59664440001250f03034009100d040c00080e1160401d0045c041c158008200600f4501e00b9904800c0c14140c00803034500070320290000d000070110015010604c6900b045088117200c1d0b2441d01c1210b0204600d407029401109102d0100c0e41e10079400d030690400b4850014101c030301440c11011002e0318001c000c03840849004410811600b4211004113450501580d4040ca10428070420594070f440c010000b4034407070b12810301c038241c54801004041440454802c1d00c0a40b9006200c0d55030010000081c0c040c015810054000c81c50328030ba001a00307511000810903282c00c0300c451100c0410b03003403c006001a081c05507400351406800108414240a00840c0d00700d071284c2004500750808418003005c03143e8192205840c481103101c2007095601540346100c0003034a03142d0500000382800c46d465915552884000d11341c9a0000d501001c0c10310950140b2106c918100603039075544500e2000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 372144802 1250 372143552 372143579
    0x50d09021f0c0b060d08120903070212010903030f02030402030a0f05030f120105040b032a012a110102010b0d02010804020d12020a0507061d0112060b040602252409050a 74
    0x711807805103680442d00c03a1a01c0071072440c80301c4c3d0046d001c0b450100500d60340802118050301c2003100e0700c0144070100041c0d40e0440700c48840040035000064007611820001d080c0c4105035642d41c94070380304000340005030301c0c0072441c11a0707160410700078010b544191520514502c81d96000985544003c40c4140c0c40d88482503e1904880e4111418005e9a0342e0808154a5031801002106e0141c000541d20303411000500070380080d204141061032040d40549181c0c452203002c5003016881c400e2134007442040195500c0d140007104420300c000c112500f02c400c0814100c0010b8003010381407000c2000010119558010b045d0300300740c2d0201090148400001001e0f68502c441401164a030080d44804254648588000c2c8041451401e0f800383c100104801507640075018100b40509503100c42c400303d03100e143c0c04010401440d241d402403501c003c101c5401c80550b540d0000001c240d4800f05810040b0700d18010035260503442c880355001c100300000c4416500d0032190380c001504180c0f040400514001003050 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 372146052 1250 372144802 372144827
    0x9030703031a101202090d0303141806012102190806010b07050705040507020312010f06090b07050c0603190606050a09060f080403030c0c06050a150b030403050d09021f 74
    0x9040c000602c805032030340e421000101c2c40c02e03000340c1e0003800b44440511441030306160350310024006103480e0300b520200e618510070b00401d60200b600d80d20f03103400d02401c6e01c441c694045803440e611800030000052540d00c8080620a40604128a04803941c8240c0065000c0b021300d540201019070000300900301d2130f05c4c9945840340c00150700a02000081e4a0440c03021030b5107659020028082ca50304103010400184006400700c011444144220346100c070385010050b0107480010703592600c49190100092542e44a0f03008024070880a20451000420020b00380034a0744c401c60340203031a99140d0820301c00740d01d00e10140800160510a00084154001c00249003840440d0b99026205031030b41e4080c0c44106040410703a000500d40d05c00200400e01c680c0c02007031054468985030002ea609501c0310020390740140e50303a01405070b45486544900740030504503001040d00780d41c0c160651501d620301038064041e80050b01c64683e120a40c803011903907650200c2c8002c80c40390825940041e80703400000c01c401d40415 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 372147302 1250 372146052 372146057
    0x504240b030903070f0c030f11102a02120307030309060b04020405010e13060b0a050408010f0e0a0b060402280801060e150f0c06130c050a030812061809030703 70
    0x410200d591440c04040364030030307804803000790b150152030b40d0f840d020010800070548501100304808170010302c90715018032043d0701074104502401083d42c01c21050f1039641e10003005014981625040310704030304100014041003141ca6a50303944281c000724914a014081208460100040c0c000c00c1680540c0141407450280f8000c02001c0c400205100480c8114001d140c04a6007408100a051421020340d03030211601000c0404e5156070341c0c1036a4101c4c0c00c00c090980100310302280500034590b00340306501450310384450500656011406c29512100c0c1c4c0000544288603450000d070454907690110703001507040d50440d10002e110300c042216241c0390b28080c100043c0b40403000250f0103116101120a4020040c8503182241213004441480c0e13010001801c680e1f1400d0094801041050220900c03419141003507034051805803030030494060150300582e200d0009480c003800419192802d40e0440381c096006001e00351912400a0310b00b403035030b0404111080740082005020000440a042c06a2094 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 372148552 1250 372147302 372147371
    0xc0d02030d0f0207020a0e1302130b0114030f010e040c050a090b090a0b090c0706180804030b1803071101050c0109060e0f01110f03100305070303080f0a02030603120a090504 76
    0x108807032080c0d126003c4017075400b40c0105000e03c101aa00c40034103070030824444030300e680c080c80c41d404507203120001c403900101159501c00d814810350700908644500c1003910901071441c941010785011120b018064400d5001600b03001030100031054601c030010303010081404400030b60300c1c203000c005030441c401094052181c05010881d1a0007134007484007501c00080c54074140c0c0d83c4550f00c0c2d880729000118240c4a550300c0d0581e441c10541040301f42e10405014504050b921070071810a003101c1c05000e008102e86200050144102c1c190120917981c407203a12880d0010100d04100049403d80030341044103409510304030700c003002c10440c2e5010102401c2408156152280d280c4180d600300c2d01040003142400c0700410462080a201d04001c6510000368840081d0391030701c07615101e00e420720701e0700200c01103013681085c40255000341d005141e1022000c1015459440c002001ca61039601c13026400c031040c60089811400d060003240000302815001d0020401c1482540c2e802c61503034501488519585403a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 372149802 1250 372148552 372148571
    0x20f03030a060f121a0601050913090b070503041101120e0303090705100201061805060406030c060806010e0904030f080a0b100c1a070c0809031912080c0a090e0a020c0d02030d 77
    0x4d5218015501d400c010420b08041615035002d400b410010082d0741000410080004150b844000e990040e5000940010310b030100c0b841d2124200d500a00b19405101c021f000b044001040d9203003c2140c1d030402c0c89e005861070460301440700500b15035142c04031140804410001075007800108501282e0003210741329000d134903400c004d0f030882c5c0280c050f001d80e125030000c1e00f4000c0f0111f03400c4642c200300090000100d0702d03526110600300e44c0c0315402000001c3d540c01c0510245681c0001829912042200d07146c140341003d59000e07107494010050070080c444d5040018030000c0c55a4461681044090100800c8201e41c00c0b00070b02c5136810300b5040311f00c0c40b010440351924000c103003001c612a001030348a80c0722601d8030761540301540e0050300541e98944200444164000c02d40118160075030301c0b1b90028100c20307031560780c05085c0c480e009110030b80c080418040208400d40c020b0b0804200d40daa46944030180d101d030001c5401a20507100004524854140b0329905c031a030000007026410340481080104649 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 372151052 1250 372149802 372149819
    0x207020303090402180a15020304140a030b0f0f1b0703081008060117010e01020c071e231c0b0c0c010e0d2601050102030a050307120509030d1d0303070f020f03030a060f 74
    0x180e1fa0041e00581c0f040c8018006404a80076003250040010004240665a0b680f40045140102c542000d20401c0e40d003840840c00c0140e01c42d94224402070082e90203c0c0d2421b00091103030080f0f1001404101750789010503004400703004000060070941060f9251981c40740030540c849400d4240d029400d40c609070003040d4100040c400c3d601c0400d007900290001519094042c0c207070b1011090b848101e5003200b40300003410348280c815413606034503031110204003420040c100a40f42c3d00c0708980303443c0c010480980c000013521054516178020540c1c0c4446460744480708500e0300410300719001000360b10078010619200e0750010300f00110f0820011000c001e4150560b1004a40082841803a01590050004105060142d005540c1c0441240713070000900030080c0701c150581d0340c140c905058503080055811000c54441c002e03940c00304035070b180c50b802c14012540d9444c0d4a10004016100300140c03806080b4043d0700c00c2c003061041c0d80341c40c42225143d05045001e80c2c010142840341c400088010040010300c81c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 372152302 1250 372151052 372151079
    0x30e010c14160512033a0c0e010e030d0806151309090203060709060206040807210c120c0c03110303040339150305180102040b210f04060207020303090402180a 70
    0x891649848a850a41c040407041d0001b10107494180880b040003003902e22200d104118808600b6a1aa848406a070002420500500d107100e03000c0d42003101d01c441305507000000c260f0084401c1c0c50161411003800c3c0c08100d02d014040200310300300c2450b20001240686500700010030750084060740d01585480d03205817040718451003040c0142c1c11400005003c41e00a20162100754011148602c140c100041d012070a49004409540482e800c00c01d40020b00090306485441c42c082418007008070308050301c44140100c03451100410250948021780f4451f1024019980250717807211014010b0316507900d40d001010840b030001c0e249a00480318002d0410100c240c03440807545200518030401b004408128080c000003400c5030309091301900c90101da00403d02c01071004002c181d900301d85880c0c0c4681201164100d0411034021549503400740002010030300200390300300d90720200050b5141590300c0482c0c103500aa09a1a50040c030200741201002086000308620a200f02c40b0242c0700b07612050005002e5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 372153552 1250 372152302 372152317
    0x2031807050a12020303131203111204090f0f141803030c070f020a08030406031d01020a2705090406090b311b060509010f0903030e010c1416051203 65
    0x8208800304020014078242d660345001e0001c0e082c6c80c07a15001098102003074201c0e900900d0031100a59405003030550055030340c00c4503100d00014201031841c2032070781031090007203020b12600d0703075030350715028500c00c1e4103602420450120202c01d0000d03850090406103880c004407072002c1490301da4507010409810100840740700b2030760200c25504003140c0c3d032164044100c4c0044202c0c1c0144500340d001c645240c0810180000300041e0307078003007000214003111400841703044140c200c0c00d030b005000e401c440343d4000440354040181e10b00c0e040c010104a80001e0030040c0c5075030010390003521100c20702c0305202c1c0c2c60f04554106805120038502645803160a42d007841510b0300018121404840c80c81e03459040e145e01070415034080c1c00b890072481c0c030b0044500c0042c05074ce0700c110042680000e0390341da503581201c40c1418071103180c1001840780d840e68401030409014044180d04000e80320658004001d01c050611310703100908022502901c00e2410320b50740903c1e590181030700c01d80c0e240002074281c81001080710341c3c1c03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 372154802 1250 372153552 372153559
    0x5090705010228080c031605030306040b0406080c040225060b01030606020a23011e020306100810090c050c010e0708100225030509030d0806010905180f0423010203180705 75
    0x102615207800051790000d0710141d0150100300043d00d24040c100d00f400c0000c0303000f20051580ca0500303008000c220b40701041c41d14056414030900704050500898410720709102075402613a50a154203c1003031903450b90f070354080001c0da581c803000140441944102c0c01e281d400c1c0ca0420006445241c1030780e440b4103c03a40144907240c00100303420342454103000e5140c1443d8580010514086845520241000784549140b08139800710402c400c91030000c8070342d140b00410f0f045c00b4455090034074080191414502540c0b00c02c1d600c0e400c8200100d84200704507154012554002c110272040340c48403d0725a850f030310401844e40705c4c2202000001c8014401c50300405594850104942c42c9001200c089801c00b080c1903081c000144075184041c4c40c180a00b01e60f05403959078103186031910b500090000c007255044940140d24081c0c16130b20505510110301d0300900340b50b01c080315565480c03030408800c211030742c8012600c1c40011303410a4107800540246020300c1801551100c2c1802c242c59003a80c40c2c00798030480d80e1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 372156052 1250 372154802 372154873
    0xc060c05010c0e0310150b0406080406140403020a0b0402030c101808190209131e030f02161202031e0d020105061801050105071703010303050a030b10020628050907050102 75
    0x4080c119031b407102801c946060300c04090075a44c1d0514014681141d4010000b1894200c1040200314003840340c0141c0740c80444184045007000e40b0000c0d564803548800a005152030000314040d942c04003d04895100024000b102100d4486801040d400038100d03111904190360201003080d44000c158034818a00a407030126650400303400300040d89101078003c4021030003011110001c188010b14a40c192141e0300000406000107140c0100078402c840c14500441d008840c0702d500990015006004560707407403440082c00d800d540006800c16406c40c240c1d404c0c01c400c401c22005040004290340001e00b03100c1c1c000f04410703603401e802c0c03108907040011341ca2801440040140500d40c011406000054052400245004c40710a07144081d0340c000e8100b9404035001045401d4020b5050140d690b074040d0a17a011180340b4452140030390b4964000e880c18203089900702044802c4d04a0000245c2110700100c002e001c50b0902c40038298484a45020342401070080c0e00c1115101102c402d0710251004201e9000034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 372157302 1250 372156052 372156073
    0x51503120d0204050d080901080c0304020a090b120f011a0307030c300f0605070509030a02010311220f0b04081f020c0a0c050901050f0a120f0c060c05010c0e03 70
    0x3590012580303111190b420300003c242502c4800d072104005100c2c11956a540c0140b000145c01d1000c01451480b01c5c010410400005031116203801084405035100441c1c15180e0000103011030104040d10a500d11a201024540607815040b40198240c1d04840c5140c450302581450341300c00450201a00745011846e0802c21812044421107038009030808000c1c85281c0c808442d506503280318001d440c410904030030001400380394801d0541141c0340c1d0400628000d04040400e84880c20000c0c042c0c14107968074941c107940001c03070040b100130707009070402c10f8039403080c03050150f220b0015405070b990b13001c00c10540499024007030002c41c6e05442801b001411800c180b03980c1401070091004d89418290780901641001c4a8104603010805d8410042185d80c6410442401400f00301684085d10031400c40340380090a40b030b10750881c41901d134400704c40c090380c801d1801e0020030f00d07001c1c4000400d0b401060100140c5140e000c07040b003c60718440d1009018407181c0e198121031003188441e202c0d0f81604400d4041 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 372158552 1250 372157302 372157333
    0xf030a0b06120a0f051501060c0510050403021002040308070c0605030c0706091a04060209031b01141b03040b0d0516090b03061504090c0201110a050417010b03061603051503 76
    0x141d800c80006402c6030b1514003079503107000d41064031324021039a81e44610048601c0241e24511140940303842e28000d440c428250710759580e200c032005103864095981d100410300313041c0b00740800c800c0310440440c01d5548543d603142c98881035108140641d11080c2c1d900002c1200c40c820710450b8000c041c1c607482c0c00e0400c0190b894500042020990031a5070b0144010707480c50074000c2004003031140b40152030058030b8042034010b040c01c1c0f1309001003040021031800d002d8401a078005030104464130002e40203e4613a08103035110054074418104c144901c0c4400b090006040030410002c140d10200b0003028012910350440c0060449422411207020990100c41403040b41c0f81d080107180e0055005060000009640700904043e0f807141e084081601c2e1507540c0c4c1807000d038090181515501042c0242072402c0450280201580160b000d04c81001c005c5c1c0000705a020703000d40044003004001019201c00b0308115203208a8040410130240c0400c1c281030014028280641a000c2c02c40c5011f00641402d040c20b2800 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 372159802 1250 372158552 372158569
    0x20f12090705090a0504020405090708071a04050d060b1c0b040204020a0219060c0e0901140906010c050102042309150603130b0f0a14100501030207020406030b150f030a0b06 76
    0x41203424801c00300006030550f9000243c40c0039241c00040000d0b00c1c02d240c014002528001406041c49502290080100100014029040794210b00e01a081d2070030005004141c0d00c2141d000c80d80c0034002c2c00d000424020664000c03140440b00b04d82c6041c00800c0d5114011403100001070107401580203000040140c10543c005007079295162060341c0048080100c10001005508000e07503801d030755a03004c601c1c115045010031004980464405207950314141c104c1e10344155010b002c5000e0601d25001c04d803241d000d400b0403195a42d000c0020340d151521201c44003040f0380007080070040e811286000040604245c2c41850040100c1c0c02a000d41c800380c1000d001003903001030600500c0c1440b009041e070200c2c88058609000d540d0f07104e541340c09410311001807000e0b900d406003240c2500c0e0103541845804c10558400740215502800c0140e00c40d5080e00019005249a074400741c80410840100007400701c07840b104800c008000c8803c0d0203008030340002d02d80c0c0c07400d01d404003c01c141034800101c0e03800d1818200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 372161052 1250 372159802 372159811
    0xe0a0323340302090f0105090a0e03091c0b1609050d020108070311090303040e1503060121051507050a030c080603030901050c0a052d0c01080a020307020c06161104020f12 75
    0x1070030030780d254041440040d04440d1a42e11000000050203d858203810090700840d03103040600445001800564070391044440003413086400400d1110007424a10100031519005180e94809107005d00380c081c00c00803075911010008001c5132010070145880d10003008840e0301a5510201aa41c46206500400a020980041c00d50a00650400740d90420091025010166881c3c8040c2000a0503801050044040610a03004400144140c403880d042c0c0d00d0700010358003d900c6c9602c5050419604202040c1c170030b800c40e07000400130010841e070004010304d0000d41950b0208140544980110b540104c241e401d40d500d90010003003056950310075006841c103510b1503002d40f5008619990780c585407000c40305025051611020203ca0101c007500c1d805444500240041c3c10581c0d15040000e05043c0010001f840c40c5e5801300100d00c41a1003000030702804103000c2c0401c0c2c0d8078924041c20440c0e85221910840c1e04800501c0c0d01101c9040600988600c407842004007400c000d071607102030441920007003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 372162302 1250 372161052 372161143
    0x90307030c150305130b0403140f03040b0f090109050d0309030201020f04060201230717071e0908010c0e0d0201050c0a06110304060b030a02090c09010e0a0323 70
    0x22022034014440c040040046040e540c44410b910080581603440051103c11039841c5000c0b05d1006c1281c0c0c801c40c56000381e051400b50b00781c42c5207a540c51118026610204c03102c4001000300810400030001c0d09004411942c3d8001c282d03541d44000380d0036500d080c40d00902a0300071603440903049000f504840c0c9030314400e0002600f00b0481d1403401039940c00c00e502c4240183e440341c1a000017800050042c0001545410940009182804002c0c0902041d0360030401c00400703079070000d1111031003801e0b8141c0304100103984803400d181d0008028076005907030045081030351800345030b20001c2d400740d070002940c440c02401d10384a100007034005440b550464150342d4101d0190000c41303000030f8000c0c821244610685900140c8178105030030010b0440b44002d85a0380203a001d42078160162391141090b541c81180c0342c3da01c80c1d07a803003508012102018022082908105240780100402c4002c500130b9409402030815101e12190401740c1b142d48561190091108a4410001801c60180c0c0e1404142d0f400b80744 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 372163552 1250 372162302 372162313
    0x140c0d1b0305030d0f050601050c15040305040e040c0e070c0c14150c030309070f23040b04140a0513030c0807171b070f0b090402090307090c231309020903 68
    0xa40b00c1c0c03410b41c0c0c425104901d503166030b54402d03131605085125031500002d003032030302c0ba04020f0403010255440072407000504150310071200040415118104a40c054508140b0112180c1403900d420b50204c005030260521041a03940001c07411841001e1920321030ba04940444103243c603191440c015018128803403034116200c3c2c40050400f85000c0d0043c0010004d45c1c00441c2e903031401d144910b042c100150444403c24080c45420480c0011074a841404161540f1518405032508000900106002d01c00c4503006428203d000700005500a101d0b0f10a01201c01c0520155480305075401c07605464480080101f0107115201020502117400f4200f501e100d00034078448035a1503e400c0600f500721400c00800c000381841803071850310040c4126002405405001d407103c6040484c8000c3c90b000d4000340e14011a0302085903c100c1d5010410700c40242308004c0100102186000c004007a141015242c0d600c1012030402c0c5142103095904540e12510a0190a04050301300f450180180d8081d00d450350703052040d03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 372164802 1250 372163552 372163559
    0xe0705061e0a021e0114012105011e06090b06030c0c01021335070501050702181e010609080a030e030a0b07050409060e04050304050904020607061107140c0d1b 70
    0x10003004000c915403540091450035100707104da10032680704010700302140e41088404100d0500c568500f9043d0b034a540c21042c074066010380308490306680240050309640c2003659408040045002035034804200301c005004043e10760b80c55000f9502d5000010360012410400208584910005410001140800546000403030342c00800786a03610341040366952980c2c0200995082d400c0950000f204280c89010035818042040079200c64080c41118180880007804400b10358807401111290441c4202c0710040781018040010303001c07156814042203624800021484600400d00c0104480101c1d0007482e024880350381c100e81490300201d400d43c0522407d5900c100041007100c1241c45050703d60340c0c0310307195480d01c0303a180c040e1500c5500804140d9442c13028040851400701c211030a80b10140c4039030056407585e1005c60b0703c41c802c03036070041e110500c2c00300403c1940007250300a100e03d5014141c03601d2294420b00030700703444051124a03c2d84c4064514490000101d42c55041403d0802240c02d000b0019078 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 372166052 1250 372164802 372164857
    0x3050606120403022a0907051e0c010506040c021c1b050d0c0203100b210708060405010204050301060f05130507020705040f0e060f1b03100b1605100e070506 69
    0x20700362011000b603088805c030400004207564139000001a0b4800d020b0500030850b0120301c0c151005002c0d4020082d00240002c2c031052103400c881409050600c1d00c641d620454aa218020641940d040b40f1550030f208207084076504c00a04030074500c4106000c29a05d680c401703800e50760042c8030b00416242c0c1c912442d50402080e4180002d1071003138100d4032811202c0c0540d01c1010304114940b5035444180e403820343c03400075684401c101c080001801d94024100d650158185031724206a80c0c0c0049554400c0d00e007080201312040d00035008403a01a4001e000300b644400c10702c1c20b039104602031160400140504c20314000d41a8200c0c941100070341c015540802d031103002040698100c000d00782c80301c9484502d1724455200c200309455000f0740da146081094100021044543c400c449402242c6000100109810701d2106200400800c050340c2c2e00c641e90b003030340304040c0c03000e070b8070104240c5960160400f561301c2c0318007501564a00c0750722080a0180d45040030204400e0f42c022000308101c0d0300d21034510441301340 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 372167302 1250 372166052 372166087
    0xf0602041805090319050c010213291e0d06051c170702030c09040501150f03031d150f090a0803131e09050c07021306060201060503070b070303050606 66
    0x7800321034804018064010040c19101c0142c040c0320540c0c020801d90f044904620b01c01028a411482c10583e128460102107000e030003106400c11015001100029610344500d86400110320300e04502090705079500248801805000e1071250604211449080000403c2000300310355040c0002c00900240c0f15000f084465010545c5080803006188010061112420942c08404244502e40b882c10300d059011070b460f44452028240503198075800300d41040001c1d013025000400075114903c0069444002c00ba500d00350344816404114041c40e8280d00288500020307000100c0502a5401c82d203001c0e0001c0501d078041d1140112038402801404a0f660799000d8030002820100011502d4820340511501e10002640c000c02040d4038814244035905800d03500c45040304c94507036000510b5070300c00c1d001c1c000600c03900c04004e40c00507180300cac4614409001e0f400f5100341d402c641d008201250b1140241581c0d00180d000708400020280700a10020307209420075a071010028040600384880c83c00c820440b032 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 372168552 1250 372167302 372167309
    0x120f12022103040503070b1003080711270105011d04020f0903010b031f050c041d010303030e030c0601151e02030d0b090610030c030b031504110402040b040902070f060204 75
    0x5030464900310810301900070140c500c900795010980d14605250351015501c0c490032500500c2503581c0c1d4000b40600441003160f000840c1c0108005980f528186413215203503050b9042d07944560f500036001c08001c954030180d4140502c460103048181d0342401c0065400180d610000030f0101803042800c01e081d195400501108081d107180c054403990040105820f41c6d03051441c450007980000e440044a032041c241c2c002810222100c0042c5644076500258050300c5140c00c400451100c1007038050160040314a028102d9010ba41c080106082c12420a074684c82000300450b510f5000e40014451002540001d1520a0660801170110344411443d40b43d208806110000035810104020007954031a001c2d4001c003070f4084828461600c3c1030800140b48a000c4682d540802d56103102a0360041c1c040d03030000384404001030444811803c0c8901c4041203500c1218112002ea01300400003800c2e09090080d901035a014001450030703c2d007030802070320080d0058201640d074001001c4049021440c6d41c801400503 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 372169802 1250 372168552 372168557
    0xa0e1908040906060503070c061a0a1205010510050102030a08100e010806010303030507050403120e0d0605090a21080402011409041109100f05031306023c07020109120f12 75
    0x4440c07030900d442d401c0b2005948200184241041041071a5030700035a40420558020300c002042c010480c0011403203603410303103190380000e448540810484071300e504401005229100134003076551740001c6586004030078450240540e000784a4500c3d514016415035511081201c1c103c0030035642d031a002c0100d410700380d0003003942c2e8001c40014410f166140c043c240c1d00c9002030070709500e42403a43d0740e2641d40400a000510411105c014004100e50301c4160b0481000e410220a1095081001c100e0780c51b110f0b09030f0f04481c140f000040d45959045100c61000c0d0840140d225060345640340d40040d242800e0b5070040b0191140c04001414a0365124030510040344040f540441c0c58040c1041803200360340c40c40c405101801090302018800701e91040460b54042d0215001051000c1146403d4001e4020b01e83c6156030501c01a01400d00c1c0403503040300c1140042403001c482c403500d00d204244035140c0b280c0b51002c4e002400109041c031110f200118445c20303281c456185502d801146d5190300c41c0c041410b41301ca600 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 372171052 1250 372169802 372169807
    0x3030a020c1006050a0302062809060909200f1908060a06111b0d060906020a020105072307030509040c030903080610092907050619060303080a0e1908 66
    0x201c07000c20065030a00401600301004103504001c00510510010b2200a21408001501559041b003601604021144488500421205006018040c00307414061031002412a181c0042c0c6407a1b2405441c0e11218500703e10610703c0904000110203601c10280011242030421031026005194172414002407041d0f0798000d8141080010031010f00c0e410342c418410003c000542c0d9145e1200800c00800c43c442d4150241c40e068840d90108400d042c07480303000780026241035880c80a01c5680d40061801c1c0303030194020401503503544010b980794041c3c2d81103d94900c22403940c3d04002400f070001072500600a0504c14105410440010151040d80141034006921152908205a0401c0c00960845400c0f0791062034902f51040061000c200c600c0340c0051a6511020030742c500e90b0304003041581c1e5000040166540a03142403481d038400c0d00303480407031500c440340d1385901d115006403003050700703030790b807581c1d818515440e80c50031400905200000b44c61a402000845001d807241e00c004465a107110316a030a4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 372172302 1250 372171052 372171067
    0x23060a020903010501090501080d110f0d02010e07060309030c080a0c0b010801020a030e060c09090c0c0d110c0a0302130b190f060815030c01051e0a05042d140d0503030a02 75
    0x1402d403581a1b10440c5000e05150041c070100c040840e40780c0501c00d00745002d022286a0110322440c081d07040420390014003a0744038501400e54107410201d101b0f1100c400302c9100a40d501c1c0214201d4140801c090000740140349401c0018203000300a0994109514109460986545a481103d4001ea10951040c0e50004075041d00035014068418813103a0100941003519000c650ba8201b4440c1d001c07001d116100d5500007541d402d4003907090b40d02e10320420089501092052101030400c0403030400042d1540700c3ca003495041c5140402c3d0410130380307902070300d80780205e04003103150301c040c06805a80c03e5001d4041d003844c017480c1c0841022171004040110001d5100c515159010b01003040c040c08a1031300c0c800181c801c007250785000505130642202032a0841d80c52a03d04901c000707203002012005200e0710000f0380c0c15507445d880b1000e4010780c1c0e50007601c81c418543c041c102a840503070800640ea08010990300c1009100c20540b207001d45603c1c0507004452080701517030b03a242940d008907548008540e0100c0d010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 372173552 1250 372172302 372172309
    0x106030c030f05010b090d020d05031201030b010b1315020c03010f0c0f03020301050604033e0109121a0c04090204121e1e02040902040c2c0d23060a0209 67
    0x2011241d0351904000f070394142035059002e40b007011032081c05483d039400e18130f003103440b0240c01614107600076041c4d0762250058905100549003c3c4000e441c034022003000412001008000c9980304030940d020300c000030f40703040080070007060756040ca14158007440d000c0d00640c1c0c800b800741c0f0900701c0c1012400660301509035800340001d40001c050304109031040c401070101d5200c030000c0b281901d80188d48003e00b250080801c40305208842181c4039082c262a154580c45080f0380c40c4407254070030903214584a962542a081003c400c1d5140280402c2d40f007010114550411842540d08100c1205945241c1500e81c0c8010303003a0392080d8000801c680307a07850b04005112649060802c000714080401b040c2205544402550980540ca05641e070000300400b10110755540d8071401800b5400f61003401a5035015030080c2201951620b075507411403800d1410703070844050583e100d200c07100040032550060410340f2007051010412550f40c6020031000507920055008020262198086e0000542c2d21800c0c01c051 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 372174802 1250 372173552 372173561
    0x70303030c110a060906060b1201050a090b18100807080c09150d03030f0204030c030b04111c0308190203190b0307182d0e060f04031e030f050106030c03 67
    0x1410304200c2d10084581c66100c020a005103001d0308244040b42c1c0e0311150825200501c3c2682c0442c03880b410000c0c541c0c045101d21f00c5994100c4608407092400036603951002d40503507001d0703c0e0442d4018403113850200110404030b2455045441e00c140d68520a8441d0b4015140c506160082c2d010381c5c1c04489110710a142c4500c0655000301c03540c82142040441e040400c0706e151501d1002014191201c16846400f8260b5054038011508101d00141c25550380c104004a003d0a07a2305517641061030440340c0d814108100c0b03195103248854286002c84003030b51011903c0101c0581041820098054071440ca00c0050001e107010344007903800305030703403c21041e450800c540340121181c0c041c3d0080392040204a00c0f002620b0780548041c0c0010542291a00440175404070802c40c4084000070b0717540307000d01c0c3d00b0194080c1c4a041d104030216140c07521070160b0620500002c440040001e11030349402c807540708440d492103a215001b402d0201c1e0b0101c1412000041e104c2c241c00c64000655504410390706254507008 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 372176052 1250 372174802 372174821
    0x302120f1b010c120c06020a05041d16110a020a080c030709091709131e0e1b0d03020f010603050a0314120711070f120210020f0316022107030303 64
    0x1c12541d400c1940001e0210122200050031007100070780100329407402502c1d01c0d00560f42c0090b046540d114003000180443c0c01600920024040740c040f07400f408180c08002d10700880740c0c0c0800b00c0b002c141c00781c1c08440f540704d680705070346142c0034000302c071030058841441e0080a050700d6000351400d04040000c0c5071900d540d40e800721040b01d0901100d000800d84290301c0014621181c0c14035583c40e046000481c400c6000760301403100d920728083c403446882050001c14410180c00078001e021420606030070710f940f035502610b100c130581d070b595082068506c0d010300300002071482401541c48100104100b20700b1075800783d0050740c150300301c401448c08055000c90301c0103000c0e26907488103090440d20760f685100300f103006204d1400d0160500750101081d0080107114014050058404141500c51456414030101c0a03012401940b910f042082e140d40042818501c240d8000021824114001800b0707007443d1020005031b030809400c0142c42500e85440a5880301005040000c001e1180f540ca40241107428501 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 372177302 1250 372176052 372176083
    0x1020307110108041a040308100f05180703060b0703030204031118060d150e0a140606060a1b021c020f01020f07061101181b060c150507090302120f 65
    0x41803400060070801c06981c8840c0030300c2d189110740d4903840e0010080800d00f44030240c0001d01402c0000701036010001d14894400751041c0380c0007650352501c2214100d004c0c003501b680440c00464442444081102c8683e1200e01441d000c138071550348005c080083e6000d408140d0001e50001000d0042c00984c16042e02101000d40f510b254550005401007449040505814819000c40c520f80d0180400018800360400c00a030042003d0390b01c018295564041e0507a00711141151002e103607070000c0000c01d06511072800070f8242c80c501904650301712076400064180003001e164071018200580c031192420340140d007410222205032031090040220b43e100d04000a07045520440e4070601c02240483c50700111059420092245204000f8283c09454881700710800408640c00100030b000114400c3e016000360908000d07003054807a0000c0f00e0720460031001501900d007000000c401c4070a1503010b164404500d107401c40f02c280c1c807035000401d640711514001741107030301c4019859a860380030f111403540c500e4a81c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 372178552 1250 372177302 372177307
    0x20c0304150c11100201090c0f0602060f09190305040e150405060411040603020708040e0408040501080a02040605031302120a200915060901110a0303021e03090c04230903070b06010203 81
    0x90b5500107480b1222800343c0c0c001c008503499040505c0c001d411001b03100398403090125502c0c0d1103005a0204c640700d88111001446854041403031080d1595141c0d0044001c0310140004000310485000800f400280807810010204000039041440c141c0150003a00d603104142c500d00c40d640104400d42d80c01605043c416031401d410001582c04610442e400c8030f40034140581c07100d00c98142511140680d50007410b240f80d0182c03c10007000320101c01401983d00c00d03250b0002035120242c26004900881c05000c02264042010854090280c07081004191000700501d00240c03001c00382c107040c21717a0039104807035403000055034013442800303540442c200c01400e4a40540c2444c024074441c0b001c1c0e2400d049030740580b00014111000b039204000d803a007180c00060072600070f0300807480c000b002540081401c00c1302182c41c41008014010a20440c0e00a608a10090408083d620104002000c038901d442000c001d0408990603d0898001880e2082c550300001d5500d40c0080e0400b8a00b000004080744e0464004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 372179802 1250 372178552 372178577
    0x20f180106090521060f0a0e0114010918030e01142701020f0307020a0311120601150905010c020112050a1d030c0d020610090504290405010b01110d0806030709020c030415 75
    0x745d45501440700348010030a502da54020340010907004090b6009942801041019181104030081c104d0b407140208102040c850b050b100f08504008100400040801d000d4580c2ca601c0f9261798814640400250b034641a000000b6100022040f1901c4249892040325101251303018010542c54880400145290124550014036034070740a000040c04580c81301500d004d140c489008004510090b00102c8010b9612414504108840070710b800c00001e0f800c4e140800d5a52107002004401903040e1100421541114011800384c5402070031134510555501c08601c140b1180e1710b141101040610143d0380c0c5a03490b0b805181441c00c6030700728505550104003449001c10201440d03108950b40302c0d41c005090303290303450320b0444401c00004984148801851524140b0350707402249000d60b101d60002c10001401400645010302c1d08150301c070302504181442191903005e928013951101006041d10007450710b40c000724040760401042d10a0550012405100ea403085001c3e550b05000581001d0b0100d102 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 372181052 1250 372179802 372179869
    0x2060f2214031006150c17040e040b010503030a0801050d020d021005040f0b03060a0302101101020a1205090a15150509070201090b0a060305070512100e16120f020f1801060905 77
    0x200805c1d0303e000c10a22031511024000e4460400b41c40c3d9041d074080c03a64441e03480318003105641050354240c50004031075000280501d8000100e03181480c080d11008800d030b1070401001030078040003000b66000800740045400590702c03076070350720317030301e980359101c0700d803a9803c01c0d40f00340c6030760915045860020010000e10031030380c3c1c07104001c00c112a811a4180c1c441900d10b40d040b1101420385040a15560012400c2c110440e0441084030000c2c0e08940e08100d281c0c0c40b018200d0b9107044000c8040c00a19071628416102c40f800d41243e100c10a510014090080e40c50011442000040380d4140c01130355242c5030041000041175549410101020040c04002e00b0350311655120011842081e1040501042085138a0700a00a4000b9400030040070000000310780700141d200c01310754010030800c003e08000072803030080004420f140a60001d04010803040c01d80e09000001245401495200d80c40b03003400302c0050610000036020300001e0340c03050802c038a85030a001234004100a03603c010141c1c610444490031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 372182302 1250 372181052 372181079
    0x90b0607050a02060f0f040e01060f08070804081803030f070c120809130b04020c010603020f0d0b0f04020a0302060c0c100f0c060f1d0606100c02060f2214031006 71
    0x15012104c040e590382544031300320464400c1c800d0144a0f5840400c002402d49107484001e0f0403103401b601c4603404400706210440744150120744020110710820003250100c0e80e0328005d420300e030040107001418080600300003440c640041c0502c10440500080b0941003051400e41500188071051581c25407036020740d1460160b009042640313000d80c0000361039000d07215151700a0310b0302e4070000d84110750301d440178100d09020380300500040c0d00525854a0000607400e207042c01d1520540c100c08800582c3d01e401e0300101c50490050003d0307a11a400040201c0941d407034030300904900a00a0051a03a0502034041c8040a000071410b6030038000c141c0b00340c4424507080345518240030b40c01040000e030002050b2588006111484e1102010b00d15121400d031040c0f400514280100e200b100c400c40c4072804002c0031181d400743c000d0300a400c01414002c00c40e50f82c080d5005004100402181000800e544900d0003110382c0d51135200908c40340000c04a068181414401c00242180118040c4641d40c2804203824004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 372183552 1250 372182302 372182323
    0xa06090627020c070b0c1905061806010807030828090806070807050d050403090e0a0f11030114090415050c07021806010203030112031b0b060a060f2102070c030507090b060705 77
    0x4400004021100c0d040900c41560041f224501043d064141400c0c026510300c803c64030b985448102407294086402c3c0050b019040312486002030500038259a581180b907000303138010031480003004504140700403030000101c080701800d554049465140c01001783c9070a00151888060101800502c4030041c0d1240440e40010040d00d008603143e00c40b4901291407400f01d5100c440c20496040512032809031a42020210a034080c1d02481910b00c4911a0901e0703200c20702c2020701068402030ba620300c0f41070844481d03a102d4010100d003109542000ba0a10544d041242c10510240740002d150045141400224640410211842c40307503143c8500043d641c1d20060180305012a091640c140805106954101914170105d00c1400101c40518115803d075a0a41c3ea0034803034589d400d800314042d03110b0301a180303074201c2c2e0f642c5903140c41101c0120b0308100014049400d00840e001c20407800420510705160000f140700383c00034012107140c041c002044500c03284a0728800c010402c5408003107407000030450b425 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 372184802 1250 372183552 372183569
    0x70203090607050307020918010b03010e07030620040803040501091508042003100203070306122d0501150602060a14040b060315010306140604020408150a06090627020c07 75
    0x203a5400f42040d6143d07001d01d03c13009511014490800200400b40e0300c0388007104584900030300168440c0c2c41014283d40c87c10303000c11500e50202030f040000c10a240c106400c0503064034200405401f501c0e1046460f070f8804c0d04484856400028200101c0d42e005000d00000c0ca000080460400c500d40d0300180104405400504000282070100303000314000c0a0700b801e0180d00034102c642a55003400558080c0d00200c80d050040717450003c00145600c00c250648480340d5002d0130500da1064002c1c00e156078001c5e200048224144045c05140001e0824803442d05910060460342c00843c0c5080300003440c0800042c01002c100d41400302103102c0a860b04c0a0940213603100da001007065807400040f070301e44000b000d10700a4011001e40000103001c0c141c0d102c1d10404044c2e00038030159503a484140000d9115620504041d40d014034900110507c1503001e05420001000000c40c0319541d9600780c106640d86500724001c05c0c880d8038004041800004604080e01c42c1c9444154140800344108a440b600c032442010503 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 372186052 1250 372184802 372184807
    0xc020109090c051e090418150b01020a151d011b020c01050a030207171903060b13060c02010e06030a020903010f0e0607180503060c09040b2d0103060b19170702030906 73
    0x1c07880300b904240c421806002e00f00f088017241e6003c0c1208100f100c03003402d83e00640c580906451148c19400b400c0450707041a00100b4044003269075081030111102d05403038007959120f004600200d0031a40e5034406c88003040020641e101801d0584100c8040e500c8880300303542c8160940c500f1039070131809131040c1030040d0a0050305c407425401d10484085c0c05a0109010000014005039039041c0d40b0040c4460782c520355420001252a400600b44e584184c410300306d500300744c0403000c1103010311841c503e01d06140b0601d051411482103401282060700152030040c09290080740e45241810300f40310780d054100c107400c4144006000206415100c44018040f1010810082c0000103004002441040108001740440c2c01d145055500072586801c2804800d10842c00d01c0081c0d410740c5130441c0d501203541c6560200c0142400b2941d4580c0c182861103650b03034145501c0d0b0b40c00290b0744000001524075208031b980b01c2d031900c01985000a2041c9409004604100103c5003071240c440c0e40003055030400e050503510140d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 372187302 1250 372186052 372186097
    0xc0a1701061703040e0106050909010b1b01050403090528300302010f1404020a05042007050708060705070c0e060d02030a0614090a1a061206070c020109090c05 70
    0x24007612032030b00a108900d1810342c20707000105001008008803901809410042c0c0d0302c4010896862081040b80ca070700c41101e100500120f58a103004111801c84c102d01081480d000c110f105007501d034112021303400314646000411481c01c0500405202501c2c10054441e10415204c0c404440341c6540a440701443d0384d20154070044000d181c0e1442e106502c41c0c1076440340c1082e480c00038060010341183c183c020341011546c2200c48000e43c21070740a40d0b8028180d0040605100600c401022000c4a41400c00384008202489404150040c4100350154018098081c00d025000740303448005000d18040001c00c00005011420310103d82083c0e500c89408241d46486290028071562409a0040d5043c011206220b040040c00d5004c1d803500807660114001c0c2d1f580e0310405e40c0d218002e220f806094101c0c011082c0400344c007821a15544440e009025220401308915410300d4030b0000c4410b030011030b0502d02c40741c05568014014030014039144409126060071004000c201d0300408081800d5000e1201040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 372188552 1250 372187302 372187349
    0x16200d031a03010c2f030c0120030915041e08030f010b16121e1106070e030c13090f0c090b0603041a13050d090f080109080702091003050601090506120c0a 68
    0x3d00c5485c521411a41c684c2455803185000b000a0041e02016007501c503206559006c00d4410b4078454281e031005800b4240c24095050b48440700103000321503940816185800004090070031050540c0108009603c92420b1403582c10b4002d01a0400704c880d100501600100b41102460b440b2a55070088400b401503003080c03015a0f500d4010f1441c001048200081e00c01c01e1548040c2c008024001300003190144d4a5025054407070541d6880b005405400c6403521580710f00701043c402c94442644200011140e0705030325800c4444510600072107103002480e40810403d1654003410104800455402e495420242d81c1d070110b103040e203400441d10f01034182c0002d4110041985100105401100f69041b6001580b0002c2001c040b5001d030243c0010300f810302064001d01441011001340e0300007885454245640c08200c070010340103001c81440007075408080006003091008030300030150300802003150706041c805c0010301d021105919040d540b091603602d102d981c61480c00401c072032412100250200e4900d404 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 372189802 1250 372188552 372188627
    0x901120c0b03070c111206070516050109030c02090a0e0a020d02060d141801060b03061507050d0f08010e1e09010605120304050108090616200d031a03010c 68
    0xa90401c4808070420040540095103509410311418000c0701040c0d0103801c02c40504001c0d00e10034010781c00840066031160203100100180c00c04001c03c8140c030072031603440e2070035140c0904007207001840c40c000d0442182400a41107400c904200c60510004d81c07554011a40c4140060020303200c0d1800d06002030075512100201e4004201c002400c0c400c0c203a0200c0344d0300c0c0d451030603500049000701e41d0f043c0c608942410b10901080c1c41418540c5403031500c43e007007045103120407040c1d00340041d48200540c1000420030000328150100e60b032100310403840c00c000090b0003e901681301c0d50300c3d41407001c01c1044c62090459200b074924904405481262100c07050305004103440c0e00a0b07a0800b0314a130500c2c445010000180080700c409a80d58080c907900c25000d1521003d00341e031a8688600107216113900c0ba802040b001c50003007074149104c213a00304403060b640c2c03412566564410110747e8072038841c0e10282d2806250420b00c103084e402071000d040d84480007440c0c01e22100042d8942503858100c2101d42000381c0301c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 372191052 1250 372189802 372189809
    0x10b2202090616050703051011070209061503040b010602060c040e0a0c120c051803010e0a0809033901030e0d050702030f0307030f170103020904080705150c070302070909020901120c 80
    0xf1030380b6402d21610707082e6542c0d185400142e031a40b040f4100c8000d07030f1000d401604000c0012514282c1803030203030b500f170040c0c0700c0c4050140c6a01807c0b03c144451070310402d00c0554800c1e4091800740c1c40c1c55242c00c0c4e000c2e050041c0640341a0003480704100500184d64400d0a445e0084041040058100324170501107800480c0300040509480c100010603030340c0c5502c03102900c00030101d40148005040f40c103003010300302d0315844058041a00030b11586d002141c034070300c003030704800c8400360648050310800581e008880d500240d00900c0c1c4942c41c050080583e1240080d007090074401c4c02c1c00c009800d504680281e40d030480440c80020040c000a000c011501d0502041c00300d0b02002046a450303401c18500500003015040703c1200040c242c003600c2031050a4480054100c81d000703000500143c076503483d0401c4540c802d88056400c4d01c030303c2070388510500341d0500403441401140d01854552019203802414070080303a1100f2036441c1001c010710007680e100100300c0d044802101000d045580c8515115806024550 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 372192302 1250 372191052 372191077
    0x603070b0f0a0c05160e0c0c060c0708130f032112020705070f0b0301240c02060d021308060615190f17040b15030613062c0708010b22020906 62
    0x40d40540c5028507080d020142d0b10500c1e001c00050703944044010b50350240d48c0c1000910b50018002c1100d0100001c000d18155000b50090392500d26861440c90300307079250381c0c00a495000060030410922143c41001850713007154000001890412002c01000a900091080c1c45182c6c0018040c040002c00c1100c1c600074801840070701c0095548003001d0129400c00d120381401111a07049a96042600300c003000c00c103013140c0d00c9403003050010380c0034005e1540102405206040c0d003000032411419001c030a4000a0050500a21462401c0700600c1440c000200e040d0000302e0081c8a1100307001c04003288813224a450b881c00c8410701c1c075560310445608400700b40f480f00182030402840705000540402030301c1410041c044c0c0110540e41c0051640d100c0c8121241030f010f485040610340090001c2e0071001503c240e409941c484d0034981c03241041c804c0c0c80c1102c0c4103c242d101c01710030000c01c2e4083c01284400c2104a50b039040000280120900c1c44146000e40c440070350340010b00030002d0b0759100076100141c81c0103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 372193552 1250 372192302 372192313
    0x150e04090602090a0f0e15060906070c05040c0302040f0b28020a032c040504080d1404140609100207211112030c07110d08070302030d050603070b0f0a0c05 68
    0x1d00340440294011409280241d007080701c04220392181c50a000b00725040320700c0da86160703902c410340758980b0100200081d900c08000c025181c40741c0e40708009441082e01138891a500301c0e20b0581080200e50000c10380b0310038940103010030071404c508200800300300d542c030030440c0e60790361001c150b05020340440000801c1040c0003030041051056000803ca4501440f90302c032590b0701207030020345141e4000d0120b82c20801c012002805069130819801141d001482004c03002d0400108410002c1a604c40002d00158218258100420300c0301511040c1040706240c5e0107810181801e01e10551240c441b1081c282c06580c0014146042161440350001014035180705010100e03140e0100610140200403407080c10707c295000204003000c03006c00c480c002c0c01640d4a162a080d01076598081e4028a40250faa00040c02c46010f000f0a10031002084800c0c402c0d405550b49404da0200c517021620040e0000340290710580090085400c0c980448082801c0041c200b03444440506003210040007007103006000e40100c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 372194802 1250 372193552 372193571
    0x90e190509010f15060905010314071107080106080c130e0604080c03040306060b03070206150a1503060f03060213080706080703180c0306020339090319080319020a09150e04 76
    0x141610b00130b1752516034031010055503803001142614032002c40b890705003800b00c001c920003c2c0114502440701d5049002e842c61666a0701020307085400942c803516403030300050005021850b00f01c011141034100090308000c20041a400c055980a004000400046001a86140f40582042590300542d8005002d02c00913407222403906164000b980c1201c0944034407070104004000c0c82481c08941440502030396031161400400d1003086101d0360401e010300d83d075900081020300c1d160340c1800165000704005682d0310f86803180701c124041241d0200540c1d4000400510a15900a040640002907444c0120780040d80b582c035542424107003900103104100000001040000c05c2d0051403040d0543c2d9445264000701d011504040c10f85140c04e062680841c43c03144010f10741c02c10151040500c041e0888644400b0b80304840680d481c00c4000f51823100d030201c03c20440d520442a00d848003104040c055080c5050706c00c0150810701d0600038201e070307008052410580306205000120281a00620a102e0b4090 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 372196052 1250 372194802 372194831
    0x40b180d0509041d120f040e09010219020d080103080d0e0f1e0a050a020910080604030309020f042703030b10080a05060102151506070804080607090e190509010f 71
    0x400b422040c0628100f1100ca00940e41080c0341d03080620034030340504400301d524140502150301940c0d0201c0650401c0c0008590803260a40040c82081c030311f40016540c1e0141c04403002c2070a414000c100441d4807030b4840041603a0b01c180c1d0030341141d030712aa529440f81060b290302e41c05010789131011940382c4100f440640d20503100143d81540902460400714480e561050360a403542014203010b44540d00c214000001400c1040740541d001c521704e04100c0c925501c882546050120554083d8002030711034054805520b4040c00e40c030900f0104075000c11151450b203c410045055420201c010000745c01480300525001381c00ca150341c0c40006101e680300742050346001d0074162080d2041d90115190800244e101e500001d03103e410200d401c80c02d5005030365202c40f0780014450f421040c81d0001002d2140b1800105e580c0003820140070000c01600c41441c0800b4000d002c40c81d29407020082050510901c40d01e901111607a4182c81450031001c1042d81e91800c3c1640509255844004040e2800078002203052 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 372197302 1250 372196052 372196057
    0x20703150b0a080f030f090a090c0c060e0606090c0703170c04140901031a13050304030c0303170c2d03010b07020a08010b06030112051c090906061403040b180d05 71
    0x804070b84902d10350340c548607059a01c07043c52407096600e90081100780d100c0c00d84a0054030124000900701c484150311000080140d03400e41d106040426405840700b41044424045c0e00b00740d03032501c4000c055030f03c2c001c00050328000001d485051954400035845080c0351040741c00c00c0d004140c84080d0101400d000700101c100c1c0e407180c81041c0a0100c0c18a04800510b4900149412642c218010000b80e41800005181d0008040e00f481502e400e20300340480011020300160004600400140c0c2426103103090240c98800c94003044141c0303541d44400c00064041982c00c0d0764210340702071040541c6241da201074102d0b000c3d0894582000d141c02200004240c02101c0c001c201c01e84c8240d5444200300e80e43c0316250700380c4020740c03002a48400300340010702a0b42d1200c1007801016001d101151050842d010744152042c841a81c50000100140d4003071207961514000e510082101d85422882900784942c43c100714000640001d2410700c5101c0403641c01c2c105150303006414280b1100ba607100380b44c00340b005000d40d0b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 372198552 1250 372197302 372197321
    0xe010906080118021504031a0601030e06040515091005012402031e0f0405090f040212070b0304150e03040902040e01270917070302060f1602030d0c02070315 69
    0x194144400815a10070600500706005260300c508001040c556003044100da4203091403e4140e002031000002140140d14544030400110305980701500b00341000400b502d00c5a1140e2116034014800d00c0005400007174550342516a07018100b2035078450000381c6003080c0340c000c110300410f0b003042c00101d000054003201c112180480005402d2803900d94070282e0700c074045d90040b104040b10b07400d01c002582c0b941d00028803401400d18901c40ca0180c9500000780410b5003940d2040343d00001908210444c284003d04c0080d42203000001c1c08080e141440300d00301403000400080440c0c607003d06080300340c1100c0d00f008041034007070025a51600c7e01d0b1400903009406c40d01c520400c8545a50001481400d511420075840b0300800c4825074840319041c521000c0c0c401c4404c200d4441c6660b070318548200c00c01d100035000d0103100e82d01501540c1840900040040c0018ac02e507102c0300c594491201140740c00100b141c00880d0910400b0a1010a903c0c0607801d0481680c8080c0142a50610f061940040e03a448030624 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 372199802 1250 372198552 372198569
    0xc0510060b0301080709062117030a0510092c0106051c0b150a090506030c0a08010f052212120f0e0115060e010e0406081023060a0b03040201180e01 65
    0x1541d511210b00a07540c0380d100e04e0040ca1423201c40c440d1016000c2d120200440e0266108160b41d021600d80d030000d56100700c81c849000c980c0c40c41403220102401110000400309908144910420520b5031909411001d400407210042401403c001c0c282c01e40020009250007018100d884145501010840b004150301f100c540d01e810002a140460107500982101405000055846e0a2040c0d4a00600020b4a55503252058200c005441d80d212402400038002c00070000c0343d400c200991540c1940c0d00541602104030329400209144030020820070341031900300d0f031040d0717528041d40c0054410180300306035600c0d064145003142c22201843c1e0001500441c0304002040a031a001c1204203c540301030091200260802c4802441503205101c200b44074580200001a455030b121302043c03404a811011001940d140c1c800440910072100007181d5980300c4004a0015180050004c0ca0603402d900514800e4000400400c007036900c00c2c240d50750a152121042d00072aa2510998003072020309100e000700 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 372201052 1250 372199802 372199813
    0xb0708090607030507050318031329070209060607170c0d0905030d23090d0c09060b0403080415030e03031305060123040c0201020f191d0d030c0510060b030108 70
    0xa5643c4644955846200c2d2035a800781140c5948002d9505103010107440c0c0100e102c20700c540403562040d000c1a00c010080e40c040c4401b140000b8421179a038400828001120390801c1c890040542c480e001055070000f41110440d81c1c0c1c4580d03103800500381603180e07410142120081941ca00090000901044259041d12801801550ba004050380c6001800c03816000800c1282c01300c16569036020f0882c0b0840d11124000c3c1411580c0d00850240203083c0b03c103482d40da904030300404c180c84240c4502030250042d290742600d010b00b15114071070140300d144540ca9112844900c2d1001c550312940c42091415241c4058a590341043d484c89a100450240259080d015800000035150101c420000300001c80100c0400c1509071001044010700c4c4d02105101555003c002407089070300104000d041c04121283e500b020004075a4004240500c0f005942907050a83c21040909a031000207001301c2d56410304e046002d1400300d01c1c1041c00e00b4507401ca092502420071001084e40f000e100081c40c1a144c0000440b00e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 372202302 1250 372201052 372201061
    0x1a160203010e070b040929010f14070f060510030305070f0503040906120303142202030c03010905100e010c05090f18010b070203060a0614060c01020f040b0306120a080a0c020a030b07080906 83
    0x451a07280613864500403c8240e126041d401a100c9402ca08003c3c100211101c001c0070340c00c0654bd000d15402ca51243c0b10791381c0701c01004098411240c0026420244d8180c007411994040c0441c415000c01034141e180c041800f0041000802c11580075100d1684180840da6407507040351144920414220003080c1801d0960100c207404110062144030110701000020b0040d08101d8010704502c001aa014081c00e540f006154600f4002c2452480c4100c0082c030403907603001c1182040327a4482c600c0c401d003070741848022000941d1240560f16419002c03140c0f186902d14a10001c0c510035840400b01461032000c1c80006550441c9001401d4610f00135002d80e441ca40d00e00140c101191200e0040c1600048a03081004250034100c000d0304600c03240c90001458405201c600b0075581e00300d503000c1c02100c000002044a14200390100316040c1200e1001041c5e0600e8940d1022072a0240c141c0d01e004012030b9580f04429940c40402d164000e6030421000714060412000080141e00c08464981c00c41c0325160105 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 372203552 1250 372202302 372202331
    0x31b3a0c0504140111010c110f07030803010315020c0109060606020705061215012106060e0102031e13050603090109061d06070c03120c0804030206011a160203010e070b0409 76
    0x14032000c0c1a500c0d81d2400d810060460b0000000c01e100f20704014000d13a0388680110300b41319841c0c07204444d4856403004048100507500d8142050805080c0d074005400030400546180c0a03281900e038040003146448402000440090140360680700c015030a05044d5802c0c005030741e000d041030b20015400c0d20b00c80764862092001901c50b103171541c40c46d441c845000426000b080c4888042a0405140803400700884c8440c10501d500c40040085140b547c1790b0003000039540213281e412203a8000c0c0042c6061008480c3c0c1d140000c03000c00a41010080c0010741e010745842c800220b040071f4000107000d6a1607080102600b0b000744540103088407000d243c40d000400036405109402d081c5008100100038503a5006011242e00c0700a000890501164000640c08003001d03000d030411148890f034860009103024140240b400c0300603031100c01c01390501c0d0a140d4410380140e00325420186101a80f1102e1012440804c3c018000f131140c00109028010002c100003d80400600445541e9503046c480c0042d030301d40b0b1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 372204802 1250 372203552 372203561
    0xb0f1b06040b0708150f0f03030f0c072402030901032409060f090612030c03140a0201022205032107060507020d0e0108010509070309060b09090a02030f010c05031b3a 73
    0x2480d80f03e50300001591807847d002c2845442144090140c07400c0000c404142c0c03c9913000780c21418041d40062109000c1c41d0000b00002c007034050f010f411301090903c4030300301039101d10070640e503981016200c0100c0001001d0b01c110003400c2590610810810607500d1804500600c1c0b01d0042d102c3c1100002e00000d004070300c0f0b024040c203907505030480b0340200e04a130354155080d010000c0128188030323296003070084004204004c0d2082d1042e0346c001503540c038800d4911504003992000c551420401c0214180440d44000030b8540b010740c41c40801125440e90b092480c031440c0980301009041c0341c106001c20020381d501103119880d00d10a51100a070b084900001034402030424010700390841510000143d80c14400d80003402036500984001800b6401c0c1008581210070466010f002c65024174030f07020071428100240d64040d40d00741c001704050094000c00904c144030150112840c13202d180c5011010315000401c940709507907201c5241502c8445003940d070348800410b039845c0f00c22400d401403841050005005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 372206052 1250 372204802 372204841
    0x7051903030e090618091006060306090513050d0c0302101a15030f1b07050109081c05040503090108041505190c030b031e031e070c06090b0f1b06040b0708 68
    0x15030098048406544107101718020402c170150711815028074480105ca102d80405401c950790003050351420701b019041950400b92540c407a0003030458010000c6203010540a40302036252504840e0030348641412807902c143e004440d400c87c1e1420b22046030165820b048103412810075240d00d10001d440c4410102c090008a40180845444e4400240c400d11020000f00401c0385100c000c43c244501511080d00311160408200d44440b40050b000445000c6040c500c02c00710500d0038180168601a60385036200d000e4074003a941031246201c0450200148030a11064182c401e0303d082082d032804642c407402c01828044116403491401c041d03103a040388680192894408040c0091920640e40d440c01c0200f04060000c00109010901000500a6030b05100841651404510507114206410401c02200c420f5000c4028405d1901c07003000103a01c0d09066541033b0140b054016220154040c040c00800b04030441a54203000f98401c01040204060b00c5901452a0369600c11440c0e94011005070100048178 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 372207302 1250 372206052 372206059
    0x6191b030206131e05150123100302040308030a0f14060904030c03110f1609021603110106090204080d1d03030d050903040503070609140103020901170907051903030e0906 75
    0x5000a01c14000b19a1600f0003500c15403020440e55444901040c10b411809400c0321242c2080d00e07002c15058004a119000d0001e0f00d684130010201d100084480040c07107051b0300d0003260407240c1c46c480c05000e42e05403801180c00980e041e41da850042442e0b40104403410700031030118a0420140e41100e44524600d20a10000e0410202a1115207040d102d02c408000b04904101e803802c00c1020018050244080025109000b000c240a043d4440843d8603200e4126502451050100e04030109006089403002501810948121100040d18a0240c0400d4220006049c00021300042c1d003800000c401400142a9640c040c250000c1003030345206190f0710600a505600038010600c9844180d886a500507000c10112882c040d5604003007030401c0002d501200c04107115900401c01c00303c40d1400009041400d2900b18600403203500040c1008040c0b14003001c07070160303010009540c98810414240513140003440103c00174406052070028100c3c1d40005c400013039000000c0c400701d041c079807031b414020301008 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 372208552 1250 372207302 372207313
    0xa02060717190f0204060c020a0503011109090705070203030301030308010e1302090127050906070807020105010b1801021603061e0203090312070903080d0f0b0108041211070506191b0302 82
    0x38810500042440001240e0190b48400f044600c0e00c50340b00900040c9070a4540011401007801080380e8030140d54441c600076414070303091080c45c000341c500303c640b07680c0d00302c03007038011038031802c1044605024460b0000d4040c440000040145600400414100c4210a00e00005541c841c5034640050080c0714009421451000c0103100314100d9015a00b4120141c1030000c80100504d265603080e03441c15601429150056018488950b030b00c0080700d42e115200d40003d1006516041000347d00d442520000c3d03d80a03000c0b010300003182c2c070134800581e4081b0f001140c4200d154036410543c0003003503c100781851001c114041910704a4450094910840150001d5070500101041000d520f40b002400300042008603076000c070024035440060001030042807000103048620300e841c0701c1101c0d481c2540c18144181c01e0308000008203400801d1a082c165850a84a0750f0042a00d0500e0b0002c680c20990307201002280341001081007a95165040c0d82030340c0c450340d820741c0010500118980d01e00000d00107030400c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 372209802 1250 372208552 372208561
    0x201050f4203061501141e030a1b090801240302060c010b130e071202060306010f0302090d0302010b0901091104030602030c1204051b030d120b0406030f05030a02060717 74
    0x400101e49103601e00305040300c011018980009080610490f00d014508964256800f440e50344061420112154003201e40d1400a80b04162807030314412422840403440000b000a0450307120b40c1208a152544194480a0380040c0d24041c213a20581d0040f401c043d8a04540440303207a4103204c200c1d90080d903405141c400142941c081c0803040d070080900440760364aa00342c04516484400a4030541400e6240016165010005503810144d041c0c1c05070740c5041541800c940540d40b41c1c0110f98004c10300f401d01400e041c00c0098140c1c0640126040c0d0f07940001001030000c1415010b42012030902c43c11101b884050fa2504a0703a402c503602c550028217240d409210910000300103900960300b08280a1303c5504010300101003082584e402c131011070315a0052900903012510355521200c1c0d4110440c080c01580940c0c80b40100045280e02c070300800e06855044c00c8030140c440e0f900040182d0381141c0012000283d9081003680e0b64050402c10700148503440000d80e1080c070400d20054400d80c10300c1c4d80101d6494 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 372211052 1250 372209802 372209881
    0x608091507050a0c1e0b070e03060105060d0b0a0515092409060a050d0203070c0b1302030c0d0303111b250302040b0418110f0102030f070f03051201060201050f 70
    0x4120011035006141ca40040c0307158a5010718401000c0c403a05412180b0300d01f0749030080c1200b80c0c4003e8203000384d100340014450766440105544c10340500b0000064445041d00000b090601ea0f64000ca4000060348070f4211400d00d00070003414441c2c010f0300d11500e03030000c040140ca400c807650b000320080090b042c840c000040c0760072002025030411510b02981441a066041c1c2e040341c0c826038481020070b01c2143d41d00200306400590390707070003c41030800982010040c1c010035240c081044900d031051482994084c101030099000d00c5003d096101419141e0110030f00d118820840c500b03071821140720340c0c142e4100001416036408007070f0b101751102981d1385140d03500703000280040a54180d07200e80c452a0030316690030940f11003101d080c01188141001540c1000340066000300401e90740c110340040015000c1d00b072040c1c0480704207035840801600300b0300050901301d585d070003007500f00400303540c519000283c11a0305400090045082c42e10500c007541395000411420b0f03600d50410000c110745043c01c00c19131003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 372212302 1250 372211052 372211067
    0x1b110a020315100e0a0516020a050a06050a0f110c0f0d020c040903030609050a060f05062107020102040e042d02010c030e010e1c050c01080606030c09010c0602040608091507050a 78
    0x70f15000166141d81c03a0785034040095400c40f43c40d044580d0310001c00200c003a451280e00880400d0380050200034119895642d00ca0103c400003504c01611403000c5861000b25901440c1e0400300824100301242c0300003545070056120504c14101845095815040e0840200303428014820b29001004408884810f110281c8059101601410307540c032400520000d41e4050548151a0310030001007850a01d020455510066002280202c2040c800d034030000c41142503441c3d0030300135882c24050a9075448800c90191145810010340103402005100c200512650344207046400c0706c602000d00306940d0201d00750b143d0345090190014107031410210110b801060020510386040c0f4060329070b11189008140d09a8500e51040207181c5140c0340355061010610654001c000300340390081c014103018001910701e00002c0c01240166800040040240e030090840310300385603000100355152990742c41d020709801d000302e40d0200303039000e180a000518075410100740c2c865000c1d41c0741c660904460030300458911 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 372213552 1250 372212302 372212311
    0x16080403120b0901081e0303060102070306110723300304020406210507080a21020a1704050315070909090c08030f131a030a0b0d061b110a020315 64
    0x1c075607410308050300e5100c9000c4a400fa255040040181041c2c41c90031040342881444071461a40040c0180b000c84da03404603002c0c08072b941101020502c401030b20070b00813992140e0140100180714070604103404848014130303004881a01429a1038949240600428940d1030101040c0c140d1006138285540d500300b41c014580141c0007400002d505505c030400c10844003966056008062214803400d410484200003810203444203201821500d202c998840d0041c408404a00c440c030709024241810711403007009a450002d40142e10340e0707440d01841f1031b40740c1070364803a001d214000c0c0918012040c1030413016104501900682c1c0d5401d11003840c000c5540d0040080303000c219810b10003088001047d40040002d4a00048c205038003d030f952140210700310018100ea80415001c10250528a4241d131400c0242c9500100c0c4000100d45030030940001144400c048000400442c6840d6018400b1840304180c0842030150b62a0840c402c500304c007840d682c510040303000a41c9603004030f010100494240c05082d400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 372214802 1250 372213552 372213587
    0x1713120f02040509030903010b010905090601030507022a120a02280513020405040e070806010324140921040918080c060603100501080c01032a03060e16080403 70
    0xd140d00c03580000c05851050b03a030800b65074004100d0105e540390a2092104501d400d00304040b2081c6441d000c0f036010300d0002e02242c141030b0707140d0006800b80c0c003c0c070451b5098040b486c003480c006002142820111516400004d01601c1401451002000c002030810112500100700c0342d180210041c6d600c1c03501440d11342d044c412640d01d0000050300c1d00c072101c494495000226000d030f241c030704200500c42107400980300190030b43d0054008006001c4e004c607407181034076000050f03910041c2e480102020403101d04082d0b03805881c500360001c0101c88581058034050503403c4186c843c1e4a02850400035040d00690740803000e03e1003000100304104442e4402103101c074000502142c88001600d0307000c0990840c4403004400d0300034100704000c0d49400d100c05080801d00d82e00411455042002103035175441010149030515544250030128a0000c028888520740d44401c00036501000200040190085216144154240d040402c26222800600c60040c000c4e0b90b8661609035075940703088804a0020400c0d990 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 372216052 1250 372214802 372214823
    0x21014060f0a050a180e0106050904060509120c010f1d071403010603140708210a18090204061d060a020c1903170301080f070f181b030504171312 64
    0x1e4030341302c4d80c0d018801070500c1034540030003403805114081929180a0744004c56494002c061009644030b4030200c1c0c106800900014155039102a5a4a03007404030140282d20080032500300445070054011018580342e040060240d1041c6c982010718051303000640841a8101000910904903490040088600000c00214810756262115a55140151500c1c0810f8001000500103004108940d040701c0a158032060f4003506510803c0c6000d024540c0d414080144148402c01100c46038085900503003e4441c0440d51142e40d42800f40a0390b010881d070342c01142c030b10070b1700000318501082901c2e02159a6005428600c000b6820813444881841e10760070a243d14400210100c0c0d10303001d01806c661038403c006c5035294100145d842c40c10503051142d1031290f00080c01407160400c806115012030ba00d01d40325019610100134281c3c0a0701007121500d100151560100329106d83c1500400e00640c0a07020583e00007100d84a1a42144a2822081c01c000c4d619002004244000310002d40401d02600e155003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 372217302 1250 372216052 372216059
    0x91b1c03021006030620090a120f1202061006080609070f020a050304090225110f0303091e010e0102070f050904021c03030603060e1902090a021902030703021014060f0a 74
    0x20480e43c00b030304152a031a50340e0092905410303a803091001d02e2680849950f0414211400280c0c1c11403282c05a00542a000c90014040022880406403031b00c1c0c1c4010800810382030480c00035038611084501d10204001400d00154440c003409001d0702605004d0000107080c3e03a038410076240414800140c0c0c1c111700ca841e01c0d0901160b0b0600140024000120015a50703074080d1584800f585003207808000d02e080700c840c160002031a14010411180b03010b41c0d0070b0f28559090000207003140951034200e07420002c40540302007191007425000352480c4090300e501c500f4001c80c1d07004981e10313038440c01082410700c0c0450301800b040c81e1624480c0d900510050080500356104025040c00400303803601180070a03140c1a0600403c81580031301c03480522250018a0f2008c803840b0603010308140c6c1c000103400791880b040801c0c00c0036400d4045403440f6120140c0a0132101d8460750007503503a8040101500103004040d02d81d90202c2c403134083e4080d41101034601e41d616440720820001d110108079140c5a12809100002 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 372218552 1250 372217302 372217333
    0x10207030c170c0103020a0e0f0a050406170d020a2d17030603010e030f0d0504020a0b031006080f010e010314070f0f06020111030405030a1404180203091b1c0302 71
    0x24107804042c802c9000c084100442c41c0c80e1600600e02d06140c010300a901c105c6900c0404240403500c2125980741c0c2d911030760007040100025410040d081414040c0c0840c08220418680d841c0020403c22500600781c200d0303040361100700c1200000c008000b422a0501140d8684443c1d8608070481101e00b6102841941c1f45820304a00c20310b201c586007000710402840b8038081c8190307a4500310540c0554a07180114120903001d102d01d04600b241d203540e03003001c178044d911000b54890140c0704284040c1c1e520700b44000d42d4a03201c41684a150000b03002d2000182c00c220255415038100c4401c041a1012030f400d540d15080d405003043d00320409407092a0b800a0190303000c000e114000d201142400c0e5003035042080090940c0c40c0d10780f522100300020018803001031000400c43d80b4040042c034042d02583c40340281a44544641e611900d103600d0b41001240702024182d00a6000300c0e0141c044600c11212680804d034400381c0b810345550b110034065042d55901300c9080b044c6c1d841d6413187c8165060003150380d900 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 372219802 1250 372218552 372218573
    0xc0b0a29010206090703050616090518040b07030207080405130213030c21050d0e0d0501020c01022a070501030e0c280b1c0b041415130c1b0201020703 66
    0x41014400c8591032640d1035601841480d8100300c52074060b000c00e90850b1945991410050410300910007260001000b0300c3c4251030060240034028040d0201d1849a01d011800c5802a2030a035003030084c250200320801c0c02842150201f550000304117003480e01d45030401480c0a01d4508880d035030341c0c003080003800d01070540f440000035500c5854001e203910f0800c4c0e2111248040015442d0482001c51641c1020400004007004090494078241c480c40b4100c401003425220012001450380d07001064120780264190040d140e070710040700c107110024080c03000d802c200d0f414503e240101c0c4d4106c0c02c01800694400d402c808542c03400070007202c1e4240e12600208400450b030440c00360441c04025562203c07511400301c0320000380810302e507603814001220312064180d144021000325840c2d039036a108039180c40d03580196070480700b20040883c461503c0e01192894102c0100c2d898441c2d60510a040303d4420749200e0300200c000c0c641c2c1c0d000071030540ca400c60784080102a030140d05500c0b0341100080000d105100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 372221052 1250 372219802 372219851
    0xd09020910210c05100306241b081206010c02090106020c010f1403070e041d0a05010e010b010215060d151e051306200a110d0801050d03050714010203010f0501021009030c0b0a 77
    0xd4048c103140041100400d42d000350030051010307600c45018440031800301c005680054048000100f0300e601e6080040e1800c1d2112140250020b690500000300e0303d4001c82e0901401c9402c0e00e8070031042a0505044407030344614018409505d00170300104071154812541d000c0c142802030030015150001545901001c116940d041040d43c1c45800308404009083c018500d02150f88002403014400f0a000070f52105da0341c001c1e004001c00190000340090380c500442442c0190405000030b007802c0b1600906015002c0c02c00c07501c64a27000010303103030b040403014411070307204107420140c1d640001501e54801d8042e0416251484800002d000926a45802c1e60000c0c4161a4152034913101148064000d509000c030480c0f40740140700c03201004018036103030300700e03011046603161601c1a51041c05141421a00f03882100d55039035580f010002241584000c140308060364000d8084a41c1416548150310540d100c50320010006100300304840e00054140390101c0e00100c1da0500441d031600c060a01000f550b11414 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 372222302 1250 372221052 372221099
    0x10605150405031e06070813060c03091a0c0f0a05070b0702011d030a0e010309060e0105070207180209061617070615060806010c02060d09020910210c05100306 70
    0xa000c201c546002c002003003d040421221414030358515084c0394031050000c044006000c0c054001440003254001031035513482d800707c410004100b51800007801002209411103114084402000b100d403e01400d40d44114004060946400d0030004000b0698214144000901c02c090100c00002078030b0403125445892564000160b192140180003c03503a03030f422004180d50010407680007000c1c1d103c403241c891506c0070300340411020301a01d000e00c0100070481e1001541d521f0102442019580495070b0401c48140e03035482030b00031540d520904100c0c401e08400707590000c002c11422118402040c0c20b28042c5000712003800b00c98102c22a4140c20342e02c51202103491035607403055018940301101442c0c025110614020509180000c0003074002c94203900003a02c54039011401c0510340c6079075048080b1499010300210000d05011000020003141c5008091003580d00380b524100b14100e0482c900050f94000c454282d80c903151030180804041e6000c090350400d500d80c140881d40c42c3c1c40240c0e044a40300d100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 372223552 1250 372222302 372222307
    0x210905010225120327050c030f15041407030b1015050403020303090d061503030302090a0503010c080f2502030a0206010e0c070b0a1d07030506070e01090e070201060515 74
    0x401540c070852110068501c1403021103006002143c586601010522003900340012911210607103200c2c010322030004d03007010f000e900d0400303810007801040500c6506001c2c1c0441d440d01014014460300c5070151030000c3d8000310604002004200d540349800c0d840719041007a520000d07140e80700c140080340115207030303118100b064000700400c0c040e0349506680041a8170f02141442e0443d0300180d02c0b84643c80a8910440c3c0a01e038801c14032506610650500ca8400000303503038155649000360180d0044c00d01c0c1f42c4180d14031000068542010b00644500300300581d60200380b66129162140420806421020b0900341081c68001e203000c1140d030400c0244164004644038840154000e00d0124141c011480030303410001840181500f00041d145240e0b88881401140d5855000c000c00806d454600705059055a04001c201e041d008115081a240a141a10055921407100343d800c1d40074180c116000416408003008031403551458145c001080744008905250b813000058141d03884a900a21040b900 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 372224802 1250 372223552 372223567
    0x402040e070e0603010627050301020a03090b0a02070c1719030504090507090806160309080412200f040c11070b03090705012c030312090c090108060f0103032109050102 74
    0x10403540d100b1907404a4225165606104005203113070803000c01246040c0d030850941700c0700741c2c02e400604040e09000e402103403503410007000180a008161804d031101c501c408041202c0c2089402252861900f101020fa0781510f44203ca01034008807010780c2d04c541c060744110b80c1d03520b580d100100c1e804030b0103580c0759a21581001308020449074058101c1c818040c20500400040c0b0011a004d540880e8244203800249014035096001e850560030003821990005404500c51500c40d0b940b1003c580520800743c40c0380c03c44505105801c1031101610b40c0300d140d03010884400e2400d070300154420161440c2003d40c003030f8840002d0f490554580c128286014020040113403c85007005000d0007031800346810821481c00250740c01e8004901c0160680003c0e01140580352034804000b11035205014945030b881e54603000080b0f43e229505400154865038020000007023410340004c83d10302901101c0703800101c5034a555001d5a2200340d10880d062100d901c1d94102c004500c0703038483c000f01d15008400150343c5105 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 372226052 1250 372224802 372224807
    0x5041d041101050a0c030503130503300702060112021c03030906290405100f0308041508010501080609071b0b060a050105070302061501201f02090d0201050d0b0402040e07 75
    0x80007a11a0400c8018005101d6940e030111701e48001c1601401d0255407038807241d031600144001f0b8a00508030303100001e10107a01d164071070080070314422413290994140011203d2480c020005039201c6c0c005900c101d0041c400b00c1805c50408a400d17200a140a091000051000300d51b621001d42c25000b0a64030400d0b5024049103010780351030542c80d00f43c0480080610100b000c40c400c90f581d14103001742e03641c500061129150800c240040c041d0b49031001c00ca2a6246480e60840d0321901030f49500b41e280c0c04103c0d005034002d0801c0d50580344c050712a03020b140c0e6208180070045100600000400408001003940086014500c0d90204d000d4802c030314540c5403260500c542080c280d402a41007280030070540010a6010805503004086641d04805208100c0012508064a205901f07aa0030340c00e50f000000c2c410000c1e032003903891180c0c05200c186d000c0801802c800c034096881134a13003014a000c8800011341c480d000500d1029a00040020b110510401180898205400040204451b101840040e54 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 372227302 1250 372226052 372226073
    0x6040e0f150307050d031101020c06040c030501140609010b130f170c122a10120c0305010315090503040f0308070c14030703230d030b100e150a05041d04 67
    0x2071058004020040c80c0201244001c406044007a081208000c00b4445a80c420340440c0c1011401c442141c680d0704240c1414121a03040744012603241d8030389141e440740300100c181107520846004000d540a0b83c41c1030340740e1600340e1041d040594100c1168101142c080070100e100000b41102c843e05131204604551000d14124003009102d2150310001c08807a641103001503091407804c1c2d0781c061208152261410303007640f0002d1100c0301c3e5210340207004050445a10195245012400d03190500500d110744d902a80ac81c0e50a00000c0c3c81d6810700114220710100d203401841070f6500c504212440c040c0d0b18144100104401e4004862110000490ba000c1c03000385440031340903100f45140d8219640c3c2140000f6030b02c00d03c6100041c607a001038454038140e0f081130319004c080c000041040d51ba028541e50340060080c09101c640e94440e01401d180140324511074880301e240c07002c015060191002c3c42c40700d00c56958002d1000403080110030032020490001d85840180340047c00826002d9906080c0750003641072 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 372228552 1250 372227302 372227341
    0xe0d0e010219020f0d06060801090c060804050a02090723130f0b0403120c020603070e03010606021f0b0312070b010311010302120411030c0604030f1502040803120606040e0f 76
    0x540c09002071040024080402d242c0596044880ca000c0c4402c103c045084c10081440c00b0300018540440003c5c5008190003007a49035204864091909460310300650701c2c0c084c10341e0054290303407100c0046801400c00c64840381d08002d80b414041c2d0300000c0b04800300078000081d42c095080c01804104100b010200c681c0100c06800c03c0305110031000d0614111840728041d03444041c040d401242d0842d03007210b01448110191130f4003d003d89907240ba0130000030f8410740380408041d0181d880e040700040d40324808a42045103c2ca100102ca5036200105661405092440100741c2c6c036029200d50f49021481c48802051030380d1241020444661450030031103020204050b5482c1451f004025031540c3c1c9051011440d80290300410004484943d480841c0c503201201c00b440d0340114000174080140103180d02040d212a104942c400844000384031900c007680030742d1046041c158001d208210701c80c0040020540d01420240045003010b03990302400f0391f0550300359840000080c0d40400e010120400c082a040301 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 372229802 1250 372228552 372228557
    0x304030c080114130602040b03070806030606040209220b0613060f0203070309030803150909010b1c020108060d0311101d070f0b0a03060504020a02070501081302101b05010e0d0e01 79
    0x4581e048003011039904001340b1040c104801450312404112440e4180ca001e0085000000e4407407814070005400190296603181c460305c02d442c00104a80f903e40201d0f0a0154060044880b1103420704482c00f040d0a9500c03008c000d00d03107601d1010520303114500640843c0461040d02150300d45042006021104412141e10440d0000c12a080110b50884840401c0b00c0e80300c542036a0340e0f83c2d100c07805e4030180d410001856006140c00240060440305420110b40c240d822a004000501d200903010004407141100901089100d0300048503454940008400c040c06070130180428140c000c03e217400c0030200d00e0348070040d42ea81d90f00440102040403583c4c4030000404010302e41c241c00d12002c241c4044843c45942500300f00051100f0b001c500c00c0d00888000c1c40041d10541d180c114144010391a900c20303005560014040320009800c43c08801e82d0402e0b081d030045e12178441d03010005021034207542d40c1c0c009441442942c045039070004400f4806d000607095628040c00342c50903021030003440c00c030094500504 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 372231052 1250 372229802 372229811
    0x703110c0120030904091b1409040f14030d021305090609040b0a0e030f0703020c150304021c0219082401050f0d0f0c030318180e07080a050304030c0801 67
    0x100c40e41c21200d040070385a19040b59040d40d00055603920f01c0c40c810201003d420900b80b5602000300320041c914096004808400c1c2c01040c1e403074080c44049501c6002c0b10aa00800d56408240131440e0700340c61b0310302140079604080681c420404e002e807031588609061102503500149554070304490340f0040c4041c0100f1180c040060030702c1c0c0c00180c040340000e800984241001c40102d01c07840a9648a81c4000400000750b90b01c40d08009440469a01702d041e00f6030241c0100b0129440c0c5250503d00102c0065000c0a0981540c0b5507400b40040d00e0b910740c0c94480e00400c560041d10145e6600c042101150920b203065000315410840d44072304040900104045104440b0b04041d40810600d2006056500540e205515070134540300050301c2d581e10720b01c050018007801094400344410840c40c00140d9010b500c907000090540c6000450b040c0703040c4207003036555140fa4002c000c481c4031500180d4a0349042000c41d400320703032101142c50a02a403404211010742c0001030800c10840d40256100050059600800c0b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 372232302 1250 372231052 372231073
    0x303070504031502120703050a06080a0c0e060a1215020706050f04060c08060117060a1a1b16120f12030218040c021507030207050303130203100506010210230a02070311 74
    0x31102c500140c001b205041e184d00000d50f14401d02c0c5d10400050826901315101007070281420074803042e40d4080d10618004190004440d070418828903021201d0b4090302056402594443d1100031040b8240809203c1d02005210003242d682d007c0e60340985c0800c45a1403541c00c0903c3c007501100c148403011010f00c426007080004e16070b0401050420030849a19040300750307840c0800034085034100c1e00020a021202004100c907404600042d15208032040300741c1c00755400140c1159981c0b108888144901d01d040d1500380100c11101840c07484e6203100e24101c5a180083c1d070349401c0610408803941000a0b03000c542c050407050f034a03510707000c280f070241c41c20480107017100002500d13030f10b0080603183d45400c01000b09200500c039504407040305400c28143ca0722810702440b0342c600740c90100d1081c0d210707101d14040210340054510450340070720030580081c48a51021040300c8050440c00c0e01148040e07071412600c035000300506d200e151150313080040050343c44800389009004440340700c114242641c4040a0074 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 372233552 1250 372232302 372232327
    0x41a09073c08060f0a051009090c0203070b07210f0f0608160f050f100219050c09010617180a170a090e091506131803020d03020c0c0d03110303070504031502 69
    0x251700f981c4d000e883c0100288029807042d124881c003903002e4a03616142820b020500ca0303000c4050807003544500b0000784103403035407002110100000000443c184040721080401d480c5560b00904183d1100b41005c100c0204140d840001c5135165400101c2d142c03c1010520080004001081c0140c5140031650015909080110300c100c1420b07540a4001d417034030488031307211500070400d000b10750622a00c0103002c603e0741d141ca0782c4c58421144195020302501c1002080550107000d03070f03410091004040c441147e03130307080482d036114088040006130780c042c10103048003103101c00303054035001101046615680c40d0700440003803031031205a000070910001c0c0750a011415a000c107034905242c01d110b081480744d44858001a455900c07421490003520319140d8440c0d500600100d4420906001c0d4080c3c690220048005800f0f80c07113a500843c68640144955400c82d01d0b0100001504074040d2070145001d0b820014014911340c403e0703940c0c1c4085035020500304100580050100c032240c10402055041010380d00c0b00c2e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 372234802 1250 372233552 372233569
    0x1080f0f0a060c03110f0a030f02090d020906011e05120601020304210303230703050a0c090e10030525080a0308040609050a0b15041a09073c08060f 65
    0x4042c180ca6a0b010682c00d0b110740c01140340c5c1481d2030b000c0d542c0d444072614081004d901946142c0003003070a00300030b00e01810541c400d45550000c0a4880c450304a900d508000c82c1c0c1c10010031180c14040e6030410b03484003040400000a005005171122a030f15103000705003040c41000208094110b5004000500148044488205c8402120002a2801c2a0300d14003038010706040011045a90b80d41e1194051015941301003900a444030303201004a910399101400903a40801560000320320400700c00c02c0002c4618400d294401c0012850104c070949950754542442e0580b03605d8500c600c0c201200001d061070640101d8020114100103000d03c035050b6901405180004001514003551040c07610203006040c0b2603060015441400d0b01e45600d400d07550006c8031401740c098640a645800340000fa41c1100a0008110b0b5a00070202d01050392a000101da0101c880285c0410317000092024465006040740c182c00c51000203c0d10301c0305001010401452040020006031240b940004a20255106c0020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 372236052 1250 372234802 372234823
    0x316020f060c0a08072604020103050a11091210020c07061707300c08010f052707110d12140f0714040810320a0902120f0601080f0f 58
    0x34405040d5480100544030006c441440155482100e1992540c4501103103900c1e02c510b1003602c01b003004e500e4034500e050444841410141100c2d50401820810f407404400100344001003004480c9030a0046902d40c060341c0005408001540c850700c030900c1401c0e04080b09043c4945403400c542c1162400003001464040e01c3c101e2880c2e43c4d60300703003490f0800c07498a8015940049c01078000b4045d8000c1003000808501092044205aa044045c04545480d100406103402022145545602d0300b2225401d000080003900c507005100289a604003818410b2048070641c5149468101c60020f5a080300d02c141e481070b510002022070301904104400e00d20064043d003000807031812081039400804400074510854211000e40c1c4103890580300813000701d4000e660383c0203000480e404554001d800c4030710325030301d500024518001c40500240c0e640040740c0c01500c00c140001c1c804840100e80c0682c03036080c20140e520341100c541000005206040e8100100c9602c078044100604034442c04a0380c03152120391041 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 372237302 1250 372236052 372236057
    0x70203250204050405061b120a1d0604050a03080a18121211040f050f0303071106040306020403080a090806010605090904050f01060b0703080105010c03090312140316020f060c0a 78
    0xc80481000003000300904941c060010015800e00c1e0410320781c0c50004441d80110350f00803401e00307600745403524162030650148854201c9541c070740c0c00240c0098003044019800320034140d000003092202c00c01101c2c0c0614000c101500c461720047c100100b0320100206510a481d08148d0101e910401160418075000e0300409041030103032500c0000c0b80c0b061101c50440340342a080030540007901001500034000c032001c0542c0c940700d581c2d56401780400c0e23680d000c0010317030300d03030814018400460360f4030141004441004040c140790517229690074040f41c1064105854146c000308a0208071500100d5003409400c6000c02007100b580f41c942c0041003407148008980c000e014050200b010020100166030021000d54000e000958650300f90602c7c5412000c1d050300003510202c0000362a500500c6001c42154042c0e8491440307500b542c550200ba440c01140040030048c88115181407603810340055409410151150752110301c82500081c60318410b0102108030b6040340d810700c8650850941192011095030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 372238552 1250 372237302 372237337
    0xb09061305070311042c0c030c0c010207020a0609050f030106230406050405150102150108120a050c070603020318030f0304231006060906030207030906050310120b1e070203 76
    0x220342c00ca002d40381c0c1142150090b000418085180315610003500e170040c41220300780038003024500070b4844005042d03600c0c0d016150100301150440440c000240314850300c3c200050314081c410f90104800c400681d004000041e02e01005011528000c241c00030352940c101c00a01c600390524134031040040c1d00c0c107018880c504c03030350502c05c403d0340343c50f0803400007803000810820007403601421509940307802d500311a0041c043d1001000c280c0e081d031010503050b5803035407008000900e45450203013869032222006600b4050103100a0454040c10007110020f407006603809030f12070030300320f1103500c22501d81c05a1100c0c0350000c1c4140d4110103e0102078030341c025008110669801240030910001100c150742c0c1d19000d00901161a804c40d50b41d4025608440443d5500c2d500942c3d1041c08808a028024004000440c000c04c200801407007000330311f8100256181820883da80c0c0c2c600300080bc040c841044400840d044c0411503401249000c2091038007070340c0c44105403443c014800075200c0c42901061014110030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 372239802 1250 372238552 372238561
    0x102011e0b0109090501141c0302150406060e1503010c0504050d0221071d060a081e010e0d0201090b060a0e0a090303020904020309010e07140a060503190c050d0b09061305 75
    0x20300b03445001070072804402c0110396103c40d00c24410000012103a40a0241104044600231041612208464042d8050441800e21200503586048050b1007551044d85410011890440d80c08100340107000c8a44400071204164043c1400c2d9061548000c00303125007403004005a44502c0a070b180303140d50484203000350b100c50104245694694032036089892080d400d011441c585104c2c01a0091900c0359041295641da202c20801014000d000e440340a400c0180301582503080100d000e2101c2010400104180d140c5050b09460300421541c10703801030b91250b000c0414890501da003c1d4002c40223a4001c0805402c1c00c088098241007d0288000c070fa80d148031990505202c0c0c8e040d25010040104190b549003000e41e0100c2c043e00b041d80426443d80104032000401c0c2c107485048240b040300182810b02c8047ca48441a1103a810080480f40043d03071070742e20300c811070400f03200f40380b005901522855202e82c08071400c00d0844555a10b941d004202450504c03c00741e0b09d1003d40590540482408284d650700c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 372241052 1250 372239802 372239807
    0x50f060409061215090c06030f1d03040314010b0604261006080f06071d18041a0a0c090e070c0b04050d02190c050d05071503020306010e0102011e0b01 66
    0x55901010200b0320700840800c00001c42d036a8211014000c05200444480f50045002203400300c4100074180002544200700e600d00940014141c1d082c42c520018001d00401022040c0040c100e03501d241a400000e428070400050110034404401c00c030000b044815014070220f4014483d6019032075240c840340e845202c0c1c0803081c91140c5040f00400741a01c920800e280d11950141c811401510020b008080419100403000500c42e0302c502c0f01d23030340d80501440740c0e0484454500d8980308026003017208403c4c9a0b2a43c280803001074080c0344916001400b280301403980801681010302107002c0d41e03040019402600390b01c00d0001054078900b407098103154503090b0f010b8400b0201c0c940014210010441000144075000c00d00d491080190340a82d1810b01c10030040c40090300e0390b800000d000c000b030401c0030b00290802541c2e0400742885001120501030710f5111880040b01c501d103031140041d03000020080207503413101118003800000c0c0000d10500d2091a07001d0034104c01c04100040290341c1e5100c2e008540c0c07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 372242302 1250 372241052 372241057
    0x60d02060c010e0723010903030806030312160206010e090303073c02010b040c0c12020f0a0b041707120f1202070602070623010b0a0507020a1e0618050f06 68
    0x200d440020070901a58000d140e8a80c0c645100b081240040100c1e03401700004000350980c0700d50300513501c00c050355040d40d4081d520b24002800454040c8820302c45503000070b000c0702e00580155000c030180201c601c101d0783e000345808070582008020088030424000411800016240c1066040c00c0c11361a0041e00740700e1812203444004619005114051140d0200d50307041d08095940140354001c0c0151803a0f00d0900c801d175015066140c001507600d00d0040c003c10b90346d201800c2030001c41c2c81078402e58072a984140740b406d43c26080a40d04445842c4c01c3c17008001c844146403408031071045500e0b0a1401e1a1075010107280f045125109014110860441561013000c0101c8200400d070b108540303404007410305600940001c1130443e2041c2c40d0070010040030b6035041d132a400c41039000c22140001c4c0c3c01d0107180c010320f8002c800800284802071054000594940d0840c40150058000c0e000700e480d2500100039100515922036020b1082040c0303003420703552241c2900e4050311000d0740c0c3c10183c1c0c4c030711501164080c0b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 372243552 1250 372242302 372242317
    0x42d09121b0b13020907032013030203010c11010b030607080c1809010b070302060f090a0f110414190c080a181b230f040506040e0a05100e070e060d0206 67
    0x1c0340c1d00000c0021100f494210f41e008079000b030300c0742e90740c5035211b4005a040390080141150b01810095000c42e00e585440300410352003c20348508500d180c1d89a0100e400e58164000d54804100001140f81d212030091280c86514013040300200b0742410103410181c48100050040d203101034001408141c207000907040c2c088821000f410b003803d190303550080c084003500401e00c100c00500035400803819040481c00d4480c05807113034a001e80400b80c1240d40b9203d651440f19800c03a00360424a58154107681c8070b2241e8650b884403506850307820320309102200e440101c1c104100e03040c1841c0c44a02051241d0141a190380044101c00000f95201007242e00d440780310b46400c00501c000c2500008516010202423034802321251000220702d0a54498800c1209001010105400096600d4003031503d203842c0d00311640100000d40700052000803803a0706410000e140c08217480552001c42181c0382e00c541440341d200c0d04840722006c6c10705c03541002480d07201c002000c0c02040c82200e4198040302036541d03075002c0703500c0c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 372244802 1250 372243552 372243563
    0x1103070b0109020919230a0b030606071b030f02101b0b0c07020405100608071b12201501060306030b16020c0a080105160809030d0515042d09121b 64
    0x95a1b0350300b12103000c52100c8010900803000c4460307100c0a50a240360280b055411680e96141555599024044035802503902500d15403d00350181d9001c51440c0b0005e07000e10700809000c0c580d9803950040c454840d030400c01540402591546803d24054516051042958003800c0c2c1580340e02d802d81c0030302030341c080d145020398080d113000207019810346014452002c40d0b245488034030746640c130850b00350750790000b161a0903e03000d01d04e0744603070000380c1000c0c45884001c098184401c000300007000d200500203d00654010079848141c000441c2001c80800e14010100342c41c060020702c3c02e60b500c0124005000c0d003c400c041804120648445009111040c0a0400603084841150b43c507000680602000e8030322100038594071094070000d070303ca03401e01c7e4801c0038890025860001d80c2003940c401040c0051100780c2040340072a10700311a50b00c4d4001c10f00400300030a46050281c070207089185918a082c0a429a51031605201000140e44040c503d00d55519030300305080e1075458074009075020342d06194001d11 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 372246052 1250 372244802 372244849
    0x2d060f050d0201112a0a120807060b01020a080a020d1404061d28030b060d0b04030c0c0e010603020a0809030a090b0f040504090609050607110c0d02040906050a09031103070b01090209 80
    0x101c1701050002517000340701255001560b42c1e64140400f941641460040d000d140100310a20200d4980e800c1004801c006104483e032080e1243c2718501c40f0b801001c0b8500058002e07010b81c3d40c0c200d5020b410740c8120112a003000c0e01e854075103c40030301100403150001d440d80c69900d9a40c01c01d5503c0800000d103541c0c0c0a8442082c20180d03c0641441040a000858030100c0c13500100c1d145041a040b200690381d48400151116226928140c0340740305640c604a48240b80c02c0c9000c2410103208a03451b00034a41c1d52405a190508440041c00880000305000c0007039209016180403158402443c5086400408009690700c80c1b80c19103443c90301c04e6402184d0080e040c01100c1c8208000d503401510010702610907030741551551407044410003d040c4110b0a00d904c040c80c0101d00d840c00c4203214180c0c607c01000090b000c40350f80c1c0c9203000c0e55130481d041380f903040d56001c581c014035401240039031700d000071500a07502e13249a40d507540d86d020f03c046c010380360055804078448500b921554510011441c1440c400c02 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 372247302 1250 372246052 372246103
    0x150620010b04020705010b1009030b060913140d03060b030c030a05131205040501120209030c060a02010902030114060102070b0f0a052a070618080715032d060f050d020111 75
    0x5011f0305000c401c1c81d005000010300122651302c541000c80a41e40e101c80c04048c80d454081c200504024040c0003508104403c403400710015114490b002d50072120b04005d4281c4060000d4080c044032840d5228240c1c0d0402001000101a4250700b100d6201d00c501e8000a11900c0d050040e50459006540090504040580c0b00c1600d030307003000c0640129542640c0d460b4400300103402190680c0075940034560160b000c0d41610803c0e01d02007001c0c0662100c94400099564929000a400d4400c80d091003d0900341c0502400030350b5a043c45650040c24002c1c40e454548114988130516901c1045194010010007085082034151130068900307104041100c801da00c500010b00d0251a204548248804141c11104180160543c12000c1045a810030003500c0a10300e01122800384414400009040545e41c01c504c80b00000001405120f540000344442c1102558560f404221040c0360449030442007180000c04c102d5403202c102d10101ca50a00c2e0046110704030b62680f900d0304443d10328200307074140311001c000b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 372248552 1250 372247302 372247313
    0xf02030307050a1e150b01030f0612141203162102190e1806060f040b1b0a0b1524131203020706081302060418150620010b040207 57
    0x7403e85030301409401c3e80d0001d0740010003031035514850005000d0500452051000c04041d80541c609603018100400c000c98241c1202c0c007100e0b00380e0840c40801c501c6501c41c1061020f001d8aa011084e0000300030705140d21240c030f040c5031601005103811214110043c480129600c01c0140c42c605002700d020040c41411800135110294204840c91004550a09000f600d46848ac00c800044940040c0608010700030452440f147c034280141943d81050b02080300d8400d04e18400e0080000b000702603015601c41d11482c50380b00e0f503c0700c1044410280e0b40204404c1000c01d084c010b180b03400c00d206461504040c0c0f510004240c14400c1c20104d04d14000030345105074a012050001001240041103d840700030391a0310381c020f0010b800d030001400503401150180646401818241c2e040210b4003058ac4100203654001a0071f03030303c2500324002c4d00c18903039130740f040c000c41d103000708112200d0741c1061028076401c00d18010800807400c0030340448481c1c07812420000740c500394032046001202034019580c42c001c60400703 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 372249802 1250 372248552 372248563
    0x21e0c070e1603050906010303050301060e030c0d030c0203061302063901151e091d0a1101031a03120f04050405010312090602031306050d0b06030403110c06040302011b0f0203030705 80
    0x101083c14240054045d03007011401e2816a640350300e070f060440e400c00d2011250010400c00054161141c29904ca030346503151080103821500ca0b42e241810100a07205141c2001c0000d0100a0300300400b4104000580c0c840d001e0f00c1e020918440c07c2d66030201c0300c9081c000e4440b51900d884801910b201840c00610506410010340000d00100321401c9a03a980020082030403145a41c0c1030904950302c06101c041a2600070400800c0c6268440307101904500080341424203034202214010000d0a00d21980d58150040102c4240100622803801440d08023182d182c0c1541115280210400161b0007038401340441900c0c00f408000c1e0007004030b5a16440d2a1040c2c51400f40c80c180840e070042c0c4001610b52001040703801c03102c810540984842d18000090320182c2040749100101502c0324000501503c94001440c4998000da5644002c0300400181e9030800c1c4000c50070f5802403004100c00d101503600702c034280c0070724000d00c980c2100405090500741406240510000e6043c000002c2d82024070100045 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 372251052 1250 372249802 372249841
    0x706090b10140105180105040b03010609150302120f041401020a080906160c0b100b030c0a0e0103060f0b070f020301060308180109060e12010b270604021e0c070e 71
    0x1020403034680c44004800c2103044182102d4000342c401c03c5802083d03508004c2d440360494040c10014113046c0c42d2550b03014980c00907000315001540b8000c0400890800c440c0c0d4000101203824114a0b0401c1c0141c62030114200818155808404801040400c8170131400c00c408045800021501c8150003440140300203400d460f0f00c40c46110362404201c01e44400d51030020f0465041d255110014125504c0d250000c0004014514498410400003516200c1c600110302c10300e082d0038816590201c4c204081e0a0105280b4000d04041c600503041c44110000714610094400d0802143d407903851b1440d00030303020035400704029015400c041c000000c01039224040c02d641c0084491501a400030740340116170003145803064000080c0c1014640801d8100fa02e100c00c01017030244000300351885844c011910040741c0340013110143d09020f0340030090700308102c0006d4100b0811a000d41c0340441c4031074610102c031410040c89003051800202102a48020080c102c018004000e4940c1c01e071820308110f5800441d91003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 372252302 1250 372251052 372251071
    0xf031d0f2104050307050d05010b0904060606120615110c0a060201050612011a10021603150c02070e180304030f0b060915130209212b020718020706090b 67
    0x1d051030a41e049002510305841003d0018400c1d03d191000700700c10300c043e421098a05550300c0341130020719119900c2542c421400745901042442ca4084000d040c1c3c0c80581c28807091a103800402d1101c0e00025002c808001000d19000526a031300c0b19a05042c44c42c0c0c14032203a40b2a09800c40043c0039a0190001803286030122800c0018103606044a0700340c51304004000d00c03410f00015001c00600d05a00c40c0300004590340f049038010400318074006c0500409070016203020403054038080c5e80d0f0243d806003001000030743c070180c03991500d0845c5048400c107025020b44010b400e0310303001b00c0c6640070130815500255080070318610101c80e1800c041d00c00c00070a445160003664078030700082c5a002200c004c89000c00c00606005256004424060002d4001550003503001429201c0314182e0500e1255032910550743c40040c10100540c502c01d00d804040210401c001d403030600300c150301e0040e000b10b0040c04035803090b443c00003194981c000301402441507210007400f003407500001105101c80d44181e1442214041d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 372253552 1250 372252302 372252343
    0xc171603051b07060213051c1403040617130b15040c030603021014090a09141b040303030507180311030d1d13020d091203060e070f031d0f 61
    0x200102e031200c0079595420726032840304105500000300f5907030050141d4074210800148103600ea43c000381040d10081d500d030800e880c980b120b42c0e0a221045904141180320a8010b41c5000d2401d0300c06003001560341c1c250084082c40701c0c00160041c000c5211131030705942c4862102c440f0319191142140c1d8012218000c3d0060740f825800d407105034040d10841d02030340d400401d401001002ca000c11100c0c0c0481c860034400c00c41d818495a4a03544070145414060010b50b08040740003a64040c00441c2007000402d0051680c09803500c1001d03a54511049805694040c80c0224550780c9040040e40c00701201450f1544030303800c200c800424030241d4581900041c004401380c03616920080e0342101e1108030507810046da10b003081a44145071074403000d0340c0942030503444094205101c02400404a60300c0582c20740c0d1402650410040366985481820081c0c110001c0109142c00c0485006098040705407114050503543c0c80c005c46c0c490b03103c40c6070000000918003104d44031941d030380041d40c450440303845218030f88480 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 372254802 1250 372253552 372253561
    0x8131811030609060a08010f0209090a02040608070f03140103080c060a06050f0607030306080a08031803030411040b0f09010605041a0c210d0e0c01090b03070807030c17160305 77
    0x214014030200000580a0604680340c200400040030000340200354001800440080d80301030038025200d4020420ba401601c9100b02401e11011a00040140300c640d4810003003031000380d412040360b540258191030030b410000c070805802e60040c88543c00c0c0310030401d0780c0700c00001000341c0c20004001e5440458103881c0366131a0204c4210075620140074940d8041c00007000688941000409402e034030b40680303004607020f03030740c3c001c42070804040090648003110b001080203000c1d044031500d400340007407820056186140548038041c850001042c0f4911864460464035081c0d61110005007011500420803021540d642c0030181c466403080c400c1000b2008113070504a072550060056a14411040307000d01164810344044001d41c42040c14902840d000900c04551803a90354030480010070340060082406003a8840003401e8500360341d2281081c10302c100300300000b4662060388560408003500b0040b81e0700e4019403050b5201511180c071aa00c1c42001c0040140180c0840b114a0100388181c078100204c3e200e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 372256052 1250 372254802 372254849
    0x10321030504050c01081e0f01030501060617060418081809010503120f13210b0109020301031109061201090f1703010f030b090319080702010b01110a03110a0813 71
    0x4116000f40541d00314075110841540100e8910f0b40c400c5601c0c00c0e0740100340591040c10f000700f00c2544c14102c4240741d1001802048804d06c25423002d8100c1d4104030090756031216100101c620001c11080c0101d88445a0341c2c10806018984c0301001d42c0143c5403611034520355642c10255500b03501540c072900c01c1ca0000a00c0341000300c0d40160149108800350b16051083c100c4034542c1e40001042000c02d044400000303400f542c80041255980034003100c260f180c49190404050805060300320070a4944108010400034641c4540310006010660b5515020760b05c1200140c60007981150020b4030b5402e000100c010400c441c240000c1051280800403601544d1031609415400300b4041d11840c40f0f440501440421950b02c0c1403607000c44010116403815503040190b1031803554009040001c60313820418403102c90340a0140c0c03101d416082c6002c04400c500801c600d5550003a0030806410720840c01c020491034001409900b0b5086e070803440b00f559134440311001c00900700707a520680c2d10071241182000103410 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 372257302 1250 372256052 372256061
    0x71104111e0901120209060d090812090d0905010e01020709110d0e0a0206090d2a03140c06090607080d021b060a02090604090e03070b09072105060f07140301032103 72
    0xb40103a4600c060058140d940800960000c0e5010794400300500c0311854080300383c01440303c0c0900c80c01e0f51544881c0d40203d907440d07643c80600000b110750172000076801c1c0d0550120b0503c040f10320910b401c1842e10703007000040c1c1c00c1c040d040c0c002601c0302d410300900070300340c1c1000c500602c0c074440c81110401044080402842c0c5800000174000d6200ea0200406222407601c2100503c01d140174401d0038203600d200c0d0381640d5400e078419400038581721500804000b84841d00b03121103102030390b06010b0a030000c00540010a244520340c1c03428464000402c011043c0310f240402d039441c01c582c038103003190345038401100341c0003030b0f1150300b100c3e2000c0c41031100241060100d4002c1e17804001003d0b00d510709046c1031a103114080d2040d480381d844a0301c800e00107a800f2656aa203c00e02502004003c0c04d82c0c641095140d2003c40100c03000c201803d86000400c200150001a0284c1d0000c0300400c1c1400036160117104450b19901c0c5080c0445e0010080008014001c140707406140085203200c0000307000e14422400d5080d03d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 372258552 1250 372257302 372257317
    0x20f0709110a141201060e0a080d08010509100902340b01050405060d050607030c080c12160c021203030a0506040501080c040c03020c0a211404060302071104111e 71
    0x214000c1c08501040c40c01000240e20041403d0301e070508220800000d1a42c08000f640213200081d0000190b4605040c8500040064040e44003e01407441c150500030342104410303c14070780940d10800000395034221420300000980000c0e8030030355035101280031882c078103040c88103000e500011050200560780501c14000da585035011507a943c4581c80c0104010080000804c0b1a811603001262180010014840035100e0441a20002041092403000401d035000042002180c00c404001d000340c02c4280000c01948400d8200c007006141d016548219030756000400002d4014030028014280d0b481c1c040b001e14498410074108020f5903450208000949100b07116500598002c481803140034141508041c400d11014103001d488c0080c40c0c40010f103480e01218094410b0a80505101c025050451503010664800e14060000c1601103015101c0c03482240300b04014158005924010000d68502454680100a10402c0548210041c000c40d640c01045a50107986005000c404400141d00c26281032 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 372259802 1250 372258552 372258581
    0xf06100e0702060a0905070e011e08060c22080f0a1101050414040c17090705040506040c0e01080415020415030b010c030207141f03060302120105090d0c02041b020f0709 74
    0x90307282e1001c03100007082c03180800c1e900c1f4020260301207101c503040c00540340200104902e40f42d16036500c5150790b003061a1900400c2e0240c000400340020812400107541902c0c00e003820a180d144103a21321203507815810740c0300d8195406125840b5a0a03440030880b003000720b000341c411302100d041c030800440f0349219074007030042e13003000c2c8000503401820154000f05803903c060515042031108050303400d0b443c100c00c5611620700d0b070100000b8007613810607000d40d6402a00655007444030b00442c0728050241c0001f0a103007410807800100103024404285140d07141e504880c0300c1103583c2c40c3c0360801c01d02c54820101410380401d00b448045c5da0f15501c284006100b9540540c080c1c6201c07070510803074211454214212a40c408228034450b401d0881c800709200c0300340303155140024403600d58418030529201d918000a200c4c0d240c941040005000032919015440749031a200c1d564428600c0058000c00030030303806544610140300850800c5400041c24806019400d085030002507030340d21004140c40c2c40b03030030f070059 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 372261052 1250 372259802 372259813
    0x71b0203060a020f120c22030f020402090d08130608010e071d0301020403020a121703040c0504050a0216060506130e031209031626040e1b0c0f06100e0702 68
    0x1d02c00140d000d005000d8141070103c2c941088000c2c0d44902981c15a0454a090390010b00d40e4003020886056051040d81c180b20002003601e036884000e1010444500a801590000b070069415501c00041c80c014990044219440301e210280440300e0075003900a290106050070004903541a602c20054420b081942d595003008c504500182500c1e0080c0444da0b4042d9028040400142d4813182600d0241051030815100b81c3d00f43d04002402001c160406844845e081041c0404120002c0190040e41c2040d1400318181d114541d50070001e00c98110070110006c0250001c00030041e10b034014034003601c0700b02c480400d4003500307401d400c2c04c5914200802c03099900400680c01c83d4544401c2d416804200c16050700e00342820042840f036001074040e02144d4881110748080d00502e126854040c600142c041c0050900d41840460b10300710303031b014140207114001881c84484101e0580d04841c20714418405075150355240c61a183e40d960002d843e5000102c8030701801141c2120071003045442a0000d5000b1b00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 372262302 1250 372261052 372261061
    0x40302090f0103021e0f06120a180f03031104091a010908060702030a0c05070803040608010e0c0906030420060c030408060c0a0219060f0c050c1905061b1b0105071b020306 75
    0xd142d1707400c0d9142d02d50040d110443e000b1482c0c2d1882d0145c030490300c000d00307886481e14203201403104a421036507219181c808141e1070030b000700c0d03030b48076204403044e505007000203083c46800c00c81a114005c0c0d9201c1c00b071050802c04201d40040c00044400b102c16001e03207415480640b1440301a49507107084401c100180e0080c0001d60f892481031500f01209400b601c00d0755a66a292000103003160310980000b80450003640040000304081c0c416686e200c03400604103414044007500041d428400900302801d00307465883d802243c10a400004240c1c1c0d14000c0c100303552240041001c5440c1d81252090110502035840081c8080781407100700e414001e0341380d0140003c2d0854940e801504020150155001c0740e96480e010f00d291101e02c102c5040307807015100c090301c0e181000b016519100703403c00303070f81001a404103001d80002e8000800740d400c005515090070072009103003040c880c2030044c071782826214400b40b021403400110641c00640148500d640302c0050540b491281c0056850410009400d0b80c005800036 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 372263552 1250 372262302 372262339
    0xc04060e150a0b03091c0e060403061122080c06071e1505070801030c0510021c05120c0409060506040b0306040209041d060609100f0902090123040302090f010302 71
    0x15011440000d040c2c040e1907407640f0059995401c1226400c02c0f43e0700882000f070004d9004001c000c0c07021090302d00880c00740150030210703100d03025070312008103034688980040d04c1c0d880c110000d4503822410701c8566036080c1c51000e40c442844c0c86511541040e80a41145e0700c4103810301a040b03a02d42d41d003068a81910601030001c9500701d0f01020002e4640c0e2081c0443c02440d458039015150140c41965500b440d40e504504017901264035070752205201740a00c1c1c2100d85030903000300b5686140d03200c401803d07140031480b0350143c40611404206081900c60401000f84a0700380c50b018200340c03607402e40100080b9445209008080c890740c000c11540c91001c1c0000b4886203007030b0300207000011002d8408110607010103801004407032464941d40d86a041002004002d040500070344d58441c4008030741c4074540b440c003241966078003d80e01410780420740024001109074026207a80d10032020415102c44d202d02d01c07009441e00c903005400224811144100428000344181101034180c0341c005004140b4035400c880d8a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 372264802 1250 372263552 372263581
    0xa030305101d0c120109060305120c19050304120c08010506030a0203100f02160501020304060c02010605010c080d150e0702071a0301060e030c04020307170105181b0d06030c06020c04060e 82
    0x70082c900f001004501e01101c000080302d03000b000d00050105049046150590034440403249030550b8034410300c1410803c0c100059a28202205c858249096048a04200f0708601c61030304421809003690299600700503400051b402102c000100030085500d071141055250345101c94083c0d0f05900540c079103091400c480e40034183c803003c4c8160040c6002c824a1840c050140703060803d840513540401040f050103814010150340a010b4402042264240f900280005100d110058980840450320003054820341c0c1c460f10101003020712204a8680c0d4016044046204840e510014051500005001301541c4001c410b0490041200e0f030840c1c1c20440700300c807032140d141e101540c503200e040c006400a4503648025400b410341a40c8805c000c040d25107131404218030603400700f80100e214450b100440104078000680041c0c010080d070190703c0e00b000c11403c46000f402602d201e00d901e030070800810050a201d9100807030300c40b40c0a80d0522a0302104000440e401480384000c0649001e00080d03d50301d030b0850 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 372266052 1250 372264802 372264811
    0x80601030c061d0a150806040905060a0b0f040203090c0a120305040603020a030212010801050117060907060c020d051504060c080708070f050c0714031204031a07090e07020a030305101d 81
    0x146001d45a10443c001580c000055000380d030107040070042c000c101c551101c282580304109540500c9203074090350b5a107598400c0241481d0746140e80340c2c0180402d80e5506080c400c9150014020354903410302070192512802c0318600d4510441a144000840c0099031880c0c2e50072541640340d1505152038044103030b01a50100205000309542040442c0d500854815990f018080b180000a0250b04100c680104171071026841c500c140d00c9402003142400b00002c41c50300b5030f291403402c03407401038072803000c00e8100360141c80003880d038040c11240b60803052594034042c0c400c9010b064244204410318500b9520000c081d90500c000542030000034000901a542e08006406903140640c0790100d031541007400c081d802e80241c00b090090000f940520f00e410001800c403a0103100300c1a10301032440d52170603058001450302c0600024a9800121868007a11101004001503240300b5241c4c41e09100c0291141c44c4aa0200c021a1410000c01c0c059240140605d0903280040840741a03200d104505a03c0c0c0c2a0051 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 372267302 1250 372266052 372266087
    0x509160f12090c1707050307030611070c0306050a0506060313030c0224040504060602070b0d050901060e07030c1701270e160321051207030b0325080601030c06 70
    0x41d08004a050a482400142c0f402120b404210a00704856956402d110015024059100c0e400070710041e41d01080b0642107990240c0001221066001615950701840402802000c01000000705000e1250081c5101e00083d600c100015540c2004010140c00180d80b02040507840351001c0001a0107110701280e4103000922001c400c408001c40300c4000040c1005041c0b5403280442e0400c17017400d09004032005800203001819101d410669142598007a9031007629045448402207001e15000b0351041010b842000c2c2005200d00d01000098007400d04031002200151060445026104018113001c2c1071301d005036607188080d00110006130b61034030b004c5010321036155918443e0a400d10100a0742c102c41c0b044040c401c00c0146181069144401280c3c50881e003050345154804902e903101d4200c03846c9500e000802c02e15612145c008074024184c4601c0d15800d4480c0a0307010509516201c10707200400983c600c4000d15686030b03005591544020720008145c601071907014800e0320301980b6802c16010004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 372268552 1250 372267302 372267317
    0x3060301141503070801060605030f0417030412120b060a0c0c1d01061715040c05070b0c04090c0c05100e1c170106110705010e150f03010503070509160f 67
    0x100a5040041d9054600100400d09490480359030304003442010000c0003500000c214041c90810042c00d107100080c180007584000c81c2c00607041003400300003290781c1850507051545920b001e203091000c43d07100c103004a01140c20302e892001428040d00800380d807020b010701000d00700b076065001070340e4111a210040b11480282c6001080340c040010702204042c000400303100d015458540058030110b1140701180034000481c040082d00c00b510b0250f0003030824203480c0080c060120b92004c584602036944014220320030071051121400c80c0740098001e5504249041200207207514080d240e000300b1001c01400c90b0481c1e00101c548611985c00000100d0301441030700c1d20072002004140a078885820f005c0046051030000c040c0304040d049000c0d0142016080402c10140d45903141543e4446a1080c02d0400101044019040d21a50019140001114621501c410024003416541d070024058a4002e108114002074185072884d121801040c114164640b00b40d407084049545c0100003a0801c07e10402 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 372269802 1250 372268552 372268571
    0x9020a06031512050c040e0a03020a080714010f05061e0102060402090606160b0f01140303070b0702030d060f080d090b0d05040f1a04050c0a0501051803070308120106020d05031302010503060301 85
    0x7406103c0c5402e2103072014200d80590141080211140454000410380c00b6480c201c0c0000c2c0c00195881055400401241c0c440170f0915124010206080d5651030315420000202c1001e20543c10160040d1012a001c10010645410302041200948001401684808080703005414029181c1da04100058007191a041d100039940700d1060300c0010072652140b0500c100b003201030441808501500b20752114003491f0b01ca08002036903d000d0818040d200c3c0500d00085140c01c1d00800c102c0d10b07900500c14040c001035550b0002007652003194402d10f46c1c1c40c000c0088000003984500711120940d03150790011410b00b00042103440003800010411184034450b0380da2000130480218084d01d00407041141040700385424900181401c40c3c081710707207020701c03407904082c450342c2e03082810703280d0f008000c0c01401030103008032000901d0f11009030310180c100c0e4000134100c00181810032200303043e20704580850311241000f48040f1024441299541c018502107403c550066102e00c0065410910040021805551 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 372271052 1250 372269802 372269819
    0x10302130501320d050606040b0304020103020d0902041104060207090509060c130518160305040305090112090813060f05030103050703060b012609010c020a020901060c033e0109020a060315 83
    0x282407600c600684001314491121a4160007002c1d8008002d076a400e08103031805249840c14000940300038181500841c00204400003907224800305034000300280324840d003d0303081040c0c0c1da2103409240010300a212001c1451005801241e000705060341c0240306d04d50351042075a000390400d4190030f4234910740100000712a43c2c2c140f440e4850010b40b83c810511800c01890384400d901c112a150024982037004100200740c00400f035841544d820f08180d404011602d203c07800070b03e4614001001603402044103410301810303d403d001511b401740c0f40c0c56092240c012050716a4082403000030201c1c3e01c20b003030a0002801a400c4200d10001c1810138145411040c0500c1003801d07450f0380c0340121402c5400070020003400c00d01604d90115018000fa1040310046c1d00400d00d03464050044205000501d0780341420103100b0703001c2c16070320344241c1e41e980c003000d00c2001e82001c86444486103051000d0b5030340c0103410700d00040c49104c0c2c1a07540244190442d900e071610139800b8288042080c14210340d001b00c0010480b0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 372272302 1250 372271052 372271127
    0x30f150f0b1008040c061211071b080f03041e15020a030f0c150c020a0803130c170307110a090e0c0405010f0510050d090c15020606010302130501 64
    0x4034040200e40354004034248140e0320640000001000110001c4c8130115200f10140c405540542c505103d80038429600c11002c1c20714600c201c1d04070701000a203e0140071041000e10950040b408a0703031092903a80c0b809690f1032004c1170150080360420030080003c08840c083c00400744c03150503806041d2603581d6450051280040e20810003513042441000201644200b040070078001c51300b0302904100980d218a440000b803240003102180d0b40c1e560560040e07000708920750000ea40180b000d03039603240c50210107151140703105048030002481c07a030220704c00040440c0c42d01c2c081000b01c025410103200b9220200061104010705803c4041c1d45804590001d881c0100c640450541005212048400381400304590341603110f000c9200000a090125035076440010856100300e141c00c42c0c845146040400003012400030041c0748014017040080d01402042e805204801144c0a46d480c03695013100660a1344038201c140c0f440d00d40000414011076001c1c0010000d6040c440798001c442c0380c680c1c000d148003003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 372273552 1250 372272302 372272321
    0xa0605030702010f18020d06180c080d0203030403120507170a02121605090d051f0c0e030c0a210b040c2405041a09031e011a030601030f15 61
    0x800010811800a409000c1c072010032024410411004121840c3c4450302c42c14200d00911031010400400103010181d0866a4040d00c2d40d945000c108401b490b162081800070300c542302d45070244114071b280050000c4262841a038050701c070b9a41340782800c46944020308000f0b0030741c028024103c0c0c40c0c80e01450070f021654801c1c80340c80c500503629900001391100c1104002c000140381c0ba0180d040506540c0e124094421300302c010f6551100e544140c0c6442410002031041c01c00c000041035284858203151504411140115a1101c0f20b1501070a414191508814002da03908a003680c14200300307290502860445440f203030481d000205505945400c1403c10035201a190000041c0e01403155009500d04103107680c054403030702c001403108078401a0490159100d98003030a140b1340b01c031030001c44c546400c071103030b0410003400d480401c0a40d801d41c010900001424040642c038001d240f400d2040311246154101034001c0084c0101e030b186698601100d05902d404440450b082080c00350610039501030b04064 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 372274802 1250 372273552 372273557
    0x30e0f06071d040b06040608190213090b0405060a031403070f0507050103230a020d020f1c23150105070c14031516030b1f080a06050604051c02040b0a06 67
    0xb0006082e803201d00c4040c81c0400e05110b07034070784058038065903901403c40b001c80d03089003086801c0e80d81e2205480205a03854400d03601250000408012a4404010070310603a070411004002003038071f44050000302c860807140b00da08405201414008200d21103030106030720700760320b00305d0b482c00020b5950b0001483c1c4030345003120729a10080c8240407960305801143d41e2210f600010101c5c2c580b07040c2c200000701e440a0310b0814403507400109013044440d80e4049948403550541195581c51002c071040c0c0d00450b031488400d1800c0e107007a02c03001e6106051083c0f81650091010300030300e10303210402123820b045c00362003c8506006042054200048030034113580e0040002c20010286050204145802d0200983c140d0740d03a03a10b40720030031801207181c5203450149601450006a8005011b000c0b0b10038010710721050203c2514020a20039803681301d05800c1c071644000ac4103000580d6a80c003030201c903000700d0041c150300c0b5085071043c406400d001c44c0342e0b000d9980004d00c0800c1c09010f40b8040b85c4007418035000f0100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 372276052 1250 372274802 372274817
    0xb0703050319140c0a171905180a020105090307051206040c15090e10030507181a01020325080310090b01022a01050c030c0616020f07030201030e0f0607 67
    0x100001c1203014a0000c10905004101e0820304408000100402c0c2021301c07400403402d08001440345da1002200000d0f0080e0403042c1c1041e1a54440c5d2481c0a544112a14103003400200401c1100100e40c105001c00c0000305550040e40c1e0056525421150701d07190903200b40130300001c050307071200031458444c080b107800703000141040e00300510300080c1c43e00440008500c03075000d00c151541c0300c56650101c0302c86544440d203a4440b030780c10810791052030740084c21910817020003285d40011407210141605400c1403c120403515070b0000700c0950100e903206070140c0c00c10321840c0300031041c80e10a042402480801e40c142000290b480c01c0490700240c4031408103080c140d000b4042c040e024480c9000c1200c2c01d00080199240c24460099100440c1c000c1c0341c0040d6000842100c164020b030191030340481c4900a40703131100c041586595440000700d0f040101c00000b0300c001d466a5001188054580444d60082d020450030341d0015030283c001021488418400c0c54001880c808080c4000d43c0545003a542e12003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 372277302 1250 372276052 372276061
    0x3031407050310231f110a020603010b13031401020a03050a1404080a0c0c1d0f040c09050615030a060501030b12060115020102071e03090e070c14070b07030503 70
    0x582288000d200034148a81081840309181d5150305503000c45070100c0c840c26500c040c4203003500901c010444c801d40c00504058420b101492064040c283e055010761b0380c0c4010700c101880300d540e030340b4800300003030f410800030401070010720079000007080e441d000515103180c5d1039039a44e104020a00d200203200040d035404544076014680c03600a640d001240071900f84148107104500d4001c0d00005040201400d40c0000c140450f54051600711422a800c000e02c0300c58956034040300744160070606c0410110403400300018500382c44080020b401107400030501d00d03520342401c492400410300a864194001d0708818000c0a2000c0800254400e514406000c15081c0c5418009019240e0b00c821881c491a03041382e010114403c00200141128440c03401c012125800e8071040e40240b141c0d100c00381c00a0f00c146204102c1100b03180c40c1c10000303482070355040030302c5a81d203e01078407101040d20100000741d0200183e0002c0b44690030344201140b00e400c140c904869854a26aa0b00e902401d03048010400200c10407 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 372278552 1250 372277302 372277331
    0x206031008030c071508091e01060b0c060114060a080f34090506090325050303161a06010917070e01080a060b06030c040314010213060302070209160516030314040303 73
    0x40d05c8105800c0c0789030f0300e040c0882299150700034040140c4000ca0300e900035a1625100350031920050200c140040d80d0b07881300000e100d45981d000d006400802001c2010040b141c2400310444410705555550702001d0340311352103044a03502001e00342101070000046001c0c01c1221004600e00000070108029070030a0190f14003804402180d8800351240c0018414010151404519615411603400b15031903080404800701c0344112460f002982c0521020905150740e14440d00000718090044110700407120301d031055a0a1403004a07015400038045000c00c1110250300e608180594009809441c80680c0710b1807002c06c8004264031119441d44180c0841e81130040c54490400c0245050310110f180d4541403910323a01c540710324840240201c11551891002d034900794117880e0442c1c142203c2c10703101c030340c0c418004003c1c2d04400341c00c1e0300c40e15810b00401c80c00c6180080c542003680640c0c8507075040c400d40c41c000194200134107000b5400e0584524841161030620b0840034030661007528000f9045080c180503 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 372279802 1250 372278552 372278579
    0x23120a1a0f0711120903010213030f021504030804050d050c04090606150908070e06030f030c1b040c0e090703060801060f1502030c07051c05010c091a12040206031008030c07 76
    0x1000c02d109030310b141444240c2004c138010110100e5a560250780f0052040407a0081c0300b41210300b10b8a600d0980301204001d0509810714015000300c488105d90b03001401c46002034440c83c803008210110800041245040180c0c200351003500403c250340c0300e82c0409c0007040946a4001b02110740075031340c01c414420400034100740714003a0654a02005468140302e102d907510942802601c01041141c1c0001e0655502041051800d98022080e682c440092440a1b9911482c3c00c0c82c0c5036aa0403020051107050a151264041940c01561080404200712003030001d41d4101511580c1015291071002c5580c0d002401402c00a01400703040800f4140303808649e440c1e283c01c00540c101190000c108400340311750001801c9041d40e001b04c4460040c60104c170040c94030580032403401070482d401d26610790115604409a03e0403602400000300704002c0c0d0426941d603d11803614450040d500d01d00c0031401508007000a1a4401d24030030084540e03a49a00c5c4652540e000280c0d2980f0550100340305100040305501c5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 372281052 1250 372279802 372279811
    0xf0203220e0a0e1c020304050f120703030302091f0c02101b050a0203061312050f39060106050a0c02060904110315040b01090603050a1104060302040302040623120a1a0f 74
    0x21300d002d18041d524020f4881c03103540310780b0f840703185440004225a5915511514180c0440040f11442603a030b1901801070340060b0040c80c0700d00700c00710500c1a08000b04820011203030050380c03403900c03000980d401c0110340703109211940100f2030f03010300b082c402e01d42109201c1380c010300030401080c1c0e241382403041518211009188101c00c0c0c0b188160100003a402c06415418a05103040c90354440d40040c0d82c5040500601451102c103502e10782da01c44114000b11242241c02c0c0c00940c100c2c4803c50b010150640d1030400303104180002d0000c2024611641c421101c03020003500c000d12540c5040c1c10031001905440901e450740d01c1040c400814440003500c840d03170421300d4610668003031012602280010b8001c1c022441880241a00d071000104000f106034080100481c01903000e503152a202c400041c004e4100b404201d01807440c222011401241e4901501030780d00209a000c22426810b1052005030040b403006008075103d008564000070304201030740c5010030048524481c03546080d9007150040341e0081c2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 372282302 1250 372281052 372281083
    0x1020c1005060a05060f0315060409060e0601020115061809020d05100f0608012303010c051b0708030403030c080d061d010510080a0b0a030c030609050105070f0203220e0a0e 76
    0x103c00c1055448503001c0d03400c081680b001080d125076840da006555203000040c015440140001d022801d0951a48448182d502500c6100c83d5070341c403030005a00b00c4203410202907640e207404004104191113101c9554143c000e000d007900350b442d61248603800344d07042100305d40c0000d511503080081c1c91420b007201c40001c00c0081a00a4070504d082405069a0018003030040c0c0044000e1100c00a03041043d10000c0c1128045c0080007030000c54030300249250040901e00320307050345140200c0100e007000a520b00c00d5411000182d40380901d03656003610441c1032480101c804403024031070291100382c80d100c0c400090104041c0d4005d0641500c00350421420141c006902c00d03450841c109414540c0400141d038881240701001511501101c0029085649940001c22540032040084100400b6800c00c014052081c0c000b803000f078850020682d0905001c80c06000164001c2c4500b41e40304004552407540e0f22000c40b01e040009455004082281804480c622180c5131148400a110901008a10060f0110760b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 372283552 1250 372282302 372282319
    0x5040f021c15021206030a0b0402010e04110d0605030d0e01091418010602010b13051905100f1e080601030b0c031e0405030c0c04060b0d05061201180303060501050405061c0e01020c100506 82
    0x62391006c0310484080c1c0041e04011050400d00460380301d40c0c5c0101034099810110b1327070702c50106400e8000644294021540240036004401003a640281c84c07100c80c041c0c050711140100783c10b0158480704209003c08543d0302c03141ea1074002954040d900c1e4114041e041c150300100c0c0307000088090003420309000c103820782003a00e00410448882c0c00017041c5079550f08511b0011842d0340718841170101d1205242c001403102c144035600000c121401c0a400d2104e60001070b007490310b4641d00c0c0b1200d9240c0200344400743c0212808000102e4140310b150055600031007242504c1508100003210540c00303481180c00f1100e0b03500001e521100304104005400000b04110b40a1109a00b829807c51f0300c1d000b5014810742c1e580d03c40c0040350b600d07511010400c0a007541d600081100d07002403c860a0582841139055000c245001000f01e03040d40f240048905846010706110b180c0344808000b0342051500d01d58082e541603803845201c1d401182800101b0002008a00602c006034440c0007400854101401039445800d00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 372284802 1250 372283552 372283573
    0x11210906280504030c020402030a0902090a020405031e01020c0d111e0715020a080a080f0a050115080405010b10030e07060203040f050607020a090509010501170105040f021c1502120603 81
    0x401d15980c00c080c4106001c245503e50380740555061408401c0254094008410460802c069034003083e040d60084588261544500c902c00c1d00b00d00c200d005d0b8540540180c503007109068012880302c4252505a80010301e0030702c408040e2802c00a403000c0640010f09096001062240c040140b82c1c040600031042103030010101a4a56403800d0030321511044140d0310f0b0040700b04600a000300b0b00d240781c000b80026a00c50368400020700011040340e1641074aa0110049100d4011300e10586060f160034401c504028005400b0a0f02c0e020b800420844040d900d4000480c5907445282c1c20050641c4030761404071741044541e1a55050038095080001158802c0c07100f00301c0c4419400900c2d08460007035440f6503507540346001089204050b40c0100d00d107242403a0901408403015480315040750703104148480d900d55040c5801d400d868040e900a0b208008000c2100f000d0718016140780e0005c43d550001004c00b2030b07503580c0c100440b1090711090314025030103d00613100507240700020758000400c9000d02160880c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 372286052 1250 372284802 372284851
    0x30c0d14030720010921110303070210090f0501020c06040308130201081b0c0304120302061b190917010e0708060c030c0d0603021509010e0109051311210906 69
    0x5038212100c07070b00c40c814141c01c09015003984180170799a04003000c0424a1400d130098206001040a08000900e1086e14150948004410360717009201c0d99002d40344001c020001107001d018006400c0d2944410310706007200042d000d100070030080d8141e2010f8001c07480c0070304000c2c0410341c0042520314496290421000182e07031003100346601260700c5058200e1142c0b2000211854003274001106102c0c4000640410701550000001524500c603608950301540c6001c0481541460320901156001c2c040c800c9009000103d03000000c12400c501d840d0014940e520780c42d80810311034001041c8680d40d500c00700e45074880148247e0001d0099030006100c541451081429a440010040a40c41c2404601584c1c0e103040c581090300103540080012001d121300c1b400c2e821040c0e00061025011803810b44d6040e00715401030350b2040031508010645851080c03a0a80d4501408601c103003c1e140102c00c01101d14070700c596070702102d91131110380d10441c00c0786080400103182c1a0003402440724164903840c940519036 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 372287302 1250 372286052 372286067
    0x40c030f0b0405070e220509060f0c042301030e011503050c0d1101120612080c0c010905030309010309051e010b1507110d150504080a020709060e060f12030c0d140307 73
    0x1038069500c051b0030810f100c00703401100c4010b038040141318108014481e1200001071b900c0d018880a141568050b1a400c03a00325851040340710388090360051420f004100a514aa8a00841c034181008509104556030080c03c680100c6549000c0c1e00801e1014020f0020800a22552803029102681529003903104d9038010240c21001c1410000101500110038203039400c0500106020510915400c142c0c0c6444486500000310f6510a84a42034100781258455801c4804035400500650310300703000400110060416040d0941c0d0500c5091a001110441d41c2030242c5e403100c444c800051b812505200b002024500d106050324000001d000d001c011030614048081142c40446903058a00c182e071512480f2903403015142440e443c13501c000c004c01d01c0004001403150603255400c0d9287e00e6142c412150854845006c0c60403507501e83c0307000800b50b00304a1803010342a40000c00b407826905400c40382034655805040815401d03088060000750594200442014030160080301c2421803504034402400c00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 372288552 1250 372287302 372287327
    0x30313080304020d050a050109020f0306040209010303122702011103040315150503060f01060206130c09050a0e030f0c07050d2103021c0603170307021b010e040c030f0b040507 77
    0xc200080801e0866452182050540c1c2e404000c0c0d030507011190400c1030003010344107c207a009012521f440070307840c0b401080c03042c801c90380108a030300640d00b103403412181c80c0c0801065081480e500e0b520100700811031110310704244c40da155031401e003c15070f100042c03c0840707805081816900a01090000a02d8100003511208615900151180c0020100d001820381c65001c40d40602640d024450103481500005060301c010341c08035011503d4070140808603401c840070143c1407030310400d81488002c0d46600309640144203081c0101c0d00d100000d05280c11340d03101904e9142207030000a6101c6180c282400000010b00040311013044000068031419914140da13080c402d46280316010030b0380b083d8001c0d8160390411060248440d8100c0180301003100918079800151602501020790201c4080950100c0e44510b502c3d501030141100304d40100c80c2801400f940040c14003001007410045600c940c4500e1054110079034000ca000c2c2c1e860f002450458112043c00e030301550a003000c006140c1e030401c041d0700f0036 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 372289802 1250 372288552 372288563
    0xc0203031329180c010f031a060307050d1422030903171b0a0503090d0305070819180806011a07120302120a09120c061e020a0908030313 60
    0x209200346450358014148002c1c0d2070500a0451001031900d000b8148103101c0e00100303484580d84199090620b0341e8104404240b40015000c4503643d001c0c501c81d070451010300664108100e4002203020001c2e0081c3c00c102c03070040000703601045d90f20b5500d0003801001003407000c50015003120700b450044034007980003140d644000b0b110b0400310182010721451101e4001c7d604141202d1391a107500c01406129808400c10805014041c0d450000f105004a80c50355441d030700c000118541180f600c144880078558102c04c5d400d20000748500707000705540000610810704c0b003601000c7d06018201d006810861b840150701c1903542c0d0b002060005102c00a1040c1c192450044010090b0381154100f420781e03c11440014151080c0090000089406802400c4442003d10380203100c0d1b0b0302d503840e02d4111044202c0241004054184459489001e0841d000c1c03400e018410201c0c0340b0b0300090a40801c011020f1846840e10740c0018500ca40c43d07030140341c0c0740242000d04040d602d58208250030405402840c40d02405 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 372291052 1250 372289802 372289831
    0x2032404170909040c0623030f19053c040305031018060f0e040b0411120f070e07090303080f0a1d101506020d0804052d0708010c020303 60
    0x44440c421040c2c600030940104490a1450130b80f800014010f8103101e1003000c203c18030000b080500c0c1c0700d03070590b20690000b82210305656130000803011169001c0c1609440c401c0008103c000712059008071f51085401841526032601d040d0420ad45d019440c0300705412000302189005d5106402c0341c50b254100750545010b035101d80750240c408d20010b016502160720200740300d03100d802103511034200304201c4411203114000715964895003010407200700c80040c06803204400082c00103401c0741e250107040e44081c1246040783e50560703841d0f181140d896010174880c2d009407c100050768003c40ca0513401031003450480042807941c0d078003800519000d8a4080701800c2c1c240001c600140660100c1141d101762102d0700118102580c03459200d40c190200101100d00b4900302d590b65a43e030321003c800f114050ba000302030701001c0403005c90b40c3e094007510480341d502500b003000c910581561001d0007614400013050341191101d00a0301e16110f80c0e94800340c030507418407407040b02898000c001c3c0da6014003214030050703 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 372292302 1250 372291052 372291083
    0xa0504050c0d0606030c0e1b07030e2e0e1e0d051e01051b0706020703030b04020310092a0f031b0804021305190b060705031602032404 59
    0x34204241c0d9641c180d0400405484079043c0301c056040b40003107a000f01d41c4101c0803030320303100641c501c04000c40d0300300d51400565000c801c03160583c50060403641e003e480d00c80c1c4460858400101489078120030249084240d0000c0e0000340811103018400200501700b0040350480341c0041480300c001c44484003085c040f1400200402d4a0b40f01c4070b480f1080d80801521941c8030040d0704044a102c120003da40b51750318000001d100250200b581d1240c1100b0b8400582c04c001495036281c019510240041b4100340d20b03004440650340300c074000f442c003520800403890317003881c140154a0304883c2041031351101d0050a00c420003007080308441c8401602c5c0540303801480c2914201e01680640b2015039040036051046045408031540309103c1da024a2080f60f03501c00c60845005144103550050f256040d0000440c40156000d401c07660004143c02409040702c0d0418204c0d46400f0300319081581c040700703c0d03070065503003008500e000d0208042c2500d0050242510b0308942040b50a4982c00400c001c1540e0414890304 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 372293552 1250 372292302 372292313
    0x2901030b010b21040303140702030a02060a020d1d06190b1c05030c030316110109051216050703050c040b09010e010312031d0a030801080102040b090409020d0b1e0f0105090a0504 78
    0x40b0004000c2c60f402501402c0ca49402001456155041031170684804045050a40b0200481392403e04031341c010b02e0151541d0b0903040c02940015807000d41c90f83e981c03a2408100084640d40d1f040780c2843d80207001107140030104c40ea603441c1c02c062042260b501e008580b038815943e00c402c141403208510700a0505440d28a8250710b10700c074801e603038803a0744804020031440e40d030000c0300c051912900d0b035110031030540212019401d0360b441070001401d50308036a6401d4407100301c0740c01508800c80040c3d80a40b4040d01500c44a052254503007040d0703440c0e08100206c00903400e003030080034a42035040d0303071702d5000350b14000c81c0011840041c040144940314004000c90080e210fa041408640d0103416010302c81403080201b181d86440110b411400b0803000400003560f00c03010700c2a2002c4448002000d890580349504000c01440320050481e440f502d024140008110604843e5119440d4844408200000b005c1e11149144009201a52008141c0c0040c0100c1d00d84500700f43d0024209000403a50303482e075180c007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 372294802 1250 372293552 372293587
    0x16080705010c11030106031406091515040b0310090302060a1506050301060c060221040210110c09100306110a020c03070302010906030209030c04020f0d0515060304031d03030301032901030b010b 85
    0x32300f00c03c0d41c003c18904440780100ba5140038902c00e0003100c00317601e680080d109050b0360464120030842e0b013406417a1f4560405810051074514001c0944200540a5510341d0403103c00c10020740040c2d110400300070319208148109000003c01c0403c0400e4640707484802441407105005040401c8203c4070750004100350754055441d0228031750220118820800c001080c0e00c0300480d4203070310510510500403c024080c1034501c0e2039050300e901400744040301c20107101c0c0c40503002e082600c2d040c0300c80500001146d26481642c5401f010000902e41c0d4414484000b40745c0750303106040c2c038881d4004010403c0140e800501d1102200d0203800d02580740c546040010781004403d551098106000240745d5840900b15030080000850074401000107445140e6500c1c01c2c0c0340900324a90b0014020004100402d0140800380d415440e0303001d10003038002c034490101b820f47e0802ea00c11200311350b070a4020090752000c1009000d06e00e10642400c130035985140c50b103041150042c4207203850010005881030340340e5400001c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 372296052 1250 372294802 372294809
    0x13140705030d050304230303060609031606090f0e07050307080703090c032913020906030304031a01090f0b010903020f040b062d190318020306070216080705010c11030106 75
    0x42c1c031440085500041c00e1648115011100d1000b4002c40101d6540c05180d9500542820700045085544120620545134002c1601650501c2000c030043e034042206034544000e001140c0c0d43d0f50603646805442c8030ba54045070007400d04444e50804001582d41d2010a60b5480307000c1d403408071200d03112030000b81d004101c900c901420340c9400403404024003810a5041c250810800c0d0309210300c1d070300c100480181c410b040e0380080c0d61050450480c00035207000c1001d560043c200806a07441c20b03031344c0d956481c0142800751107800703100f00d40c0004101807401031168241481103510103002c0300317014400007880d415a50000a00c55010042c0c00151911181d00210940c4809441a41d880ca21810000d5251851811020300c1284d180c1070401c02601c104241c900440680300140c003200e5a203802500a00444c810046008200040050160342c0802155016500b15006414441d0316000c0d0320031651060742011060b6880142c00f0001ea913404601c100d12240c004030900124400c0d900040d0140c1400d50 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 372297302 1250 372296052 372296059
    0xe070509220c0e1806090106030807120e1806010e0109061e110f0a0203190308010b0309010f06060c15060b07060906020d060807090608060408030103060903020f010f0204030b010e13140705 83
    0x401442070396038259400007942030000c803421903841b21101400c0e1451404018651102405201c0000350703400140070881c4000c0c100020f000b00b081e0082448044003140d102c55080a01c028003000f940c0115005842e40c0d000c1c68440001c4c1d05044010b800d0010401b0300801c070104007240080d1003482001c04408140c01c11381595138174915407000a50302c4101e01001d070302c0b038041c00d508450801c15102400060540c0f54031000c071960b19000c41440300e5080180200c01c6552180d40c00c01e501491841020040c200585402c109080c05003040c03130110226200a9403113910304002032107000e600609442d641640b00001040300c412916090000e40102e5140e441d0b010b04080c004182c0c5071003c40c0380c0c0f0a4175280c810420205603906103603651001d0540c9d010380401000c00041c004100c1c10b400032040103001c2d004484409402d0700c14127003106d01c005695050680d0108051082200f140205401000300900c0c182c210b00703000a80000002068030300a00a00085090514410040c41031500519008 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 372298552 1250 372297302 372297329
    0x90c060c0109030e0a060f20010c0f080603010915020f0903010905030913020901080406020c0a020d15060f0515031b0304030203040e16020d0e030102040504050a0e070509220c 77
    0x3a100c40c0078040100c821408140c00005040ca20305080c491001101c52642c0c90342c03011100d10b1415500380444502410009000c910b5003a100c0c0000d0083d4107540215944000040c0314061000345401c5020300200c0c440e9042c5801e038000b08d031210300721381000d80240d0030040e43e034071529002c1c2210b4030a2220080c0c0550901c01c030401030000c04030140c1080001902d0064040e5000800c01c8100c1c0305000d80d4034049043c6038003140110b82154003900c0c0c2800041c3c201e404028a070340019008200000301105d9040701604002401c800e02c2c0a0603000709103d04100503c5030034240080d0301d005440001214000000c000030302042035036803080b540c2800d080070319a902d0601d030030001c2d10380e4018007920300e9030320300003011580e2500c02035017030a4082c08690280c141c007071100c10b00300c606e9003038000c0c02e9605640034000810260785c2d0b0701c60b45000748070010000528140115041e82054090f6010314442e01d822002c0009500d5241c0000d20750541d100411403000c401c1d03290005411f55240c21044070302e00c24 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 372299802 1250 372298552 372298567
    0x310081b060d090203121213050a380103141b0d0206130803090306060109050d0b07020705100905240f0309010216060f1b171b0a18061803030503090c06 67
    0x81c6c020b00c1e0707a86031031000112580c0c07240a00c11000301c08442c000c190b58041000078001c645860741800442c07a0115106003a88121203020b003008280d01c6007403415a044170010402c2281948100a02da50300740c0c00391011466100c2c03000000900c55414600880c202c0303002c8000c65890004484000d078a41000d42401c58850140599a41040e41400c2c083c0c0f0a803008905158010780c094811541d009004000c2d21003d0f50b10140b2a0b400500b015040d84507440c00814a590344090500507134120355a4003000d5483c00e02000080740003000c8400000002104007010140d12030100d0711102c0010001c00d0360307500d680a40d18024800c082e2214509250801030b8010003025800c0158240502401030041c440401d1060b211002038031515000700e104505181280c4102000d1f0542c01803a01103082090f0444c0c6036040307110f0b80984988000031f0b0045526940f0303000c103040720744041c10700f0b45802500f01c005c0f0b14204001203072500020307013030140103c0002d104031410072000024031405011aa107030100b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 372301052 1250 372299802 372299833
    0x40611070503151914070516020306090d0207090b06041203090e0103200109062c0603100807090506030c01030e10060308040512010506030303060411040305120310081b060d090203 79
    0x4165121a82e4407100132140101d04854011040d908900c4404451240c40d40442540d0a9002807000702400030300d054860f0242c0e0b001d00c150b610070400b03140034144102e00c848000b401c006103500304007422841c00514401d140c580b0b070151130981d410b443c001c03910110103090a54194903542d1014030762168807000401009004914a855820904e4559116904186c01900e044400340165800128410201c074a54620780c5810401c41941080068500c0001808961260300895000c4024003414104001c04001000160b00078049104100814140600002d0300c50201480d86c6041507110201d044444000380189201900540420040c142d564540211503401c1031082d103104000e0400c02e65965001801020b11501008000d5840d40c2e80b000e007000020900010f1085a0702c2083c000840000c8003048800034815100580a449290545c040780820751250809402c54011443e5000d81c9040035802d0f50704510300311805500c0d144660305d03d50082814604c00303540741c0309103500c440c103122 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 372302158 1106 372301052 372301093
    0x21080a0f020d020d05060307080714010503040303110a030605031002071e2f09100503030304060e0c130204090f02070f030f12020a080603150c040611070503 69
    0x2d400d0800e900490708581c01440032142d541d07040c00f44078542082114000c1c08144020f01c0c0c070504107102e03a006482c50f519141d0601c00c4c0031022908260098100303210034459201c2d01c1d030701c83e17680540060141805201383e500030b0052000030b50b82c6020728022100c0340d54121301c50207020204100c403500d480c407401c18144c1700070f18400c88061007072412000011440c0c650385140b104444802d01001034610000e0f007002200220150b040010f41c8010050300da0140e049840054018103503c82c1b01e08090514005c00e9009650035110041e890095011700b041c0c0b0a089820001400782d0700380b4608900c501d880141440380d10b0030000c80003a1082038650030005061820000b040307000160082a038100f11105004a2450007c100045c04c041040c10891880018030365000d00b0b001140c001b161184c0e0203000200200541c0d039900c0c1d01d904001c041c000302006400c03a4040c138191044c818111 = true := by decide +kernel

theorem cover : BRFrame.Cov 372122302 372302158 := by
  have h0 := BRFrame.cov_init 372122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 372122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 372122302 ≤ n) (h2 : n < 372302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
