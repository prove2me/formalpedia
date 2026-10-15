-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5501
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:04:35.906412+00:00
-- url     : https://prove2.me/submissions/b017b423-9e65-47d8-ab20-3771f596cea3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 989208633 ≤ n < 989388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 989209883 1250 989208633 989208659
    0x403090915031403090907140405190302091e09010507080c13030b0a15090e12030703021204060e010c02010e1015050d03031d070e1603021303140c0901050901030206070c 75
    0x1100c3c0c0603000403442c2c41503410300079200c2e031788078029140105000400d17603054042030203117000e81c2d0f002d0500a920401c0706145012050050b523002130608440c0e180031100c6682003040c000400070320030b003480e000c64580101405041e02a140544030810a42c1d561000b039942504082d4550510b285800700c00404a2401d502c0710780200e01c0440701284070700c8040890108500b00380d114411a0380341c01c02c180031407503005c030304160440c10101ca0180d41c5d88985030110068040c0015181217032000506200c02c129055101c104240f007110020310280071442d10036400c80310302c2c030444005a000b8812746844d04100c3e41c8140d1100c9210000890304940f17030700200e41c1291641c513088010940c1c4250045c918149400e01038005102c00c401003081c01d09103a4101041c080103045503801b021302031400c01d00c980c003070b8041d100e00c03039940314040d4441d540d1f900305030500c02c01811110700e15018518414100c2d081211030b043c141d40002c0c00e144603607461030342441655400000f0a0305c4040c2e03001c00101d09031049800c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 989211133 1250 989209883 989209913
    0x906021207030c0914091609090501080d09120b011404021c0207020a08060408041a09032a1509060c0f0307060c081e1311040e030d1103040309091503 66
    0x58009103281e44004041d05048030703504400019090b45d02c02d00f0440d55590405540b055442450b91b005030300c145002d96104016030001c5401c24202400800e2014000620200540c20395448010003039451090010550703010b80042d19030400c810041c880340f031108070025030003d00030344010301d03104030441c080310b01a1040340203c80f156000900b1005500d001806036003d482d40d900a490309090554a0200903c114440e21040403006078415201d0140c2c03000b5a09042c074050142d808540c010300d0503c174007005592200c80c2c000791000701002181443c00184400300700300190f02d46040c001d04100410341d0000070703020f11603204400400344460418006850854032900020605c0705100304080c2c60240000c0c03034140d5a42441c0c01c10044078010007805a0401c00c1004051240740050074541c8480c12908841034205042c071801c0c0074426030000060600c012030650800041850000d509042e120540b00600000c3c2d489000740029621640840c200500c8200701080c5140d4030760f2600c5507284105 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 989212383 1250 989211133 989211137
    0xc120c0c0203120f18012006090610120611041e0e090303130b0907030209150103060801020c0303070f050c0601230916050a0909020c070f170a0201030906021207 71
    0x10240340c1182010095441ca600510000b98100715100d00e840889025100062078215a40303407070102182d01a0205110b401034a42c4801504980c1915095490b082541e140145110750400a0b8a28110110360b405580d42c050031038118103051740395900030700840d03525041000c40c104030005007004150f02c4480440c45422140142034503103184260340200082401c1c0458008204010f03a00f071112071000e014543c0544503042c15150110080d00d002129007000350840403100034000e42082d40700c1d1180601c1d009903030502071765844008a0b8241d01a450a82030142c2c414004601c40e01c0c09403124400d105640d19100d828006820710641c50801d086e400040444840702c90251020310030300e0340000681c4241c91030310b52801d0203080690107820412a0f40200000410480440e03445619a440104403020040d91034401c5815003548400040c0704a8083c4003140e50005140388d0722201030f294030203010001c0c1c840a8299001980a41020700c41221000d50070000000b9089402c3c1516000300340d0742d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 989213633 1250 989212383 989212397
    0x21306110d021209090411040c020705100c0503030411011101090c1508100303110a051e0609060f010501050906040e0a150f0315020f120c0702010f0908100c120c 71
    0x24034166400d000e01d10400c5011500090450520700030900c1c21240026001c2d148000c103a9a2030500b510700d00000951a0380c418140800045481d60005020090700d0303007100c0300500c07007200c3d2009590405950318002c02d180c0043c0002408100001e80b040d4401c9010f0405183c8540c0380347c1d645084584c84642203c102c0c103103403818428030f502e1070303c940e24603c29810039620030b04280104100000c0c640c40014101310741280318810f0650140000d101c0990310408071201c001c03200d200801e5400001c042101c0300c0c41b61900140c8281400640f86000d550707544032010041c0d00f020011a80383e80300455040e003195007044005211001c510115105c0c0c01440000030349540700c00e000d50b41004069010390104429020288081072142000080c0704d1101c2c04c1c0103980b9103000007a6000d84c01160740030365407a10034108008281808100410049200740d980307004c00b0070380c1e42080e90341d034032a1b00400c980f035030050000b103134030245a52003c420010f990916180400e003900c204426140c00340769020010f960 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 989214883 1250 989213633 989213657
    0xb030f010810020408100905030d060905180102070818030a080406020d08012c0a0605060426150f13121d0f0105091905030304030b1602070503030d02070501021306 72
    0xd0040240d0010450010f61406240011541e50b0740441e0184181c0c80c1d9441400208201c010070403200d0b03200101405000d01170741d446901c0024a0105ca90380c0124410a41101072240c0620071a0845d030380c0034854905082d80c400100c0900d8014003250b58140c4030b49000300001c1a07031400640001e040b140d00529249a101e28020a004030692081100c940d86d2010424124020805106c9082d100031201d041136540c030960102a107000d0f44550b070800301c00140407844d0401c40008c01c1c1d100d0411aa4a1500c440c03501140d5551122021440040055400490340500442420b180c0004410881081d01080c0b40c8482c2800c41c07985840c0e002080b030906420501114901003c2001502242c5540c0c6411119002034076910460b6000d52090441c8140a4005003101c144030002d403102604880d00c4e587c481c902080324813410360748031403130007200050511880e01c001006420f4690140203117040c1984000c011019412084086400795000e20100da9103141421150004040503070b103400d10003807 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 989216133 1250 989214883 989214899
    0x14070804030614010f0b0d0b130c022e0e0c1e0f09190504150903020c090f280f05090d08090f030307051c050403080610030c0e06070501060b030f01 65
    0x300f03442000b48400260310040100c03c00422014080f02c026413404c5039a00e01120b22400240f0408411f0f90b800907190a038000704102c107a1003892280080e40031201444c8100ca00c4002c3e1503d50000450041d4038401c0750655108540c00440020310383c2c1c3e04441c0d90000d0100040c00c0081c4101c644200c29518840340050380c5001203000b02c145409440d040054142500002d111461101059a090f030700c03078010404225406071128403489041204200c1e034401458003e45810a020b40350b80f00d904102c02080c402420440f9aa0281d03107a1501d01c24017030392003540d03c001c0322510515403070066640c0b020111520201d02490f4410075404015280900d486c11026003480340140c484000c3e80c1c07210100700f4403014000216900071180707080290320341011221040520840b9000e03000c6e00c505280038401003581000d441e5000313900480c0c000510300e164a8084046800c64030f855030005000d4000c810650802500900340b0314040d60001c10300a880300304082c900e510a1305c05203c0c0900b51401003041131 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 989217383 1250 989216133 989216141
    0x1140906120f011707171501090212060109081b060c011a09070e030613020310110a03060e0c1b0307051f06090c0c330605031b1f140708040306 63
    0x104030721201124a20070072503455500c400038092030380c908840740d80ca0f0401d140e042007107030410a47c05210035029a1a1800c0300e012790000384014082d808418085900356006803200c800b540c0d03501d4001d00c680c007040301950381e000c03d008828541208040042d4000e40100380103101d03842c0c8865805989211072881403260081c001005441045400462001305541c04a90940c0040c50f0444101150409000003400c1c20550094500f04034a8000ca44000b171000d0400742074038480640701042203580e503070b42c05030411404a030302080c01d0504000f5080d080c04850124141110a10110b81c00c01c850b680d60146804069030103920070005106580d155103803140500e00180c250301000303200344068078001070b2401800c1d980042c28110b0100094041b1546440202c10840726511000d00ea03034600c1004100031b1003180520f9020303014412014140e021125100005010060410b105070303036490450101c1c4054542000d020440821141800c1d01c9aa0380940080c5008000c03007560303a40f03949043c02c222 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 989218633 1250 989217383 989217389
    0x9051002070203190c051e0d111009030c051c2a090b0a060807020f0607050d11030f310602130602010902030606040510080f060106030c020f0c01140906120f01 70
    0x5029084800c40005d840710581104441080d40c402031100c510900c03100b000000411000d07040b11a000038042440460110041003480a40c0c0b0258514400b410417503a002140c08050283c3c0d0b940d980c00c00c00740c00c01d582101c81d503c0541c2d101c100fa002183d6900040c14403052400c000c001d4018058400f040602032880000380310303804040042c12640808503003079143e1441901d00b80711105c000603082c0c0b40203000f050100c400b2071064541d103262000700500f003608200786044010345451070110000e8101c1044a0041c0a8213802c050036a466a03100c00680c94140c0c03a200440c0c000303002000c1c0c00c582c0ba01c55090076910426000d070304c1e50100000705600956580c041021a81480c1062000d43c801045280c1c0008081d20040340e555142028031040e41419030181f00b05204000c1510191000442c007141616203d41d404d0019004407801242c0c0c49603210b10102498100740c4e2034035001e41c001c04064000340741c920840c6003030138081000504990060700009001d80d030303084200242c00381d0384c0c070b0181d000d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 989219883 1250 989218633 989218663
    0x50a0c1b030206130510050a0207050103050a02040e070f030b24031f0b03090c18060f04111c0c110303010902281205070306120b040f140d0f140a080a09051002070203 73
    0x20f1000c41e1230001d41d0b441d910b2141034141550741000c41c00e1600150103d8018100701c801820003402c4c4290700402c0c9050081211000a180000402c80c510300805500485d4210706001800c61845617081c060302d80c0098049100c00600400800c10103021040c0003000308a46502d060701d91038040d880500b4009100c604610840c0690121421504138040c00703a0484002d403842180d0031055004103008005000c050f0080210101d00700d4600d040f00c291640c040000010280607601c55000d055070307000401d826a03200c07500144014000a011a030150219000041020454a01540140f00403461420000700061845c40b108540d880c2280078440d00071b4500d2404210303d91401d0200b800000c18004010000c245000114040c4080c08140c42d1030366401c000c5d600050001c1d4041141e680c0d0030421442c01068441500405250182074407400d0b1601042c000c0c3c1c0b81003e080c0381114881c5004001403503c90307442d02040c0200700204141e00e600c00f013400c40103980c3c041c1da0040615043c0921003891ba = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 989221133 1250 989219883 989219887
    0xe06090f061003150b0d02090907210f03110a0b131a07050306010e0d060c030209030d0206160806220f0b06030c040303030b0303160b1006050a0c1b03020613051005 72
    0x800a51501e00030360711054082c000017184400300d0700162110107854000303544040e01000303002241c1c4001c20240e0444a06442140841c03e040074039400c1d4008554000d00080909040c11010074092480039241c002c1c00d1054559002550740c410410f00020ba44101c042c0400020200800226a025220720301d0710045e0000103203407050006042d132200505050420002c00541600c50301d803086618011540143c060145e40600f10000f00203400130143c0ca071082c0310340700c01d8110060000c0b903418050848071540c00036100c0b01020a54514030040e0415401400c80384070580e10081c420500d81c4e0013826800041503a400d80f61603603059074804a1864481c2c1c4040050000070940c60040b00c1c100c03649230a022900d415030300b00003410b41c001c0300d105c6080b01170120904403c0015003241148a0248c41c2c808040c40c0380c865604490300d00503544c203140130403007440502c0003107054038404000e440c100da64240080e5443e540806c40f0b5402000c01b40d2001c2c04144000d000e5880c140f01e04800389811361178428 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 989222383 1250 989221133 989221139
    0x190320010e03031602130212181e0a031b020301020a020a02040b150d0509010b060301030c05010f03020f12040c08030c0606040501060f050d0f020702041404020307050108091f0e06090f0610 83
    0x5060011130440c000d21031013446072000708210700d907010b031040c1c2d10030360940016131301d0104944281503050700200030707103800307002a10300d51004070600740040d1052160081220003140c4c1d500341c3e00061840b41201e4000110907901005907024001451858800c2d40601007480444c8107200585802d001001d11078420400710000390441c040036290342104114022859881d0302440c1c0e401040381600803a0851000000071050124180c084400c0354801e0341d401c5001d0a880c1e100320201d000380780301d10140103420407500901d091071004031508075024642c40000075941e0b024441c61a807240b04584501d800c0041004682d20b40f1344103c0c2d004041a00301550b007404000001852441150f00e81032801d507a40c00070841c00001a07040d90b0712203501500c200050195100912854502120124420b100c1c912000c0760b5544110141d60040000d2801403080381d190310b0010300c0400d0900d211400283c0d03600e02d14cc0028031b007044002e0082810f207014021480415450074100302e40100304855200c6090410 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 989223633 1250 989222383 989222407
    0x82a0606060f13030c0b1e090a06120b130902030705030f06040803040303141e0907030c0b0703020102070f0c03050f1b010e190306050603011a0f190320010e0303 71
    0x391514003004103900c0d503d40c1441c40d0010366030a241c2002c0c0024200c48808200c0e803a03110000c100d41d002100103010701c1c05200e84034812520a440009400c008a0841004224000e4422040c60a40082d02054020301d18002c10028001405131403c3c107a01c805413241982824421a009400254045c088030305442403a1036a4181c00340004103c12000000101894460f030b11000c544404407001c60b049041485460407207009407916050010742e00c20106018440000c3e444040b6070f03001208010302454803038208140e401944050302555020000e8000040200341c3d89000c4600c2881d1b504015400c40c1059072078120b0780b04240800e82d2202c00080b21075000e07002d00c008004400d10305001010100000710300000008603041c11a02d959110200401c550b0ba04058810074042c0d008008000050076030300482218086c1182d080002400300310114103185942d0320101165104810300982e0303d60700c1404071104500c10f1703006c06040e0981c0c03a5203903901150a48022004034001c6050101c00401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 989224883 1250 989223633 989223637
    0x30603070506071a010b07060e0d140c070e0a0f0c022802010e03010e060f0c0426011803020327061b010e0d021c08160509030a082a060606 61
    0x784621410000c00c1c0c540800c40900d200303900b0390850800030050f550795200f100c01720742c100312801c585aa0811160814543d400100c500100380155a04580040c20001d24241070348070b040e4000442c00750741c002149000c46007000364000d805020001504212440c680c004031007000b0021021500001da200144001141c4030140c2a803c5417542c0c40e01006a10050b40e42000d11038045405508042010107000404100103201d140381c14004c811647d1140d13941c513014811070151f44403e00038940d007050710001c031b81c519042681c07400c800003551407400c45009415280c10442180180e0000881000056180081c0d00082e500c0905864409403400001940ca0003030340400072001440c080d4559060400350445e041000140c8180d40044240d04002034552440b24040d0748441c417030703060f02d9041601c290055403140c1601840103104054080c022189030780949412a85442444414404140450000c15080603142c08043c0040c503091011126064102040b6060b6000309007081419141d10341 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 989226133 1250 989224883 989224889
    0xc030c040311061303061e020c030a0323010b0c0f0a0c1202010e4b010c1b061101050912190c050a0503071401020c0c0907050d0c020105070f030203060307 68
    0x3888011503000200840c00341c1c0101c1030401e402c0c6114101c00411b118441c3c1c40000110401800801c003a0604071015081c4d1180002c946da070380c2d00070000c44018500c40c1e80008524502051928840300c030507110718130042000c1e0810060b03a0000114038003540b004008442400d40410007500c00c800c00d41d20360000659843c0f2a41b0203d0076050865411a8030411072003000340b0300101190844c1e200c0000052000450075000303240c0e40b0004140c1e0303088042e03914440c20601030307550034071002144e40401111600c20015007141d42da190b46e00d6483e2110501351006000e4903080e924802810030100401c3e080d528050801b912541210480381e14008d003190403545c0f5052241c0c0c507440c240600003c2115000603101d00070b0694000c401c1c1e98002c0080c0400103048250003840c07580800c06690302c03010700700d1041d104041e51540c484004140706050842c03049a101e000c03810880e040c90034030086001950040301c1c1040050750b648040058070b541000c11841002841d20713046056103020740c0841c1c1d60303c034240 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 989227383 1250 989226133 989226143
    0x1511120c131d01060f051303050709063002060706091109160c060506010509130f0b012105190c230a120209061308061504090f020409020f19030b0c030c0403 69
    0x5401c1da2203038000c1c41110410407003a4400304a0648e681402500e5a045004e1174140c10308252002454110b000482054185284411f1410529203c0310b4140c641d40040202e812500500101c0c0100e845841141c2e269400f03080e0b40202d07402400e0401084020040a107051402182880701c2c0d8180d006003d6044036a01c00320008807034440d800144d6250140100f541d44c009501295103032101c4b00c0e83c200b280c5012242c4000e0168404590040d1354201e803c0081c0610044420103800803180a900120b8120032204440910151000d1841050b03824580c4110080b03280f840c00c0a10350074050b06800340072555002007600b0012141030080404400e01d041008d601d8010910303101d15602c2c4000c443c1c1509610280c0c1000565800f070782c039203074001103e0703030750240c00e910307000200600345409411002580000710038500006a42000000d0041c0e0340305136041030700411862166212482081c2d400e00700071a02c590290f00d14a0030103140c540c014461051301c5020f03c24002500700d00020b980644e9480 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 989228633 1250 989227383 989227397
    0x1060203180a170708120a02030f0a0c0f0812070819050916030b070909060303120c0306031202100e01060302030a0b19020d020c16031511120c131d0106 67
    0x720000800c0e500c0e460b000040010003d402008032214002041011201e60300305503600351504050104c04ca00a845000002d42c00410507143d025400b0801040f031108103041c100d11411107034981c1942e00e10f60070b904650341b41000135a40040d900000e5021750220b65407411048626000340030030f0700b100d1601400b00640b038585000c100240ca0904c600301e65000c4110003031103601c1d500e0808c20003007001074580401240a04201052034010360080005903078154031484174901900b10700c2da00510320360440f1410980d50b1080800000c0c4640002c40d070003010359004100058069010500b1a880300240070b07016031618104100507100441c6c0909001e130040114051559a51a10100882407408801d0030701d20002e070313110004030907902404c0031951401c03c07a00c036801007614059081c512400080d2011450f10000122040117030007509034107901d480b02c18140070501c4c9001190329020380ba050842e03800801d1003205401900441c5e00103108110102c0345083c40d5007640304000e0701c180220000c00c00c00c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 989229883 1250 989228633 989228677
    0x105070912030e0d0b16020309180a0213090b01020d030905060f070c0b0130260405060d0f0b0d03051c0930020106210302121605010b0901060203 64
    0xb440d03d580903460301400070f211040a91501e5010717580100c0c2c802c1c2404405500790710040b84008241c840c0c2540281840742c646100701e0000010410041005801c60703020040c204124500c1a80d240c010503550002068200205001a080a02046c800d50800d85030001040108900055454101c2c0864003102c000c2e464a070301c01c039140441c0010103001071000f000000748003cae0f10444441007011a4100c04c0941d450840f0315849600101e00c0a400100d04041400c0c690600d00422240d1049800310580740583e00c0010804030340211600c040c80c559a001e05c550102c80328000c1881030202241c809a181c0c03a01e0303034081e00c0e500031510103004800e0503540724500c2d044d007548031024140d0801c10300c1d03034030282072429210403450b0140d22064144501209201c0540140149020b41c0c0305904082040380440c8016041c003102004240c085204069803806441c5030000141121056075040111031071460400718255103017401003501507840b072001041001d6001c0255a4200f000340038002400310 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 989231133 1250 989229883 989229887
    0x50403030b06130503010f020307080f0601022e0b0f03060a0903030f05040605090d08072102040e01060801061710030609020f03030f090109080a0c03120318030302040314010507091203 81
    0x110401c94070380203040000c11440e00940341094800304c890403402030180c40001000b5106901041d2025004900000003140400b01100e010360351204d41031044500360082c4810b81103415111281a1084c1c1c02520000300030b1880d20302600640900c19a12900b0360f010580210b07035201d00040207101d8143c0e5449940d020076109810200151205840600944c142030900c00300515003514843e000c4d111302050600b0b414090802948501056152490f041003494030303440d003030300091800c5a020380d82008080342c144641388116000e048182d4582c4c0180d8180100035008018441104c400904003004201d0506103600b4010241ca500c4400800c0021840c408522950b845104c3ea50b4180408034180701e160380c00a014009202090740e90002c125a1004419140c2c1ca06d904068203810704c4a001b84003044920812002035012840c000507024140d080009044c034400108500103500081c1c20404c1c0150a44860396040d0028001c103c942043c04018140390741c180304d10a0b50b01800c503041e1041c14 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 989232383 1250 989231133 989231141
    0x70f080718060b0703030b010206100b1804020c01091b080a0b011526150603010509060d050307052b17070f020703020303120f0f010b0d1a130e0c03030c03070605040303 74
    0x8001c0f025916881c0c50720b005000f03010144002801449200c0001e40c40100030000201103500300d60906140c0f02409090580000220301d060350010f808202c6040d03003590034440d0300510340c0108070f002c1e035903003007842d0501821440d90310102017544112881e0010076007965807030f41124295030b03000d51480394a00c0c090b40c05240514040380c150081040c000b0300c00d4100c00710907105001982d041c000303c444a0013000501e000070b010361500071816400003229030030070040c50100c5602130011603003491120341d03400c1d20b000c2140c81c40c0340c2480301038038803150419029175590b80104031500304400301c1070001340c820701204030051101040040241342051038500a0245102654018090b2540c0b800d03407a00401e440c00054a00d80042502e0b080000c03071766002a41e00078103a0f82c0c0740161038a8503202a580310050042010700d0818910011800c5d0f0075542c03030413014180540141f101050080d4210300b114100211404010f000b60020010300c0040c003008011200d4182c3c0c09000001d40b6215810224000c2c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 989233633 1250 989232383 989232389
    0x130e060a030212160602011e020a0e090a0207030f0c050604030c06060b0c0f0d0915032307110c091e0a02040b0418050c0901140901020a0503030a0e070f08071806 71
    0x3c11460010b129002c20042401c40c004882d814250b284590381c0c107802c0b0300300c51a08880d0803030703c00d83c4d01c4090b002e0b9005800400c1c2e080101e10300188143c0c044000a84844004e450400000d0f900203250740402d50803011014088110f8100f0350303000d400750384030f0b0f540b5a04010300003800c0003002c020240420071207038459400b0700040e699442d1900060b0182c2035480d47d5a41c1c0b0108288500644030210600c02d242040070798030f44004c213107550703204400c00781d01901568a00080ca00c024071101c4140c8a940d00c0307140d11a14440c0c0c1ca2001c14005c1445031030400c42c1c40340c44a401100f2150400060300010741c8603081d482c02c56609071456a86010f00300000f405150003c02d041c0c0301c005400103243c0581c02c02c00c005860b5015041059440c0c91507a05403034890020380501085c088204405024201c80141c200700c101801a1087c0c42d10550b0788c1401d40d4070445020086c81da66400a80003482c04000301c00c00f034807c880241d0551810800c074943d585030240315658400b210822041c00b17042d01a0401401 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 989234883 1250 989233633 989233639
    0x61202100c0b0a090312020c070512010f090807151b05090303040329090c0a17010e0d0908010c0201050c1605160b0703080718030b090a0803040602040503060606130e060a0302 77
    0x2c0d400e2008400c0b002d400c50718000d8000844540410743d000303010380708580101980000802c1c40b18503010a100c209a952080200e545d542d0b9644413030040031a0041103252441a49060383d102c03002d2404c514064001c083c0c5844e032a203030a00400040481420400d03401150b414116215140d120000386180f0031a0401448001018400c5500042c0012503800000044421004540d111400b0b00d950342403c0c8000303503000018407000c02c03c5014112030b0003a09801c0000108003e01203503215450304081000c1c1c140018061402000110420306c641050f49a0a1009211070f061031300d401402801100720410b910840500c02604010081107254901c010100d04050181c5c1e80d1403d0031080c1e00003003010b90105840b03d00040000f8410840728503004440c07500c041c211401d41d140c40b240010010210100c5110303001d4001c1c0071408000242d84540d01c030358000760351182040182742c2014070141c40540a0381c014407032140036103000000e0905986001c0d008901c1c41d9207040c00110020b10340d80c40a50 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 989236133 1250 989234883 989234903
    0x5040b0a031a010602151e072d0f0203180915090703050601020d170f04080c070f03050f1218011202180f0f0607112b0510061202100c 59
    0x54249240b480141c12a51a80c098032181401071808240c03d84040700c04010f070300548943e0010348500040c10341c2e0000c80618082011802c0d80388030540b001196200400d00b040c201e400c4c01c0c44690700040d004200c0c143c82c03018505160300b03d06038010f1411450085031249120900250645910b00540c540000009080160a00307000201400921041c1c40305801170041030f5088552a0180303940c40c148a401c1c1954201940c0c43c000400180c050141084604075010881071480080401a01026001c030410300c00220380385140072840c1c030b41032007500441c6030060710703048400e030415000751070244121486446500d0508030040b11064550800c81440782c0c400700714095803004a01940070b20f0f0000703441480508920074100700000030801c1500794400000c001160005414251240038544041c00702c80202c0d01d00303000b521010008903070502604045134400018400204600d002d0105440c1c01080400c1c00e1041c10450360450880c064052003100c64102c00c01882030f510025150b0304040814 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 989237383 1250 989236133 989236163
    0x50a06050f0a18080901080745082d0601060306091d03180a050d0f1707110103020306060d0906020a0e030c060a0e031903020c1309050705040b0a03 65
    0x4031241d02590103040840ca0802c24980200c075005101c021207410084090a201c060001114a54001005001082101d10007a9141141c0049030003280d0140b418100300e421101d014401c007480071311419031002580c00700030818038402184a0845e20280d80248107242011400c0740345803002c1c81d1890f2450700c00c100002401030f038954004029603068000c1070100301c00780d420f02019405064010b1041f900100811050702d03602e0342d0341c2d41240202070702d0140c240c0d959000095075016102402d90b40040d0510300003040050203a01400c0345180c000e01c3c50704160446d107401d541c900e01d400b81c2d903052640c00000300b20199100d4058070855015070005102081103444c18401a4101c1d0070104003040d00303500914803900c0e021aa1901144014000f1410642c0003881140c0d800d5003650f155070140208080d8188103c0560115003210340250020903954144005000c03a450190307120001861404150100050005c6482c000b1144100c0e00820b03205041030015040084640c0014056440d6000344 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 989238633 1250 989237383 989237401
    0x1110601091a0301020a170a090501090b0402010807170402041a12010b01020607051213140a03030c14070302030a0f02010b06070c14090907060f140301060e0f100e0409050a0605 78
    0x812050b5400041c51100c075518241802d070700802c90410301045c0b0124039140d4100c0c40388015035128507102000720381c1d189183c80307403400c45090910540389031003d50b04000541d604521220b0b0080140d207013020844282220b0442c0088014000030f108a8841000c107040d04a6454044685007009113840700401700241c183e0700074050b10302c0a6002d4000d81d0b0004400a00400903035602d00c0311805403030041d6854140c0740d0380308400d400003102c01ca40800a8030748a08000c100102106100e174900181c401d4841d4400741501286801d0700072440802c000744400a540801660804005402c118880a860384004d80c058001010169080000400c81c1c0c418042c1102c01c0000700c074800c80d00030346860041c90a003c04140c0880d9207000a6014000170000d40d0701c1152010402865480c0c040c84a100301800342003036500a0384868001000034100b10703810f1500f02d100c8000c0d16011034203c0342c5403e5041e0013804210302c400003280b059996120420a02c0824007416041d10307840300c020481d1b131404040ca = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 989239883 1250 989238633 989238641
    0x3070512060f0f2206020c01060b03010905090102090d030e150c030d0e0105060f190e0f071b02131a0301060f1503020a0806060a03020d05190c0c200111060109 70
    0x310824140b800c000c6020740f001c00b02c0003030186280c5411a41e00140c810000c00400355210011920a5401c02c5101c4031404c0c28805c0001400310101003c1d0340b94500310014080d1107024200080e0369204000c10001642d0310441200021340c1420301c107041c1204040000c0c030b440802c202c1c03000c45020010f101480000007200030800500c00300340030410414409810380c02c0f14005c980c090340000442c03064818501e445454070309a60295100307800340c3c5880350301c2c17103070044411340d42d940203c1103400901600680000d00c0300b000816403c0080741400c820340000c2d002000c4100d11a1000c1c1e900e50381c950358480f041c20358031155100a402130010300c0d960210104014010f00c10740340d081c60960304040c0b14174440e00031500c05012503036030116282c48040410250b17900801000d8107040c0e081055410102140c02002d101d0416960030b00c401c0202880c400c4140c1d0250f030120301c2000300c9a001c00c40080c0314407502c406d442c0c1c2d850180c08680c000203c0145d0b201032074170603620210302c1003400000e200712180e04 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 989241133 1250 989239883 989239891
    0xf040e04021225080705030c01050c121306080c070b15060421030807051306080c21010911041d0406110c01050601020705040614010809120408031b1504110307051206 73
    0x100f070400c0c55a96000040d110940703400b6035035268001c0c8070302c0c422340d40c8980d000d0207407024200c09441c0d09a81d03894240c1c0300c0382e2002640824110022504200441d001000250b0000311004010724200c40c07582ea47e200b8038401070001600f011242907155840c1c1314041618081d140c482a15240b24001c0400360040c6600020228002011031000408c55031080c0281ea103120a0700d200c072100c29042110603905224020504501028240030f02d814038502c20311682803450044088881d2941404078800070b6890102900c200d018003013100300314098a044110303650800a00c041c243ca52218601000034045194484608900c04101182030943c19840140120026002c445050340c1d03400500041d1010340c0b150607001a0000f403500d582d54014048650300c0302600080e101d0302c1150001921054005400c008000d92001c540141d828641c070351070420303095103100203101200c800608803102e80c038000d00c004c0070700e180f0748504102503e003001900c000c3c2000a00c252030141d000410150b450b00219 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 989242383 1250 989241133 989241193
    0x6120606150203040b0726160507050a06020a0b04111210060815070c0f0b0c04230d1203141602100504051e100f090c0b0f040e040212 59
    0x1001c03400100c0c0004100c604917242c41d40d8450405581e40c40302c400501c0107411916030b030050040854184010b8000a003900141540e40040c01021418014a0310a2640003117008001184043c40101d0b000189446020760202000740d0702c0d5240d20f403801009038400c04c141c0d0006c4581c2001250303071102045002003d1000c2c6000c03c03e19503541b071002c4d0384008480805090100b99008150340a10a000410081d4021041c180000c0703c1e42e43c541c1c0d40884115500c503080080880c0a0160b03d00c0074038644c0001c00d003114094480051500081e6140c00c00140003801c024201d130020160502a402840c6294087d11030b540851a04a030500c2d600d40456404034014002c0301c0c410310051400348556405680c20600404414152030b011001940d1060b0f561492881015521281c04000d4011040d00709400300f008034103140c0b40c0c5480e56403c0c05070b4000c081310f1082486200300b10040a0165801c8400c5005241d0301c0381c640d8004200009210001c0c40380300d000780ea04490450b001c1a05940ea141c01117 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 989243633 1250 989242383 989242409
    0x30c03020d020c1f110f160506040b04090e120f09041d1f090c090e070b0a1209020609040912090b04050102030910030b090916140d120306120606 64
    0x250604903181c0b428000308a9000c8501d0895010341d908400c500c12062404e414a17502d43c01c444074551303180c68480704014200c3c1e80f00344020079441342e20302e03508002080240c2d400b9007080d081502c644140c2c0140c0c0035002c11182e5a0620700d50a950801c0403d5176580c44000f0b0a0350380d049911503901c2548161282802a8101060074120100c10b218810f008001580580b80d40c6040c08104000788041e19110707005503445150070f20200700f07514030183c000d08042d140040c0d51074081490354105040d9500203a2542004d03c092400183c0003922a020300c1c90040c0300050780043c5d440080c050f4090b0300d03e51604645092105070400070b41300075000d9541d1407921142a03695540507400f040e40f040d07010b500e006030824410081c0c141030034490700382111018180030030340c00790440210308d211400712810359495000030010408008a803048c10060900840c15441003190b6401052940401c628001c1070301400040c00d0880d244070b40c0c010405884403d008801d484c2c000d0030041c0c00b0300030f58041d003005a890 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 989244883 1250 989243633 989243653
    0x901030f12140702120705131b05070302100b131103070207090b0109060507060603050f28230f0d020f150106080c0c0a12030c0206100303080115020f0a030c0302 71
    0x720b002501050344081c82d94074010fa607500340044518940a0520303e0b1040d0b1101003400d40e00c8100d4900180721400300008d0342c55203651850385000d008040c1001b40082005210b0102c0c1e03000c24060f0300c0d4203008201140148000b404200304010a04031007901a16104080100980c040010340c0210070f036500b220000c41e21000307070a0848264640107400704450300801c0003d02d0240700a01200c0e4040c4500003103c994070303105c41c0d04280700495030b00710681002142c1c2c00e0414540c0d01001d02c030340c843c1c0d10340c00b15000141d440129102c0c0402040b021525084418010b143e42080210002016481921200ca10941020303586105030f80f00c4001500404038045120659501c0c06070485001c1e0380e174100d881e102d06035002065030003691011b60900030540c4110101d944030340c070741c80c090441e130364005204030100703030002d0400502600810007501c0000e002c102095010501034152803002a605202940180050345070060201c0b92034258010b41800c281455000100c0b50380701c03400780e0240c0c2c0100d0301c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 989246133 1250 989244883 989244887
    0x4050907080708190207080c06041704030804061407021002060907170705010c03230301050a080105090a020127140a0f0b2212210c0f02060310050901030f12 69
    0x4800c40340d1100059060002801c0b042c038502407130004902ca454014605501030303d4014a51340544641c16981d400300051000b00306146942010a0302c07040300c00c90410f070440d510120a8415486518108140b0882100a607801002160394296005101d01100f414a42001c5c1d1100c40c121001f134158006c40c20700040115a2107800980c01c0d03a0350000d080328038201801520802c3c1103040c2901000382d625070082c1040340f140210385800040170a40c030740365807414041018401c102d8102c0c1a042c0d0400083c429031140005581d03a2a59090074107070040c3e40c01810b2131018881c0e04a081c200c10140c101c001070f41d04a40d54002001c11b00540b415035405c1c0d110325406842d040d540c0b042c52180001044914205d0040f07400310401c0b03204640b40c10a44503544c0340102c185011074ae00c15180c00026041140c0a02d180540280e00d58195040c08000c462088d220394401203c0c04a010340203a20020000c0c00c403041e2481c000c2c020b400e005000440650b101d0401c0f400404200108030344005940020b20b81c014 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 989247383 1250 989246133 989246147
    0x1a060703020601030204110408070906080724140d1505030111090a12030302040e090c0406080f120c0109050a0f03030522060c1e02012906160c080303040804050907 72
    0x1030305074005104991a5500340002840c0101200030f06200c01d00c00820107d01c1844908014000c002001c075109090010503414004658481c100000742c03180940c01c0c2540d8500020120000350900218804400700980740c58811055000c40980c6820300462540e0b1001346040c003501e0080e0000c2291a001c1e58090b04144108512a41e0000b00034404001042941d000310304c42600c2490003508103a03503808000008007003542c031032075076402a000e0a221070800f80724803002401050028400c050f6466401070700c4441620040c501c10000207218441d03400300b508882d0601e41d1040403251140c1071400d190b12a48503001d000c800290803c40030903410f4100031864415035400052051a072007165a80f18001c080d66500203040c040340d405030340300c0341c602d014036201900c2031500003041c0351104801c0b001d5051036031b0285201c494070ba1985522140c81e0390701940e41501303031400076880c200050f05242c0c5007091643e000d100b184c4400000c2100300703c6140050022100c007695294074070f480c0c02d502545d0340c03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 989248633 1250 989247383 989247397
    0x1e02070f3f2a170309031c020c031c2a0807021e03060a0203060118060e0a092007020a03082101061704060515090103061a120d1d060c011a06 62
    0x104201000510091000c1c0c51286003c11036542202d14010600010a04111440e006880a40301a000303c10724250140061000100124003030022040d00030003280071140d140070f900040041240090180817032451001d0b5003000d40200001c00710059180c440d8451b40244d04c100d00501d002d8034903441c803404455200f5021080100681140c2d6034405105009401c0104114104103500300105441040540c00c5d902a101c02c2c1e07100c0090031000002d11420907000d5026400140c604000000c0038072069009414019a81c140e00d071b505c0d00c0b0b138000136400c94200c0d0000b410480c030025000c82000f844081680d181d030101032481b02180e80e00ca0041c0c4003074241103200341101e030710309000500281ca9030b440540d101c4c8041006e00030300c0c0389034004180602002d810450301c00b9551040c4071009600d20316501c01c030380c40490740c01640510200c8042e461f1100e041050701800b101d001c0712069400401826921200050711054440c070310001b200340603080c4079500c281c1d001c0490f000070481d402c2410031a140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 989249883 1250 989248633 989248703
    0x121e0705070b0307030b0d03120b0f0d020904020303360a080a15111209010617030403141f1a01020c0a0311040212071e02070f3f 57
    0x2101c0d281c141c000c80e441d8402003601c41019510803034010b541e5101d240500c03c0d54001e980700f94081c040c8044800071100e03409409807050010080045465880206080805a0586814002ea152403000c240380d8010b031002c0d82420000c03c181d00d00c00d031079002090781180304922110101608500280130003c1014041d40c00a60444190003001c10071200340c0343c031002c1c4c54110010b811031130782e40c180c07425400c100c0640c403200000c0c10511100200034010403000e070044443d00c0042c40c1b4040c000d5a624843c174030000b486451807811558580009104011015001c03145826164102c0e110407001440c4500c0808219030030139070508450351000468110101000e081a4041801c580707800c80c8003c0d2078940341b0341c0b041d020014540705220030014980107000f184c5540c00d002c40382004440d034285080300d20004550182c00708021400003c506d41d4112030f6609030070441500300c140900f9807045034036001c1e10750040f6202c103040c05072940c8400c0040389000740611040c0303440703213203002c4181014000e0400d1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 989251133 1250 989249883 989249893
    0x608070e060f040e100306060b0901140a0519090815040210031103060d0c051e0907031b030b010309052b03110a0809100501080c10020303040309091d121e0705 70
    0x4100790b030705054006030409a172415095480e03441e8429604260040b88200d1008140e4180558006c900d814503095000d99003800c0c880519401092170140c10702c0024091400c8800e000002c2c002c0d016440a8601502600c015000c180141212d0000948040f03000c1e464113044038888900c2482844000540d0340d00143c5152900343c10040205001802030b00c6012500c3e00005c0c03035507220801c12004119400c0440d02020910041158400c0024281000d0501700b0098940b8810303000b4840d144a030142c100081c82c0c1d241500100c0040c01c80d0040100742e4410940750110340c00303201c40d0401580416100364007591003090812002d0f24080c1000e80b000c06010300c41c842e8524000c45d45143c0c070640c50011a00c0501e00a2126010b4030400c3c0d020700e80b150081d8a40720000d041994005415041da4002980f85050540e00107110f4a00d40c811115560741e28095a40302e10442c1500d410301c00040800c54000b03901000040056502040441680441c0c50064204015100701035642042d00180540 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 989252383 1250 989251133 989251139
    0x1d040c020a1101140c07061e050915120f0a0f06030804050402030c0c0304031202011107030804061d010f0b040e0715050a0e0402160302061803070807050c0a0608070e060f04 76
    0x5101102807116a050020b00c40340080d50100000c00340c003040e5005802002c0701c6103044005080c088094460480d2030081c062980822398000045a040070000d032000d0520f0650070801e5000307402001d140d007084004110500841903034820540d03005020350b50b400c0100100344ca00d050202c03010392000601e0110140400c211615184d0301460380004086000c0c0c0c5400003801d80141154001d8204980a680190060b003505a09110b1030581c108800600c6240ca0010745014281c8840200001d0807280ca401031040c8000400140307426510509000344040c0202c110b0b0742000d8090b00d0314a60042e441c0162844844000180e4501102d050760654400015800310455403540404d603500e05219003041211150b4645200600030011038841e0024031103502d190090504801820022480302d00a4a42c103808001000b202c03220380e80050441c0d0f0ba40c8039403402c203090801c039040040d40a410135600080d0681c0007100d4a11403261a5990031044140d20200492405400408410b20400b44014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 989253633 1250 989252383 989252393
    0x1181a07060204090606050a021605061c090b070c02040e010606200c09040c09050a0b06090f03010f02130821070303090201050d052403030f0a030c09030609031d040c020a 75
    0x240201400740d1030240c07401c1e8030380132020140c1c0d101380e01c1400020b10000b07a00010340c0d410301c5104019040c448402c1c83e6503243c01e0010f4042d0103a520b0800701206241802d000340c03070140d400700000340e9102f480e0100717518041a010f01b05100014043c0d015600300120b4803034000c010320461040e22100d45503200ba00e0703003040b041140c03000d009594507201e1042050240c20b41c0c0d075400000344200d205104d12410617042512801c1038800240c0001d2440f42001c6004c02941d0750a01074411815060320f038602200e034200c0010740075041c8104040c1a25100103100d00000c01c050070a0800d44d01c0e190300700c540b03080801d07001c456180101d42c11100a26000e02c01c5500007072103070b000038101e140140342035030502040030cc4c00c40031582e0990703145d001d10942c04d00a20440300206411020301c40d040340610b04116500c16600014492403840e04205507507a403402c20518014810540a503030001c07810030072140e103407034050510400c044c01c40422103291070f07401019103841d010303418021019074081e04d00e131b070b050b9030f99 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 989254883 1250 989253633 989253637
    0x9151e090810060e1f080f03090f2215050915010306050d0b0606030a060e16020705011b1e12020f010612241d010b090106020610060f14070b0601181a 66
    0x20ba48502c00340d17080004020380c04000b07420701d030000117015598801481e0104500a01c40216503801240c08a1302580e0303000304002c00300d0012007803c07000b040c0104e40c50b1190510501980000b64010480300034849203006d8402c10318982042a201080340780d0703c502c00c0111000b011400100214501c40c00100141400c4001e1364104204035004115192600740b0029880b80854541510000d641b0516143c00d504010010040c002824001f401880038002c0800c07007050105c4c0a00402106001c41c104d611040c0840d080c2160801281c4c000d280d01000020749440e4580c0d24202d20b50700700800805c09a22880444240580c40f0085481151245042080103c9600448010103a842141030050745409103002e840c42e03000000000c0d241c000c041048034800044e00008110f500800c100000000384d8a511300c145c03109803c0902850100e082c003120049140007201a03445070200b0480100501703000c09a019a03401d0300c5480c0d0400230f130089966074103218880c00c0000165a4460303900709441c600 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 989256133 1250 989254883 989254921
    0x11e140a1a041a030d170c0a1209110a0501050906071b05120d0206150d031d060d0b030106120f0b1009110a0201051e060402070305090a0f0303110d09151e090810060e 73
    0x145481c0c2c8000c10386030700d4210ac130741c240f040e9101800c04070f4404091510000e040007400007400c01c0380c1820900004207025019200005103140742c4403243c0e00301e48520088240040a00820b01180300301c01e12146a04d444409001d04054070605c004203191a110103c0050000805004040407190640742111064001800c00ca400010103511250070303290140181080c040d10b48011030703250140000e040c04c542956005501e900c98070380780c0100040c0380114107100d05400006d10407164480b0840d080304506213900091000d031402c215014020611800f521a00b21581c000300000d988940030900b00500c03c2225015024203240016810310b02781c0e001e003240e41d0003450a6400d01e0510070200302000305070781181ca001e40001d0410010507522a1155400821060180c25003110191014095207124001c515040c00003950003041944984034184012182064803c05e0403610b41015104001c580202441402200300b402c0007640140503d1003140c80d08203d41029030f842a60141c1030740ca181c6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 989257383 1250 989256133 989256137
    0x10f0308070b04030e04091b0602030301140625030c020a080307030f0f03020f0c07151106070c02040b130c0905061e0703030204080f011e140a1a041a030d170c0a 71
    0x78170107805484030b1142d003211a1080c0c1504000c00600300410700c0803141a8440d00840d8070400040c44a50703201209695400e9055614645840428581c500741120441c017003007240501c0b000d01414964810f1510460381d00a845001c0901d03100c3c02c0080e140e2040440c064041034601204076101c074803580d4042589400d5160041c04d2107190100724040390702c4410740703140039400000300b800723441e55500b442c0445411900384200d1241000c1c10440e207803103000701940140012800d0710070554803184c000181c1d074103008011034500d0b00f01e040740c400205002226400043c2c2c07280380109617030601d0710442d1001c01580c1c0c807070b00c00b001b94070250a4859010a10441c01c15400f030100040050781080043e203c0180c1800105091203940d0018982c5083c02c400f080a8a042400000071062000a080e030800040c0ca00132800c1d500900060300c0c1c0c0b40440c00c034160001e103000480f05490301c00740c000c0b6031800c00403000d990038580c06407070403500d0b42580c6da2070a40d884035020218000701d40800042c40c14000318 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 989258633 1250 989257383 989257397
    0xe0d1103070602240403140f070f0506160302160222050115030f0207030509010e0d0c090b0f100e0105070302011e0b041d06010506090303040807060e09010f0308070b0403 75
    0x101010908007907141d4040000b40e0301c00f442900010b00a40310400040e0a100c0e40e68440785050340b00104281d0503114018080381c40003480e001a1243c0c0402c9803002e980200100d0401c2c2e2242c50070980d20801110702c40ea10410070042030f40464070a008036140070018082c00b00d0301203416000c2210341e1204020111200e044040880c10101c4103001c1d2034020581118084404100000c029040c0c42c0d240f242e26025500c1008102c00090700320040c0e40d0000b2003841c3c41c0d14040754000c0482c14130300126102a0000803aa600020f40c40001d0b045440110020358100b081239840e10148065079511030303008804518a01d0f40711016510440140a90601074400410f014040380c01d40c5041e5084a150022440d445482d811418103003405174100c850801c2c500311000c07403010303c0e00e40d07244c4006000e014854a0002120001d42d1b4080050b02c015100da8400d0303600d41d550b20900a4452a12a40c08034010010000001030560856522000303d0b42c0003042c0130700c0c110b51992805076044009004030244504 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 989259883 1250 989258633 989258663
    0x3180b03161b03020102040e010e1b0a03020702040615021002090303040e07020a080c06040b010506030f01050103020c160e040b06030f0a0623090a061b020712050120041e05010e0d 79
    0x7201242c07208070b0740243c00045e601c0e81000e607410080c001c141c100c00402406034003401805080c0c801114034000000f80c0f1a40c807003040e070400b00d02a110b544806940181407180c0070400019031a100c0400c1026034003221440e604815040e81079003d003a1440360706800c1444200300701400d8064050303121048e8410f0b91101511692080410b0b0420412441c00c0d038810020442007010160010f030241a045441a041d03182c408502d0303c03400014001d882c1003540120b14a100400104582c0c840646d200d8401c5056640300e494600d0340b810101d03002d5508143c4040400e201e4100803612501311903420019009000c5640c942c90094421034440031070251131907480c0444507404901050084500901134a41c80302c0c1c1e0308118043d00d00c0c0440f1080b84128510030b0007521900007554204440d0202c0c650f019041203410240d0050802030588503a20001e4504840003940400c01031050340c0c140c1e0321101d00103800c2c900100383e901282c040c09012883d103440700c0c1c4443c9864111507031800d11480401500b091 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 989261133 1250 989259883 989259917
    0x501091a060307020106030c08060a050c0c0307111504060305060906060901021207031704080a1403010f051c12050a170105010e220e0d090e0f011a0f0406090303180b0316 75
    0x590301401d882d4000c0c0080c050962f11a000762904200011011410700c0e4017010025280d00c900d40c0c00400d40d040020182e40f15460b0307221445501d8154000d13440d10303107640780d43c090301074581101c51510400401000842600c4d010054032181001170380209018030008880e800c181d03010311020f40c240f101454034604400c40c485d803210311891203150344c5510b50a0b80c0b02c0180003000d8446e50810800303008e2006100285456000360211801200e02002a1920740754414280c4c95800e0003a000651003040c1505164108004022041b0750b0b5407058a401400c03a801508154203000f12800207121014090a520b0400c003501e81500361100b1005d01e403120b00100303104441440e031411040340c2108507022845c64216071140d00405400140291a00d445840b8800d465414000c03403101d20a0700c2200c206a55180f4192044014540d401c260340d140c64402c003812490051004500084c3c0c407d1810b040c210f480202e003c1158a0340300800e0a40e25140e00c01000015101d040c0c600300840700c11074a15480d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 989262383 1250 989261133 989261153
    0x140307210e032b05061518040c0f11010207050601091a13200f04030204051e040506040212011514040f060b070516030b0402010305151002010f0501091a06030702010603 74
    0x42040ca6100b0542d42200c2d01c4481e00d41c01c2000710000303444c5007004000d001d4845815200c0e100103055162a502c00341c0c04180f6030034890400005401ca85031841c0c0b0180700c0e400256600e41c0c6071468840c01b05c000c040b41d686074241d1080480003031840d0040401000900c0403504450a004400c80d12554012070750303000709062021103114486411345603094a00390804451a20301041c0c050450306141106a000440ca140b1076840000d02070f41c0d42da800524484510b038001807582020707100d180200e04180c1441981d4840c261000d0b41f1424190458009001051103064901891210300a80b50740c5007210701c050200f200c06080d40c119850b80000b0101308050320070800036203401894262281001d0070f01038501514521640d814006503001030000c515a005466805617091a0104007a0340703040600039074507001c07441d064100104428111a598040d003046410110b1221b082101c1c1e07a945410800340c8440c0c42c1d4148111000000e0400c00b07050039802503510440d035000101e42e070b59a036541e0740701d01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 989263633 1250 989262383 989262397
    0x10e0907091122210b040f02120609010e120403050a1103030c030424080f0c030c120f07081f0909141e0613020117090c041b140307210e03 61
    0x350b5030b400c01c0c0103144c00071110b8400740c45a602014500842ca5403105460800030b04040c181020300e0254104541e103520309041c0d40d0280c0700c10b843c4141001000c280c068a0354118005440c010700303c814107035842d07446c00d031070440c0d8102004050280a5884a072520306540d035907140c0500042081d00d05590003080100001c0402c20602e460003440110692580600070b00b5400c204064402400307200e945003400d050b04942c9242105550fa00c81d42c181150310301c618a0345101030308900f010080d807203600c400220711814150b100c20071181d540d025610465001d0300c41c0340800c0c0308500707424070454a1a512200c400d034400c400c01c00c1961b61070308107280780c40ae250302e403000900d0301114000c80003101445000e402c0601810602d443c81e51650029090110401c00034100321520710016030825010400300c4a1044040c10401403054102c611941c43e0b46c0d800780c039901146e1090088000c006c0070500b03c0e4403074086503540341540420700c0120303404004a014100314907601c610b4600301c03442045c0010000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 989264883 1250 989263633 989263687
    0x509240414072a050c120c04060b0d0513240e0a05160608010b070f02130920060f03070302160b0106050d05010509151005160b010509010e09070911 65
    0x80030b618420300d034440c9203070f1040c212280800b8800d44001600020706401d00e030310448100716842001640980303080c0d8000c86890344582080790001d030700ca001100403c40c0c1685d02c00c0900c8507656290301c1d0038036103005980081c00303041c0c0754590010320030946198603524620b1903004501400d81c000010710744144030348142c0b883c0c1c10001315a642c800c039100c02600200198200740c10703658034100c0600543e0040c044080c04582d1921070b80700c110f42c0c80c40480d01100b400030004000040c06401e20341710030818441038508226584403c42203520b480301c01d456007070700d142e95031610b140d844881c2180079401c100307080c00c2402c03e2039110b5000900c00c4403009020700400e60301c140d11107401182d80419a40103a0040380600b44030018000140710300c20101c16921002d503080300041106140c2242e461244180d01000948168011810840c92400190403228110b400e80c142c2d989030041a04040b82c02d0396008aa940003180c104400140380e0428107141c2c401ea18440d040640c0c81d508001c81c1180724003c110 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 989266133 1250 989264883 989264897
    0xd170a021308100b030f061909060c080a0f0207081b0f0a05060a050105011106040b071101060f05100807050d052d0702010606020706211112010f050924041407 70
    0x4602601388100802410b0860041007840009102c840d03c2d10310207022600740c0c401c04507840200c054180c1040c0d51075a44201c0811090904c0d8000400c004070589404001d41e0a00505640801c20b5000362030800d46c00c103221600d0002c0181c0702e6500310360b81800e04a900c0c05401c82607190440c00b8020f003a825401000908001c0c5003a900d41811900141c110030305000124030540b0b0020000a412907029074005c80c00d641070b03101c1680688101c80d00995600456003824404604809070b4003003507048840c00d6684808103540d45000f503c00c01011101080051f009120740a03445a01c0e400c0380d500504520b64281c101c19400c070102c24003140800c902e0780c0e012050810b03c22502da09204031001001140f0140500d2810300c44000c0c8841d07040c1e4041c0070704249000c50403100c1101270740034000c807603200d8a0060b9070340c0c0313000e459201011007441145007014140c000010f843c100700b03080740d104400ca104450034040009000301285c801412140341c0040d40c0e980c00071100c0010b20b140d207000f00714907244c41d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 989267383 1250 989266133 989266153
    0x415080604020301150f02100e03040303030509011a01120207020414011e05060d02070201030e030d0606090f0f3b2208161505010e01050109080d170a021308 69
    0x250462402604003809144104010410840300001d156074442d007a25041401e00b04185003289422412680318920314540341d080c0074503400000041003181d11a45080c00036680f00c4614508a446030041c0c60050444c8000a1035598440d810402115654010042c1080a0398000c40c0172504139003108102e0b02d003140018048225004410781c035124102901403820b40c14480031921900801c07458110041e000f041e440110787c06600844007007510401200d8880000c02281e901a00b40c03441000b012502850010846643c4442e800d01680c12522402c03005038508a038100303c0c0d100954561801c131a0900c9902c080604038694940008214001c1c211541040c0040b1407262058800f513811500f406444031000a030130006503940b122402021440740200340c117000d0001000299561122840d15001084481401014a0580d1001c1e0f0310020007a494017010b0b6a254080010300e40400d95103001178a10110040c034940e8400301a40c00503050061070340b2101e1121105800c003801c0c6800c8040300c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 989268633 1250 989267383 989267387
    0x1020c01231308071e080c0102100b0a080613060606080121031b050705092d060307080604080a0f08010302181b0a21022503140316080907080d05031b0415 68
    0x180080c0c48010003411f4144164030000c0d559201401420040607180d8800420700e650301044030b402411a0001e5a0301d40c17400880d0011551038101c4121059481d0003000705501c0c0c820100c0505031240c0060920015103040b90403002d034a034500d0100c04002102d035401c43d09000c8091000072040c4200c00034500e82c3d0410b000c104400600a1550300400c101d42110304861501d000818240404010141310316110351021909041d05900112007a125171410b00041010341001400644403c2d5035103843c000c0c0589003114202c00a102c040e42c8041200c400301c501000403110b403600162014252a50031a0351440d14a40381c105142110100e00e0003860040f03600740402003107410300001070046280c9140403181c101441c0f140d00148800d0000e011460041501511071032148402c628441a00d928042c2c1ca04c9800d4552441007100180200c00441e105a41c0040d060301540c90400140c1002c2a0403101129260402800c181704010f4010354506c03c00c0c207100040025101d042500c1c10040100040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 989269883 1250 989268633 989268689
    0x50307120f030c0e010e130b0303070311060609060f060d0e070b04030c0801051b0307050412080307110d0e120a0c03050732150712020c01020c0123130807 68
    0x1000003400241c3c480c50505a07030001d00c0d12114442240d1042c9074170b0307d4504150003002c1c1e2011141e018800010910309142d000611a44c0f12444e280032a1043c6c1d40d10403d0114031041a100141c00050300510340d141031030042c0180000180302200080d0072a00e0301c149602d081d140b039210003201c690006e8140709100a00941c0030161048c14002e028078240707210050000880052000c0c03c450740440400e403034a00c01c0d01150000d0000c0e50340b104001c10241811603c035403041c0e84500100c3d050100c034041041010914179040ba0060315003410210340c40c03050241c0d4100440381410b02e80103202001001641528214010b940200c004044150a2415211403103508204604402c4100b520394400c40c240c42e14841074140055410800801c04820354400300d0042001c01030103080200d81d0b0b641c0040c1e00282c02d010664090f400c442098050310019100c01c41060707004101c000e240d115003a9141454802015922241003c120b05a079803810014201083c0760010001040044501c00d412044100703 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 989271133 1250 989269883 989269901
    0x60e040b09090c01080c0d0213051003051519050418050105061f350a06060302070f02040e0a0f12122d0608030409200304030801060309050307120f03 66
    0x40c0c50081d504240555a6a64034280302403410011441c0006103008400029102c0c44c030b000c21429034450100c11720303051010b00715001b201c0c081d00f00302c00003545051003409070030300800000c441001980740e40c20a0140c42142c1035031142041444ca14009443d46480c82031410603852035201214641b181d180150039142c0141c04580702d6980200823908242140541d140c2c01000d90529000040016456100c5001a4651140301c291140ca920341014040c0c0704481c0324070380000b810040e068407264180c0132030007810005440020200100401030902e5440300d507050081d0000c551071240745035283c0644954002c000c0f6400d18411281c4850660800c602c0c03032403054482c2050044000803031210b2900c0080d85000003841800c240301c543c2d560070355800b450141060106581da61600c500c01103018000fa0800b0010540c0345048514101e900301d420360b0300899241d5582c60032a481c000d82140940341400d400d568500080002d6000282500c0c1c0d128810181515881c40440302158040c0480f01641 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 989272383 1250 989271133 989271139
    0x30c060201200309151f06090f0b030a021b2a131a060a0216080a0f080a030b040603060902030c09010305061b070506010b130b0702030c062101060e040b 67
    0xd24491960005091031412200c0c86102c80d203983d1024602440d00b0164621288158036903024000700c41003090200d04a005614a0030030203941e0f03648219860906881800680f550202e0203018202555005507041002401d0140c208034000c06601075400601003505040ea002010382c507036042203080306203001c12541d00d1140d112030801c40801e02c039001c0141c80d950a40c2e654403c1c4042810380669026808001174640d036115911070350041d42e01c03031103c4501d140c000215100040c0948001810f070034007503444440405041803076a1445c00c0c64111034558020305485240e10600ea440720b200e110b0066018110120310040345006250811441c175203030324007a0366034074010f1012902c00108241c00900042914011210001303403019a0b01515074000d201c4d00034840005000d45004001d002e180a58281c41805251b8403041c01000e8030400070000d4241c1c01051041c00e040c54008061300780c20150b464580d950712802440c404080d1426040072002c240c180c10703420320b5030a00c2e111300d40f6241c07825 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 989273633 1250 989272383 989272391
    0xa031407020d0f170c070501020c0d3c030507120e030301060806060c06010b030606071505010807050901230a0b0a030f1508030405040b0d0215040305121204030e0a120309030c060201 80
    0x8007181c2130700c07010050640c0b10b81a0005003003001c00100758100d030500900d01c0d05695891280e403034010242e03030300c0c0d02d000c00903c107a08055049040982004600d41e580b414513580b105118a0411340250070000e00580030300c50a840303015420354940c01840c0703134110035001641d0342e58144080580041005003c160086c6414090740345849000a000e07815990f0454056840e5500d180009400340b00c0d446008006114400031240c102c252038010321705944190007600c140340d840d2003d1201d100e00910507125405c4e41070b1661100f444d5001d81030101444040c1440b1249511103d050403550300947c04200001c0d902c54807851303200744034412070790900e941902c100c085500d481d480f03030b64a0155004252241d99105003100c1e03943e4540000c4900c0c2e6501a1270500c11607045550b04c2d605070410b100c185da180c050002c0c5001ca242045045500d074006402c0001415252510125080380c8022005904800010300c0440d03884005007a121000340310b44e0390441643e0440c50089a84040c5602c80c2c420f40e814 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 989274883 1250 989273633 989273657
    0xc08070f06260c0d02040f0509070c051e0c040905061b0415030b0f10090305060606131712030c0406030605030606101d040501063507050a031407020d0f 67
    0x1118000345454101100c150034544610800f40114420428003104c10751000a00048401c500784541d0211042211801c023250380c0e0860940c0c50b940388002c01000368006640100c0e1400819004082d954203107000c036040c0c95042404a011591a10825202680004100008004210706e04d0080d60b00e80d142c1c0508003840c0030320041c0f00b0800321a504085c1078440c54040c20340e07110500000e580030b40041044451020307102000d4540901c2e40070913245801044002596400e00b0343c101c5400c04c0115507022106071a006220000b1003002c0004201400342c50100a00d0100a02c00303035000f800000982551645000342c003400312a050b5002500a8004104011840e6140d84a0783e1140061713003440c0109402a4030f10400c50046604c1e80c03584149003400200f410b42d444014070100e200c00311184e610044025003820103103000004c0c0810b865640b140043d034654802c502400040d9034034140468400e802241104540d007040342c0300c20069001c00c01d4640074640c40017103241c0400e0319091846031504c1c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 989276133 1250 989274883 989274917
    0x1030506181e0102132706080c04020307031503030908160e06090717011e0b0c340e0916080307081b010c030b10030b0d0f02010c0c08070f06 62
    0x407100e8802d00b600c50b5008030350041020740444a401c8002c480c40c0a6541d141c1c420400080c011b8081140120980030704120f10045910808040d01c000c0c40090481c00401c0c400c00c0043c0d0320080800080580f612031312084a03043c0c0b4038507001385200e503c81c038211038105100c4514142c000c66a4070b0f4124411141040480006178078540c0001007a1050f500d150745450003074a840425581034644840e025000003080c00404515001014412200c0d5118942c0c4100181641c000c100d088481504168602103126800e1495040c1081a4076204800601e403000242c00209055202590410320502040680101404078550542400c035800d00d446041140b00c950300e00030740d00e00800704c0324001000041440c1880640c010511042e00a03c94500e0a100040c090668030701640d005141407401c0e000c02e98080e000d11005c6000113824100c0700b0029403a07119071000c2a0f44107905006684205c800800d8030001d25102a04151000303084142c901281105401d0441c1e10800c1045551420007031120703 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 989277383 1250 989276133 989276143
    0x1608070e011704020303130e010e24190527060901081c021204090b2b0803040809030607050a09050d02010801090906060929040c05191110050103050618 67
    0x10b0003440d294449591944086895032140340e409082000d503a0301c00007030b0300b009643c141c3d060300c0d26400200c0f4152078800000254030316407070010504906000ba8190b0500741060b41081511a1100d150708103036503007010448001c00940303d030103c5170f002601155034000d1101755503000b5005841814184d0f00d0084600d44a44081405601c001070f00701c010030a03039208008600c04450003107070300c40e607980c0d8601102000780741c5034100c10301030148180070350a40c00104440000106840c8c41041c00b00707200382e46102640d40002c00403a244a810320100185880400400b8401c04140c1c4489a032952f944201400301c0940f03611251080030302c01020801070740e024441ca41168007002d4081019440c91603c0c001500c0c0b0354100078251850b0600c1a60700f11500008105201001c002c1449068074282c103000c182c0e907603500d5078404204100302000851001034203441c01d028180c07038800e10200500c0c04032810019802e00c1f04031542c1c0c43d60010300c2030103000c4c00516004541c2a0031181c0b0f45040401c0c6035192 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 989278633 1250 989277383 989277407
    0x3011a0a050d060e15060f0306070906110312010f030215041a030a02071b05120606030604030f0203070501061d070e09060405100b0c031905040308070f020a030206031608070e01 78
    0x42c5000707510b00010000305400c01c80c0f010b002803050720014010780c1040b0b90f00301d40864203284668001010003a0b90b09001ca291400780d081c80c4d0b10f0b040c1c207904100701601c40d080c000c26008490b10007041090620000b0780c0486018002001c01c0304111031541c010402c450780f2844500541c1141044104071000901c20800f000c041c0e101225502c960320241c040009000700d0360040d06802103118110074500440e500d240654400302d902c00c21001c851100346544d2441141d000e41c0560108001c43d000c0703800342e030540d5410105407048a2070840195622800e4170840e50013012141c1c40070702005211592500b0450b48a009440c0600c00c02c561480003803840d02c005040c5034010342d903540114510311087c1d401135024009d620302c1240c1c2c410104e040e16a4039803044522214010700b04100c0d0601d58403840840741240d401c60075290070084143c03540c044400c1000c4040340d01c43c1c90027000000503200c00c80918820a203078400158880c045000103400e0b980000d083c8401c1000303c0c4503042582e0f070400b0703c0182d4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 989279883 1250 989278633 989278639
    0x60c0f04050d020f03010e0705150a02070b09033a050a0f0806120706020a0b1501020304090f0605090c280909090c0302031507020f0303040c030b07020109080c03070203011a0a05 78
    0x2d01242c3c00411502820001d4858055007084103148400200051041c210340781503d0b024140060b0400712517440c001e800201c40146c20110b020400501c2c840040d00700c03282c000341918895400f1869030721400404204641040084841c003081c0c540c04144210700c1c5169a0505900e044100000140020400d404002c180100d10002c154180c0300d810305c1c0140e8641e00f100329520f06450300b0011b5544c005510b002c440314421400002e5000300c0030f0002041140f0181c004608040c00c00d20108007420000885009582d5a0381000803e5604c00c04103e005061450880343e50b1503150030004298410b0194103d9a00844c80c00079450b41da020f8004001c6482111000400b50501d00d400116080c550380080e60602c100d40c940610120b141c0c1045026160a4084030040c2498254058580c002114007501c001c6e010030013000072561415041d075001d0307242d10000603505034954139109070b40c01160301241c1e9a400401d0700d004508007440342d4001640c141003c1480352b25010005038030560745000d8240 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 989281133 1250 989279883 989279899
    0x3170601080411271003110f01050a050a020f1c030507110304120c0810061d220201031b05030114031603060e150a0212061c1e0503120108060c0f0405 66
    0x141040141408003040c1d04c00880c1615402c01c01d85907604082c0c0c0d03002c207a5030b04204803000d2481d40f600501c219154801030f11080d04000c03142030203440c29000320015800b0b50050160034000c0e200c0c1407002c4802448a04c05440c109180d64000404a61008103070750107101c144484604c407104008281c400f01d5548501101c03800f5500c1c0341c80d80c10800740c1c0c0e015070b413a1f20034030303003482903002140d0046019560740200c040a9039410511602910f842a01c3c024001da0400180442012410300000049401130402052888000b600d040d642c1e2140424400012004030040c4446040c1c00080e20b00510b04800400c4d25403141760096002d0100b503c401000560785032020b039041c0b00103111440781c01c90640b0801e1580e01e03021042c20080d41c004000d02090b40d0404000810038a030150342440b0007090310102821a08055491812541c290440b00c004e5240801c3c8000014a08000030181c000040310a00c8665141c600e1251420002801c50400d150090180c120ba10f0211400c1d10203c41c41220303070030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 989282383 1250 989281133 989281159
    0x3070305091b0909241b070305030408070c0e0a091b06080112030e09130b0106030507050304170f210603060c07060b0402090402120916120308150d03170601080411 72
    0x18640003e03d20f910142150303141c00507182201d590b001c0c074810000640c07203803100100340c06c45014520070000020049030702403020401180900000c0c05603076109400403000162078144440505030200e5090803502d445050368010088114021000f122482542c030111038100710004c3e160b08014080e9180301ca9810380340c201070511401a80403c10009480c1c07038500e04100620401060040005441c011a0b20f400001c510b0700c070380b0401c3e00c2005a50b444c81d0554580d035a03140f001d01c11040558505100900c80900c1c4200d10400410381d07110500700409515100580d40550b80b10000d024510035008803041000031280c083c111a29181d000d0030000700e035000100010000d00030142c4040c1c02610100c0c006440c1c10b00505c401d0f0090083c2000c071054032180456603e0a40390f14043c1c0c012905c0300920040029000f0070385a9044906014600001c0041d44081b581840003848290700007281441c003003002c012004c02d00340d040b00c000c1c40c202ea00346c81e0684960b8400c0d881100c0c41800342011404d46 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 989283633 1250 989282383 989282401
    0xa0f08090a0c03140f1f02130f0b070506090c01081f1505070b09010915111e0a081509040b09160b091e13052a03070305091b09 56
    0x25014168002c4a62240c00e03103a00304190709490302d03c4e09140303610a864043d07400c038800081b100f40444000c0701c420203400d61403085101a412028034001303281901840442c02d0500b08003204041e000682c080390302d03803909041551030004003900904d07542d000000301c1070385644d0211800307a20915462840000309554550340500300801e03880a1a0091304280c60030807207a0180080c410706004500210031515698106030881d00c6002c0010408a0540128501800160800786404290700c0549003800418801c00e10010010104509860030001e00c03800b62681110b40c09800684a44940541c013110b180400d0031914086c0000e0040303400040000d10803070081112000070818002c80d00c0c403841d81d5443c03a0360143c00c90428107100d4407108075103070308042c22142e64280c00200140680d80300308520054500504000d407040d040119040c1064000540020ba4000750a43e00d0b0b00f555546c1c03030a442c00804403a405001001c1d6a00302c2b0740d241100070f411000d040e010324801c46000c0510740f02d000ba0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 989284883 1250 989283633 989283643
    0x7181a070204050c0f07240b0d0b150a0305010c1403130b130210031d0c0d080307090506280813060e19050a020a120b150d0206071101030e01020a0f0809 67
    0x242030b110380c41c0000c00f00104417034000002c2c00b04003010701070907641c0c00c0c7c0c3c1d2800c1e00341c60415034040c1c0c2108503000c0580120303c04400c00c0c0e4110f4803864640116614250106140d440580c1055031180c1d190301d01c07005c40f10350140303601c3c0c10800e0000b445800d50810701308450358080c45110140c00056147c1c00308040c203402e0000d520748250700502ca10500c1c4900407001d030150051880d100e154076404c1040610b0901d021900064000c4001c01e1109410380036594049140c00c09415641004255500440c503911500c0041400401c02c90074404e045440128824240319603d50002c02c12640d403007401060180c8000312032041e40c4c40140880d82411130a4070070b01e089180641c8440810341a4844002d1010209404c80c49034001c0d00d00c3c2c1c10554076121a221950300c20f150040101107000002800390745507a0501c2d80b5580d00038185503c03e0044e40001d915904452401e07120044150348001b090740c0c261090028103014007000f07604000c08190040e04e20b00312007010340c00388101d450000300c0307480080c45 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 989286133 1250 989284883 989284897
    0x110d0e04020909010603150902031e130803070c1110050f0a0e0a090b030f010e0c092e0e09010603080316090b0d020913050f0411041407181a070204050c 67
    0x50b8260f80d680d502001005091050b0301140050040000402c8182c2c0e00c0c000c50340309403c621103080d000022200c58482405004200f5500882d41e00528800610010003c50041a80740c0c3d03100010303020750400c00403013241100c42510801c5809074417001550080113480010401d81981e40d1600d103081000e4600b0781807051403e502c03500000e0080b0b96a00e042c3e00090301000103804643ca021180c1800c0782c00c0300e00744894000c2d150301c9036003610a185040710380c9603848403c0c44001c005440101c14030346014032200784a20300548076000c0074030001e0110002241e0201c01031000f07100081c80d544454440b40710103800c2d00f07140c0414107840c82d034160083c0210801041d0380700c04a40c0d941c105000c148000d410900c0442e00ca14518100c01c136910b034050040500070441064202d5146e21242e131101e501d244440300580c0c201d5140c10355426403078107121110b403040856444810800400c4841ea0104c0c070100c0e080305040017083e0b1410442d1240e200c0507140c07240d9040e5000599512a1340f06c104560103648 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 989287383 1250 989286133 989286139
    0x4032f01090302030a030b031b12120c010203072601060302091c14160b090409150e0604050c010f09050f06161208011d161101060b070b07110d0e040209 67
    0xc1e0210201540000182032107130841c2d40c104015030b010701c10161a5505c0180180d030404842d1640540792034081a20151a0206403c450b80c84818610010711500010794151869501004001045401404040203d440f0358401142e0f5402030317000105000041c0104800c1503408507500b101e40e01d0341c548003041140c40c103103c407050414901e02824440151003607003085008901400c04400c0c041c554000a0352034402c041424030305c10205010040500c2a42507800c03290f648038130106d03a0221311030b5002480140303000e003455203454103244e071400c1c41c000c2e0703080d0400c9101c0541c10001d66203c0e4042c002d81d8401c980c040c80d02520840000c409002d000d1014411701400b4220004110880c5004c0d001d05842c3c0c0c0743d05035941e030303075506a55800c070b803950310000c8500105000a0241e011801080d00005a074248041015909c1d644a82107402503000744030a4200050a007040c030060307264107540310b101484c04080b03907071002100c25119040d40494406211504002265541d1546c0550f00000b07806 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 989288633 1250 989287383 989287391
    0x10110d030b03011e060f050f03030a0e1305090a0201030c0e060412020310110a02010b011b030c060e06070f03050a18020904051f1b020a0507140a0e0109020307020f0604032f01 77
    0x2c00c4000c0c0c0101011b00c10307408608400720002809041c17041c2d01c42c0100030005e000d5400d081e1200400d86000c01051195903004d0719035450440f09114501c240f5001d520b6243c001d016588940c400502110b141060140034410140350030404ad13070f81d05003203400b80c3e000070010300083c400070320103c0e18229600441400c05414404500304141100001d04010340702c42d8001c0c050403048200540300760405450b02c00c0d80c2c001d090360b0840030902621440603c54890a40041d081081500d9281030030340984200c400a240a1584ac1600c3e038540111900300d1080e400030001044100f1000ca846101030200034060300e118400034042c0b01082c01661403c903019841800c08288a4012100401410300c030380c0d00b621080022005120702c0010b00f01480c952000c028966542000c46600030f1f1500d03031520682c03003a0303080c402061481c1c07000a290f0090000c0d42c800b580303d080c50740f4040c0c1008405115100310790310001c2044042a440702841650340140b6100c0c294484050480c0300003001c0c0c183c0300134255820 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 989289883 1250 989288633 989288681
    0x204050405010b191d071110020301090c03020903060103291e18150a0204030c0305031809041a0703090501050f010e01080f0a021c0507030b0610110d030b0301 70
    0x4190030512681c0030403500c24049584c07400c22140c0b00090340c050340b14050440c0d01c85207000200c950803503401c142103040c005420014035203550310f0808440c9240b000c2d47d801100401c078281441c02880d43c60b2009007019801c0411401c082507964205200180041028400413920120309052103410b4035480c0d110300c45d961508a000100a0001c4924002042e68000000c1c1014a20004803018514103030043d041000c0c0181a6111020700a400e1046c4203038200030000024200030210002184204069500e482950048a130134100300d043d403500840000040000262140700f404007148250340e02408079866400c4110024032641100030821340c1703080240034046003c1c07a440c904a070802c000041c52130f030700c90090702d440344101000c0411030b5120500b031500501d00034410a170959004100c01c03290781c1042e11038034580443e80d030056545044820901a80d42000c01080d103c041c040e0408842640b04140c5095440c465201800101580c071025020507942c00e4004814403060011016039280c8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 989291133 1250 989289883 989289893
    0x140a020901090e0402090a0c050912070918020a03170405040f09020f1f260f04060c1d0103020d0f020d020909091c12060b0406110d09030b012102040504 67
    0x404034100a010900301d20380000d00800d140c0f0780520076a0301928840003a101c0001c21070160a05101d80070501806012010a81d03c0e00030100100c10711000090004074030f01240d030703011503044aa00c0740100345500301c1c0801503110302c803095003244c0c5d201c03044009018450003010002c1c02540c000301d0344a410110244085485604401c0e000c50003100d000c1d40c612418400c0022007134220102c0300f1442502000080104e00508421901c0e070640021103003801e2501d0300803060503608540f180382d420341070b90500050040c54441d43d41401524100040411060018050004c2c500a001030401d0340018101c00c0d130038255000050203045400080d500e42c4c1007081c1c3c0c2d202a400003031900340504c8845001400d1075100140341180102117018a0000107040c183c11503041c0000c29441c0b8649480d070794001068502d98004000410283e40c2d00401c2c6004946424206410344940e6420001270a400307101190400c4445811540e0010010000010304c4445601034956107801030f52152800c402c01007480 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 989292383 1250 989291133 989291137
    0x708031824010302040b120601050f010e04020a11120f0306120336030c06041a130f05040501080606010f050a0c0506040b0a0b100c030309170a091e03080706020d140a02 74
    0x34400c817401c0c032424441c034041c07025400505030f0741900b07070b8000401041141000c800904200340185010f06103000b80001007005c0e07900c80c00000001544c150b0345e5059041003403000d503440d503c9105806142840707003a4802594013000e00750500c210240d45102070424020021a400a40301000e08602c41c01d5a020881030400c0e0b401ca050041085000c54210b6843d01054070740c4010002030545007418200031b20a200d25075540003480411000f0024129042c0d4410704d4207008281c0c0c01f80d52030105050034188415114103038411a03d0303074010b009004c1e0b16030b0458001c0324141d06074600103072282c0001304102c491340b40001000d03185005607820701090102002c1501d2144514010a0120ba8843e03800c2c010521542e65401001500052440c00080c0c0b10360080d209d014001c0f066940c0c0003a840b40480c40c9580203411150201e08000010842c02c1080d0340c000e00c9085541c3d103121407035840d40d141c903c018480c103d002005690700180c8007840c90301d19401920305200c5207007480e41910380310550074025 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 989293633 1250 989292383 989292389
    0x5070b09070e060d05030d09081e0403051902030d12060f06054f18050a050a0c09030215040b19020c03070b0f031009151a070803182401 60
    0x1030307142200080090800082252004d94014011841c02c0e03d135100395801854004001c4030441c0c0308000b2440c0106c1c00b4911150b400d8120402580d6640c40c601d00a8944101c2036000343c1d0a28141c000301c03015903800b156402002c045414011104103402000d48014141e0b60841801d084000350081703085680302003d458108071800484a2507010807400d1640c4c5045200c0409a4030074818940010310012442200080210303a9080202c64440014010f41240035959840f010380d2002003003155440d6000d002c1c1c000841100400580300d44100082043d0600c0c040640030b001e0100c1c00b00302c18171030b0004030f0f0700030f1101d04480f603218149030320380308415070380b1050810051003405800400e510300032a800c07080b0380305e04440c14074007502c00008410310f400042c050340c14201c000c54002003480d03d50040c028850101c40c00000318178200400e045224040408144004100784900320000d40060100e070303001800552400300300702e540b1503080c0c6044041d0209048682d03c0603545141d0446009007076041e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 989294883 1250 989293633 989293649
    0xa080414190b010b13121104020f030402010e0a030309140d02030114101505070320070e0619080c01200a030207150c020d0b0a0b09091005071b02010f05070b0907 71
    0x81e44d0f40c0350a5648207005400305200e1251030703444104692015164964501481a490744109101903c005030407600544034007030008000000700f004640e8030841510208104132480e60140e802c51310002c045030b00134014203211000038010312401d669850600b00c042d41e80100244400040545002119481591203030003002401c0300100f500021502c000305020340c190381b03071340c140400d0f504c044440102800907183c4110f1940342041240000b446038802401022222090341d0030000b0a01500107500c194803654050075001c140230702e600c041030300180e0040034a0141c2c0d9461184c2c0d141d4440b04c2840d01d1460781c2e44100074103c010503030080303a241c0c100c80d4542e88070380c480c00742044140c518403602d41d1f00a5100b42034020b441c0000e20fa5402c21a000342500c000010710400050105074a448195202c4540341d000650b80306110450f402140c4e480041d524010944454030f925461012840e144000e06003c00d0b0b1038003241181c41003066a40c0550054081d809508000240640b2404079000b0342103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 989296133 1250 989294883 989294903
    0xa060b03040809150a080f0a06081518150a0e0c031e1b031005040302100207080c0f070b0f0a0c0f030c0201030b102007050a1502060a110a08041419 65
    0x20b4035101001e80b040c2c00f00c86d03220445d00d0ba480c0071102d0008080200f00c022042d80e60030001c10051001c025001120808488020007070400e40020400b0309094000b0400300e40c40404d034510f1500108581ca604040f000c1800b083c2030030000781460404100300c2d80305800d4400c0440d10500604010070f030704010070590050b20000c641c54543e4035185103500f06600c0d0564041200c5402c0852941d00042e8481e010f8810b40c2c610b419118580d8050303911588003982c545901007964207a00609126030542c55010710000e2009901c0d054580215024001120540c00c1000c02c104028600680e003e4403e80c0d809219103003140201d14000e020040c0b0f043c802e0b4002490400342d0140c0342448411aa40c04a15485002c2d5001c5240c40000d2104060120107400d405250000911515140c442c4405000c0e0540310603d000b100d0307000249040c8000306103100b4641401c00021400c10020121441c60340146030a03000ca9440342088080c0100c4400d255821b07202e0005400c10441c15420043e010034031403000c40f0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 989297383 1250 989296133 989296159
    0x215014202070f080a0b180703060606022b080402010c0f0203010c120b040b03030d020c24090d0e0a030206030604090c03051b01080903090415030c030804090608240a060b03040809 79
    0x759603044105e01c0148245000c00c041202a05c1d00e01d280041464807604854a407a101e644400507240e80d98088000342c0c6c031010007688004d401207a80107800c04004401d80c0b000204920080840d440a0400b0b814403890140b1102400100c3d070350200740ca9005402486446e12042005103807010007000001c100349030000701d03502407030503015503200180024010b50404801420190007540500a20391031449900710800702c0110000c1081c2d4103000d4505078483d50f18004100e5400c0802502c501ca0030052880a29545580d8031030135038081c0c0c2d4040c1d41c2140c481d1783e04001309000700301c24038000e010740705041000820460002031102c00020056080c0812211a10042d0303100f8106654850240e002800000075905040c4e01020240c800700034074500143c2d9a45034190b40f4800c42d0000c4d90f0039100094148a40840790082c000181000002012001044601c18403166030803400701e07090f19054000700d00000442d070014405009001c4a0f1075032418a0f00c0c00582039400641e07480e004028450b241 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 989298633 1250 989297383 989297399
    0xf0304120c090b0306010b030a0f050a0902010e090723040e10050a050118030206030c19020f071202010c170d060b0d0f020f0a0804081201060206070215014202070f 72
    0x543d03149000a401880282d082c030201641c2900b004010030b4119070344880b0010314010074010306000d030130700500000312000380340001061821207504090050b01c2aa05225135540c2c003080015a03d0807141d180c03500c0d1048500025100d102e00c0c0e011a02a0030004184410042a00c0c81e10003102c42c21600c00d40305a9a600040d6000841114210344c40400c1d00703810005401e01e0380055038009200316082d882c194401c03290800c51035084219200503072040c0d440c0c03c0c0c0c1840411048000d4240703045990098942540024405400c0c4171004005039107200314098941066002e44808400c81e510a200080e141e10b8603050b96000108216000e508040c80c00c10041e40074421a03103003001e5402d02c145045074050055034030810260007221101010001d02158649450000c1c0c060100c0f58040e02440c00c20410080c40c084c020104d600307103a105a40104109510407803000c03503c0105880d61124842940e07800224410900203500076480070800441c0c18641c0801c0c4d24003038403041c0403544c0c4059144d00170 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 989299883 1250 989298633 989298641
    0xb0709170d020f0d020c060d0908070b01090501080615060901030e0303130308010b0405240d05010f1d241512091009020607020d08090a030302030a110f1c020f0304120c09 75
    0x82600546c0103807200e00102e003030000080652003480000820243d40581e030311702c0070303071310603074064600301c0c00c680c0140500503080c01103500400c0c83c1c2c4000c0c549030604801415244803d104d24901c14a000203000940f45d001c0d03000801800d148405807a142d103007a07a910140381c148200100c001031900c1c400450b010760000103940a03118007804020078070b100000000365041030b0444d5003030142001d0042e180000f5403801440d01a014004042a001c0d02e4120701c21901c9403d10b900000c000312043c10810405000c01d8030340389040b01c2366480c8044105101c045030300b40c2c0c0c881c400c600752120009241c03240704106001b41d501a15141040b00c1050801100b66011104040030095004804100e078402510f040041e501440c0d0141003881c1c43c00903c800000c80881290f4400c4000d6000400c000701c100e0380080c18990701e0b0040d02c010b00105110200380030f8540302040d00e02049480c2081d21a8112031082001c0c410310070708082100d42d42d40d00c81c0039100590310000005c445d0002a0000800d030301c1c0e05402 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 989301133 1250 989299883 989299903
    0x80102030a0b0d0c0b030408250c0920090d05030d0b030c10021005060a05041503050c1509060c0c0d0302071a04081b120111091806030a0b0709170d020f 67
    0x10056506040944205d5a0380c4080d105840c0404140220201c3c061050005556020130b03064402c08031940740340c050314210155000301009460510039203035040300c0500001c000103c102c03200f80e42c0c0b0350a00014115881043c800361042c4030200d59042e410034103600201401d8011411540d1a00339078040000c102070200c51840160440c01400203104026080981c1240d8001c14020506840300c01250894080f410350400110b030140c010410f003c0305115445103604e05680c01e40032506406484442c900c96445906d0007640300168065821038280300ca03441c10a030050080360003000504000b580c1c1d04150080540d04418580e4011902c00078008681c00ca40d030784406400d84100013509480207a503139461254025000e00b00c481400503081c895503131705403021581c841e2a25a07450a10440003003072100a08207c41e0030007805026500022442c003151f6000360084000d82d101c20046400004940c0f00c0084242c12450f06540840045114a883c01447c3c0c00c40d2121020840c9a582e6031103840 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 989302383 1250 989301133 989301143
    0xb0a0605180d0206030f040c050114040e060a0504090c151b062a0f0912020a0b0a03150303030c1115010510020f120306030d090308181801080102030a0b0d 68
    0xa045140100181c01000104005020020242e00d5030041021075100316041042c800901d802c000c2003014802040025100070710f031016001140403480144e903c40c9010301064030200c00005803455880710860b801070440034005000048061610b030407000214022000c84103461446080604d110b055282c4a000e404c101810000e02d481d00c5010080c003000411040d03401e4600c0440e40c41c40303081b1420300e00c004002e9a41003002065608002c0c8820a1600400e042e20405a0b00c0400743c0e0718021003400341c840598002e5035445510034158010300d030845407808480010341c000014150140e100d2640090640c98124806801c800b000784ca0792074020610030040342650042c80306040000252101c19002d004841410602100c80c600d02446001001615100041048400d0505100100f002c909030b042182d0380ca811540d501d0b101d030165102d62412840103002140d4159240135928507111400703083d142d4503584650354030340030390710071148081031380d041966004141c10700c880c01c40c003115084 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 989303633 1250 989302383 989302387
    0x513020a110a2f3604120311070c080d080a0209030a061a0306040c060f02060405060a0c0509091303140f0301140402210403080a0e1906060918060b0a0605 68
    0x2000b160202c080c06030b21400039102ca105828a10707484401056130820145400102c441e00e14040c3c0003444105030880c004540500d009110018800d684450001c035050b04001c0390b020400108808280122000a008401d020f24000350034400801c0c6c524642160750f481c1a0a6904c886140c41030380b04181115406600903001500800c44a60101452401c0030741c404008803825400240340c030b0819a800d0700c181c15200e0f800c200350b94202902e03007070b170300414005040d981c5807680300e00d519080014801000c017600c0d200d020a8552007101180c14000c00244540c0c0c060030501c1c43c882161801c0181180483c200c1e201030109140d045040e50a1500003611440c91682040c1c558042c04400e403104d103400076028000c0480d004034403015138102000036001c24400e481c16040041460601901c81c400003450008006540400890202c49141500021040f4100c7c5443d01030020300e0b07280e0107203068501e400240b42e50310160348041c400c60f40c001e0106112000b0050100135094045120752700102c1c0d01 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 989304883 1250 989303633 989303663
    0x6030603211206090f05090a020901120c030204090818031b0103110d1d0c24030403020a120c0c050907020705090a0f050114100f080117070513020a110a 67
    0x1c06003120200c24442c5030203a08050030312980010741d0181d42148a81c144c441c8243d90b0043c502d0302c103441d4064518401030481d28070340d80100b40e00e0b001c1800b4480c401d021419494040c0b10444e14410010340e40548200119019400d00301020f40250ba0207603605a81590380310180e00c1e00090741500c800800a6540c0d1071031240300194010f0003000308a8030f03004d8050124400100103441400d140c10325810300c101303884030300602031801c014245800c90b104600207001c1036281c0100140c8405814541d03401c1355525100e0b424181e00d06400f40f003008003504c0c8200e0700d03100744590024000014610070f421003880750b52902c04100f540c8070216400e600680c0f180c1030400082c5041006960041c0c458080040c2080083e9110020380d6400d070048981652214040503440c01c2590b20b4043c0b02005103407503032040940d024000c1100c031040c0300e82d44800400300d580403561007042c0403500080a009002c91440e40014078940060b40050003d400416a01154018a036102107080c40c0220340c0f221340e401506070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 989306133 1250 989304883 989304923
    0x310060f08011a1e0c0a03180f030605090c310e0c060318030d0b090a0b18070203130e1807060f2316140d08060607050111070308090706030603 63
    0xc504c44414444035054203541500c1c104005040510722003001e004142440c0c01c0140804960450100003040304c80c1f001c20449914400303000580c1e51210000c50680c070390f40c003010710f80500243c071203a01c2080040f8400c8420f20b912030710f0b83c0ca2038007811421004000300140008484002440e04500d81000d503511a180c98003c0c02140c2c4810700c6805a2140e11501900034956003100482700c010654a07100700c00985480051558032100201050100c000350001141c0440603034001c00d030840d03103510b02043e0050300a10640c5c0d0f0006400e6403551311560750b00307114012400255900402910100303480303040440040f441c2c4017076581c0d58841c42c5400c3e0650b4011100c65542030040c81607440c107050b089010504440c003c002c4c11032040418411420b90741442c3c000507104c040d1500055101e01502031110381c120a680d40e222004030b9103152190543e040032405002d062400c01c107620f10000f103c0d41016001141180039440c014100c0302603a4464038241c0442d04c450001a003100300b00886100c0c242 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 989307383 1250 989306133 989306137
    0x4080606091e062731140a0c08010209040b0a030510090321020912030a2102070b0903070210090810020d110f070b0a0b060d020a1205010602010c020c0d030c020907140310060f08011a 80
    0x1801850484a00c07c200d40c40d440b800100e0703600401010f03500000d007808980341a0055003404402256028142c9103140e507103507505e0500c0f442ca080040c1d20b82c1042c805043c042c4140720400c03101d032107a80c000c4910341c1080300000e510907005548690754400070310340d41034400019074035400860b0701c0f1000074040f1641e08844c40484072001b002040e07001c02020b00010b00d00e01c0c000f406608251300451712020503104114007048444520030802000d0340c410440301c500090801c100c0b6020304001aa9034078020110006000c1001c50503d0500c0002a10804101c41c48010120940180708525440c1c55080c80001030354802c3e848a544070405020f00e41e940c10542c0c2c010500d40c0b041f0b041c891510414904014181c480980c4004090303551041041419078060240c202180e40848540e010300042c0e5401801c160100c2c9400f0740a01030105c005213859000d0060010b8001e54140700640324a003003c2e2924007035140e4001c003000508403a40c00b0310058000c50b40c481c16606451042000e81d415242c03030303189603 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 989308633 1250 989307383 989307413
    0x28150b060a0c1b1d090a0204020409050f1e060f0a030b01060c290406022a100f02040810270b15031b13090c08010204080606091e062731 60
    0x46c1c01000d075110010303a00d03803008100401100002042c945080d84400588250007065182070f03201035200b001848180944155100c002180d00d0080c03445604045484000580c00042000314147c0000c45c0950f0801100c400f1144130b034050b916680301402840c840030030801d075841c09003841c00011400042d51600500a11002104e180c0c001310503400b1414242d02020302d0301d0200d034014803500160028603004001c46444000d1041d89498608400d5030b81e94035402c420481e501c1e80d10b80745140b00031100c0303492602540700c141282800039042d0030550100d40064035201c030079949180c0c941d052418007017504034401c08a041104000390380801440302071154000d10300d000995a0a6600024074580c1c0d4503009819074034001608c80d810701091600c0d01c0c60180405108510718000c01581010500049104040c48001004c035071301d40001044080f1564600d81c0ba402002400201d200815085003e105620107c0341c00041002159043c4000204080d010300c051001c0300b058012580300c0683d0404 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 989309883 1250 989308633 989308651
    0xf0406030c030f18020f040605092d0c0c16150c05030913050a0e060402060714010b1011010b0103151406090303070c030528150b060a0c1b1d 62
    0x840c0d0005044181240c0905003041c554a4100c5075404c20750a04020b4401d2a035020340d42000340605007030002d400c10700010080c50384c858a15400110b1405600710360710f41100b4025400a10b030418010f1666650407901c14699544207001111401710b11016210080f41e43e4008244068004840203c403007442980054419110800000c25141c445d400c22545001c4400800140c40c01c1880c0c924080d10700d84902c1009035031022081c04050307540c0d10100c44540358040d481c0d110485290302d0603070140098820059101d19a0060f1a2080c4d0b00141001e0200641800030480c17403075220015411604007400705801c4001906080c889582044456005203000070061410103071040e0010b45181d0250800700d80440c4890300800030070800b0040000750b03140d810707424502d8440d04221614000100500070300900031a5545c08403072407095104c010204009001c0c0d50780c418803000003620344000c0c42400c407410702140d652844103489154200041d01d0b49504807042d001200b0114011141001d4107920f5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 989311133 1250 989309883 989309891
    0x151104182028020d21090f0b160504050d03030908070606031202070602120327160b04180c0207091506080c09010818100e070801110f0406030c03 64
    0x4441c07120a82401e01200c41d1007601640c50401d480104440003800d04a40e8544890901401c400c0d83c0200380c24400302a5403a0062190700308504115030b0440641000e0407080c9030803894000e00031010f0224a20500800c40c0e03034080e45800740d942004100c41c554403c0002c0c03052100b4455031038690b0450b1320140c000d113404038441e1066124030a05901220040f1030b00c6648150800401c90b510304100d00001103400600982490010080d40f00ca11305181131810b070342d0000025a12040c44140c00c48051812907000e400c1d0b60010300c907d03940c2c10310742a280e001c20880500001e0444240f07012901a60161080442c180050605a102801400c00d268040d801350b02d5001c038611130300740302e082c0688815146032044645054000703490003d014241c0d418800080240e480c42d6600484415084800c103401c074100d840c050407041d0704201da098030700340040741061a05541d618001400c4003e40e000400200f0041c810031103504014811a100d44410900501007002080e00903442101005040d00703003c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 989312383 1250 989311133 989311151
    0x140c180c0c0601120501141302060d0608030c1501120503070209070908060c0d050709031109220825020a031401020409020a08040506062d0d0803040c0315110418 71
    0xb42012000d0700b007102c02e02815021841480002d014504641049900000881c1001c1001c442c0d8107000c42c1010340503a40c00141c1221443c0541d0100004003180c900396520343c0000d40c2c3c21926102000110070004601d0000420b41040719920484015442030040d4900012a8244844000f004010009224881500049020003409141c0c0f10340031000700c0e10381d02c0010000707400c01ca0f980130b4404410003101d040180001403002e0100c1c1c00813101120000701c907503620340a20f1180003400340251407420ba070800040401c9507141c00703040d800700d030002e2405000b011491301424000b948100650700c00640701e000c20200d6041c80c81c0e079115000713503c0090718003612a0300c9802a644001036007000501400200400d000e028004580c01ca0011500800024842d8041c0c01e0380d45050b05a4040c041300b075100c0c0000c2ca035603014802e40c0b01a40800c0b050745078034003824810b03d1824244030076211646074000f4aa0141c0305803184000345070240c87c11a00b41401c00c1e4040b0305d0f01c40038080840c1000da46009207 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 989313633 1250 989312383 989312407
    0x1b040611011517010e010524030705040c1d030c150a030b06070305120603122203300e011d1314011a0705030f090604090207060504140c180c 62
    0x5009030140da100361400006211403c0e00f1900d03a8040c01600e82d240a090100100c0316080704000040c5003090007100145100000b400c02850b5032099a00c42c0c90944c0980e40d81c0e404c211403140010940001102290203c014142c950564120b0307281d01866000c021188402c0c0b010142c0801d01e41031400041c020104030204025620012041d0b02144000c5040104a10038988155200320241c0142401c070450300c12004040c0142004400440020510a900c0c054550108401150042111100401402d8402040c01c03007224201030705080c2040c00e0f2968600921502e00c1a10301a550403600c412080181c3c2000d0109240c110351141c613240001d49030300ca050151905020301c8a10741c0f5503c3d490b00d03424403140c0c0c18076421030443c0c410601c110000700e50080269508002c0e0192215903a800c1c600006020380304a1b0030610250303101042000078044164007151080f4400e00c6800760b0003000140c0c081d500e004c001d0803254803030b4091715000b07502d00e1a40b00f401d030481c2034141402d0400810a8032 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 989314883 1250 989313633 989313671
    0x415090b060a06110d1d09010b0a0f0c0c050d020a0e07031b0f050d050718060905010f03090803180f011a0a050105120a0e0313080a0b1b04061101 64
    0xd954509444040c0003035850902103200080103d400c201e080c29a154201c40c1c0c44030460780d01202400985c0c80424403008080000030441039005001c3e511568503103a10103c41e8102c8003070240015150b0b500500b03c14000c01401c46540c0e04190380130082c6241c1810400078043e450012070b0814291170300000c0c0402e5400c000c90144207107450115805d011030b1155130401c10000302074400c1082c0801500300b001d400c00c040701e00e6050280404243c070390310b62205842c1004030034190b000106051000080c05c1b9400401c44090741e0007607031200381d03413482088c00320203590b519034000d03014036402c0007c80d001810340713a01000c1a4800e40c040d500150048190703982117800e041c0154840000039024000186000482c8802a02003400c05030700b0200701d0980c5420b4000c000f401080a20703942d468082050744101b09490700c448240030320b101d4040e01c0745220342d21b43d48110b000b150080e40d0f030070204229a500f032112600c09201c803aa02c0f820180b0f4103408503024585007000c5245e42d56240d00741e200c0c070107201c17030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 989316133 1250 989314883 989314901
    0x7020f0411190516062301170c090c04090b0d0c09061403010219110f1b01110d0f051606020309010b13140711030d05090105150103090209010506030415 67
    0x30000d500d0302c1d904800b03002002003000701d01003000000c1003982c0d000350410000c00e0189410050000300241c403017503003051548459803040300e0062408000603860581c00d8030192198604001d840000d010602800000302d025608a404280c0030720091001c0c1e02e06602c00501d88000500044900d02c00380c41d0302c0201003058111902041d2994000c0c400340740c0c881707429500fa82c4207074003c51170020505050000005a5000720081103e4800c0d14147c1660412142142c24400b801380c440341e1003250b01440d00c0758111a8030502107901509141041c031800724084d03e50b94015100c0d2498454604800c0b5803590240c4401c0032441030031341a1a000c207409101070340c46000d400f0000500030030001e041104003c10340c440202c00c1401e0070b08000000100c024020b41003a00380c140a024040b20101c0d0b00d0541c0908084480050318007020401801815080345010320340041c0003080d0b0040c10001117007a60b158100180d04011140700411150a100c0c00035076210340540c52070a2030000c003544001c1078919a072 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 989317383 1250 989316133 989316161
    0x50f0402092a0406030e07030f060c210f0c0c0b0f09071a0903070b0403050307110d08070c0302120727020f07031206050d0f1b050406240201050108030f07020f04 71
    0xc00c0500c82c0a405101b08841c81c0e07010310040c45c020b403541c0d660581500500134000e01241d1500d0141214500030310240e08100e401e600300c1ca84d08000307824080000c210381040c0044a41c100342190150750300681505102a0300641420b8440e65074440480ca04e68000d080f00801c0d11843d0400524078a1903c1e115241510014072960790b070002000301803401d00c1d607402a400481080000b0800540000125810b00d94440700344001c0f04910790000d584240ea5510207407906200043c42400c220800501d00d098a00c21140307900c006602c130181c5a82e81010b801242104052044c2c82001d084403440c03507600503000d81e400545450001048081550000b1604a011603044a00c0c82c480380ca0501030080500380036200c660251400762110030480381034400242c81c4035286102651200a040c0c0d18101801e0090018008207540722034064483c1e04054008000d480c1c2964424826841030094034100d800702c0f0300131070a01209904900d001c0c0c0c4202401c03a0f00510761801c806207034a1b01e004620785d0002107 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 989318633 1250 989317383 989317387
    0x17160303200c06040c15020d0e060706092405220c08070b04180b010c1e02031903030b04020703230c0d090315110a030f02070c0b0309070603050f0402092a 68
    0x43c41c0826168045030042c2205681c006c0741440300c10350024007003000001c145844c845107040310003c200e040c890700502911040c1400d02c05000e00c2030044c0340041d04d52110325150325520f00b506095088035000e03130b02036100b072992060a411f090f20220304005224059860b41e8282551106400e150150550100c43c1444011908000e80f8666030192403241c11035460a01c411200c020009000e0f801e8402d005004603902840d5002d4080fa883c030348600b00d40e014040b40c4424a00000e0004440e4450b4000c0300028182041c40f00c030f9040900070b8510b1654035403281035070455407183c041c06468a03040607014400c8140000c1038000e00400500f1350415458854050150640c18a00c1c0c0c1041401012101e01d800c00c040b04240b80202d0044a0040c446440c00007100d060800b0f010001e441607403c0500b811b004a080404c1c40d0b540900214081c1c44800200d47c1034907078852047c4d056400480c0c44110200c88040068054109810700d1540007951514450f64031901290450103900c3e8030038514200080 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 989319883 1250 989318633 989318641
    0x61a0d110d020a0b031807080706020a1523090c0d051905031201030c050f0910090e120711093108120411030f12090f04110403080717160303200c06 65
    0x100f1f002c40b0740030744081d0300a407022900703000010b1340e21071103200003e000da2601a182130294002d41d01400a40884680e80019242c0100c41c0c03c1307211105461040c01406110014051443c0109954544990000141505030f86101078450049003221003564140401c00408001200240202d4040c61151a80b0340744e403400e0505200f0000f046d603140c0b50084814400344000c0030042801d5604556004101241242c4606400e500f09626410704030304010340483c1e04c4042101d0f1904c0700ca809c03c1c2c00c1e910707580c040d907480484003000c000c130481007450100030074100034450808280d0b131481d20f40101111803418030400300304000c610080300c0c11b41c1d403203030009411081d5142c24030440705000040c40091000700080d0000c054540f1548440e2841070401c50350941c01901c0300d07001019081220304210341c0341c65981c10f00d041107174808403003243e440214202144803a03a8a1080d19000a141d12a04c6003500042e0707000ea00504143c1102c82030440303002c03042c07501d103c1c4c0d680041440c11b003c0c00191036035040c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 989321133 1250 989319883 989319931
    0x9040f0b07050322080405220f09020d0312150611010b040605010f08100e090a0606121e0c09020409020d060509010e042904061a0d110d020a0b03 64
    0x80c06840c1004002080003800b01103215411402140c01440c1281c000d281101d142c0b205191003554051500200e07451344000070344107100410182c18171003400074415000300000f9a070445181d0500203500c00f100c1d0007a0f01c042803003101d49040101011a001030745c103043d4034000c80700311065403020000440c03a009910440500780503134a688003040e40d05000990820700040c2010380c0b052903000400941c89d00162582185402d028002c01030680020090b05041c01416168984000156082800d1440000390050840c414141564000c002c90842501075000d0005081150350280e460103900c010200c0c4440782e80c0300070402007111940059503407010101131401c2c0c0d11a60b00c400d20902880c4010420711002803881c0303030300ca540071428040d81d00d03e114140411044503030201140405c07403400c200410030b030355100080301d00b0f5030703050420300d2145c0800300700800c220400002d00c58001c0d45010790301303820b007140da114989200a1513044540c0d11010311040d43e41048030442c0c2104101c4001488101d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 989322383 1250 989321133 989321153
    0x30a091a040203160b0d0f0207080403030f02160e0a050a0b030607030b04060f0b0301050120060906070815010906260a050a05071412040f08031801150303140f0909040f 74
    0xa8200070070b11246040140c820318050300c00580c03001703907c8289903807103584543d048400750b80c0e000c6013154840d0349904000b040200381c003009101504c1107109c91141c06400c14440011241540d1040800c0c1d510501c02e80d02504025240c03807202c684030300c500b80d5941c9c0e0900c910f608c01c0003969400211118100300300010b44c3c01c940d01400c00c4c050289801d10072001214100c9054075420b0800c500111507003140e00c0003216420300302214030b00985080c00704403140820340c280160080c3d0303a01345081e1502c502040d0005640130f043d60104540003820410386000341c0c0c511343c10301e51640d214556040740144003107001714102d030749680c203644e40e100700107400c43e40781300303890f0480c403035251890403495401030020140c80785000c03401c1c01e0040f0b40001030801080351441403483d980117145680342d04081c205a0080460700b100d058007035080c400c0305132010900004004c00c0303070382681e140850401d040a00002507031002c038a0058103601000a401584c0340d050085d80a940302d03051a0a42c0312480c00d00302212 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 989323633 1250 989322383 989322403
    0x1b0302010b100c02130c0521010810330807090540022205040204060e1006031d12040306050906010315050702100e031e04030503030705030a091a040203 67
    0x3c08000c41c016005602c882810f00210007100e44001190314840000780c980e406121814040700241303102a081d01040444034034100d0301544100d424039606035024000751801d00f001c1d40b1001c52807043d007984d0745c60b070488079a03103170104408250145600e4042460801d0b00c039410404156071200b091120b0001c410030b01e100001609460704601d0a0150409a51800a030071940490400e1040c200150f60b159140340500d01040c004c10017856000400290141c8030807541030b8421444d00b04009019203c40858900c00d90010002000f00c03801c14505500821514000b8101e0300e0740840b549040c00410450346142680d10050241c0f102d02d986000c80030b90300f00901c0c040942c0c0011004100013240c408034200c006a40b02008078003952481801c03850300030b007441400422408c00580fa520140c0100040c1741d400d0b9640801781e00012100040c11b028415803000400c00d902c10400a1851481034001d140c0200b0b00007800704820318191a81d12003070852152070004011410140801c500e000c01011000d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 989324883 1250 989323633 989323637
    0x212070302151905130902070c031505090d0302071406010b070c06091203050f220f0504060825081c0801091b08060102030d09050c010e090c04090b011b0302010b10 72
    0x1e46054000307800f8010101e004072100340440031172041154a5070300140c0d405080421001c64942c00342d0304141030b40b0552480107807050a0200b0600940c40c101d4011745100f004944000d0158035a244000c134004d50000d02d055641c500034024420114409000f000d00038204459140e486140342c2c1840340e200601e56000000b40180480c00700721050409441d03880f1300e605401c1580d01c41ca0314a82400840c40f9200080101040c4d400160800954100390301c030550390306440140200d40c0712010310007101c4050041c0d25460340304851182422240320003001c6502c10421204808580d81c691461410301c5981c100f000003000084840c0c0c00c2c540c01080c181c0101000602404004000c0e01d0036030901d00c842403058204007044e400a0a564002c004541042000c0a0100600c103010301b003d51700c1c0d00484031458001805191031219034070b400c040c9240900005411a4030709850211413100410803425040d05100b9805292681040554900b000f450b02980000c030700081c01200700b011641e2001c1254007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 989326133 1250 989324883 989324887
    0x3100f0f030219060801050d080d02310b07140111070609030f030902010e010c0602090d050307020a1d0a0b01020c0603070e011806211104121b0e06090a09021207030215 74
    0x8413196001301c82030304540e010b844003240010b00b410000000e1042d05845400c40c0c1c00066401400064241010b41840c0c42a4540c80e1300b414200d088500303a912841080d403410824003041e0042031707045940c0070a00a049c00000381c0c000040e041096142c22a6400b508e0560781d801c1d90742e00749504030082c000c0c405010b1600f0402440b0700c0d03002910f1548a050094108104401e0324402c115069048909820005120340c442032454503049586e0740c44644128015440408005500c0c1590002c016601511454030b0719030380c1e56480a00024410a480d140c110700c07550490000fa900e40400441c06154141c3d41c0b941070304600f100140a01c0402403076450307603400040b0100f090780d9119040e004512041c0720740e90181000f00140d0310107400c42d5100e094410400280000300441e5600300240380f203109902c0e108076041c0c0c40500305460301c15481120030328070f40030000072043d14003100e00d241e000c49501e030000f030701c9015500410801c05000c0b03e2406290b01452007032081d807030081c2201d01d0560007011024 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 989327383 1250 989326133 989326139
    0x30306140603180a1407082b051e040f08010b1e240412030f0801080c01030b0303120a0e0c0f10080c19050a030e0313060503100f0f030219 61
    0x2600c601c002000300110400401180c64010010300a1000700d507008100d085d8800000b4034450740301c9070b0340c2c0f0580c8000c0c030510721418004140a0403501380607683c0303030441d005d8810040c000da41c250700c000c006890070254443c0c854405e0310a940034002030305c6042201d040140c1022283d03400c586506030b6092184820205092110b1914804002e00c04c1c02520f410500c92408440d02c0100306030003898181411000c24086a01c400d01840044841d0080e0f66900c0d142c0344112054030444001e010741c950a4001750b454800b5540641c21100c41024040e00300c07494406010a0941c0520f800d503090309440e91039082c4811003010410100f284400d08031012000b110480f40001d5000041684044c04e01c002a070000b901000346100351801700a540c0582e241d855050f40000700346500020444000c00c2c501480114070010010a84035800000340000c3c2015080400130303105030304028113a802210350f154010030303c0070f015500308008104000800362983d0852040046000b02e043d403503071903100320510030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 989328633 1250 989327383 989327389
    0x60f02070507230301020c030721020705010c2a08010606020d0e0906041d06040308100806041b0b0a082205150601050706091407090e28021c03030614 66
    0x140c000c5841c90203a00c0100c3d211a80101d00391030880d00300c240d05500c041849125558040000e010151182d0701031020580b00d02d0090b11081d4601d00c0c000d006030702c109000c1c4590b5024074a000708150003104540d001200b2100c0c500000e611141c40d0f04500c1e800d20904000004003402840003031301d29400544420070015900500715208a000a4072404000707020030060f03210790740100403000200c245840c4003071004001a940e4001642e089001401c2c1c0400180441c061405560603908100040d10141d00c0305d8903036511183c4489018101000c00d5000051000032480007003071a032409448000b82840d01d00034405c01810b4291062601040d00410040012000b064205070740400b000d0620a42d10b42200486403401101c100a0003645003400440a214042c00c80350742415160301155415030b02c0d9608141501c901c400090255401070581c102011010740440c060502e0103403018000b08559000140c0c0d0b010410035004041c00c0d244084810316506001d100041d01118660a080c00d0160001c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 989329883 1250 989328633 989328643
    0x7030c0b130803040b2a06040c03120305041104020309150907030b090c06070201050a23071e032c040207060b0a091a06030411090108061608010317160b070804060f020705 75
    0x480e1300c541c01070f064180000c0c420604081010b2a06c8403ca030300746d1900d843d00c020010200d010544480300480c1400507094407074000c0301d100f90742c40350000d461242007030203100213500060810704c40f0f401080d51300284800360f41810752280d1400307401084c106281d8101641805005040720185822001050896450b6201102e180343d5080c40d1265079004004403c50f00100d03c500f001e400c842200b081662146541d90241c5a01801548900e40546803e101c020203442042001800720b11810700d180426495801142c13115000c0c0e00b440c40c003c00340603001800702c0c1d100d80021100144d807005c05070580c1c1040360041c0082d00c1c010303204100c2c28000d849940c445281c3c002802c0e115500004c0043d040103891000500c4040010f000c0c5401035844086a646814044461407452050204100300152041c409681201d4108901c150001031040060607254410000c0541100c0c181c1d202e00000360560103464841c80044d500c000c0d80e4209482c200c01515041c08407061818010702400300071a02c0072030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 989331133 1250 989329883 989329897
    0xc09031f0f09080f0f04080604030903290a0c050f070606030b09030c07090c0521040201080606040506190e09070314060d030e120f07060c0218010e040b060307030c0b130803040b 78
    0x46840d40b117240940303000c0d03098800c1d40c11150184c011101807000b0950401c0f903210a40b441900d000d50038902c24440d1000d01003019009818021207080402c81040040c0c1c0003424100d924500103140c041d130b400d141340443e800f20f40200e5085559034001c00520820040c04c1d40c020824401861510400d4100340e96115568051403200c25910140303800c0080c00303082100c0882422000000400752102d800c000d402000319400c0e40490f550100107030741751800008940960710020200d030f041030001c940601c0d0b0031081c0c034071400600c0b001c2203d04d422641c400801600c1391400d0b0ba0041484c42495030350018000c40500544d0003044c1e610551400a50016414030203094181d0303600001301c00001c4101d1510202018006d0701340210b07580480c207144d1051042110134001d039003507032440700d4903030750b00850410920660417080011004030b8001810003210729000b260040c00c480c000c0340c990711101e10f6641141e122000528001a090301e030001c5000c0640001c1103110099400c2905c0e00392100920f2042c26 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 989332383 1250 989331133 989331157
    0x3030304290c07060f150b070c0317030a0605040c0e091b030106050901020c06180613050a0914061021150e180a0c0e0c09031f0f0908 59
    0x110444045181c04480304080a480d05000c0d0041d08000407200c115601110b4295400740c00d18546001510050103600444001540704020301c520704408030540d6004140212142510000c000001c41c0000038046003c440000d4000d40c0d03420060101c00445545601880c007890505401000b0260040030000402e08241d6466041d80d45085050340260100e0019095605000c0300200307101d17901a0240a285400782c00302d8000c1b0391403400300303c9140180c005166103004001c50b0340c411410400041d00780c0180302c0c64280310080d241d10010b043c0c45001c0d0440d01b03505503103006045010a40074452a00180f0070303141c0f1403408003440401400d421940c103680101c0d140180c42d4100310f5500d940650101020210214512500d0308040a16400159034195500a6006c0c0d40301081d41c0209124082a9101c000c2651a40c40d00311505075080d0001c00484d40da07a0f0910128146d91014800c0924072202440c060400098189040e0207d45040c131291060501d8000c0d04800a0216801c0754108039502e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 989333633 1250 989332383 989332403
    0x11060601210f020307050a120903140c03091302090a060504030b071404030c0e07120e0a031b0605090a03020d020f0c01141207020a020a3204091e0b0a110a0f0324080f030903030304 79
    0x100ccc00711443c41c0b107403209564000402a880081100d885c2e0b0160800703190840301c9424060b41e4040440310f078080c6002c0501540c075400041800b050140c5100c80c0705000b18044241415503a481d00151403209500081c04d444100d0200326a1513840351800041e1410104100705001101c200b40e55900303c0f00e5402400d02c40c9a44054440e04091804018200d9010301d0602042c40c161042c140c40b007092044c118050310a82d4800c50304180007150b442800050b00b001400755414540045502141000c230042c05081d007080384210007260340300c900b03101300c40b1038004150084891052140031903140d0302544503060f01c018002c038680d00f65401064501000c03460f80618004030030001d030081201c41c1004181c90b51060b00070340405903141003000403500030707100620035556002c00e617805c3d04c140c07007800d03514000701b0040118920b01541541048502618000816140302c001c1d5241311800c8101401f5410031210007005010700800641c0c5034021102c000e1410118030a001c6070740c0c1d00014000400714906 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 989334883 1250 989333633 989333647
    0xb0c0a0201180b0d1b05031608040206040b0415080c0c070b0304060b030706230a0c03050741070302010207052812020111060601210f020307050a12090314 68
    0x10b111208054040b401145070b4648101e0201c60003454a088005601050143e6042d8032500450640b807080441c80e1140f00084403824045815400003442285e0024007440b020620b40811030281c8080c01c0151000490803070042000b03401400002c00792502c040f0204a26480c0c59001300303110044401c1c2480003600c80e1940d15218028200600d40903400d44103440740007514a500c503007001c0c0031003071583c03801c030403200c08180309080e0b403040e001700300c021031240840040043c1c4214001c101c2e0500849a0080b0f803003e1480c0c8030f5101c1c681000c03405014083c00404203503c0140c1c0090792896120b007005080151840d80080d49441c080d224440c411074101c91880c400d03007081d483d018800c0791a40f4601d070f4281c0d2100c1d01d041c081c082407503040e0300259076018540320740c0d00006103544c0100f0341615400340d800c1d40340c030000034602c691100e60240c0c60380b541200405c1c0c4415001a5006946035101e042e100d00812500401c0380c1c46c0c4c0325400e035030941024140f0000c42e41040c600740d8800d03520380380c15541d00c0f5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 989336133 1250 989334883 989334917
    0x1d0601121a10020c1e060a08040f1a1603090b0a020f0f070b01170c0a1a0c15010501031103070f0309020f1c02193503030702070e010b0c0a0201 63
    0x4012001240c000003000c20b6141100d502041007048000100c1c1c200c0f496510101d4a00f03280c5004c5075140c2d4001004001400d1820300901d039081c1e1181c410414003203200f03510b070780b4440346018846403240103410000512169000701c0c0c2d602800c00707460b40707410403081da516144c1085541d0041e207162501c03980007034082d010050b444100d400c0070200105090343d95416140c5551040e0302440340300301488000200e0340d0927060100355259043e000a02001050382003e04400340e0701d00318a194107000e5000c07c070106403080d0a110401e03044503142c4c1318a02d43e40c5814005000d6441800700d1302d4082600b00f00308040039030040e209004160741ca10340000c0c540c0700c62001c102d00c00c0c1340d40401036214148505095044410f19940c0b06514805c0e10006803d04904c4400c11101d404d03030090890324050268030b01c40c00c0d0403141688042c0100e03164102c04200912a80c0ca085910a548040050304440d20078010103035001902c500621032840d0b914500b404026a084d20b6000f2544000c0c10410b940400c105008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 989337383 1250 989336133 989336171
    0xe060d051b12060c04082109040507090f060203030603121204171b0102030402030f06091f020d06151803212015090a0c031401060312030203011d060112 67
    0x20480e4002c0360f015003040894041203070800e02c1041803c0c031510900c40a05144441c07525412400005c1c0c40782852000703001c00016013002000b803820881c00d8200081c2846c184807039900144440e0300915640e00740b14081c1828040c2c08039880001d92400c200c0104504030700d2040035840703900076800e0f41c0301d01c0f81c4040d03c00041c8104000619204a04050050046010340c01180654400c904449440940c00705003621168110380000160708001104a40380454050a80900c00c80e41030040ca0f00040064180469015802404603601880c3c12040c0302a0400d0407038480102144c040c440321491545d91502aa106413280d154128400321f4600e112401224840c0d16910b15005400f0100840c6d0b442540d0b81003641003154400c150400460f092007070200306100a40d400c1090350181c0340c1540c445040700030080e540c0224079903803101d0000108003001c100c8034074070315661b402503540e5160544e40c5801c410380200441c501c907549030900c94103a81143e1440448403d140010848000b4001c880e5207071 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 989338633 1250 989337383 989337409
    0x6042304050a06060f030606120b0f03060403170c0403110d050307050604030203131a0313051504060f0b013e0601180507020d090b030c0f070c0e060d051b 68
    0x3400d01080c80b42d0400c5507001001501d2141e80d4080e88501904012004c0c7d6003240314a4000c07900541850300821001d4000310100d50000e003240044d01556004680ba140003101c00f98002802e8900e4140024240e6280ca03401030011a4101d00b00303800e548074100e210303405d89101c0384104c030400f540004010050040d18210b903005026941d6500d82400c010351258041082200703040e12456010036041c440140d8032034a1400c00798140d00b075a440641038450b51070388160554462041d502000c0005800d0b94110340303c4c1d48901c00100c0c0c4948031000c0c102c1541d2440c00b90034144090000094005107a4039400030000643d444100001111030042e00c0b0360448006c0c0002103806a503002003816205c6180181808410002c01c120326a5036500c12600d954000091100056800c03608000c8000c0c284007864108c03a0400d841072034400c03c568185415400707000111160b0442c0e540400503004001c40e11603205100340e49250560865554a9443d030f44540082d4004060004080d9842e03201c1d41c1a4480c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 989339883 1250 989338633 989338639
    0x4090915020c0601051f171315020a39021207030308090607082e05090103060c12150b0711040c020625170601030b0604140915060423 59
    0x1c0c0340c0600d0b40443e20780c0003d0103020302a9204c0e00072080c800c540d1468885c403210342170380c802940c1031003480600c42680c07000e00043c10310080f00d04190f010862046085050351192003006030f44240281028014500c0310b0700c070f22040312511081505100c3c1d00f40c50542528000e07142c00c002e101a901c0001c0c0248408404645984100040841016088101a4010280d60f4103d585640d0f6004049030782034000c81c1d106040481c0f1000700030f05103803064035100d2541d1107582c40f0401c6503110008596031050980c0191492a10b80340c02c94001604115031000003000010144855480c0e9406600056028807402ca941c510004d000c805009007040c10f000c228a005005002c0d00d000d0040080d40d441c0c041d54070451154010a00c1701d800c41c50200c08e8032480e000ba881e18600c08141d01d02c02403145400402003414551a4004100181d4a1800500180c004d10402003100314800c428030246600c0145480420981480d42d054075a0780d030000e40d82151000030b04100c10603008900d5104100d4003c0d02d071a0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 989341133 1250 989339883 989339887
    0xa0e0108070905010b070f02060d0b09040f020924010509030313062601080a030f111c030c0804080d05130b10090f1506261e1b0409091502 61
    0x180403601085480c1128a10141030010382d03207412108450784107000008081d034021204510040c1801c00241842c01900d43c000216400201d01080300c420742128100e80d5070b06043e80c540214a0f00d188070f03070781082c1d440c84001804188083c00201100c0e0044038036060201c0860b880000d544c2c2001180c0ba211809280c101442c1e039030340001b500ea0034002e04804128100e01500390703034101c10100d54604030f40d0000c0041414008a840c10b60f111100300b01490108100d1001e0650052002c10070f4610455000a0300701d004580d890f030050842d514107400fa0100010301080c4400b081c1c200050b07554030880b40304002015140c844540320200d800303080060800060001f0040d0b0341c0596503e00c806c940344ca07d02401140c1d014a840c1e411908400d00e41901100d81c0b0381c0c203206948c480d44061400c504400d00740142d0048103070f0300c0305001004440c03e451085007a11042200d51001d5503082e041a4400c2c0703002900b08000c60a42c106000d1030280143c0e6546e511928414070101e1918980b0000c10114219 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 989342383 1250 989341133 989341139
    0x10080910110a170f0c07021512070807020106030b010e090316080c0c1503160e030f010912090501091e120b0402040b150702010c0f1b15020120090a0e01 67
    0x429810035220180812000e11a501c4101440322031503106180c0750400420a6482c44624090381c3c2240905230b801c4512001d03621101c000c4100104903501142441c0300e103d180604000304108801000c0c5021641402e404000044030544800d06580201c44441c51235a249002c01e859402004400449007140301005828060f410000b8104480101d05843c100342c40d060034050400f121002c081c1d6400d03002c1001500340d02a402d05600f020b04980784c41e4402da0200e01c002890000d41a940c41450b9640742c450b2380030000c035240c0b241d1088800d42044a121481c000010703000c074010748076000b4404100a005030040381c40c0320f507200107070a81b89008081072030a0306120040b2039085030224050b5250008000291401c415100d840d401805411454168541e004454055000104075981d61010840e200022101300300c2100c601216100c191605240046050b8103042c1c081c1d2520969140009070412508072850007409100040845075645a82401180c44601f0603445904400d003520004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 989343633 1250 989342383 989342411
    0x6050f090432090d080a0b0d050d03020c010513022b080a03020d200a120b0d050604020315040c050d021809030d06061d0d03090333090210080910 64
    0x10740720494003610301502981d40c5042c042e565a45402208001c504805c001a0005c40d036030304102c03000038001c2c0c410b07038031088166202c0385403a6803404004042500030070782e6161040c09218807030344846480a003201f500825004281b01038858803042e0700000340402c00c4035000c40c08005000c6080e83c000e0209580d5420303208001c0007504140d100303c10306824014880f41d20201d00300100110030518424600e80b20080744c098070000b0f40200403400030303a2036480c841419610001440301d010f0140c4081c2016140071320401d410208480a060b41c0c0744000f4081c07001180d41e802d00c9400f500c1055901c03443c42030301030000501c2d00c80c0c40b51911042100d8401040030601003c40640441c020406c0223000460700d4641c103583e09001204011451030b50011240d00c0d51822129400d000c0d03009050031a11640c0382c1d00d480d20548002010190881c20b100703144110302c05400394240c0c0300c0f090f500041058043c5680082c00d1250050f070180c0c00c00040e5030201d40e44e9201403007080d10200808a082180c081031401da = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 989344883 1250 989343633 989343701
    0x4030602030f090a1104050915010312020c091003080901050c0d0c110307032001030e07090b131a040c120c03060e07080903120901020d06081b040606050f0904 70
    0x41c10a0b0300c00754004201c0707210700007076040e50040d48603800b002407070500b00a103c000d002c000c000031558407840c191007038109503260b14030340a140101c2100b8011003c0e08006460026581c0ca804c4c091805207040054280200d031540054070380c82000940d6803642c00e80120b4050143c0100c81c8d0b4036000e984810280681c00005e01e41020340f041020365040c125500030161101407620010780300d08140718011040304008589890200014103000807070100300d2903070f2807401d42d06802c003008080c4d55819084480c07074446d4010076a103004180a0265500034070b0043d40b02d80d2442030460240f034848500d412240c0c000c88c0d5044014482140c10041443d80b048002c0243c1041c0c40b591039503d6002000c516900d100d0744540d445076910310000d502c0d2105070780307506880c0314004000940c0c0303545c02d0203d00356140030b42c003030000280311100040c12042e030181141f040d10b44440e41040d10452601e0401c00a040c0c104081c0c9d410808224500e03621000c03a880441c000e402000148c2c80a41c10000a4003501c41020308 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 989346133 1250 989344883 989344891
    0x280602070c17070506040810020705190507090e0616031806020c010f060e04020a0e100506030403170901141303031407021c08252607020c0d11010e12030403060203 72
    0x7181c0b0310940d01c04c14040e80d4496405011200d404c40001201c1c401e0b2143c006014041c450412520004280300b00034900ca003400e1000c40c0c2507001503108000c458510300411401103003180180005007481260f40b04c180100b0302d0100203140d15224030048420328949084112500108195610140da03002c940c020115540c00c00842d601d040c20104a160420048901c51940589104081360134601000c4100c0c40085c55202304004680001c40c540e00c03250090360066119856421010340200f085403510040144001d1a903031500249446500500760441e800c01500e184200035151507081c100e010344424407824502d61014401d2084250380080e0000c2c1c0c2e8105198410308902c0035400440d14910181d0f202c00b00483d800e0001c4426005030441814540850305045094592500155200c610382e49000c42c15841031000308031b545a014400800c5c06c40089442034200030480d5034107601d9008a480c031904100415120150545890761181644800794044a032529520720b480000b03988215 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 989347383 1250 989346133 989346179
    0x1b050d0e03160809120111070c080d14090301020412050f0d140405060f1903061e1a030402040e070801240501080a0b0a090c0c0c08280602070c 63
    0x54140303900c420000c0141c84644058609a0742459590784a0000c550404010715038000081c18000441090900c140c9040401f41c00700c43c0c1e142c0181d82090308115040e42e102104130b80281d1003500219602103060000300d140880c2c0d50340ca80300c202001c00e0081c021500010480015031800c001030000008002c00d9003800c0608a42c0702a10062040f00c2a811098014420280601c400c0c4034602c3d01d180504581d007103821a81e800c21015103c00343c0d41e0b141c024604008240d46060038003070210000b406c1c215869540400b51405860140c8490340400900e524101c03500300400403034215519500300b010880900d0302141c4c0740700d8941d088140206030274840d002d485d201000f00a0b2404d550700e4032140880300142c5032020b003a5075451005000d000c07412026a803041c01c051011540301d18074840d0640d500c42c10340d907021079080d084c5045030701070380c064002032619805000b40b848009080c14800007240484141c6000000943c64070001a00801070700070004402e04501240d60080d84100d8000c0c04044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 989348633 1250 989347383 989347391
    0x15080618030703020d0f1407080c0607110d0309080415020601060306050f010c03030f09050f0109021c020a05060d0f060e061305010f1e0503070b270f01030f1b050d 72
    0x1040c9034560341d114120009000d6000810202c3c1180d014848060300007019051981d404031070541e100d04958010001240e052034003041d8006104010098182d0040041c01c2201840e422000520ba0310b840c941c960904140c0c444000c1002c110201098500030800e400010503400c03440040a03407528800d00a0b800002d1074944001082d03c1c0084403140b0515068680c40c8403001d4a840403000340c4002c0c0304001545480d48115400100c0410020600260740300001903034040500c10030081d460300d9070210084042828510001d60354040e03806040307503001c99003030359560210818040501810320748a4941840e000d0006038040030a60014030800007210195640c100d04179465085580078043c1c1d080c440c000c0e08040c0400f40944a08143d01040c602c03881d0411580c80c000645040041d800c29254a0710100d13442c0c05182080030031503a80720358518048048420300e00840c2c0610b6031800c08904154543d00200c500008035407101e4002c0050b500c1d003050040740040050010780c0411100496030380f030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 989349883 1250 989348633 989348671
    0x213061d041208070c020a031b050d0203030904021b07030f0b01060513050f010216081005060d030219060b180402090702280203011b170f131401150806 67
    0x216500038856a0310a4042c200305800381c00031548601c000b0100c109010505084002507600c0007101c00c0214420501203012042c80504100303103800d030368001070081c222040384d000140d0f004030a480f034090781501c0050f12950300e1040c104800c0c861001d07000ca203005065001c014020f0152030311184900482c00300358241d80e5040b003241d05102c0e040556001080e003c00501c1245011030300c2c1c00b00300c18148102e484290410442284440f107a44c400425a03000c0c07a82c00c502ca4806020b550740c41481110300740e09044091b02c0294841e1282d07002400c0700b0780c7d061160070400880d544441d103030f0f0002601500000385900941c401c0480141c4082e80f103070140f00000780c2000d200107034180380084049480c0c41407904421801d84a01808202240d01d55210010b00000300144549010301241c15502c90391020282c0828682e1044054103803030301451040104880003000844001c0410b5010318a00c240305560f00f4814010b0006c07650b02c000442103503078009000e28000034154040d204c900c01d0201c25a01d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 989351133 1250 989349883 989349929
    0x210a0905060606070f0318090e1b04020c030d051e04060b011e0f0509030709050c03011e0f14120106090f0609270c0902041d1005061c09021306 63
    0x30408001c0c02d1781c0c081403040d00003e01c140721849501c000c0c00100b0501c00e45a114503000e4820080044660b94040e0b06030841d16028030845503484401034600710314000fa20561140c50703200d0045190004d9440300c0114911000e1070704c403412100800b805040007800c00d03140ca50b01074100719824a00148050901c001000c242c43c00c206281556500c90004031f07010610103540d80d40006481c50703414024184001441013a070b01801c0e10883c852568140d996041c01b404188520101901606190325104103020280c503001401098681a01c40740c0d102d07a11410000380c3d050001d01c4180c8203942803c2c030000b0b1001594100ba400c40490000074420940c480c42c14200700d625115148049418030b06007144115001351640b510180110384e903284d4a5100ca060320140d9100307a0080900b80c0c0040c0000c481000264850340c0c105d2100d1030703443c4505150400160240c000d401d56241d000042c00d00e00e24100f015a440072121036030180100980d01d0001001c003005141d240714001c02d011a45240d286052 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 989352383 1250 989351133 989351137
    0xf0f0c0702150712140a030b010e120601032303040e0a0b10050301050a051507020f01120c0f03141302120a02040915050c0a0831060f0f021e210a0905060606 69
    0x40c17540da003000300306403044001e40000344d00103040c07180d1146141e400741c4034000004490f821402c02070603a540b5514102181c03c640250050030812110300c1e9450014000c02210304682e49503071981e80980318203181c14005d00000c0d4403168032034000c00c3ca00410580001c0914103d581c1142e101030019510f20500c0740b032082c076009104d8040f4003000884014546400822003c020602d80b0071900b410040120003100c2190880001180180364610364850b0315004940610100522070030260405e011890081e4001c410000d20a0f4100101d8806079002000419481350700244140400d0645007003210b00741c05410380309002a0f0401d070020b1310307440800b411140745c104541e0780d0078a55076170000101c4821442000000810305070000703400c140c42441011101d042d008040c006404134228000400301e4030884009003902d401404040c00e0300441080c10911450100c1140d561100d81540080900300c0700c0382c441001d440c49406100d1501083d60142c0500b52081b400c032a05a111841003000358 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 989353633 1250 989352383 989352407
    0x403210c0e0f09040618052b0e21010e12030405190206030708040501020714030d060603150314070801020f0c06070306032111010507260f0f0c0702150712 68
    0x203e805103001ca40098881d50003041d15032200d558100b4504800e80d00d007410701c29030a203da214410005070b030b031f11030480d00010f1395252001824000d1501d04000041a04060b00c1c01c070510310100342c10b5562800d50405e41150125040c003000340d80010358507448e44030942c1c205580c15202c600c5a207a505038080c40c0d02c14581e80d40c0f0b400034003407401c640c2c0d04a000c48030020000c1007160295000c1c0004400900c0140494150f208400080c50721990101355142c1291900c0c2c1c01003041600b061032409040340c03600780131800d0343d030080b14503101d600781400101e190003402e40c007070b03000c80d0b00c005001d65140e664000500203003100142620801e0b129128106c058911a0201514001c80e50482610040800840c0c001060160a01069000400f0041800c4420440b000000704524010740007500c00c94020002c03520780441d501e01c0c0941007401c48810006802021405003040400100318145044410360741c0455008007070721a2440344003407810a40e0040b0b00c00b2121120942181a000c60189c1c001a480c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 989354883 1250 989353633 989353639
    0x190b010504021e03041b030305030103140d140f160c030308090c062b060b03062706010c14030309010618021602090a0605090a020901110609150403210c0e0f 69
    0x1409428114994a940c0041d100710780800c0180b038841d40b4030705da01b880d1038000d5000f5242c264032585036041c4684002601c2540080070382085c4030440d1082d4000c81c201019040e0604001d4984a81c0c0080b005603200d80507041500115800489080003804003070441500c0c802e07550341e0b1060303e51600d51996404481c4142ea4007401c1840900242502010642094994800c0340403540711400040c50881d007094001c602c45840001c00c000641c28024000703892010868801e004560420b8100000700b0b00c00b4083d58104900d00d070700f020500400b180c3c03103149110b000c4c007a02c0d0740b41010291a4000d015070b1140e15868500c115507c05040b1180c404d40e500c10140e251500500101e690030012a010010084400c0c80c4d955040403a1540352452205e1080e41410b0700180c1e40d404000c000740c01c00c1601e44508555602450400c00f484034086181064580b207481100000c0c1c0b914039003502c00f5810303061524112441042680b048400a41011035502c03e203840b82e204030040c174001d0100c020290704507190 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 989356133 1250 989354883 989354917
    0x10206090d23031501020714030a0f060e0316030314150d08130f05030c060405150f040b070312110a020d110c04150e01090504230f190b01050402 64
    0x1c180c000c040307441c03904a01141ca4a20000344070302288a5400c240c80d100329603225840c609070036580410000303014241c81c4200090207416000001d036141c0d000c050082000c02e0306a181c9040101d40c1d04501d00081303503c81603035117449001c102440c8251400c8001c1d00000c2c01d214238280c445d025a204240981900041c00c1c4040c0d080368180501c1001c40081100c48010800c40c00d4a20214011040e001d40542005d20701c000e8a071508051800043c9000544079841c10001000b00d03990f00003150840c0559082c009441c1c0c1c40c45000c440150045501c800c00b002d40000c1c60104155116422041d550098039040021240b1441c1c00301d82c6015404c1f071000583e2061184000b010b008241003100010b03007600301ca00c42c043d903001180c05c0d10942c8001c801c0441d51810180301c5040d00a01c85d034050b00950f50104020f00e8291500b01070252004450840001d00703400d5080d15400900440096052046c03c03507034618a4580e0500040009030415109070100c88008500c40c5410700032642d070500415a121 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 989357383 1250 989356133 989356153
    0x2030408030112230a050601141c0305070204020403030309150e060601231201080601060f0e01080628060f0201050c0706180515180c0d06111b010605010e01020609 72
    0x80c12980034110282ca804c0c881400c1c1d5258851110104100412144050a041c2c8080d01e0420f1038030506070000012454500d074490f17020340303c00c1042540c1440c0f102c3c2c4450481c0e0381d82010303101d510440130041c0d0001d00008000c0309054158021081446c4a81c450040d1019031028174412148030407c003010541120700440e01541c8901e4525507050b903280491400720000154400440d4850600084e41c50110001040560014807500e401083d05003418654020369500081900060074101030622a1a40128a45803921000048082e90058001090703d01402440e888180703548196000504215012010a84180541406400c1170403446041070055030342c680203011910001680c00c0040030720031020030403c208020b4100420500c0034801d0800d111905813004140800040c9a442800c0501070341c0c4441906025458110708002545c0000c01ca92f0b20180c0b04043c5c1d13200701150561100c0220b81030661100b022600c0980f626500810b2900c01079032140300440d4260020f0700701450003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 989358633 1250 989357383 989357399
    0x80a0f06020c01021b0607020c1002032a0d1101051315090807120801081c0804030e031c05130e0915090c0406031a0106080907120f0f0b07030f020304080301 69
    0x2421080b41c1c080000760900100b056080d60a20104408102992056090000a40d01400803910a110682d1680c240842005001c1e599119110340c1d4278180300d80701444a1801c84039010048052001000d0303071002c02801e5801410412070240a81442d460080071a4110403011002011564000e808001c050741c10701d801c0d801411966403d84410404200320340006400c000071803808540381e26400010b5043c1401136240445041108a00d0b02c029914610301d55000030285601503450b103448041c2c001020007090420701500a15056560050003000c5604e030040d0141000490a41e817a00da60355560b00e440390000e80a07510413145420402d10f91410901c4504826030004020301200e10302c00400003c00c007283c18950080d501e1130b2080317800740d4901c00c0e9040721500502c1d071441d2204003420807640e80e03615071001f0b2040d00219501c441100d01006071081d1486001c54002c85c1d180e4142d8070f0b5040c0a65985011212080000d103040c010900f603070704510130b80e40203a821180940c19a0300301209 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 989359883 1250 989358633 989358637
    0xe031c0513111302030f101208030a05060102011b1101150617070c0206031602010b0f100f090905010323032b0b09010801290d020105070311060a0c09080a0f0602 71
    0x80540205114508540c2540540000d5008020f42d2906d41c2580c03500c3e0104445488190300030f00a02240b020304103000c2a03802d0192904107490b4100000c01e03444160050f4018124490b412110400040c2d90f072214680001c0300d48243c0310f8220007800208100791900000d411170380248000708041c40b0904041741c4541c0e001d283c0c00f1405090400e28204280c00041040d041201c4403403030340301d6003003d071010702c1d9081c02007180404003038800c101380c2e1138040009001840800402020440c40d0818201254032034001d100083c0201d4008000a584a09211a442e0381c012607640250088528081314610000304803076150340c841201204680c211030340340880c035800d403000303078a002c0d120100e0800d19511000740e90b000b88284e000001d041b5524841d600200e20409041c03502d614041d070700109141d12404d950144a41d424a8480d40d00d94441c9016500807523100710442c2c2c2841a0000c2000e030400c1c545c000b2410030b80c19141d40c1c2d90259180c0c0410359401d02aa001016412400c0000000607001d0300 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 989361133 1250 989359883 989359913
    0x10f0b03150403121505130c0c02060c0a0b1306060512070902030a0902040c03091203020705330f011a0421060209040e1b1005040b07020f040e031c0513 67
    0x1e012132451103055544016103002e8030110031010540e100802081c40d0510011456050078802407084445141010b865800304c410082d00420340000c040c60b800b00140001c01580741c2c0700c004000d1a04005060140c14918103000301c48080c0b80031004030345031800c0852a4110000c100c010200345003000000780c06500080d001d44881a2240c003a0401603499001d0040d500301c0a80c0c0000ea01d44c040d0400b400134000880c0c0c610141881049440007062001c034960480705190703e04100c0340303443d001c08526601074002000303c011010301d040c4050201e0464949040720182e1250141c581c2c040d0091070300e648583d200f40008600c81080560b900f01503d0050103c9500a040050801c00c1903000319056509a035210051900284a0941c1c00600103590300c0400030700342c0380c44bc80651801009042d51243e40a0ac01c0d4480001c9010011951685040c00c035690300034100340b140c008603030900c540d00d41080071155103a03040d4121081c040c0d80c0f0340c42002c0c450801c031205509c4c2c2200c20b4075100c0300c80344224 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 989362383 1250 989361133 989361137
    0x703020a020d0b0403080a2003150604080f0609060c040501031503050706020706030509030a0207051e0607060501170f072105030310180902090a0e03120c0309010f0b03150403 77
    0xe900016075101850700c881640100301d540c00300d24003407400901e4181c1c0240039265061400346039800b06111403010205100300c2804682d0b40c0d4030340001541d4807440c400030180d440785c40010007181d00b007008a00c150f180301d9214111003050700c900c054251209412912581845030901c000c05c41c56110390480482e140555003202d11058981e1101030801880c1e4100e5005070b840f4120030004103078584546035200e0103040140d8100b02c1d9114009440d003055100f60b0384100c074a4040610403c400044000098500912040c0c3d10001c0b441c0010140109116500c0005510480d8640300b038004110b4070030304040303031001e401c415041946030381c210710142c01d009482c0b40340182d6900c00100100021405120080c481010306860b10b01540c00c003640d01101e0b50201c40c10845000010780300c3c41031160b005100e0303000c080303865040115008e103503008941d0f4940d02c07a030f1040144011a40510700460003000c101000384041001c035401c0c00c3c1601c00080150b601584851004044010401d203141d0b04940b00b8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 989363633 1250 989362383 989362393
    0x4050c0a1d040f08280f0e03060a0e10020d0603060c03051614120411150c032a0d03060905090307050307120e030d05120a0c21020d0609050a0c0e090a02070302 70
    0x40441c0740c800d03158401c0b0841c4d859400c4032507205c640d034000005044501c120314000e0880300b2041e0119441d118041c0280801c4c43d120a1f031038141c808280711035000480244011900c0340c0c0048500f00181440344800e49181d454181c100d50028443e001e16441040e000e0700661104080729412a020000c216452400c2881400070802007038060800c1d602441c05023200901c1001d07400c0c00c208482c09118000e00b1010010425084000800b10a036480d036040c0001c8100c04800841800e02010004448045180690003050306180c3e003603401742051710010700041007103642d4040015613a1042140c098410340c030600a0600161100c41840780e910094940040076488100100b440c00380704c02d0340b01c0e0200300e000c24184030318603d010401e54400d09400c024843e06441401c090051000c5081500d800c410303400103118090629012111007294500302000500c0d69509203c0c0245030542c1c1151404d8107041d071901a0a204d510f03000315210008140d620031381c85014104000b584082c904600794010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 989364883 1250 989363633 989363647
    0xc1706151809060105030403020a14150406050a0c02010b01020714040b0604060503090f0a0c0311190603060f0b0408071e05180a0f090506060d080408030304050c0a1d040f08 76
    0x6003406029071011032024404810101800c01c4281c10b001840030f0304100c024020000482ea0018007034090503000084900f0381020200c1940c2040702001890030104c05000a100400070140d00151041e0f8150304204034079001803004038280c5190718500c81c0180c0c4000021303c650544140d25501d00040200006044c1ca542d42c0402c039141c0150b440400401c10120802c000740d2030500980340ea050140300a0103680e241550f481c0390311b640d540005861054140600e01d65912180094098100341c0286c450711a40c1e1510003c01401c520b0088800c04090002d00144180340c1005072001e85592034090503a0754141250300c4569011140b1200f054024040c00042d1511034040c41c48a060307401d00d00e00010b250201842080c1c80ea601e2001e40f083e450720384900c0c00300354041500e41e0008012100c402c800051400c1c50212401584c008082c180000001d0004002c0c001908819403182038680320359450740d80b407e10450181c034040344090154444000383c001030750b201400c80300e0f6200e610140c0c14400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 989366133 1250 989364883 989364919
    0x60504090c0501080114130b1824030a1104180c12020117040f061a0a181409070308070204020426060901090515060a1505120a0c1706 59
    0x1a804054414070801007042c022075034888405030151a44083c55480b9400e2a0041411100340d2404504495039552600140396104030140800800245048246007441105072000c448602c60b6182403c00c2844100410b0078040303411012140c219403510340811641c400c0c0409800b05d80705807002e0021004001000441d01601d003000b4141403d00712034950454030014111204e12904400d003400104100400644210149000781f0361011300400c030400c0070041382c0c1c805419044403640c014016400030400f07189a142800c40040e02c2c3c178050041c408188001c0c1c005110030744006000b900f0064080c40404d41500c010090503202401c01450283e4030110028502e004c0c120f03119000300c0d00301201303144000403c002074210325000e000700000c0d440707659050369034581e071401603070319524410020300c1d25510582e10300300824452001c03c030112200c00000707005c0e40c05a030b20609881c680d0008100c000d85544686d02c010481c03078445012960000000800e4904004c20203503104001c80c0c5c030900c101c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 989367383 1250 989366133 989366141
    0x60a05150d0f14120a0305070509100e0a0503120705060606040302031b151606060806090309150408010519060603050105010c061524080a020a080f0403023c07030c0902090301060504 80
    0x40c0c00c502103584030041424004d01f60b802c0508400c0800400380190f07519a035500c400c0c0c517204140ba007010b801d10041c1c0300105605246541c08150f0600401031214007409400c00202641c1d4841c20980b0307426940d4204010080c00f45000c080c1d003542c090803046070300c0e140c86004642c0c008070040c1200c0c0e854204089060541c0d00c007a03400000e07141c80844a000b048544d0003034001a203035403001307000d80e894200e07141d994a0203000300d40c40c46168104010186129020201e030042c0c4a01d030024082860300100c0020701500365581e550800385084d000248040c030a05c1750034145c82c016546d409850085032a4140545080503008004800704403000030320700362191038201808006005801e0398048034a000d025903800a10240c0b00038010020108443d6010901d1a4400c00d90a070702106504c0c1d40c10100c0c60400c0070140745003045801442442010105da05000440d0008500c04200c11941e10015840b03454920009080840700c40c0180314500c2103130040c142614000d0000607295540d0b10000b4252 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 989368633 1250 989367383 989367403
    0x100b250b070306050111010606050901050a1209060603203f1e07051c0f0b19060501030b031b1912030e010206041505041e05060a05150d0f14 62
    0x30030f949031020409545c0107101c4500d20400400200901450000c000d007031803050382c48090401c0070014a0042e09401203c4c10206401040810001c0b00c2c4a483d12400400c4580016900b40056180b00030410744420700c21009020301034070790f03003040c0805014074150071300c03034114058030030f0b2030b00c0b4061a600c040180c413030754034000140104121008280344041e9241c032040c00d02c0703864200210500441c5c4401c01041003100740e007210490b998040703041c150408030321010010040112001440381030001001e54110041003500c1c10008141d4400064046900002e4403640580082502c040041003909000e8044600031740b0340d90a41c0d40b880340300d0fa801c180340e0700400c00480344805400140342d881201c1c080403140c28001001ca50820780c0740c1da032418a402e00ca242e840d0b40c5070300015007041081c1c560281c1e46c40b150101a00041c4440c502103444003012a101d151151400000440034128031080c80e1803000302030410340c0311801a40301c0d1440038071801d50a90b201d4500d8514500703d07440070000da12170 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 989369883 1250 989368633 989368637
    0x151811040b06041413110a0c060b0105042105160b0d06121a040620180a1406030c120f01090c142209020d0212100b250b07 54
    0x2021690000c00045515401c1c089024580911003448240307400c0328a1003074440100d0304c07204403c9614050380c025210b07054041e1588440810400001c5800c0030160340c0c42c40c80b54005010740c0e080711004403094000d40c4030302e184040100c0c000a05115248080303c509901481c15680081c0030f40c107803404a640150701c500343c0e007000042c884140f0344080c400c00c4007401c005107407240d03108000e80f031700907000270000140e4260508040104080001c2a4401c00102250308061402c83d08200d119131041d030894462400060f245000900091801845260551b403003420841c100015203010300004e50401003030300d10601e2080140000711071070003002604c22400c000f000c0c5500e42c1070140036800d03102442100418400109004020100342005540c0301c04501100d8046134180c1d0203d154510403170354400ca480520006401c03120b0400c81e0020480d84038056003c156544950240b400d525800384903030681000c050000d4811518100c2d22060450301001c560555007400392100c480800d000d07941100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 989371133 1250 989369883 989369903
    0x9050306092812050a0e031903080901140712060905010f1806080a0b0a0b12070812091e03031216140a0c1b1e0f05060f071518 56
    0x4081011140402c60012005411090201603640e518280c610003d0281030083c08265204030720310602c940b1a00e90401070885100060804003141d08083d26070040c1c1c00601681d002648204050046040301142007084829560324090220758038071040b00c0c00d0618545500c000965101d4a0081901030802e0440a881c0300d880c02d01802500121043c0c40001d003400d01c0f00800002c030b0080744002840d90407121024043e900c802a40f002031054941e140d80c010b00310246241403550000300c60040e40c51000480b1805203201c0c001559134010b5042c0310780d0080d42921700114050480301f83e0300f02880301500300c0342001031317001e210020782c8411106d0542e80072400e9201c1e55a15440318044c0e0391004980001841d01c2d000f0312005007484c0d503d1201801c80381350114400d5642c94179109010082203005290001980200350400440c40d0a01c10003c4480d08118041071514126080350803010304486e00c20300d06482c9564244003103131029005003240751b80c0d003c0422500141c0940d212414070400f0200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 989372383 1250 989371133 989371153
    0x14071b060e01020a09120c03110d140d12140402060c12030c071118062134050d0b0702011107080c12090d0206030a18030801080f0d050f0a0905030609 66
    0x40005e1303c16030009005500500446000c0b4140b461800140c030740022900c03823941d0450010903030030132042d203004000d8440800c0324032441c000456010040601c0b66a40c109504030070b95a030f81555590000965562045e1021400525001300104102d11080042e220200302c0600d001d9280e810860317800d8800240010000100114441c8060800764101c0790844d41d04100e1220070001a00140003902401c08100d1001d850400c0d5038403001141251011282660014428650540041d80141c010140710800c209002d0200580107804c2d10340103040c51202071210380328480840c0e005454641035550b2184403412071100c510082c042035016102950b95040007410303503490105183c0c60225a0360080c894800d130303682e500100d0242c45030100c882c00d0300c1c1c2d00c0b6199034800826091001c403007004c962062540825401c518924120f603c1c000580d9602211203611310342f5000703c41c0100c800034071b0400c000300000c4020340140400800f140b902d004038036214408640741c4481540c0c3c0c0d0f140307907121903012 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 989373633 1250 989372383 989372387
    0x10e07060917060f070c0303060302090a0914391005030f060a080d0c0510020c0d1202030f0f07020a050d11010b030703200d0c0f06030506010314071b060e01020a 71
    0x11200d20100c05000348040d10340b288040b138188070094445010081c100d141141418440e420100156800404000e101d00b480843c00004000300c00044a1200342d1000c0e10303a0340f56012403102d92040e40700b40c0c02684916600031040400c07210b60215102044a0f4451075080d4595034403282d6414030f56180c450b501d00b0722000718242000c0081070944a08503000040c0f0400710003191002c02c0c001541002c0c09500300c541380c11802c0c13603900f000342c0c0c0b070061010418030302c650000500310400320419214101c07000c2e00d681c092010703480100c400000809080021545030ba071079100055000d903982c03059591114240d5211b030f05240b80e8041060010311040303078850450320b0a10542d090084114010002c87e4a035540d54142e00c482400d4001d141c5904c146502815160b44074240270b050f91003d44e03503a229850700382d07072250f994160041c4030010b482d190010f40e20394040d21541510504840c100c03515580d44280c01c0b11320041803230540c00801c894402ca800001d0b02401ba00c61640103010015860b9407140c080 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 989374883 1250 989373633 989373659
    0x303051b0a0c0b0a11030316090e150607060603050a05150601050418111c05070305010501080f0a0f0e0d020604112b21180f06020717010e070609 64
    0x510070380118400200240004894004603400042d801d52503007000e01c400d0300c01c000c092540d46045c0c0000802c01c8840c80092000d841c0810a81e01c54810f959100d00c81d0440707001048400342d15804200c3c03402581c9160120162401a1085401050a580701da03510390030402d14400803901d5034004250040c034040040c031200e078090401e10b00681843c1c9000c1c001d4035008001c131400a031842d5503c05d5103400c1d4680300d04a501141e12442080007400888030104018041100d8520000e454400013050319031140030528043c20008807901c0a0391a003981410050540c7c29001c0a191b03a02c1030302d03455108040c0413000d8000410f801a080c0c0f45018244803a10003141c02080b84220f0640c40010352000040740d0150091045444289100185140c4042c202c060050b01030458900901042510355015202260034a10304444506651351007030f010036460060700030316000d83c1021009019080c030509036058100311810006c21501280054581401c0964200400240b0094818082440300b107803 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 989376133 1250 989374883 989374927
    0x50f040312050d0c0302090607030c020d0b1602070504060510080601021509030a0e0405062d060403061e09052a0d0b1609050102060403210c0e0301061707030204110c07030305 77
    0x4040d1f1519a541c000501d9500c12104000e050080b08075121007592540602c81c0041540074840010758101503100344488000403c181e00144200d2802141a0915004200465402409005185802d002e0a4032a80c5005103090704602c5000306c623000741b680d0054000c0c015600d00c0c01450703403801841002400780b002100348034001c0d81081d00f444070a40b10140d9404c075220713034010350f14903500c8801d001ca90405010382d08558880030108010040c4015030f804250140d048031081440300507102c104130151148040060300542055038643d0f00d6840d80444800000e9514400701411800080042d03490156544183c0300115014100011001d0304c10030f030301c1c00c007002d0300381618180c2c50600000e42c1c503038000f08014200405119000e40c540080c02541c2c0c40d14079071400c103100748000f07a18001c040b10745400caa240320b5030a150b80018000d480000d05041c0101c0c060160411504607005d21016084052001075802002c02c03201141074410700511000d944a81c1d183c5030703983e0354040c6030600280181 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 989377383 1250 989376133 989376137
    0x81e0a06051305010b0d050c1c05010518061008060112060306060504060b07240209030a1b0501050c211c0903031a01081611010603030203041d09060106050f040312050d0c 75
    0x3c00500040e031040b03060714480717100050081095502e04c030240940c0d020340300b40a4042001220b880150205541006044c2d5400361005c56100b0101c0407840400602954190b403c08240c00b038140d541c2d44106440c590000041c18075040b071008a48114080702c419a001351043ea0b510f40042c002071829026a0005011a030304407801c001ca02e4036041840c1500203034645240c43c6c41c2c600c3c507900002c00d406031444000000c007030300c50380f0005081c03c40300d00110704640c645200003032001280c0d542c040c400790340707480b0a000010610f04c1c42d02170740003071600b0400d1840903403031009200190030b2180640340c602c480302c810003010030031f0503542c87d0203400e40c0d050701848a40c8a407800613107002c4d66030200601e40c3c094560301040c100c0342c0030140d013a54400451003106903e5402c1c02804014150008010821144401121241c090301498212900d410550300a40d00f82c211200402c00184980301a040184003100c015242607a03903507880d0081030705c4031071070f42c0420b40100314030303000030414807401c110403000b8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 989378633 1250 989377383 989377391
    0x60201020702061603120617120f12090a0506011e080c06091306050603130b1003030f051c1d0c0a0509180a06051e090c03060106081e0a060513 63
    0x1d035001a50a00408240400c844240b040e11014140704603041c03150346848610803c900b0340c44800d011110003e030035140e08507102d281c1e040f1161074400c6046400d803a1100016a040941000b04103080139805000340700144141c2c0c0e810004282d041c00b00c58020010052040d00390201d644030b4040303641840c1d01511045c0c00c00360300310b1110389035030b03049030301316241107812515038464850084000d00350303508940e4001002004004a1800015007115a1809410b0440c115960b0703440f10307440110580402400a11006040020780f4092000340c4000d0300481303145c1c0317850041c220b044000c540c0d440c46407244190085142c55043d03c0280300c0d01080e14019224030540310704100105039284405051500d0190000a4281c502c42d002e0190b81c074501d50010f4107028504041914072004018042c22541981501012507440c1c0700014404a4000020340501003507841d05600b541c108030003c04803511040c40c60041505429140c61040c07040005c9107000681c1d07030501c030070700462807011406c00b4415850 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 989379883 1250 989378633 989378647
    0x151c11091c0507060806030f0a03051e03101202150d0b010e040905150606070503210609070c110a2601060f060c170c10020c01051308090d0c08030d090c06020102 71
    0xca075140c1074038024203200c805506e0301000300f81351002464403003400e401103500800c100f582c044e000300141c0b1460580300070f02007401f20015a1a00c42680d6001c074a40103403108010340c0384058a61031a086c0010b02b018985403031171404144592002902501c442e503202c40c192800d41e0800150700e100481580c04000c5c207146681c07142e596024242c000c0c0041a1040c00060031603445104803400140d01205036511460a06011071b5849104003404503240c42c5480040c0c80c03800e060700700c24816071140c1d8440c91034800e151140e010540095117500e42250404001203030411a0020b20010092460509401d81f08482009821241150820024005d20800c02c0042e00d511044d125141a0049a001d641000507040700181d442404010402401a40c0010800075503950180a809001000038085982c0f0340b0321103914030344503800060501c0c60034800e48160f4100000d130358100d14411a01030b0728031900d9010040c42c503009510700302041c03620b81924100300021001048000c0520b80000c3d818041 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 989381133 1250 989379883 989379893
    0x12070f1a03071409060403080d05071b080a090e0108060912210a0608070e0103110409031d040b03030c030d06120b07050d0b06072a05151c11091c 64
    0x40094404001c000381501c4096500803c40c2c1140d060352030040030565a55924500003240340c002d444020000e625140001d6400740c00781802c10400c2c2e85210090788201c4140c0e4451047e03402c4915010304003d924800031036445c60301c5050f81c3c040c0c4203400003080580740840b00c2510b0400c4010030400d550905100c5405010b41c080c4124120034140304130354040e036507281d002c940104840c1d4040072042c40344950000d043d0410400c002d040c1c81c043c4000d8080180d0480c20f0105403865181d0042c00146000d64400ca240790082e8200c01014006201081c9c5201840000307265401c03040303103074095400003d181e840700c02c8a403240030010a03a60f04510080d0441d500c40070342540c0c00a0000040c400009210b00c0b02e0031059001808080c03000380721031746075000c90400c0e40c0f5218640c2c1008801c0440e1410344042c905808051300122103008210310030140c01e5a0800c0c01d150043d034403007900d05044080550551502d8000d081105e07402c4224103407203070040d4003001942c000b0012804002446070b0700300740c0411 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 989382383 1250 989381133 989381137
    0x9080a0e03010f0504060509071a04050609041d0105011e03020603062704050a03080f060f040e121c180b0c0a090b190e06090d0b07020c12070f1a 64
    0x205050811200d00c00000000c0790241c02000c000004180c58034040004000c140e500c0f06025807070041c11581520b45070007000c1c9008a0700701104042c103205100402080c42e0940003005090809000802c1c542030780d03159104104440801103015945640c0184002c2c0b810b10308046121031002070080d805490340d00400c84c60312000d00014060403120b051100110019000d100c407644260302c01c032800d85050f06210f0b8455203407080407130020700c005000c50450041403405a000703140013008850703040c0700c0c8000c1000410b40c07082c1c00100b5000b241323000030014200d1805006111000e1200d09541010a40d012080f19103541e4510007240c01c0214183c081041410030a1713000180307010ba40d0351003502c1d84058038502e1695000d90801000002c04040038518400e0b004814079840c0c071406900c090300c00c1003102c20300954101a07007010b445560300000c1006415069000852401071310726400d001e03408900c003220881341c40c6120b84d2000100b040280a00d210880060902c48076010008509020f074480f03034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 989383633 1250 989382383 989382397
    0x41502031501081f0302060325021f0204031a060a0f1205010f090f060203090c060a050c01060807050643120c150203100510020a0b16210b0303040311130908 69
    0x140d100400001e89c0c034042038080109035140c1080201408800042c005c0d625003551000084808800b221b204074080e007402034405a9074800494080b91502c0c4040135519200101801d901041c80100062508502081d035405000b4003030015a4410725800d05509480c03003840100d082034a450306090106001500d650b200c0d80d84042c0140c0e032074035004141842c002c0401d202c1a409000080d5030000d04c1d40120080c19641b40d204021300c8030580d2040019102c680c90f106040d040b607020004e407a28040c1030310080c91460500c0b030100c0d20341505003419029540003010246000300302182007000744a039113000c2c0b5100343c1c17491802182d00c40099441c060035041403d001d890a580100200751580b03020300c003940107800007521000c3d2008003154005c1d070380d540402d03050340d13500c08100200c0c0404060991050043c10b030340d141e010b9200c801008289e105800420a1803c9a03901c4500040d645c1d4244000e00045000711018590b8440a030104135091514800074806640382011120003c1c010385c01303407024 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 989384883 1250 989383633 989383639
    0x20123011d0408040e0a09200303090f1c050a020102100b011409010323100b03090a140f03130609141003050910110a2c09041502031501081f0302 64
    0x407a00d42d072030a030719580620b400c80c040300600c1204000c500f510340d5021490060007040c08040e05102e00c00b00550095454078195015007042040c10301c0ca04007840c00303c0d200701015000715649082003400b440d448002c0941240c4c181c02c0420103000355a2704000075942144200410468100070350000303030696407a10408130340c890003c5202d0768903a0190380300c0a03a0480e00500107181c518250528107080d0022280306281690709074010500c0c1c040c41c0181d1f40301c3d0b40803800802d001d401035104d5201600044c6403060307541c40f034908070f410b03650410300203090550301c200000d440340c078280000074020000c0c0e9001044102c1f104800280941d8545a00200504481c100001c0a4075681c60013410004100b0306035040c2c90605441ca03210241403030081a00c074601e0b0740c400c0c51114480d8442d200d1031680c0d001c07204450381c2c100301411191800c0440f0710f8200d807082c2c016100040440c01b02d48142c0e001200c0d801c00151a000444843d0b50304092150f0b40000c84505024140c00c0d0505951842103240c08041c0c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 989386133 1250 989384883 989384939
    0x50609010f05090a020d020a0305070908030a0207051c0804080a050d170a1a0a080c0a0b07021305151203030a06050111100203060f0402120106030606030b31060602012301 75
    0x40742c03200360b80c100c840340000050103548e120310304a00a0003800f81540c100c80051040d00c0e00003044000401500d00c141d40650143c02641d203098100031400e001d40e00c1c82070040c00101e4409000034a442c0c01000140202c80c0a0004840c29085c95800e243c01c58950600340300321480c814100c4000401c1180d0300040240000030905003c00c03050000ea8521154150040808000400e02c21400104c840581004542a00056481c2c2d403031124180541a40290081a4408481558411034003d00c1c0d01c00a120810b4000e00f45a1001070100c180961412045800002c14011621414040d00c4054035013820715008161003620400c4ea81e90888010a58181c0c1c0803010480c0d1750b031018546101e03032400500940d102c2501c50b01c03646085c42c0030700c94076010a00d05400016040c1c024001e5800b402c00003001090109841c1038881c260b13403c0c202d40700300412090944200c0c0e00001d4842c8101402e85c03a400002c42c1d00c50291701c2c103202c001d2803450700f48a030180801000444200541d0004451503014050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 989387383 1250 989386133 989386141
    0xf03050714070f05040e010212012303031c0f0624020f0a03090e070f021011090406080304180b210a050303150a050d110105090a17010b04050609010f0509 68
    0x10701c200005444406440c05014000510f2680a040f04803d659049504005201e2101c1d15a1300701c3c4284010781c899503c20000403c5100341d544802003440c04801080d48130320082c200040d00b984d1100c04c054295030716403910148901030038400c000d000c501c81b200c00c010039410485d010801803e00308a51203081c10720703c21168482d100380089000040766008465107492946806400d0340301c14090034000c1842600018081c61040000c005402d5598014048116040c0e007400b003d030031f050061092507101081981140e40b200c0c032034078005212420156845030700f481e6001b4030a2088030760000300341c0e0403d102001d4030754441c034010550304000c00a01d4440740540c1d0f4507509201f620440600180408010403c1a1a4018000d42201811910200400c0d1144200302000b80b51503405011092050b60346959035000328002e120310100100f0707010f40e059407003881c80080500811000e400b42d4580300c418030381e818640140c1e40c01550444841d520b0350b044c0307007003207811040501c04c603441018540042 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 989388489 1106 989387383 989387393
    0xf0106080a050a0e0d090f0f050a15030e06090a02040605370b0a0306080d05070f03210207030f020723041a06340f030507 54
    0xc1241c551840d810010003004144035007071a9600407001c103000080116424802c0c45036200e020540c00c111180c04907562507400502c0e820310b030350014415175896003800380948010180001c091441d40404801034480c1602c550441e0003aa4140810040d000c1688082d40740251014890569118144494480310400442452145001d010031240902c00b050500f48a0f24000f5011140c0301c082c00c42c50fa9000f08152030109654000030060003001303100e0b18105441c241405130a048054858912480d0032920003010040f401c0200b140c4421819406040f0f41c0280008546a002510b009049100c440c800200940705142001820450302901141000444240c807100441e60303070148400750010658000c00c0441040302c170216134841c0c50180c200028418030021000141402c403047d00c2d100300300c803011300d800303503240c0640491a40d881c101c0055a151809590300d81540c101 = true := by decide +kernel

theorem cover : BRFrame.Cov 989208633 989388489 := by
  have h0 := BRFrame.cov_init 989208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 989208633 ≤ n) (h2 : n < 989388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
