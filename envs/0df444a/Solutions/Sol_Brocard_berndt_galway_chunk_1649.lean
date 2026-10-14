-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1649
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:02:50.388404+00:00
-- url     : https://prove2.me/submissions/6bfbf8d1-5212-414b-8eec-b2b2130f3050

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 296402877 ≤ n < 296582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 296404127 1250 296402877 296402891
    0x30a0b06192a0c03050d05130605091f05030a06080106350f0706030608190308070e040f0c170408070b040c05041d0f12041a1c0b100f08060f060d 64
    0xc15120f40005070781c420380555a1001d052101950f540c0905000020000621907040c09107a20070000303041c10450080030f02d140c0300d035000329981484c075814032143c0000754000104024501e6070300030000280307901c0f0002c0225514006100c12604400c8040080350f041c3c0300c003c0625801c1d140c0b5481109500141507510140c60000380ca5503c020ba8441c003000f00f8181000003640d40c002066003a20040d4002c0c07001420001541c1c00c54050000400c41d0050104901058030b0341d0300d540c070a00e099405030b11000a840202c4070000ba00740052481e01214a0112104002c002600c00040d0384601d40e02c0b15005049071102e290203500c035883d81d000350740c01c6131a1501d0801030044520b403004116034a0030036274a840350b04036200340d2510104140c01000540801042001c03a40354520040303c40e4000940c42d04241d16140742c0002920340305070400c04562240051411458046c0c4003c40c4041c071410280c400203010703000a800500d006281c0d610841c490300283c442622103000700c44000788140004c024031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 296405377 1250 296404127 296404133
    0x10e1903051504031106040302030403080a271a030103020f0409080f0c03031803130e06040b03010f0c020d1e03020f120405070303080106020f060a02070c0b040308030a0b06192a 78
    0x29030203c0d41a40081c0c00d20261484d24803006c20389500494056003c0c2d0300c0d160031a264101c1c560720545412080040341c007411440f03049441020003410700000d000d058260b00d0f002401c0503500386903a00c90400b4808000400040c0e840762003007004000140c80c0400d00a0079400d0400090296041c034500000002480f4001d20b0808001144a812640d2483d50300b020011b180d10307540d0144004050495002e07000030b20440c012040c0050b4085030003080441d000c40c207080881e01351002034003248145a02c8290781140603806005288100d0064680311901c2210080e03445401645404150b06041c1d00140802c095102c410403500e1841c005038402c80c1c0c6061038130344a41e032031180b0b100c290001128100049002440400d000e800c0e20350003c02000c0320b446840e0301c88000d52111100710303032521580d440003d12030f40d0b2001a000841c02009099100e1034400010320544040d445014800c000400c5171601c00c175900000c0660031902807420600302114460002130003490001014036200d014501d980c10 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 296406627 1250 296405377 296405413
    0x618100e0708060a060e070c081c110a0c0b070509060a03020a14040e190e0a0b0603070306110a020f012d0f020c0109050c091b0c0a0b070507061802010e190305 70
    0x100c0c6c600340540003590b075a003070040300c0da07408511004056040c100030041561740ca51341c0d40c800100c540c1d0000a0005441d418800030b036805500041d002c110303100221030512900e0041c15601c4081800c16614010080c400030ba0144245103810303050581c081446010b0a01c143c800390300902d030b280100c585e100d84a04001261610486800c01004c03009411104492020f000b042c004098031001003203011100da4403d00629401003045170103106081c000804504035002d601e80b4100c030210714583c0c03002c403004000d003418a105800c00080c0c0c10322034403080340130b0080030300900030003000010b880ca00c400f507044c2c0c0c014123011101c40503024000b15602c030840710190b100c0c0f09103a10400442b00c2c0e4181000a104080e00129601b00c01c1104040e41c0107514120800104141a03150058030780e040c0c0c1a5440d45c040c9102600c4c242d0005001048600c108021403040d1032900c81012010419a80740703900080c500d480e0060094010956100e0007545401004411006507a00c4002e070380020b0102104001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 296407877 1250 296406627 296406629
    0x90c040614030105060a0303120b130c0c0b090307030906050d02090a0303050a0207091103010302010c14100504031412010501110c1c0b160804110d060507020a0201020618100e0708060a06 82
    0x2120f540781070301150b040c0ca00001b52004882c3e0580761510801e41c1e2001180062043d10220703500220f08a40c1b80003000c41c01e20680c20034110036200e01100076114109058003d00040082401e64410442c18011070742010300d11046500d90301c1c001d581c801314010b81c0c1001e4014191181d40000c0060343c0070042640040181ca9008855400c0319005550781d036042c0c1c2030341c0c603400c0d40d04a012004c00046c005941b10f0515400098080c0c8000b41d4401c0346000c0c0240307004404203088580c00d50f10b005020030190b1100c50444030703030b58000c84a4202500c101d41e42032001c0040c41030714140800d00c0050400b90350240905503403c1c10051407042401c41c04203420000603220002203820040c1e00d8002440800b01c3c54041140e80c2c07456076244015526a0f50340c1070104040c00f40d6945c481401441000020082d000391440b03030a183d40500140309052002a140a030050441d9400e14103460301840000170018201e00d502041060125000d88050507003410b00c582c0e5040084140240c008002c81c00485400141c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 296409127 1250 296407877 296407879
    0x9040c060216030201051902030906040b0a0306060305070203270301023c03040b100314030711030106270207080a0203130503010b0a032006041d09010c080f090c040614 74
    0x440c2c9180082c54065120001c0c007000f4040b4a0034005104c8484401d90800c0f042c40740c40c011649000300071000034240b9041607100191000e40028150000c950501580004040908081c0001e0a10441c0a5200e024403400081e0a84038060301d80c100740804114a806008050021595480a21440f01c4100c105456100d41c0c0c0240308081c104d08a04900d40843d5015564241811500c070399644408445000c1d1003100c100708040000310204400c4075011040c0000780b8002c5a0343c4a01c0d2072311f09108845901d02d684281d140031000c204a01c151400904840c0d203040403c0b00c0c980032101800000e0055000103840f4090109031920b5140e00003000708211880607030b03c4200e55a48030201401d8400c0d110f03419400134140300c010030014030101341c0f03030721503c1034803510710310828a840c0800c006810a91050740b884034400311610002c1d4600d056540c01401c4000207101c0c2c1c040c1d0300c1025184000140102d0100d0600c0d00c0014916101801124842ca0b0010414001a0750f20f210308488108203d40c41 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 296410377 1250 296409127 296409133
    0xd02040c090504061202030d12020c070e01080d030b030309040c1214010f0e150409050a0624090e0303010e07090801050106020c130b130b010e0303030a0912020604150203040c0509040c0602 83
    0x10a8400175420040c2240b070b40200284250802490102d41045209039400140e0b90284264414600c0070311004014221407503100403290302d444500340ca01120a007803403040c1860921001c1254074084104c07050761005440210f20b08621480c100e6100c10103a550000c494038000c000b1801850300018a4121070f806c100c2c00d4003040c6c4a460714402e8107802e0b210070412245181c4070720030314102a0000154036010f00e0950744172030800d8175400140d03001e1032440545407000c80d082c0c503c1c0241510096010382980c0310100114240c40c0344140e070f030344418060a10b8161580740050610380c8191300a4019000c070800030320980d40e45240195840000d00801440340130940000b0a5010092151a204a4008000003500c0c1c00210325180140503101c0214100400011103c20301e84040000b180100e080304c000046142503400c1c948030107a0000002002c640268080c400030840800011a446450807030050741d94480e0310300501c5c42d10b0750341c0c400c6800c41003000800042c40320152942048485a07029 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 296411627 1250 296410377 296410379
    0xa17090a060e060702100b060d020d050a0e010902150706060b040f091a090f0405160e1008010501051e061b03070b0a0e0d03091509080c010e07050f040b0d02040c09050406 75
    0x105600c0b0700f4100e810500590246180222090058100411140000e4520341c60300b8241b0244034141c1e031108c0201041c103900c40e014840356251601c6900c0c01c903aa140002c1100745a17a40c00140381040104030f030764040c2c00201c8c44009205032680034400401c45c90481507526a03031024070700b03100903152050200e060b180030034034404c8000a4803003e0f055a40249001d00980c1e138507040c450b0010b0068010b444c2441703184030201c1c040c60b0840741e407009440c40b403020620341e1034507048403074014000d0303000390460740d0525004208503107440d06024010369444100d40c00c6940f03804080340300c60254559030030f030914840205d8030981030f02100404a20307008102610055654140a4095071400b1f030341c040c1d9036446104041c2c40c0d14401e90001c2e05007403080c592200031030b400d031504805940d503182054401503000900006040740c2403081c45a80481e100181540914200000e00c00001031682c540c0510380f28103140100340c0e1040e40000902d41d00030b00c01c02c041160300c42d0040c081441401180c1c061450414 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 296412877 1250 296411627 296411651
    0x20403030801150503010e16110d02071a0c0c0108041514070e030106030c15110f150709050108010303030b06090d0b0109061205100b010c12030c0e0402130b0a17090a06 74
    0x4110390680341c01711000c001a480e0524001c02c908c001c00302e00710402403a00042d02c500701c014000c100101c4030340e034002c2c42c00a003132403100f1180e107018a01c55404034200700500b040d024804114501203140c242820040781c0d0700c80c1004d5020300e2400ca4120945860f1141c074500030119000b09500408061f40c8120f8542c282c85c052500300d8807640009440101410000c12401c40031010140035180c1c80c1c91300010700c00d140d2242910341111200d90305555008408006084658512031310b91200103803504500561411001905150f070602000e01059190400c0c610b0780d4035004201c03211001d014202c000201011300f05072107464000c1c050b1a1201d030030082c0011345481c4480700c50b07540036040009085500031008010008001900c841e41c18400c520983c00042412224600c1d02000c1d01c4d203020075002030204009001c2d03480c0250052207130b84107100c103000c40d845104078007096658100c98a0b41d03442051a054030b801c1c0b05e6402c021114031040c010000445800f154440c0f09034801c10040c0f2104050030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 296414127 1250 296412877 296412887
    0x10020a12050a1b050c0402031018050a0506011d06091f181e12050a050a05100b0103480e030f0607050f0a03060e0f040302060603070b0f09060d02040303080115 70
    0x1003006004c961010344d03680614a4075500550b085841c3c3c1812520041d80d8100c0c00b140409d03d03e09040c44540d454040064060240c0200d50b840707102460a074400c0140b03000f9200c0c0d480348803886103000345004106014152260030707064502414814200c0c80041008500415220318409480d03951741844070001b4040e00516120481c1c02e100d083c00344020350404103818881031614101341c80354440c40c41d0010204a050010240302d0340a40301600c0c080c240c1005820a96030507200c403604041c84c166002d4541881e8038414107807038004020750004078691401c0207108034049a2200e441440007500b500030203400040081c9000d9042d4145d88070403400000d5940c68010896000b004038004100e0b200d00150843d0040040044a040000340d40d0348840034407841200464903c41e0340030310304060105041d01000216484801280100320071340c1019050360301030060301d115000b1000049445c1c1600d583d43d00c25210441743e58001103445036a42c0c14002c107200d13002c1c4100b060f4882c0030860107941c14494 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 296415377 1250 296414127 296414177
    0x204020c0109021021050a180507092f090111010c0c0201142503110102070c052d040b0301330f06050a110129010f020303100510020a12050a 62
    0x501c1035405c41220500c0118081e00008003404c900c160f075034080610b100300b9161810280e50107100203141320703400d15612004590050a150112424942101844500c8000d951505840c00340301c1341e46400d0600010b90b200c19441c1070003100e0354245100703c4082c40d4400310880c031b940d000760b0ba0321581e4203603d80d20a010784102c40100000c62126264440076250b18182d230300c0d0740c5100345000c40c41450100c541900f20303041380f98101c0d11a049074500704401d1511507102d440440c5d20348900c0f05168072a0030441d010158004c0e0180c010340e228040d81225550039400800c03054400b41364040180000800c03649404c880c100d18a0800f550100301140d02e0b03e0106000d8142c40c41a280c1360700c0c1600314042610401e00c0300081304403d41d00c40402141c00c2a40403200c40034032100c43da401c031300c035460800007500c0780300c9401c2d0030030444d403003441082800019410035000f2203000b03456110160704003071412421701044210181215001103410309110383c0c0000186a100025914032800b4040b240d8036034151410 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 296416627 1250 296415377 296415407
    0x30720070506090a030516030c060503150909241e010e04150e100903030c020102090114070302070806090303070e0901150e01020106090c080f0708060a1208070204020c01090210 78
    0x8900e006002904000380103080e00c0e88014800c140713099032035403514030301540e407101d00b01c071007002941c100104400441820043c2c801d9003400c070304515080688079441d00449000601c05e44514001c83d0313407042d040c0103003181d60003203040b030010321002d52040100a01c0c09a848640e07401480440c0f051040c2c030000440c2c1a121001c41001e0603444907243c604551503ca1550541036036510700502c14001e0820a8420000181201080c1401903060140032110b20b480d0302400d59004021074110327603070301c40b8003070700c103804260f10190f11041c140c00c0407860001d036a0801c0f000c0e88526418852402c80020103035100e4485a031394410301030306c89014040628028032500e140d50030401180c41c9280d01660340483d4240e4184000111165108169400d0742c0f1802001c402003200e0b5014410200d211151603a480641800e00e80541d0416401091415010780f086060a5110030444800c1106140440b203a20f50014003d649036070178009900c1c007d19001c2d10407403043c5140b419159080c0c4c0294003403a85480 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 296417877 1250 296416627 296416633
    0x90a05010608130201050d09030e01200d05070f080f04090e010b0d230712030810030302150a090b0a0501080c011103030105040c02100c0e010f0509030303010b28020102030720 77
    0x2a100243d502d2054907510480c10f019050003600c0c00801180f003251b150034066541c49140515400c0090f0442404c0e410403101c030300d0203e003480c01403e000606420450b00364a000380d41c030701003410301031903903840403000034110000080c030f41965408000281c01035400021040005040800f400e508888440300c056400103424404071000c604812020012071004400d19654403e81280503410104181c00090134180400444014154080d00d80d0b5030040c240b1641d11265801c5440c040d641e00c0251030006a0440c01000142d9244119088400c009a01421000f0b050901e030f58513001030030090240d440c0910030b0a408081da0745c42070b81c1c805030400c50440910b103164240402d1102074900d503900c080c190312441e006203242c11080e114444039004140c0c0e60f0044011810001845407420038585010041c041c07004d811659004400c507030443d401c007940310f40e44982c00c0c080074401032410207601e00ca4013810300c071103d4450b0301074004520421040d030b41c050f098a42ca07040d42c2c209900030722001c91154 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 296419127 1250 296417877 296417881
    0x510061d040510050103080a020d02161203110303042105160209060402090d0807020306130309090c03180b0402040510080a02040c0203090307031103151909080c07090b090a05010608 80
    0x100304210303030390020700841c243c4403200030044440050362400c0c0e03c00c48401d64002041c1a445606228003c0044014405400701c840e1780c041d812040200c5006031682000302400c40740400d40140e980205465580082c1da880c1d2805040803800750440490582520780c112916001342c6120354122007003c90000107034150403071039801340311a610008103040d40065003004203903a3b680e00e1840101049100316002c980e81d200c184103141c180340e07000d045154000c140320380c60030001e900026118140c55500c040020444030b1020118003410762000c0203030b05c062400c0744039414032448144840c45103000b540c05000c41c2d100e54480b0046030781c0a20802546170410307016a0010300e0302d500300c3c401c0d0415500c1220300300190b040019040038215801111043c078291408807440c1014012414440c135840094403081c075000c80c01552440038502c0c0040903542d6004400c08100d92041542c1d8144540407c03030b0341050f111140c82c0020008803c40c1885102d0400c0050801b00c024041c15040c1e40c215a00e00d0b035a0303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 296420377 1250 296419127 296419169
    0xe16180605070f05010b0303040306150603050f0f130f12030614010912080405150d0608030901052a16140d0c051005040812030a18020a06180308031003051006 70
    0x320f000300800310b586540320451410569001c02c003600103980200c1e0000303070301103610351292a0780d00e00381e002170700380350528041140e69200c0c416610b9100e040da0052802582d2034011300c581646070303180010312101c003012081741808000c0e080c16910300d203e502c04014054a61104a40c03081d410f07881d00c0d000038140e40f81401269103e400c0d4a10103171080b0b0340103040c2038030340c0001401744956200d49480040046000c031542c4915004c5c1e200200801317406035140440c1400004c10303d11452000207401581d40f030f40721032155896100c00300452100026500d110300030600940c0c0d118100d2003a5032074411005d45030242d92402104d080302150b4042d002d2030741d02d4a040f052200404000c0d1501090100130311000603041402d01542c401c8580303031803d4903074a107410f2803510100e5001004031403141c460780c0c41c00d50060b104d0010080c1900c1d0b960800b0404d01d02051b4031a03c0b00d42e001d410062440c00e003c4103104000b02500c4000c000d491051003074980054101c541e103c102d03030703092103040904280740c2525600 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 296421627 1250 296420377 296420393
    0xf1b060c07050301020d0b090a050c0403020f0111010e0f1203060a0603150b0f0316050c0c0103051902120103050f060702061909061a150f04090c090e1618060507 71
    0x4882040300c00c0d551515035500000342240c0000380d00e01c1880d506c510300d8084619103003030550381c0011524010012800c0c0300c00350300c0c400c0c0503034000203008500f802d00381e4196a00501d40801214645002481540b01c1c1d00c0c0c0031a00d034181c548187e5038900c6071000b043c0d1019442c81c1502d111341c030050154940c043c0b41840450103407a6801c101d00f002c0c2c080d04004a0902508002080006c182a80d4203540c1d0410300c41d1080811185000c1c0010888288071500050780085000b10482d02c007403030007160702e4644800c5d40300b091020f000075502603440028240350101e0702c044e007030741241d01503820341e9010540c9c1c0c8039a50b1100021a60800140c1051000030aa46000c0c5200240c1c0b0240050003d543c80966440e0021034842080b000342d010307001811407109242440c0820454600040c14504006040c0c1d4900e005010724020070702042e446036680c2c0303400d61084034510b00608025003050740340e0514030403003004a14811403030301c001005a082c08400481d898114800c0b00e0095403424640111034452442d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 296422877 1250 296421627 296421637
    0x90d02041512031805091306150b04080a05010c030b010801060827061b130e130506040311010c0e0f0108040201021c020f0708070302031e0c060a030c020f1b06 70
    0xc0044104080400e0030340182c1080d440036442502d960700c04501000240049000c2c590009120382504c0c0100107030300003540d0351800b003181d12401c00306a401d504c0c01c150410510130b070008800400d020500050070940081c200b00310b17038050b0008006001164108401b030307540700d207403150100d0390071401088014410580c181c1d10600c0b81c0500d01c0455020035021601d5019103418050030303400301003401215804001540300303080703154116030300e0001840c04c0c50040e5403041c0b045201952a440000741480405581004600d5208003600d04600c1c25280141040c0c4d6004d18083c0d03690303e009019041c4900420130300205810040c0454100310500004466124008108074118000d040400c01c07030b850709582d0703040326640740d4000d0210359189501d82490416030398072841595200c100300700056100407400803101410510004a441135036100c85283c4a81400220b8208500081100d010795041d44080e038001c11075402c0d666042c1403d501c441e902d15564a00800142100144003628500703100102 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 296424127 1250 296422877 296422901
    0xf031314060430080f0301150e010f0e030f030c01090314090a1203120501030b15031507030207030c17070b090303040201020607030e010605090c030f010605120a090303020903010c1e05090d0204 85
    0x1007854100f503513855030140c0040900c132888030300c00320050201d4940401d04440304404e84c58208001080344e00001c001040c0303c0c480d07a090112a80e03412101351418002c3e5060b01c000c1c7e10440340c3c1c422141c2c1400303009202c603100c150005000d400e1561b0b03501c01c000e4100e9088070402002002041c1c1001140d401c01d080800c030490501422820b949140c03a0540540c078000c600418802c01180340040050009110605035140700342c0104040400b1907920410207500101640350040c2ca03608140f4042d1003004201c18041c0c45025078200030b80c1d40013146001050150320803841041e154443e10a2640c0d00d010030f440003809038002c0c1000074001442544800702203a940000440d01642e640046080490180d172107041c2200000308206441d43e1441c011030040000707151052406a00100d0802109405403600d1440e6803030316001400c0c14425010783d014044000c00030403001c1400380000d003070780c2c440c03584402580508004000c10b00303004d00203031800e0000c090503100749400d15508100060515400070303 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 296425377 1250 296424127 296424209
    0x6040f03030806010c02131a0402130e0603190c0f0b2503121103011401020303060306010e04050a08030f0601090b0f040303110708030c031b010605061b0f0313140604 73
    0x10502580c7e5075608a43d413080f000d6000148440702c6008058428a0030482900640c0108441008107202c2188407044464918180c041d9442d01c000190504800002e04510103454006020511074207640050840c2d9512049200c4255a48030010301ca0181d404ca0b0724004510104051800010703100044040b4881d240c112480c100c8000781200306c420700b01c07201ca560070001c801444651400d440d4000900800d0000314194607001000903611041405002c0001502c1d1001c142000300c10007140c0c84482c0e004e01c2180d1280351241c084010010210355550000300e5036280018101100c0381220440c04900380850300c5c0c10300f140c40c283d45100c2d0348120301c51a8403802e040029000d000b0f1010b8124441400003031079550800c00603414404400102040b5203924165081055554030011070b01c225001e20007001c1240030101d041802d00b00d070394140b090603000000c0c0c456440340d420225201900e40c000024821800030b0418096240990300030a00304501e00031640e0b85401c680d0000c508400c81d8883d035 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 296426627 1250 296425377 296425397
    0x70f05090106051b010e070914010506070f0210050c0a030309030e0d0c0909031b050309090c04180513050d0e270703020f041d0109060b030412180503030c0f0c06040f0303080601 78
    0x304900e051f503168082c19851b42d40307500e00150b04c0040302c1000d0060000720740090601450ba2503440499001002c001e10a0142c420340401403405082590444203134881542c80310000b60030054050103250b00c1c2200040d03900303c0180307020b1520f20344094295030403460316242503040410000c02006012416814001d040841200c00015102c0d0605024400c80245444071100e00502a50301e0024080d110004410321041c0642041c006c510b400454188101080603125198540c005994002d000740240c0991501c1c6410560032811001c010301050b10040c0d00880d5030b03141403041100d1002240003104801d0003042d8107500c82e0b0050003400c403021030680d00d003507074071400c18414a01c0d010070f10340000740c0100100500000b07882403100070031090880c03030710707510303242c0e980500c0c1d005a20403d80900110800040c800036400b00c40e20003610300501201e80c0c0c4e0000205d45951a006075903055264800d856200c80f090070140103a07000c4841451b0003280c5079085540980305080000c0a46040002d074001d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 296427877 1250 296426627 296426651
    0x301180b090a020402041e1d0c0904110309010605090717010302060706140f1e0f04150b18150d080d2318010605010f0c1401020d0e070f05090106051b01 67
    0x1700074402050f02c039038110140602800c4000290f409584410b03480ca9a602c020b03915241c140014642c0000c0c040035080d0745030030303402c001707801060881c01a2400b002c2c08070400c401d1003015800340303081d00c801b01d98459850791403000403205122518501010003903941c0041005091820142002510800012036500d0441306409200801101c07000e5144038204140035114030f10380d4010f1503d13801c5045030b8100e40303003260702d06e0080c0c00c010700000c1c0368960490f000c64085250f0307840640c403150010110030b07540c1c26082d1400b01c5000c0549045004c60343c01c000309080e505e0305041003410540d00036210340c2040d943e500b98400414045088800950101d01403d0311840100030b41c0d8400e034001c1070400744e88954030103c1c908481b1280c01c05c60500c040303100c0c01807106402120341c0c041d940e400300700000300790a4818200d0190061141e020079031418030f020f503040054007041e0002a03d200740200413009586004116003503000781709600c042102040300403d03021950000d000c0b200c031440700100ea5501806 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 296429127 1250 296427877 296427881
    0x501030b0f09070206220b01050d020d05010f060303030b0306060916121506022a19091119030612060209030c12070812071232090901050301180b090a0204 68
    0x3d81150040c0c01200030404c0d0300412101240d0784030b60b4034030180f00075010380c1c0c1c405007034090600905110b6404010b960003155204104d24110701d0f4008024405880210b42110184c40c0d140400c03004641000708007000d0b4140041c3c50b902c940e00050080d40d107600e50f0340c4030b25078549051000c18200980440b00844016181c09498103004031030807680021490094006d040c84c2200960307103051041d00c865805100034203331074420480001c032a1640c00400204a10081481a900400c00503050510070300d4141083c5000d030100c1c1003d5081c0c4111044030710130440449640740160840c4901000340310020034034960191840c0840034044401080141c0005004041d01c0d01c0c05146913806904113003c1c1500038441d4404003080300c481d42d400e040c2965200c20400960040c528204802c81032001d89118402d0800884844a890403891070506101d081d035259011614442c0951842000000e02c0d040502c252216006422042c0c0d92500f50360366120501030020b00b1040c02c0d84195415800580d0381c1d4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 296430377 1250 296429127 296429131
    0x60702040b0d0c0b0304060c1d10090e13050106081203040b0402040605090a051f03020f0907051605070e0106080112110609030d080a06050f031b220c2003040501030b0f09 75
    0x300013548920305460300001350b8090040d0682007003214028501f055181c500d54056010046940300002100c414084074101e040e40e01545852020700b0600803211045140c0ea01d80714080c00080c44600c0e21003401c80e07641c0c0700c03100301c0e40c001a0b410800200410b000301045a0403510090011804565500000307806c00c400791110b444965460040c0010000c1003030002907032492100032075a6151030341e0005684441d4039940b481c040c840e90000030b000a8803d42c01c5603d0300e18840803554042c0f0041c10420758559180c0110b000c031076500c0c000428010301400920703048502500c0e40c07240c1c040865548032804941d041c641c0fa009101400081e1660340d00380703c2c80001c00040d68030b069852801102c1001695200c0e8481409001c81c003a461340c5070380300403d08140120200102c10520014a0041407440605520405014040809500c80284d017034101c0482e500c1030356211800c0c1c0c0b6802c07400756140e4a00b1601c0590691040108001d10b5000340c2111144000080410061501ca0f0000c629030303003c2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 296431627 1250 296430377 296430389
    0x130905030a17070504030609020a0509040506040b0f0c070305130902030a0e011503021c05160e07030c0e060418060b0304050f0f0c03150c0d1a010905060702060702040b0d0c 76
    0x1166008007254444020542580040000009800e1260b4054441d1085000c00b40402e07031503040110554560141c880d0040101501c030b9501403406003001d0380c07240700070b0304c04480f801c01e182e002c120741e110b92102060240950012061400c2c4032a0340507900c540c032036561000600810040000da001483c030281d44104101e0f503000c148892107890140c00c440c00d0b548060300d03000f04ac00c0c081c400358464805084420325161410741010b400e500700780b80703410039411801015007000c0e01b000c02c45682c503207501c5018503040d4600740f041d6181c040e03050360701c1c00d8005402c50700f240301403000f0481100707072200d44110140341ca2400104980c84080003465680101ea0980d40da6001a01c052607400041081c8203003240d20320b000d4959065205c0c0001d8a4424818200380300c4aa58030225900304c0c00101141d40390080c1e10001c103c0188a800040800c02c041d00301507010a10094000441d41881001c41e034007140e005000318941020703035080000500e41c054849400910491990000401c8070038004040c0c00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 296432877 1250 296431627 296431633
    0x140901091419090f0c03050c12091c0c020f010c0b0c2104050f070b040b040312050c150703050105030a0c1509080a03050c0606040204030f2d06060509060303040e010b09130905 77
    0xc0450900704c00d44a840c81c1d400e0401d4603100810103010040d4041d0b440c075045c3c07510302c241c40c0d480e1001024989900c0728000e5203240c44101c0c04141081e04000840c100c18400c1e5001d840c001514401920340a480742000740030316034003000003aa4205c800c00104032404648052081c0e0310001480c0005815003114121140da000000120039a0001c018883c01080007101c1c1c10f2034507007040c0cbd07050040e0007544001030024840e40717000c0d07544d540110107441c840080c5604503420381547d0010000d40c40c2082d07403038a022a00c1c02c000031900382801300d807003542c480d0001c407503181c0c0b6854065002d24000a04855004006086601040b4403a06010b15030b000ca01a5481944442860005600f410805440a0310442c0704010802c00180303180010489907400000d40406039800c112241c5024070560440d20250450866010801c010381e0b00c0b5005841d0706940b808074a030340d4a0203140c1c0d00d1049004030711000300b401d40104564225030004181c84400070b00b12910102d90f8985010a440060b641180c0f031350 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 296434127 1250 296432877 296432891
    0xf02041505040f0b1c090201020a06050c07150c050a0e0a03230f0106060905010806150d090c08061003020913060603030e041a01081f03081914090109141909 69
    0xf980681d0b41c1014002c070607940d42c07500c071901c1c2180c40303c600c0703602007040c920341c0312011402075a000b07000ca002500d4000e00240302034030b0686003a03040c80d4816042250020509a625041407006100f54001c0e0b08040e01d0746480c2803100c0a0070707110f00c2600300550364411444c2202000162069a60180c03444907100207001c0310075800d042e1030800c410707401046451b0b031400344100161544a80c0d0744088903400e080400c4651a8607001c2030031044507a62008070389d04002101d40700c0900c25401901c18902801d1811031250710b40e80c5042e247e020030750b0861600360501c90180054a0000703034003508410795a9414581c040d503541e925080d01e80c5540240c01103400000b0602443c01d06c3d010360301f80b805188891882c1603114400103409084090181c503803114102c080c1d1354807240116502c0b400307540c0081469446002c50b4140b02c030780c91608050000002d085000c20300d2085941000c1d20a0b566050b1641914141010701503900e2480d48401c7c19440815011046da00c5082008840050041c0310b00c085029 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 296435377 1250 296434127 296434139
    0x8041d060a06020c10030509160311011b08040519080109051513030f1202040f080606031203090c060315121c1418010c050609030322020f040f0204150504 68
    0x10306041e600100564005040013419681e81c291403048003955070800203036a0b1684011303940b602600c041c030846104682c190100900c2282c603d1035100c030b2400d903180360841c4104031074013090b960003a00007014600700744001c2c00f207490160302d004403c1d454003410f00074503551455100d0035a0040301e010b0303540342c00070f1320322500e24a41c6120607544120160324010310001ea5940041c0503540205c0401700308001104616009009601110000c141e20555a000c00e030310f031a0515100c8000341c480610030701c104111001c1e1000c0d003806881c032030710003800540310019428050103180d80c802010040d1030700c00b032451444156a200d03520781092a5540061984510010050a40703403e0260000144440b8504200c0103e10700400c403049440c1d10300010501c0c608c103000580c1d445071020300090560060000304642c2c0c00002000e14807425074400384181d6010020301d410040524a00e019400c03035136862580c80c0d0790820f80c0061191502284005280c01c5c0e80f80c001d040c24455200709500042c400007030800c04 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 296436627 1250 296435377 296435389
    0x80d0f0b01030b010203030f06120d08010806070c0302070b0703090b0d15050f0d020d1505040b090c0a0312030b0d0213060303170106020a020d081314040e0619020708041d06 76
    0x5003a500382000c00c260200b40700042d5490100420724280541e1482c005417039511038045940c035503400c1d00221510451021400f0342030140034018101c07a8401e00340007074415441a1949501d098143d0054030030103042c60081c4000d5408600e081d000e0001d81c00001405100b0f00d0001c040c5900314440000c1c8401c406000441c0121140d0300c4140700c0d442d400702440080c0d99803010850350550440309050031712a18942081c1046021201c082007500c0c1100308014070004162083c421503a1200b62000001e40d00d003004484281800040c10980180790005000e0780242e11004541100401c0300b2130150483c1e001074084505502c405103038940b110320800400d80c00c40075a40c0f030060b2040c003020166040c0b2400039518021300c4030181c49000c08422040074400008100c42c0010034034007145c100c0a03101e031140c81c0146000b0860b140074601d4101c2540d4400c102180050240383c6640c0e440c80d1000910a072040030350072854081d5481032013004005903010346417148101c40c12081d02171001500c1c02c0030802c08 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 296437877 1250 296436627 296436641
    0x80c161404050403140d14041103150405030307080601020a05010f0605100809210708130e060603040506011703120406150506120f0a02160f062f0c0109080d0f 70
    0x100882c202018080001c0c1c21030b40c9800020b50391440e480d1038012610700780c005002000e0a000c0041e450100b440140a800c0b141d130072410034150300300c550030002110307104180441204c01410642080c000320326151712a00c1044d400500510407a4001442501c0f484d0071584050241c0b45d00c03d0b580e540400103414440038004c021006030508001e2031030441070403600c0740300441c240321302c1a4100c4001107545080c0e1054035841e540180c8001e032640c03803030818030100301418041c6081c0c0d80a50710010f052442e02070700322441144c2c00300160640d6440d203d00301001e00485029030f102e500080c0700d062088005018041d02c5613000301404210350303e100c000c80c00781c107c40d50003460052408119500c0075010070007000e0380041201d1241d0300780c0d0b694a12003000074001e0700b1b41c82c103004a151400782d09200b030003d82c4071201341c02060700b0070803010030402c0c02c0f4005500c040403c0228101300e81c2d01c0c0010003044003900b84d40d8a800c0c008900d4120390360710a00145c2c007c0c400c104410369131301c1020741e00448038400c100d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 296439127 1250 296437877 296437879
    0x9030506090105071e02030d0b06070b1503280210050c010c09050f01021507080a0b040501080c04050703180f06020c0706050d0c0305100b030a11160203240112080c1614 74
    0x41d4140b1703003203000944a21941070311800094581c1301803843e54950703000703c4544907004450021281810b9100e408001036554209210b03229907046004180e0400008055110340b0240786001c030401507003400074402c030001746601440300921425501480c2030007040001c01c3d10303903070fa001c4e840d051408001c3c0c9400441805411540f00840c400c000030302d1410981e401481da41402100c130f81d18071040c400a400c418131560b0b0000d0800b000024580000111003140071812038090006941d1300d8030440844649561102c0c81c1078000965801103011450700141450044002600d08003030140101d240c604598000000070308001219a0031032114407510030342b04d45503c0e05000f1820702c4503c40d098130b1000d006042000320008045080e10419921094440401010050311a10540221001610b01d40e0017603000e80525030041c003050400004c901140a03102801004d184d00700651b00035000040c0c601110314810420117441410710410290a82c841a511070f14095802d0111248100c02680200707 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 296440377 1250 296439127 296439167
    0xf0c1501050904140c06070b010905130209060d060e0d0e01020708060c0f09130908030a14010302030a12020312090703020a1d0a110904020d0b04050106050c0d0509010903050609010507 81
    0x5000c56500d030b1000c0340d0440d401640d080400c5130000c10550400c04100c144540c00000007030071100f0051124400c43c12903200c91001c2003560307503100508800982c0100300a40c00003440c000580c0603d03200c01d2040006001725130010310604440013484ca000c0b0b41d40c4084010071410800b5100d15039042250700040c040c44006020a0704003880c030410240a008007a402c51070012466601d1038032051801c4042030305056090040406c1420030400c50340c42685ca8802c038038201a0521719545a4480b194100e0754040d0090030b5004603625441e55801d03c8100005c00c602003045032001ca03a0301440054014025880a000c4561a40c030402c0f482003242c1c1d100d865903081c5020740241c1180d04d00c5031558007880c040804248414003280301c2007548a0100c406a10910204485c0c200700300c594400702c0390760b90507a4100f08076601d4560a1725180134031846074400e0350086100c0d083d80361150001e000081018104030359419284da8545082281c00c959142d103c4c0e542e0b0f003c1003103869101c82010000c1c241c00c006 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 296441627 1250 296440377 296440379
    0x209070f080f0402060d1e06080a020307090f06050307181415100201060f080105041704080a1106071403030703061a042907080703120203010506030414070b0f0c1501 73
    0x10707140520060039200d0207200040014255140d8108440000c100f400f410801003040d1103013100420031491056200910b852004500705000049460b03000341c00900901c46d8511703103c0c880000e00030100480844035203a64000401e40c80821200c80a00b190307600380031003900007100c1c0108540c56090b0750698072820301d0074444400040388007840c1c19030003136403504548101580160301500e03407548580c486030702c0e1400018503210198480d0740603a10503042c0643c044041c83d82801d150207207018401c410340250381c0c11030004920074075402c080b01010f4191824800e00e6140c1c00b20303140003400721080300d400000803c9080b5034140305102c060b09001e00d900c940d48600d0107507044507004601880115520f000000015001c03101e600f0740c002500c100440d9601e1603030f46481c40c0c4035003141004402142071443e51a459881900039a4140e680151a46003159120b441b0706422030300d507024061050251a00124150103503a004101c0c003489180c4c0da03a0b0304c424203000c003032410030410a500c14400039140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 296442877 1250 296441627 296441657
    0x131205070510060b0a0806011106090a050c04020301030506130c05090103120e10080604230106050912011a040f0b0a27051306021b0607081801050403170717040609020907 75
    0x41030317866082944c40e004510b40c0c2c8102c010383c1d49600102028925100394410010f10300c1c030001e0810800c1e07126009070742006c0702d02d50520059000a002c02000b58001a00081c10400000c54001c01d071800b4000300301206cde5568020400000d404e03001900c0b40310040d400d000c3c2079034000011800290060f80ca8902440d0004030080590001130101c07482940c40f900401e80d421901509841d4041182001d90125650307600c002c0c19a60010380c03000d000c0d0300c1c003910102d0a400c040c800c042c40e55204490488158076600104002800028031100d41159244041a042e4441d00c80c42005008900700f404528025003031841c602029802d81c0c0f030003140c140350400c42461441000e00e14612781c440360258542000400c4055103400543c5400060b1148004001c7d606a200400c40d000e1b03440b0150301441001c1600c055030a1b00c01c102c0d00540420920041d44c0b4180a4001c00650b0203c03503850044c048821a10300524142010b9600b561040e131102007100551810060007134008800e8246a00300c03400c202 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 296444127 1250 296442877 296442899
    0xb010e030c0d0b0a02040801060b19082505070b0a06080f0d050d020c030f27040c050a0f03021c0b15040f0306110f030c070c05060a051213120507051006 67
    0x40b900800701d005050101d008000d582d01900c01404103e002030002c9911403010310b24070340281c1214000703c504c1c1b0161502141c0140d00e40341c0581e030075096030807403a004e0702c688000d20041c00c0304400402004100307200c003280406440d240070350f10070000030070803d203410441c40c030b804203510307182d880c85c1c00c0080260885a0440c0441d807a00101003400740e11004d44107480b600318020421181d52440d00040c0452a42c541e002c1c0c1d102810000708400c0501d00c00110602085400c400c00e4400071aa04120403e20240071780c02490100c51246405032400702d0381030314492008a08101002090707180c000d54000ca24060180e0f5508038071010308a800c00d4500f4051040620b81c078400a402c441c0e03101d46a03000000e419044600304020303907001301d66a0402030500c50490740003040540c1e441c075030b000b8080391500c0d00c042203401c40181e650701d260410035000032451012501405010709001c64410744c2000543d40d0251103041c04a94690039114207207800c3c564145051203062804140c64036005000001d080 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 296445377 1250 296444127 296444149
    0x306010b0a2f0d020d1b020108040209040c030507060513080d021e0a02150c0d080105090613180804030317010812090325090605010e0303030604270302010b010e030c 73
    0x42da01c41548000041640580c00c0900c1d0025030882c000d5080d03030080980c001800c01c1c4400e48541e41c0d0001150031030000b00301d461a40380b0007800204020013003005458201080da0f0041c0c003078003200301c2b0a0740d284d9644e49004e400354082e80200e40040760340044068800b803000010321228010344200c01c02000b000b500c034418032440400c1580b000c914640c42c013004101403001190b014203015040c00c600c050501e104d42007001c0300d1600d0b200d1201c2c400d00741031080390514100d98014054040d42c0d02c6140030000030701c00c1010704500c0325a583c8887c80700c044400044551850150350613035521401c2d0304005001106c0040360342041202403004000c9810000b500d049024115050140c0740c0d64007000180c1030040300940741140056a0040d024040040790300001182d01c816000c10403140d0ba0401520105504010980d140d0002c0c000100d0030700309030b00032021015042401040981c0903c145000b42940c0940650041c2e41d121079524055812a0780c45500e000210300424121005200080391100c90f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 296446627 1250 296445377 296445407
    0x405011203230a09140102011b08090f011107021f02030915040e070e01180308030f0a0908030a06030c1403030318011806051b0403080f07080d1a0306010b0a 69
    0x803129000c01070000806810615070100440b9612400410004c0104041d4040c510f0603005040c4410309960051280c2100100444100703941c01c1d403001030540707458030000c041d03004501565005102c025820301c691804081e0120049072203151500501c6040c801c03201c1100d421441d9515407680d540d8000003a0740c0301b194222540c0850707483c0c500d1158803030700440e4032001c8140340304414000350a070414000c0309a2103080c3d0302e4154101c0b1081070b8074510a030521002d840380380700300082a4461100302c4c08651003161a24046011065507854a03403603401220040c00e06980c5080c24002c0001000c00240113100c2e2000d440503052007079000039280d22020705110b410480d44180480341c42400e40040e461500c403110302d242c44c1ca200703091950142a0407039000b1080172503128002c0446083c0802d840039a50000b80c0b0904001005003504074680c400c2c0d000b83c4000030240507116501b80036006403040c40b04c41403066030700d14082c041071610b8004181c10858100e4820300c50f2000c030b01e40c00405003c007082e07 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 296447877 1250 296446627 296446637
    0x20d051608011208040314030a030e01060b07020103150f170705090609130c05060a0903060e0a03090302100c0204110702030633010e030f151302220e0f0105070e0405011203 76
    0xb03c54908a006071049901c004d00328003e540b800480d620002c0054104403000c3e4400303102a04800380c46508841540c00340e6140c40c0070078131911016511039070101c1300d0280982c001c0079000c1c0d1a0003603a1055095907009040d030140341d0801880401041c003100c030003000d054580b000c00d81414000601e61184c010480e11a159882101d0340038400e0140c0c07000700809000c0c00a0340c0d5000500002066840280030030b4815a0403d59015210040052038412040c1c1560f102c200440c02d59003000b0300c61103181c900f481007002c8503a503030300942d0f5030348a251079050300b401f0800e54585480c41454103001008100c01c0440c0320040001410202084610400154624240050601d544010707034110f40840f0300a60544500440140c44c036900040c0600080c120050014495880d5600602c1510600380000d400c011045119011f404841180c05445c0e07500d00c0c1e01140c0020585441450584050780c1948169115818060100e4200c440c0b544405801c0d0345c140b1442d810004001004246a80300030200a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 296449127 1250 296447877 296447909
    0xc2102070902040807261905030706060303050a0207081203040308091606021608010c0e060310080a060902030111040305071a0d141506160b040212100c14070327090f020d05160801 79
    0x28280708440001da2f10240c104640ba450b81030050046c2c008400400141c03043d01800328903001c0000d8034040c541d41d440c031a42c1c50b640d201e550031540400c004d4040d594500c24078200c01040241445170742e003c1c1030240d0040207500a11610030502403241c1e4040347c0280d14100d89091440d9000701e02355000003007510310720b64a0321144001d45c2d80a410b5488020070b401f411194004100380f5420030100315000b10020322009111940d004054440c0f441b0043c85030b0300c40a820010f1155800c141d03442502650361703960a2414072103244043d33860700d0140c046040f25050400080d048502041152403100399070f0300f410400b4000e0040c0403001159005410740b00d02000060455841c1203040030348084500680e8241e001310300c0742c90050412640d140010a00a0095805140c0c500055031030031501a03036813180401c2440c2c43c240c8090b00343e103282103558459103408141c0603510f01511601c00541200103988040c0414000f0031550003800d099038918211007540b00b201e070700010443c191030802c0b691400310 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 296450377 1250 296449127 296449133
    0x510110909070c03271a0901050a1107050a08010c080a110a03050411120303090f1b010305100b04140108010b04030b06090a0204120606050f010c21020709020408072619 74
    0x2001c0003040d0110003902d14505440c40340480d001075006c803180a20300c0c0d5134003200d08a1824260259010090000c0c03002e100a26501e8450403009042c1d03015032080d1211716442e8000310707400c215260026201e503034640c580c040081da4000070841e4801071070070003040003103002c0034001000c1c81810b020788205a00c1d0070214080c0020850300380b86600300141040300724030000412079169041103a58050501034555603100380080869580410ba68140b00c45100030015401500201005402d0b0040c00d00c1e0300e100071a03146041c40060010b890350081175494000c0300b10004090400503000b01e03400304c10903c010000075041006483c2c02c04021174900c1c08941e00c03c2401c1000740999808580d04440050340041032046d030398424016100152544c0c0850080307003006460140c40103400400a24940c10040d866000110700304140c1c4c2a03034410f0310000781d82c40036110306981050300000c100c0c0d0040c0000300080a10456400f9480240700740030100c690300000040d441e6006041248800720390001c1032810 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 296451627 1250 296450377 296450387
    0xd0f2f010c0606090c0306030b070e061c0e120408070b07050709050711030409020d061d15060c0708060601171501030c031811010801050f0310090503160510110909070c03 75
    0x90f02411030704001405c084400180500f20310b10041d920b1401d1140850409480740200c1c40003200050200d034508810355034501c1e0700004604919a1490381ca10400910b41d4060080f221000340380000e154031541400300c0113042c9005a8000801e01030f0030064600000c07004210b07401180c0080000040540da40d000540700d038180c0d00c0d8042c0640c0400140030569042c103a02606001c04001c0c000c006140d00d403c2d80b0441000d5980038040c0403071803000000c510120080109010300d8000e071030203042c024407900c1c0a191040302d40110b510b94010380300700401940e20031202080400440000505030400800d17101d121880f1102e094101602e0325441c408543c0290440c2c0303030b40c50162070114030402036400e12a20500c40440804d00040b000e01c00080d4525003004aa120303248001c001d0018044450303407200060445040407607450005214035900d01c01c0148200d002940508050420302d800741070002c08450b1000c010450707c900510011719aa21504141c1e68080c08900780440c1c00b00c89810103a0b5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 296452877 1250 296451627 296451629
    0x60c020418050303040308090705060c0c102f010f0504020916141b010605040b031504020a0914070e0901031208180318030f010204080604200d0f2f010c0606 69
    0x2c034902c800014001016800b0303150a100e86001c02c03d54500589440403c00548503400c02c460741c0303030320000440000c1e107030600c03102c16000d2060908203090854820715a144c0c810032844d28401607502030010b000b082e001e01071071141c8900807c080006141581c0000c6841c0d20180041034032403040c0f498580d10318020300b00f80d1940c2d444440c1c0103032148852505080d194103805100001035081030800511420180220141ca49006001e003a02e80740d03101c0c1328600d1420003441664880050900001c00002620500c030306800c201601307147c43e2034103801c0075240d80041e00c1010b0180c00b40034010408074083c03040042c401d91140c03428030160b4540000c01c2800c0384a1304084a51070100242015151140030f20304075640394250180c0746500c5a01040d81c1c00c038040d030300c525183c903041100020005400c00000000e0120584408104119071070081440c555081c07904490441c54400e040c0c00340309590840c2d94003160342d81071107a039516400740d02e001c80c20100c1d00160b052180402000041010981081c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 296454127 1250 296452877 296452883
    0xd0b0303070b0601020c121011131d15060304080705030d0f1d03030405031b0f0613060506060901020a031218050c1009080615180403091509060c020418 67
    0x740c0741c0d00c181c242480340c10015120b803400f502c030b00c1c8118481800d1000001991403030001c09881821001c60b500c2028225031007820781d07402c40411108281a401030b015401403d411141f54944c07408010078450018400b9040b201004d81d5444103088582d111030449a000741c1c003c00c00c41c1c0354a0140f034040d140d400b45010310300a0780d04003040c62412440591103001c8001a501d2a41d103042150403415403640b200f550045c00c15001084099400101d0300101c0000c01d1043d0122601052000851400c2640903100c0e000a1000c144011060000c54028980c01400c11142140381c400c08000103565200c8002008040c0047c030031100180b0302580c2d20040b00204242c1400c410707041589011070302d0354480d80d64035100b5031102c507020041c20700c5103140304142c40305007004010a4452100381590858403051444d070182c880101404032008a1361828001c80c40303034441444460a1054103030f4126100c01100e0100302c00602c2c100041603008000c503918076015580056040690003c0040c1803c0407c009 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 296455377 1250 296454127 296454133
    0x60c0a030c03090209090c01030614010e1002030405060c101505060d05070e031906050f270307060c200102090109090e121c0c080f0a1a0a06030c0e0303070201140d0b03 74
    0x11921038030100701f03d800d21754241d9003003181c213860b0070503d4410841156000e0002e0354405c4400b04c1810305042060048015004407800d2072b50350000110355034800e205140090300031800c400d500382c0c180e0007400b80150610080030900e07401d00000c11524091074204032955611000070a08050240304200c614400140c162031103c5000034141148885121084407511701d8032001826010090099501504404200c859200311004500e4519120905458018081040362a0004249200314000c100254490707580009411b00141c01f4a0b40e044502c00269004100b500d104d6a444401c807815921164000100402c10900c1c0a103815a0349142541c420720010310ba80340340d040c2e9800d454101040c100c003030003d8068036504842e140b000b611020401c50b00200800c41c0303500240c001c240350491610111041ca01104000b40110240d54011404a5507071891100f03d9944018000d981000a60041d071600301c2c9640001c0c49102440c1c0001c13020b41e00400c55410385806030300240c4e810300008040f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 296456627 1250 296455377 296455381
    0xf0807031d0a0209010509012114031605060f0417070c0f0b1209010e0604080a030f1a040c0e0303031f09060f2309070518060f04090e060c0a030c03090209 68
    0x45640c1e440c4802c41c20b901c100c0c699800040d1a260503040399060b140d401c14100f885540101140200c1d0521050442d280e260000150103000002c00c080c240889038004075100f8a01d29040c481d003000f0000d0209040c004201c010400840ea152250541400c064510103039500304500300794240c2d101507044080a02046400010040758040180181e005081061460381c0c49000c401422202c01c1c404030400e6411803000240840e5082e0003a1003050001c2c2404140c6000c9070361840304030f4050102a85c016441314400500900301441148141c2038541000003a102c1c80c100001ea4a0200505150a0414103940b0320b0040c0d090003440300c01400410014030a032525913a0034080e41d9410701817814940c544041d600c2e27540c01c5150800d4503682010340101070a4869500032200d950095070071221000de1131349060100e0301e440700180a2440c0041001d5180e50502900c041030b15200e2003a0b10f290360011003802800410482100c0d0300f04054100043d810304102010707009841102c2d4041d60152030101 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 296457877 1250 296456627 296456681
    0x30c03030f090118030c02010f1b03090806180c1003090507080c0f0a03080909100b04091b080705162d03020f240901090615080106150f080703 63
    0x900c96018503030b20402804a0f0358500c00e0b406120031450409000600c42081e0341001d540a803100004d24041c03464102e03080c000004001c4443e0600c004c0c205c002580d0b400040000720014002d854002d4809984020601000e4041c40da03036400f2005128440c81d07241d19504c6103e0301aa00c030407103250340001070b40c0c9079503501c00c451911003810198190090500000743c4c0d96a19200c0410005d42e07038003d80c0141803030200020b00851100040ca844075100782c0e14000b1a440c5501c1001e0720091450800108403508052241c0320000101000002030044203400d01452036040010f80307441d0500c411031403404050703d040c030081565a600030303404007180020581d40c42408621400e047c1720f0080d005c940700c0800c10000d440d0b48001d000b0301c600d08000030001059a800204007200c0c2c02c8400b800000c181841561601000c407540007603c105441106c94007000064000e00543c2c0050010602c01d001d46000840c0140c40e2040f02c244500c10040008005042ca5029900c4038032400e42c0c8520442001d402303a5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 296459127 1250 296457877 296457901
    0x2b020307030b07080a020a050a050903070f08030a0e030d0807050a090f0e010305060f01060f0e040e030f040302030607020703020303070b341d2103040b03040b041709100809030c0303 80
    0x1403400c1002610030000585d52000c68000c5034103e052556a040c80d040d025541111150441007410f6418042c140c0b000032591580035844001d1b00b00c030009940e981080d078030007611401c0c0704c0421354020380080035294400c0d60800303450fa6004101c2d0400ea69074221495044800121680000d5410f040c00b28011640745008019107050b240306504803081501c46c00e44035a40f1113001d20841002801c0c0b10022000c085c82810510f40140000c0c1000c00e0407000b03071120504680201b500e800304000e0100d010030079490104502c0c0d0f0040072030f0000c1c00f038950039500802e490341728484003d030012001101094144850050096103902e1201c0d00303240c0341d65400041b41c081203800c0c0111001544015081103154030b6024421005800141801c0c0400900000135000300f141c00205800c50206000000300101e03590001c61040b441a0f91a0016103818030b898180c03003e9402c40c8400e150410311509003143c03581d5500d04449016070605014030303598490350a245104040c9c4a00031404084103211343c00f1031003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 296460377 1250 296459127 296459131
    0xe0613030c091a0d080903010f14090c090f1f03020607150f0606200c130209030105010f0e1314010c02030d051b03010315111b0106142b020307030b 65
    0x401400d210b21580440d40c20328400c1d403003d2481e4482614403822000030016402090042e0b406800401c5540304d001030002100c024442500c0b41e05e00100c10000c1c020b409010309500c2034403c5a40300418100104108e00d1828000c0140c2e088400c0c0e10300c00800401c40003e200c00455004101c19030f03503202c1d40f5002e210180c0e807582c01400c1c02e007001c405041d0341203180a104182d882c03d58410241210300f5182c411800d0000700e01601c580148a017101454407140c0c0d6200d600c2d41ca040c00541c0d542c440000341400c483c8140c0c4040b004083d240024040c1c060b1425155030031810b40c2010240000503814040f10900a20b00e0070348840d8680404c52261136000b02c050044117100c44c000f0020313960392040d4250607181c01d40044c000360100304018800500d40d681b0a046920046800180440001154075020fa010540346403c0b480d07072503810782000d042405900c001c5c001605c119030a2020903408200c4480c00ba02501c10042c990400c920100301408548018040d00241103c40541d07481c2083c02c510201 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 296461627 1250 296460377 296460389
    0x50d0305060301021608030c0d06060915050f0d021c020a030e1c17090a05060f01170a110105071e0602130b03071b050a12080601030b120601060e0613030c 68
    0x4000c0025042e2a042c400c0c0d4000c1c05c42030340700440200c0166a202829400103103c194058428040c07410844072038417440f000b0300220b4461003401c1d170038184a014040c81102281040001c1004009458801c040584440950b21200941c44102c04141c10031a01c0808024541692001c039144a155606400081006180100f078807012a0782e03001f1811190a00d849a4004c13a4031800084000001480c20b583c0c000031142c10f8807035032915640c4482c2402800c4d9900c1e406440d1300c6006006007403000e81d07511260f664081c0240310028807655070125802110ba41141881008110390061000c2c1d075109645030303007540200002219041c60460002d40100c88020b6102800c0b06021034020380b210112030080c0c0b49a2201c00c501c104e500c80800d91060107090884035400365480c001d00040300510025040b19840c3ca814103103182c0303500018103c880d20004103114008200240080c03035404182141500c44034900390040d4010307030001c5401c600c50f201080d0644942500000144030420071094180c40b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 296462877 1250 296461627 296461631
    0x6130309153e03040e06091801050103030509010806040911040f0b03030c07140a0e160e04020d0f05070905090412020a1e020411090319060e010c170108010c020607080a0b0d050d03 79
    0x1050009441d501e003e0303030107480c04207900017001c90450329242401d41c0c0c0c0500b281c0303040300480099640803400d4034400ea0007100400d6010130074400315a0401030312580040c007990f04001d1560b0759103031200c20b0710f544c4030f0003030180d079640507421362030019504040310050001d0104c0e5a2100384081342981c0740304a01c1032a87d603001a2030b0781040c0d45011b070903002c120f50513600c012420b03071074049075090000904071559080c4800c840c0c0d180c00980300c9001801b004010070000182c920104030051003541d1004000008000000c00700344401e40c2c42c0310450b81c220703401141c00c2d039813401c8200301685410b0082c00042d080042601003240c403005507a40c00c4210a1082d1400d20050080407128000303400b03038032482941030308541560030b125130000c04030700103950003400041148000010320700c0c00c55510801d00000a0503941074100140c0c414406203004000311030003003040d142c103040000e4503030748050001d03030800c4096001301b1071007100d940148800c07050003080c01004240034507140c0e9481404182e40c0020134 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 296464127 1250 296462877 296462987
    0x21009050c09150108370f060f080a110307121211060103020604030204020a2a06050f060a0608070c050304060302040503010c110706050a030905010515030613030915 73
    0x125904802d410f141c80c06071517440c82925804680c8010030980f100c0d401c0100100b040c01c0c201034030044a1780801c0d02644000140c1001d144c80703080141c86440e00007070000461261304100001c0002400c0b081d01360442001106040401e0000342041c07400d600c2405c190a200e4001c800f40701c50500003203007041543d2100752000303011030169516000244406540280148810005410150001d2903004441e18001c2010042180c4040320022500d580d20451190741c8010000c00800c1e200b03294201d0304074107800700c1c90324060000889200d8240501c1080240c2040400c002e035001e00080d00a5179440340170f4030340320360310791170000e000b500984036080c07081d0700f13000004041c24055603203000c141140d85c020300043d5080650a031481e070302480348801016074401940010900170f2160a014803d20480820074612005c01c05240143c06001e83d12441d041140304d00020741c109100346c044500780d142c91900801d40f42003c0d10f9401101c100780300c408015400c2c41860105143d400360340c4001d0309020f00215 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 296465377 1250 296464127 296464141
    0x60f0c120c020a0801020f0c1b0d06020d02120412020c0402070c09021c0c030522052d0106030503090415080a061a12070f09020a05120606070c0e010f21060b01021009050c09 76
    0x5505c00000e1640c122001c1070b020002f08020303400a0002c0f8a4581001d4501a508100d40711074000403101619044490207a005969a051160b8112401304540c25403c120326505d4050f180b409500c500c0d00084c0c3e000416800f1040000003e1000c26004d4400f0022801c0041000c0c024000403a410401070091035400c000045a180e00c140186421a0080103000d801c071314010710034480c81c0b00441c4400304400b15003c150800740520005140301744007035074642c0400020302064411b071078285540c03a032060708148092800000c40c3c20a058000303c02003040c10382100d0070703081030110b00c4190b138202188880c03a21600c2000610782c01111030080c043c9060035520144a801c0340584100c030800203c0c1080aa140f000d0000203150704043c00803e400c0c80c064131a0b580b0708101e4520b0f0f03ca00c1800c2c1402c00100042c451110010f40140301291101811065800c410710464801420003070601350b5844029a2a9100b04410301212034804800c0018040500304180d5551031900017506c07900070714001a1340 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 296466627 1250 296465377 296465413
    0xe060f070e0f0f100903050d030203060319030507020904080712030c0f201501090606020a0b131106030a0608010b27041713060f0c120c020a0801020f0c 67
    0xc110322035680c0d128069404000c1140c1c0c8402001c00a5100301a080202003aa0742d21004c2e00c402c605907165140300a00e1490050704080c141305002e0141403050007080401e80340030881e0800c907514142c80c0440d8480340e28060300d040c010b010700a034200c40240e0420023084009802080d907103000e2800e2030005100708000300c084c0e03070710580104c0000b031024684080490003150389103980e004c0060250458101c00300558a001107200010700210541d00040010701c03030340d102c0c44001c0e1080748050441d156130368407135034005407001d1300c28810100c0740318070841403000c0c500d4801d50b0440c00074040c039030b0703410a491007030302409092c014085554030708840c002040c42c0914001d19280302462100c114200440d14800701800d00410955aa120500720010b8181042005156200701c1a050320240382c14030000030100d10703491000300c00b84103000041c00c002c500c444402825201c040e10b4600c2d8188441e1001c24801340c510740c0114019070020442150803040304000c0c01e1140f002e002260300d56289000b401c0c40d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 296467877 1250 296466627 296466631
    0x30c190b060a0b1e04091407082a0c0c0d0302030a0e040905070b0307140403050a0c1d0c03060301090f0c0e0c120105010521180609161403011803030e060f 68
    0x41642002646820f60503134018000d869a000c840710300701607450030b000c02503038007010504000c2c18508040008850304080e00d00d0308941c054091140c041140059005a403100c410012403640011920005044c030400070b9061410010348002c608000c4c52801a541c0d401c0070a44401050110118002509041c450541d0083c1c101e8001c010f8a86044800700e150351021f0726200400c849459040303488011000140700451050004140742c908a040544428010f07400c20603981505100a441c1540e501c0306640d04a00082200c6550341c44030070000e40141070110300280405c410030188001c3c07045007141101190002c04a0f40c05550340c00400c100c89226075410600060407075401400b007544201e01401038400c0082980c0800c2c0402e4608882d40141140c040348070103c4a103254015842c1484075a0300a490040204080d82443d402d82440500c1c0703005134607c40b802e0410355050313030780c1c01d400511900492904800b02c000e010b04004002d0007003000c121415200c3c00e0080340058428005e024 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 296469127 1250 296467877 296467889
    0x150911030a110402070f0b0108030d0633112506052106011b0f050c0906030703030c0204021908090c060307170432013209030c190b060a 60
    0x3560b0301e840e042048002c2d008074400382c4105100841110010f200e40000d1406010078078011a1103404140680b420741c1c8040d081030f00c6907c1c840280400140011001c104440e00d542075641071094480c404980b8405a00015856445400a44180202094104110025540083c05040303440f440f0903261846071b1200d20346005d031044034112107100710f04091600418140340c89050940040303e19000840840f000f6500340744500184400c010040017005060341080d0f5203020f243c0b91080c0040e4032001c41e48405000d001d1031000071030441d900c1d076040780c90a1f035204501e42401d190344c41006105d90000c031000b4005202c2c00308a0383d12031034110b042c0da110304003d039203e880c2c01d240400c02c04a090006003080701d0f00030800d0780b0020042c0c003038510f1207407103d5104183c4420b4003030140740380e00b5100d05511009200035049041a882c85c22070100c5a0030382c1004880ca1116102c0c8a80c80b480e5200360320310083e0307a008000e00c061400c146202003101480c01190080ca0030303201c200403c42c0c0150703203108003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 296470377 1250 296469127 296469143
    0xa3e040609290715050f010302060f07080c0307050105010303020d05030f0610030b04060803090f04090510020304050a210801241409090f1b040312030f0603150911030a 74
    0x1003200064000050000320000144000701c2d410801c05102e19410081c400c80301c2860300d80000242050510440c0e03880f1410545d00c0d41194917603004500e03140314616070410206000103080090012150865500020560450303640f1181c03420658020070084c0400c0f0014003499481401091050b000e032405030544030442042034580300200807495458290300c00505440d0b594940d07065540781308a030010400c940240d603a07034040350300f040b120054503081584541d181c030f0200b030701003900010000c00c42c12500a00594a894a0500614201c5241e00003010700551000303900400d250041c01210744812074940300c42a07601c80740011401014412000144201f4036a01c9110078441c440e201d142c641c01000a500d80303035407a804134904070001c03150418403800307003028003540d1260054448035120305961003e0825040d0741d01d107090f4102a1821104050716018007452486127603104100465000500d19126014004640c010305401034060707032000340c0e007820314110b03040100e200c0201a0b4040b84c0703 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 296471627 1250 296470377 296470379
    0x40506031f0b011b06050603010e0d0806100e0a0308041805010335040e040c0807060f0509041b020c030c01020715030228050705060106050f070b0a3e040609 69
    0x4002c004070807081e410450304500004004484d80b205440d0309000e944040780e540f40c02c0381414203440100710185090790000c411032120540c08034009070801e0302214440c5e038a5521035000c0300d844814590b07a40e40703d21441800002c0002010003041111b0003003000031011544130f10350070b0403241c4c03d201c00342090309035401c2c0300014040540200a0408541c101c2c0d0300c904000312110465820903040300d10402c0c8810203002c01d00c01c2c841e03016001060700c3c0c4001c101090510000030b100d0040043d0682c14800c0108980482d907503650061001d00300c00c46000880d51244450082d83e54081001a50003400b40e03090004a952002c54888241e980c40154011000303103180b011802584400715031060780b06604400265400600c0da4030750500c20540e6010741340d0013182005070034880e06034003520900004200389541c0450581c2510450f80d040a01221196201c040345005010401c0c04208000c080b02c0c400c40d002d403940145240111402c3c0a84242c844441c08070307002c640b1883c0140c80210b003001ca0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 296472877 1250 296471627 296471683
    0x4061d0906040c120c02010902011116050d0c080307030f08181e030705060f1603180f0602070f0303063807021f030204090c05030610030506060714030904050603 71
    0x20030304050b0f06280580402c5003001030003003140d03040314820006035119000041503680c09203011041c07040d100d01404180b0401c400ca0500084644107c501400c031600d158400c4c44100300602006141010a50b90780d1005894020170392100c0c1802100444d51850101d1907201c54210584050344d01c1174000c0c01c10b0b5031480703c0c05c0c0c6548000450140c0901c42042103500041c001e11005009149000104082d0705080100c054804c014442100070113281c801e130601c81c03030036003070041002c981c01c089803044507101030a064010f0302c5210b001400c9010080303503d508065060b84144222011558502e900c0312502e180703105c4416030302103c0d0480850701030404000041107030040401c4c2c1c1c030041c040d00100e0940c0200b08034251a241590020039404581081800e10f24052005040e81c14906145103250807130001c0d003190001d500768010180e80f10005407864403940c044449581d01301c42c0c09214144880143c1e541e0358401140340340240c2c00d04010504a08000440120200e1418982107044403030344 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 296474127 1250 296472877 296472881
    0x801030620040306060503010513050a030e0d140c0a1d0c0f12090d03060510050318030409060803070203070503120f2104060b1008070507231204061d090604 69
    0x7045036810611481c1001071020402000b80700451080c980032500c0c03460f2104050844800400300414070140d4048407000810120381e51b070005c6d6146c100b00c04500505404259102c408aa00804013060b041d1002c1700d03c0d5002580204000d4112440380001d40c07102007120a501201c1d0103801c21000b414040b9202036056001341c24030004104c091820845820040c00404c0c0050b18030300038540201d00036840c195498007603d80600b000740c80e000140c05600000421521006080c541c1391301c412071602d003198406000f224014090980144135040e219190503490350f1201201728482d02c109ca0000600d0704001c240e40c0050b070035190030307141840a181e0f580c0034581d0104d85120300d1028055116800700e015071074554010390040c0b1000681c81c02c81743c1840b444040300e4a0490900241d1400c200d00700f42d000c070464815540c8190328580700b9010510401c0442070501d0303c12594002d10780c00840031000d41c00684100c3c0d04aa407101c9030000283c54182641c540b029980d600b00340000c0014266080072b0b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 296475377 1250 296474127 296474141
    0x3901050702040b03030301181113030206032e0618060912031701060c05010b0411090f04060b0f0c16121e140f0f0115120302030d021c1b08010306 64
    0xb40c0302081015144001038190350090f000800c0c000030310308460900340103501c03800d0720202d049442e580c03038441c01031324120003043e091100078032800b4000001410031741c2ca25503422107a46529a020005d24600c20300c0c7c2540a964066600090400f0014216107940c01c80254100d0340a038441c030341c0045c1050484071000410750b409030144800c100c202a2010400905103008000940d01d600d000e00c42c034a0010300356034645402e107108504254000d4043c4040c102120501c0c0e8080710038000c0c030721000000c1005440180d202500340100803441c800400382c00f10040400b0307011385050300c02000d0f6441009a00685e54000c90882c1d81000072590001000c070b802505044600002d22641d4a40c159a00b418400d00c804070200750360480a589800d44d0710400142c00d614a0360030003440710078043e00c1c04d51103440715841012040354082c9400002d050080c02142e05500d51040c00b50755589148912000b54941401d103031480f42d180400d6449074446091030140c034072046648480050f403031503d90601500746 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 296476627 1250 296475377 296475379
    0x10c02031c05031b09011d13020315010306060212030103060507030e0109060e0d030b0121020702100c02030601060507050d08100503031201090510032f060a023901050702 75
    0x44a4510284200c8500880401c031556916940c0d0b07894060710008215941000044c0488424890604103130b030070a0400d40500c40406081c02050208000505824503515084d50402d20002c14401004030480400424100031380b420300c149955004100e03590b411044000f000104140010300c000b681c2c5c5e8109a030800024034000c110554100700d034a085031421403046803001d6071101d030600c0c82441804840400856420100401d054400029004c1018101c4000d44108180d80d03d00301a861681541d0f165500a045403a40001c1384501400c041e002c14400d178800d2040c00000a4601c0c4100c044a00050380507020b0121700710506800c2c1e506d08400341c0450101002c82ca40415692810409480f8000c0c0243c4170203100c0d450318a84504490703020384901d4441d400d041081c000f01703141085228074980c690801d04103810000c1d0380d210100801840f225032054001a48001060340040d0000000c84075140d03000b07085590044604401c4040c50303502e991440300a9040c1842d41c0102c020701a0280 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 296477877 1250 296476627 296476633
    0x30601050d06170601450c11060130061407020307060506091e0a020405060301030632011e0302030601030302071a090102060408030a0906090b150102160302010c0203 73
    0x200c24004010b448890b00000d000e08468804014001010800c4500510605181da90036000c01c00c014007480d5418010f404510803260403401a420041c4143c00b0f60b548544d4041010420342800200040105c4500510300d01c01c90001291525904810140480c419452042a98201c0307000350041c2c62003030015284a5505c4101c84411800e04503030740d100d1540b9601075590b507240c2e07141c60310403100040d1942e40198a500304103c00c10004900c06c0c103e480380c181c20010f850350fa07091040003034840c0b40c0146400034404800041080803031b400c4001010820019003442200740e400c655941000d000500c1118850100100500500e004140c40d0300c40c3c2581032001c585440c1d0700400d01e800b2003a8022001a840003408100850b003c20440050740030160342c0342d1400c0050b0780000d5843c4d9000e000034203000400404a12118400e50150162030703848030040c04044480d040c40311040000303e942191075011100302542d00d40c400b01e1558541c1d44c401c11100b10782821074004442c1284c4803d0100c0c1c00d48 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 296479127 1250 296477877 296477887
    0x90a0b0d1506180909110409060509070602211c0608010c0909050709150306030615050108090610060e0a080a030c060f0b060715021209010b010e0103110901080907120507031a010308030a0203060105 87
    0xa107d81c01185162402100c0104403030900c410150b2800e6001d80c0300310110341100012907803441521041503240300740c0c004c034940c40d5020001d00265505100d2030070103065191134000a04020190090910707030045854032240c1551300c0c0c1c80305050354070843e0988002100da000074000142c284150401411003403070006206501c0b5501c481c00c507030200c0008403601420005c1005a076078405465540700900f100078200782e0900490601c403401150044000348882c1d0003c030300060300c0e02400d50004082100071140480624100070b0034015a0310010b0b16142d040c4001d2101441045c09281180070f0060003c500c1d00031107413540100e080000071801c940507002c000c04955001e510300001e00031102600002041051070001510100740d040c030041c103240c1418604040c00c14814152095203000782404401507461814035070506000f0342040c0f1000c4415400c1a050000004070782d01520720440681c90b1800f100807840302045070074800100980020800603458160b2500a03640014040c1400e42c100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 296480377 1250 296479127 296479129
    0x813030201020c01020708040302040b0a05031c020c280b0a020c0d0203121219110301030b040302120a020d022407050d11070f060f0b09060105090a0b0d150618090911 73
    0x2a1b8028407007514810004a014030541c6054812401030903401c035108024507150002080d161050440d40c1c00c04403c811420165541c004d004a000740d03039004004106800040d02d00300c405c3c540070b410b980204401c2c03400100e00380d614001118462040c07034004111420b084030811070100d40312042242c160003030002007485401881c001e4442e25005011569031031401c004603440c2c2500205200f45c031603040c0118025000000c800b03c90540360048004182da070f6840c24240e10705520426165814040010b1100d03440782d01058a0405030103d600b550400035002480c2400e42d90030341141003403607035440003081007140500002c00e440c060380103001c02c040c0f1444955501c90b07080700f5815a41040827641c05020003500f40304502c051a042032080098003038185c040781d00d95500400e0707141407010009420703031603940305c0f00d0100c0141050802550f1704c0120400c0240903000c80c4050200c0a0350190003c9099402042d16083d82c4000140c48948940b5010980010340706621050352840c1449040f0151 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 296481627 1250 296480377 296480381
    0xf060d110d06050306070906200a350301030c06031d010905011b030509061501030f1b09060801180b04020903030a0206060f030d081807050907020705180105010813030201020c01 78
    0x5540300840d00158203850f080c00c0c0340c10241c0082c102400c00c080d121003400000c0c0c0042030710700d504061041001036034400e61303201407502b80c68840107003410080100c1541100e2800c4030500003601a0260a0001100b00703500a070b1600003804010420f444440040c00b072a0304c00d9000c10310380d80745104900e064410f04401242110a0640c0c20307100359440320704c0e8400b141c0c0740c50340010445005103000c200b80d00c0c2203180c4545444c0c028001c1c5a10720425491405e10fa8403941140010f51404881000f146030494a000c81f100842c0010802042c1c0c0b0b80400034400b40902003103812a07061080c1c1e00b503c116003da04c0700003003542d4240345a00c00d600303000c83c00951f20104042c085018058000b03000c40e05205c0c04010282e00d00101c070714070961000c4542c551460b800642c0b550000c0402e40500d003000f10003811b840c1040340340d410bc0c1e40c1000510381000346255000825604a0341d003aa40e00c60709507101107603034030160801d0244a001c1001000411540c090b0000240610340c040d2000500704030300d032101103003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 296482877 1250 296481627 296481637
    0xe0318010912080d140c0901030c090f0e0114060a080103060506210c0a1e0909060b040903050304060c0203120c070c1a0405040b03010203100501182105010b0d020f060d11 75
    0x8500202044d078207140c0c6401d100d540e1603540307940b00304543e51828000c151102d11890104504141e1100003030740701c0c86d00a800c02d1029100515400c40300e00c1d140e02190070595000d104507950080c0c10081448907040c40d0b01290300e141c1310b032fa603040456030a60311800003078034000c1c1145030800303405400d0b405242c100c4041c22200542042c090002141b2a00420112400c160010b44000044c480001c49102c805080c58080720010039011585c0760715800c0440040010703051094000d820240b00034105030f8000029807266110740405c02c0f45080c4101c040b42d40340142e0207000303805450600464035038001c1c10003826806110382c58803005561503c101e40c0044051a18180c441c10b4003007021f00c0140703014002d2921580c070550007181940340050001d007564205219050510548180b04200c101480d001000a454a5031031803a03074502860760104001d032510703425110b6501e031041d140242c1ca0704401410145400421802ca0300558908001066025000c070f920040d6440192500e0168154090a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 296484127 1250 296482877 296482883
    0x8060904141204080f0601051011030702032b0302070f030e031e28050705040b130905030301031119050f0109170703030206092e091b0503010b0102010e0318010912 72
    0xf610345240480191811642e0511103469070070a000510490300c0300e5080c1c8206010718503004080c40d010200c40c1e4114400d905010350940120b00b000507999141070f20100340141e588006050303070181200110f00300d000d544002000103d5041e14080407900c5860100043c0000500783e0f030070407400c14800802c0400b10055a180d0b030700074030b880b04260301000440e1603010b003071110f146600000c0c0d9070350b1949074036050280510540d030351914140c0f50f40351803c1901c00c81007140c90400c10210182400c0b6a26002484101c4034100c42c1080d10015040400c20310a843d2543c0b4180d60320541401c00708056030858001d05410050303040c00018541c644641501e6040f00395401070880381e0700f5030070001d080c0748004000c44000e40c03001d202043e401c24074544e80c541e1821201d1400e2090040a20701e2800703080512406081420240c00c451824441c0180e40c2085510444c004c00101a105005a0036119900c4000c50300303800c140310310622803005410403811a101450907c0c052a00d42111510001d2114010b0b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 296485377 1250 296484127 296484163
    0x170406020307020f041103090c041b0c0b07091509080610060509090a0f061805060f10081b0c0f010f0605011710150203070506100e06040f200d0605060306010806090414 74
    0x31101d812b0034480d008880541a0740070160078220384025103da50b0141005003501c070b80e0000079800601c1240810094200810092028400004000e02d010031038060540c6a000e070002040ba00e8941110351411152107850306400c106125040190a01006003c00c0c840341e101c03140a240c4030000c1c800e4001030403d226070200780010600c040310449000400050040c07608451118107540c1e0314502d0004024145055002540c44c0c0c2c01013004621180801c024404d030124a08071086400b1540200e0100900d008020310620311180900b50b9129100e500c1c0850070034001030030404414035501c2c0c1d201c5105410801e209a50700c05040b042004403a030440180c10100c0d4000c10854280102500500c005001290540c105002041012405803401d0f220302d50350b071b0100d0011803503904900d141d00c1d03890781c0440682240042c1000c00da40103130081945146801004a02c07454000c0c25a4090071040e5101c0308035036914024000d00640181c8241c4584031282030441c0050300070002050090100e03021 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 296486627 1250 296485377 296485393
    0x815030a05100c1d090103140c03030313150606050a0f051605071e051503042a0614030c040302042d140a0c0f1d1507170406020307020f04110309 64
    0x3009110781c0301600d03015080c0d0000440513400390340d1a15401c3c19030b50403500c1c4290420200080a00d0302e2400c0d03e40f10f415001c040200802ea1280e0204070340e915015103450fa082030005030207402107480a0252070007040e418410340e0202c2d8450a0990080c400c5800d006182c062900d03e0440359000d103c0081780c00d0303400b00006004843c1c4004000c15040f0090640444150038a80040c1c10b10394560003001c06032002000050a103c2010148122000346103d8421039007100f131044034410310a03005010201d18000c052606800c85602201e20805a50106034103040c115400c10000c0e0501c0582c83c0e2901d07005200302004102d203903030410181c5400d402700151000846000d0708404800608400c51586890f0300680342c660401c00c0d10200302c0440c6010a000402110786000700c00c0186140360b040b52500c550031101061b4580102550380c09030780154000d820194102000d441a402850011780051100d1001400c0c0752042c020705500007840420300c00422080c9280b40d400448a01d10300d9071005007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 296487877 1250 296486627 296486651
    0xb030106110a03080c070f0f1109061230040b030412050a021b040e0102041e0806011d0702100905030a0306080c15030c09041b02011b0815030a0510 65
    0x4031648286081c0141100d21800c0c0c4020b00701e101c00400030050b0060000b0040100200d40c0020302c4841c2d4012180c0d1010781c1582403014018940c211850f005411070000304416180c003c0e201d4500e0034641004110268000c2041156501d60a401d42048100b407000d800c28a2200000f92010700803030341d001504c80c50681003007800e0030304040c0013405101003003050002c0304d40d010a080ba403034a598003900c140c151f02400070400510424841244551020402290880044c80b000b51542c0c031050310805d00d907840c4c803189500c030034080c03042c4624610100105511409c191a41c0c80c3e001a40d4019100b00f002e0f954228010350351469811036040d08000f6000ea10070760188120b801034600d410003441402401400300e0745112071940034131a41c00d000f02c001188042400100c1d001404050402d2281c1c1c1c042032072080050201140c0c00016500307183c1c0c2c0911090158042c041c0e40c00c800c1c0c1d50380042e92564007404101c140c544c08907981500405d514000850410071181d00004081d080014907544c01003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 296489127 1250 296487877 296487887
    0x303140d090b0702190305030630100501050303090a0501111c2c1c05120706020309120a0203030703050604200301090c0c020a0b0a0207271803020615190b030106 71
    0x10b01c86514803045c1500b801d000c00d0348502a2503004c04180c41d841d603c07140d800101b00704c150f0001d84034401e00c54102d54000c0d40210115103104040c00c807410901a507603c0d0710401d0789030701950032020b07003000d8552010007a541c42030400c48111440901074400703a805908942d00080720700303d82e50022405d03101d0b003082041c40c8000380b6121004400e042282410390030b4001342074810b8400d1001020400c1c50780b050b051100c280300850314101c0705245c42d59a141d06103400300c080e400403110703c0c1090140d05000d80e0b144442d0800c40e022841641d014502d50350b601902a402000041c2c01260000c2d80c4003a2480310110700d442680301d40c0d688000040c0c42e5031510881340152440c2500d04006c21503040107a1006031210203805e400d480d2070441194680400320000c9192201c1c0307a108408195198280a190400741030f803d10405174810428031404650f4426240110700c035940060045c0c1c4140002821254a4140c940d00f42c003004246600074261445004024070264100b0741602900200400c0019001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 296490377 1250 296489127 296489143
    0x618100311010201230c1c0b100c1502070602090d03080f01081b04020f0c030d06050a050901060e0d03020102160302060f2d0c0702040e010509010b040608070303140d090b0702 77
    0xd03c000e103c0022407003400ba034038101003074540c0f15214828000c13a24070b140d104d058a0f50300e0340c2500340c0c0b408800c00000c074201070400d210078103001d40321816801591070b01c170f50302000f4074a81126050700c1000340c200c00c54009501c44401560354a5007480b241049699226003c50b00c035000f035644400500300090041d81c52141a8400001d82d0b01c00c01010071500840140904505802c0700c005884544d82603440c1501d11aa0203201c44500001500c20340b003e201d41e0180c026180151010f002c0310391504180000202c0070301643d408200381c0003201c0042c2c81c004100c1e90255201e8400036040c440c6600304130005001010702100560003c40c2005011100451000d17808624882004040b4611034080c810040d2060b14075100d000380d080000c0c1d00180d0441c101d91030b1070740c060001c00c60b40c031500042600900f01524221119400c000c0c4020007441d02d4091101980c2201c80034040032455035605907070354000e4040700b0300d0301c8005000c81405003500f441452040c5018055001107490501c00003800c0000c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 296491627 1250 296490377 296490379
    0x607060c090902090310150f1503060801050c0f0a0908010501061215030807020907020f1009121d010e1318030f0203030c0405010e0f040507090f050406080c01080618100311 76
    0x41132241404590b400299401907849040c40041c3d4065064082c501715041504261043d40e5020800a041c1300c075135126401d00b240940e401c03c859500e850071301d8241c80041d1010218100c05004241c1400c018000402002003123040048031703281c0d07a8600341c1c03c3d40c8090b44180d02103080a0a012114440b03800390f181400308601845225904542c0c4003540c40c003440c800a801141d109000074010b43c0200021442c0e045c0d43c0d01185c3d519100ea50800020b04080030048840340f40140190341c50038000d400b4a5a000c9100001084080e8040c004507035440703410050580c044038410040e2299565441010b941c3c0f0111044007012601505004e46000380c00c0d001c1c0002c5500c10002c0081040d4050296810b40b0000d28202c104403442c000040c5002c17034020b2009500514000500c00e107142c0282c03000c7c1c102c4042601250301555644100000c0310380702e1049841c00e4010000740e00d000d40c406c5501c0c582c0305000410110703010300580c20f0312075405811100074404021081d418418007440354800c0c80c501c0c0b0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 296492877 1250 296491627 296491631
    0x2011103091506180903091f0c0206130504090501020c0d0f050d18140a0b15030616180b0c01112a030f0d060e01061103040b03060307050607060c0909 66
    0xd0044080d5a10500b060b54001035a480e640030400955510403c207000520840744070301a418607110454903030780190040c511a040c0c4692400e503c82e070340391004140702495201c1c00c942140c141c0034030025070f0059003400c507002d412142c04a140d550728802d41c210b0b20300a40c00103172262500d140d1185032022201c01c00040c000202e08605403130360b02404555034400303410030100d02c1c2c54040e10306480140b24000d0080c80b50400c0d50070390040040c000780030f07029603004680c1c0e000c8176100c3c03d4481c070b40c0540d403140d5250180c00400018081649500700340c81c80310101d2030315807083c44134454050400b614070b4104c04030103580080c0f00071050001f4003501c4100d41e2009191ba203402001f42007255031b03200135509000b140528004100d020348044c420784039480411101140e50315549101f80006024a014082c1010003034000481c00501c03c412a00706002994015483e09091041d13146035508000c1805505100d90f88020440d0348422015020403485070002150402c0c482c01c0203049502e468005c820b02da8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 296494127 1250 296492877 296492881
    0x609080307060c020c09011e0608011a03041b0e010801060501030507050d09030c0c0f031401053616091d0d1209051506130b0a05060f072102011103 65
    0x116000c401c840e4501d0303002d80001003810003102d05a003000c8000004950295058000045440c00c250302d50403514602e5411405641c2c8400e000e0328513a200703026072581d01489d440ca5800c0c0005079402140c0040c0240074900303130405540c270002c01e66180d5030446a40707042400c00400500d94240594400741a00342420300140c501240010080e019040c180180756071100d00d9801490f0240f007505e2003a5030880a0211465224200e07910140789502c006c81c0c0c151490700e0840005241846594016010b030021030034a00e0500300149078441124032440700720314090000340c1d5940000c004c0004124921010013110f5482c1441180450308007089900304220281c504111481001c207000d002500207043c00180074a0400c103642c01020000c40040051144030b0850801602803180d0398840c0e00200c4084105005003d20402510080c2604682096a00d64144154a4244041d0a003401d0000c5010705040458440521000750300040b6000040d5201400207815828000c4035114070b05102e03128558 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 296495377 1250 296494127 296494139
    0x1c060e06340e0d2f0d060c05041706010f060509031005070302041703070c0617040204020702010e0d11100203040608061915030606081e0402010807020c04091b0609 72
    0x12480059410650a09044964a64040c07802c00b008000054502203c10045150009904400b00000d02000c0210300900c48020064035000da0681e001604003550404940d5545000d41000b11480c003e2000038040030a100045141c040d00c0d800c3c0d06802030a00354501020000300d80d245401c0f4804004007004040d5590702c00141d03000174010200c00008441d61800c0f0110024010350708002401c8648002d44140702302d00002500d440c9004d0420000d0050351154252100031100360042071100d5190001805860181c2c046e22113640103041ca60080c50011300000ca032180d142e2400c82e8507000500c0c082c0350f1030400e00e20801540146000440c9080c2c20000c0c05071080030b0003000103200300c03004041012030908280488000f04450300803908000380e03146020780581510301800c40010a1000003407214071540200388088001400380b1960307600c5179001155190801000c41040d031090825004080d12144590350119008006200001058120030b002141065000c41d0401c80320710400d00c00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 296496627 1250 296495377 296495431
    0x8010302190b090f03190302030d060e09070b210103120e03030f040504110409020a02030a0e03010b0f04020a0c080406030c020c040603020a06080405250801230a09021c060e06 77
    0xe0f40d00f007121082c03030240060b00000e14251941c0c8140c0140f0804044040400d0f03000806400c40d5400200144045500d0b50040001c0f060102e401000d6640b00364010024841c000004252800f412500001810031401c144030898600b07900071191440e10a101000940d03102c074417216042c0b011005903192044c00c26500c807403401135004482c4200e54518a1440c18002c0380c040390b00074411a9425921801200030103512078100710780c2c050100340b40703091120315483d0611403d9460311009103408180007007041848000d420030b01d18681030113400c1d400c5402081c02e00025100a2880382e0b40466420f107a018000d0070822085041030259081060600040c4d07113454241081d03502e146060700306070381c0e1414054900754154065030040d500c0bd480c0c0010501503080c41d4801e8804a100074005640303800e2b00740a1100303103c1040700da40b1034998086855401960418880240000d02c00540c502e440c110301c0515803050b5200f2521680d80b0490301002090902034182d1085007110035a404a0030300b050714003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 296497877 1250 296496627 296496637
    0x5070614070c1e0b060f030c04051f0807050312030a02130306021908100b07080f03040b04020a0501020a0c0905070c0b0a050708090706050405040f1d0607080c0901140a0c0506040308010302190b 85
    0xc860086d903020407500380c40c10040e094000d44001c5c4280414201500140e00d507501849004020030030100c40454080741c009017101c01c40d4409001409000401100c440040d00003030050041035400b00300d103015550340450038001440c0100001a83c605203001300c1c03907142800c401c00005205182080001020034007034804104c8604d21011f03656607801e80b624030358500c070ba042d511818500c04800e000c1848200c00703040d80725900c02e0b2911a041502ca0b030041ea0303a01203548000780300c2d403000c80080c03008200380e4001c1600201541041e50140580fa543c0610004d4200c0d150f012040e91001001080f560018a06820410301c4018083d041d05240d030003040c500c22401014083d540711011b80d80c0b03441096002800401d290080041682d080140d11074540c0425202c0c1c1c00003a604002090303500c0800002c07902e00440c142c6516800190390700207075805030000081c000030b010900340c003640030035820302c03955102c0d51081da51680c0d10341c103500c10820080d4104030b903015218402103041c04141c0054041324 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 296499127 1250 296497877 296497879
    0xd05150a0b0a0b0a0903021801060311071e030e130b0a1203090b0702011709010504020f01020102041412100c020a030f0912140c0a1404060515090105070614070c1e0b06 74
    0x26980c1c66011340c090701d6a04203a803000f074020200c01006c5000482030540c080c1a43c54554052105030360110386441207000f0f45001030040964400900c586190541d10506c82510078103007500c0d19a103080019040c441b9401c1101c000e0341d244c6644c1c071020301d030464006000c0c020800000240707131001d40b4010f00f0403406000303050740000c0010714041503a0280c02542104d40e0301001007012031404800d464080d0005603002c0380a81c4882c02c40341c07407641c0107009540035143e40307a80c82007680001e10304000500740c40c0b5490a0441c0500c9004001c0540d040c0102995550150014080200c2d00e10b001006403841401c1101000072401e42480310301c02c00b41c403c0052039003082d5031041d9641012051801c050100402d035921803000d240001e24140c6071560301c040b02c2c0d400c413010000d059540e414094002c00e001c6e010303900389400b0480810b0341d42c000c00142032003034010400007072800340c41910f0180c12201680c0701c0f00800c200783c800d03804000c04102140881262000c0c107141d080310982d22249406000381c005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 296500377 1250 296499127 296499149
    0x1103070c080a11030a0504030b13150207020d050304090507020d0206010305070e1807060806190b0d0203090a0b01120b1806010501030b01110a140c09161d0d05150a0b0a 74
    0x16070b4503600c503a481801000200d815a5910b100c0e15001500d03d0380184801c58a11080e000000d031000404d040c60842c141d041002c0c010030615080c0c1c01c000951180d101241c1c005994592003010a90800140c00600044800001c440c20081c9010f468103842540050442d441000148005800400c00c18101c85a00c1070203403164851080600c00c0c904040000d203800e100e200000101103910000c4c003400b541c400d9071a0960141d0390b1a0003c0107020038051610700c400d04100d440703903411050f401540e2060b140b0301039039002e0006a480703000858080c3c0c022440041304290302c030280a0050f640d282c1049450090390000d810920845840d00c2c01485000d051660712103024119902500440e11030018000540d031580900e40761854680b0100f440c0003d4501c1440d018440d5420201031042c0980c041c1a00e40441c0b8482c3c00d000c403802013842009081030b000c4242c07124401d4035510078408004e48a00e000c0c0c0f540042528021404100c010003800046081003280340c400d4440c2c0c2002d101b5181c1910300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 296501627 1250 296500377 296500387
    0x6150901030b1f031a0301091110030207080c0609060c0304122102040f0305010b010e180907030c120506060102061306090809030307081e0a051204061b02030702041103070c08 77
    0x3c440c1885aa0381203c240218000070000c41e5055020640841313111402c00c0107941c12209240c225241c2c10350092950058042d21076440c60030f4040740740d0074a0589405464402c41d96a2400103030030a079803030500f9138850f00a01c400c52500748405070340a1001c1b81442e08510345500d81c6540031140440040500c0050b02603100c000101c1d040001340705000005c250341c2d83e5075070789200510040700d1000f5aa154070b09540403030903600c5909044040c54000300995060344450703c02c001103680c040e00281d030700e02c6142800800254041000e400504074555040750307c1c0414200103042600042003c1e0464000d6410400c902000001c0c0c004a6500018002204141c42c54100c005100d264490707945440003003a00e6080040c084c0041138a98101c03040e8102c00240c442c940b100c3d60080d400900003140d01403060f0755255188542d03a0303a0241c015440429500c140c0c0c408074424101c02c0340d51600507000040c0711019030070180100c5083d00d000c96045480c524100800404180d44090020a6851300141c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 296502877 1250 296501627 296501629
    0x10e0f010c0204090b0106020a11100519090f0b2206021207020a03020312130621090303141f060e090c0a0c0503040b030106030f20130b0414040506150901030b 70
    0x8003120f0b40d2507005030030170141e58450380060341d214140041241c2c004a103240b8000142410f0a0045101c4000d81f07505041880c3c0f88900103003855040724080820499510004180241543c003100030051002c105941e141c07036102e00000c44044003032140e031505001008004503940001d20045415400c20000e4903003100b4400104031800540c0069810300c61000840c02c138150800003412018601d980d807203507072961804103480c1b411801700c0e0683c14541300c03103034850520f0580e0085002e031071292900041101081c0000f1110080a640440b000c03000b520600300c1c02d04003600450027034103584c140700c20440c0035a00002d400c45001442e03151403050210303030000c2c0715014500300c1034101d5120041d242c40740d0301c500310841150800d1113000d000a0404e0720b0011402c940340300300c0ea2001d181d814039000101ca2032000d0500c6600007040c100c10b200c1100d1001868000840140000d09035032040031411013040010841981c6016044902c150300b0004170f00d40504070402110b550b10700c00c0c20045841406e000c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 296504127 1250 296502877 296502881
    0x130203070908030c071410020d050702040f02121803070b1503030408030d090302060a0903020d0f050d0c0e03010c020c2209060c08040b010b04060c080c0708030403080403030e010e0f010c0204 84
    0x580034800c588800f0454060034000810303000291903822402105240c5941d08103c8115050002d040158100608409c075aa101d48003c00c0601d0018001080e01410b4041d54022607015000e04920300075010305100c8102001086441506042002035040911766200c5403041880a4240c0701c03980c00e49008000c0c2070b1000d000750ba0090052105076600e5031040c4034050040c2500c03010440050003800d00181c50303000a48aa0005240c16a00410307612400d07050648808603000b500d0790a0100030b10001480301c0f06406070300c0c072a9216588030071300c1001d94400e241c00d40300342c11a05419500890505030041d1260708007001ca41d510040d405685203a401032820007030061000150070785003003014660003241c0102c800c03801240300d03030560348560303070b86200c10000d5014900400d000111102220404a00940f000c1c2c2400c8000f401a00c90303941ea41c00106180d0b600c41c0e0710880322010f01007010010325402007182c004009080c2400502803041d8400201d038414100016814010070000150941d1115 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 296505377 1250 296504127 296504129
    0xc020c0d020a0e24030303070c0201030c270801110301300803070521090d0e0a05090406090302070b1318140a060801110f04290307050306010f0e1302030709 69
    0x44200c0c40a642440d20a0240c50715801c0c0c0c0030504c201e06080403003014200081168403400040c0e0b41d000303441103190700441c00781c003d8680810400009810f03003183d201000210a007139120030000700440e103152490880c20b440a10712154511001031004000d10b2000e9080c40c20980c00c05c0480b445ea2694400c0010201c1230282c0000e03041ca030020003089015a0070030f00a09118011800407070082901c000c00b0607a00400721001c4616400801c000c1d0112402221800551031006042070341042c0c599022980f07010045400741e0341503442d40004401e01d9010b00c0007001a0040b07850140c60000035000503800300b0420f00c209898681d003000100d0303840c3e02581c400da08040000a800c00107041981c6064081d206a000720302c225440c0045014808010504980400c501840c0c444d05203407a200b440c0715808441c1c410705c07a21215107031061240011580042d8454030141d05d03265160f06188000414007000482c40314244070781e01c0e148160340c1c5daa06800b044c855000070400350b925a580d42040b1607031649 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 296506627 1250 296505377 296505389
    0x1050d050109050403090e070e0609040b0d06020904060f122904030210050c04060c02100c0b04060212060a0b030f15060a021b041e0e0c060a0e0f03010c020c0d020a 72
    0x5040004110400c02d50400c0f030042e4001d981300c0e001a620340101170101e44040c0d640d100803039080c004001290915102030140705100810010f401512000030030304c4d1240f1081d08079040c650001f5400c0076803605125020182c0707500040400d00501f400800b400b03601c1000406444a0540e84040100c44806d401d03050003080181c1c15080c0310708203450b02a54440a10440b1a2058100300c0000c80451070401914221070300d5a5804a61582d65001c1c88460921a5039040812001402c0140461881d03070f5484c0c010b610074200140c1e901402c1c24481c2c0740701c20103001107119000303902c01089440445001c0d2904403d41340503146041d1107a40074150031004400c0001d03044000480e9000c40340380c02003410203000740ca11a64403d5005441d041200b194001510fa1142218a406404042405500c0001138a050500300e500301c0c3e04020005150b904001c003440b0003e07444095001ca40d0401448608a5607019070013400303003a03101c0c900603403945066a00c0314002e400c0703c0c100c0015981c13803225003401000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 296507877 1250 296506627 296506631
    0x211e0507030c27020306030a080708041a12010e011a0a030b0a060903063e0f040e0402010f1403010510120509030415140a0503040f02210d052701050d 66
    0x56a0701550312031140900a000a0f480c0b64141e040d5895880d000320382c820fa8005029000c114000e585180207030b0490001580e5443c0d0910020418005050854841c40803182d00b213a142d1000d41c109040380c2d04160401d503070012084004103c0c01c8041052205850070100c8059180e0b035000b20200e0017450304901d9941d0121484c1000035103103401807040d0059a000d00028413049018410103803c020b40b0081044908840c046005041c0d42084160300150b201c256220307107480348081240c10581c11036041112251921400e22003150703002540410b00300b5aa0912100d80162401c5041c6203000c14801c050003a90801100707a0094410002050b4055030188100b00302d081500c9038503501d0700280907005515804080c500034442c01030034000b064a20703c92030719141060703640c1c0448160708082d00840c0c15080005035000142c2c0e840c01103001c00d00c100060740d00d0361414200300914020707445101500780681008502049054160b01800d1305101038400000d111001c001218a44501c15511035228 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 296509127 1250 296507877 296507879
    0x5090c030109211b080f160501020a09050906010801051504030506090303041217041b05030a0506090607030e07090c05070f140705040c080a0c0203040b0703020601211e0507030c 78
    0x110801000c1400e000011004010341006410b48241003004070355240c84c1d10503040741e40040c000ea0010150006060030550400f4240c40303200e040440122021140c0303940205400c2c01d604d90203030304840102821036208071f0a040140018194500600600e40168021006941404d44101c21a002980d1117411160f070b6282c840130003a1a9081910f0840ea50009020003020240c4141c0c1c00503000d509044200e42582c03625912012070040c0c40003220100520480000b03001c0ea0144445070702d40d40a107002d0032583c078007040079504040c80180818103051401450b0300e0181c00008003042501d05020340007448640b0020151003d00070382d42c00030440701201148004100c00a01140499146001210309041e110003c000c25107500000c04000180044005480712043e5004100005010b00607a49020388501214030303e64001c1030143c0c05a400700d401042007250340e4020110b00301500e404070000e4000707580c50008510300420341c050142c100d003400b08140141403100300c00455010482c500300d1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 296510377 1250 296509127 296509133
    0x20f0d030504030213020702061b0111030403051c0e030a0c08090a03050f101406100908121b01060e0f07090f0e0412020d0918091b08100209010e010305090c030109 72
    0x90b42c02404120f000d07484400c42c4040030b010f00c1c001e41d8001640200400c0c1065060102044000d0310028103244a640f50004112035100a00081d4004c90003a0303595661480a40007aa0b8000010640c15601e04e140025113034003660f010050390300e182107503e084000c104a0b41004031003030003041c43c942e500441402c0700104000f00002c81650390b1440c081030381c8a805591030980304807541d2031092200001da100001e516031900c0084003104140c10f0a000110380d46580303038689020402e81e003004840300d0019030303006403850f056080021100030000a0044a0908110380503121020f0071408603081d51401044000b030095401e81c0140509410411100e86e54004054980700c09980540349443d0002040c50740a20118501141109a45035104104d04c1c25401e61140745101585481d015569920080003c0303035072088003050420388421000d12424048060309150410020150303c6104001d039070f0300b50360481c4d00380c04090b8090078000350a5a842005606080c07003d00e1056041d46840085410 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 296511627 1250 296510377 296510387
    0x1081011091903140102120606090301021c0204050414060a0b0f0d09050c180906070e04020d050a0b01090506190c020a08010f090c0b0a090302040b01020a05070e040b070504060516020f0d03 83
    0x80340d004140d11490310340c141300190308030321039600b050701c1d400071900006040d400d00034000e22040c44042d00040c500075001c0000154800d03480040280690001400c04c207a1070076009214482c10825605940381c240b000000d0420b51891040f40d00b041d4000c900780c10040e0003c8155000c8010030213082c80503400c00d10300f442c0c8a03681511a00c2c49422544035902e0005441ba215a00c900d51040040506071038145081e60054a424452a405502007107100030014a5000f070b140101e82c15407010900d00c501c07200260070010240c000354004ca50500020000662155840041209900b4000e036004c00a002240a20010f500414015800e020b030b04142918940c2c495610580955003180480d0b8071008615158481c14a00b00002001d40c442803015107441d5004421000f0305004683c00140c481c0d0381c0c00e0500c58160300c98011440304d007042009000c420811a0740c403030300b140b5102d0f140505046c0c02411902941c1215074011240a021500715200d13188880140310000b803180d4441c521070715000f00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 296512877 1250 296511627 296511629
    0x1030602030405070f0b0904090c120c0311010509060a0f09030f110a0504020406020304060522081e0703030801030b0711012d0513031107180c02060708010810110919 73
    0x83c580b0500030b00060000e02044420140c0e0882124140740c03e41c0d1808210180a90180554200c0c24200303000031020450801018034501c10020010114503500300f45448041d05940c250500c5810840384200340c1d40c840c112509101c1505000203920000c00c01210741a0181d000181441200325440007800b1b50040d903160040f41c204c82900c501901c4009000c00d0380194410603001d640b043c031060084074080c0c0b01500c3c010250040c08e400c10900d6501a04c9030740c1d05540202ca041d0807400d05100c4418403d4048031038824a5001040c40c1380c03030359600a01100c41440041c01c11280c101c081654644904803149031745c1c40c000020321460100d1048440d42c403034400c206000f0110b0240118400b40d04d1401460f00c42c8030700300d9080700c0300c00307403030b2419100b800d00c0b001c0786a07030b40c01014808128646c0b03650480420702100700e000151001d078008041c0c600315028005209200d0a0001003143c0300300000d11605000703507808041f501c401c1065820842c6d004140240da480190754818100c8d41300070548500c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 296514127 1250 296512877 296512883
    0x150621010507051215030d1d150310060309080912030c06251d0913240f0203040b070e0103150b130f230a08011a0f0102070e040227010306020304 64
    0x148640345d0300c100128204078081015095000345a01c02c0c1142e010300340d20f00d0201401c40c040c07031020762140006440103113030240c010b440100c04400d11040e910044480386c060041c900302000390302c130325482e1103410340903071a0b850748900d42c1480c0e020004d0605201b0340307500c2e4a484046419a0400c000104c0c240500c1d05514100812219440c0914078407461101920190100080d1641c01c1d9810505c64007402c0100f44141101d041440c010009a525504030030600c5c412501e502c40e0395043d0009401d030384442031100c001034014030912000c14044111140c104805092400c3c848032158016000341008840c00207070b18201020001d190f0200388010b001000146000103085511030580006480d003e010320020080b0310000c0042050801d208030659043c0100b1192002d0741c2c0f00c204609440c10318155071921003c012280b542401c0240214024080034000b038041a0b08107151804200001800030f84510010414001c0c3e4640e80c10110351507200d55a40010290f13124201030000c0c0d44144c40403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 296515377 1250 296514127 296514157
    0xe010b01020f160306050411030a06060603110f0d1518020735030717070309120203041503020d020d05161106060108010504020319020a030609050915062101050705 72
    0x9a203802c0040b076140c052aa69800c2118940e0075611282d005100050044500c552141c00e65030b0b41742d03020407035030510b1403040a011036490700781180101aa030322846a00403c140501550241050801c143c40c180c0030403002c001143c07080101c4102c50108a50f101e2200c5d403102850b60b11400d00300740c0041042900496488500ca82920b179801100790482c44020658800f074862444101410002540c00c442e81c0d20f032031f041b5910382c4420950058402e40d603240129036940d94000802c03c903440040410050750000d582814903285614220b0010840d000c0201a400245c0707800010f02c0740d06559240801a1042010749081a00c002100c801031140c035002c03900d1000c0d00e0072002e0f00060410721505040c0c0d9a030095034601424040070f50006000c44004140094807410300054038409424841d11075540030801a242c25440002c0b2000501224030540000200d140f2407052a840c02d07810182c265000604c404160b9810340d021a14585d01a056500700018040116403150152003003401700061 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 296516627 1250 296515377 296515393
    0x20c0a06180b03062d040f0605010216080d0f050f0a020d090b09060f0d0e010e030307030f02090a03080708070507240201090f062013030302011d2e0e010b0102 70
    0x120003080d000031500e89602074400c0144240740c91954509482010050300300705c8003012403c0000302a6090071641c0c1291607a9174030308004541e810806200800300900c00c01d02101d080904007038903524a0300c804014480010120070203240f18400704d13070044000004150301c0b1203001100944480001040100081444401103660b82210040b582d0082000b440240707450046d03031130200d4982003100300750b652070390f51100c41003130a1080c0170340344184540e007014640d03070701d40520003908071900d80341015481481800340000316110034004030b0980383c20915098440c900d600d8006642c0c851410001d00c1070003032010008010401da80341107074403442c0d1500c902030310050440c02c80c01c075050380001524000035001c140c4045481c0c2e510016040350f00945464585240e255241d40b1030b0b20841d28144950400e110810034180c0c20322501207000c1c0881440042c01240b00c00c5c00d9079420501c0e03403950401d403800d00518001a070400040d001006214010b100c03c000420300d085c004e02c04100c00030b016000fa240 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 296517877 1250 296516627 296516639
    0x60103050717010303080408190f081302010c0809062a010f09080915161b0806010308040e1906080f16050d06090212010908030a060b040f15020c0a0618 67
    0x541410101c401c600682c0181e203540c0b401c41d107100002d041034800381780811480f0381c000301c009000201411a40c6a0003035003034090300005c0050000824100041c03920f10f00c0800103131b920014081362242c04c005160384543d10200001c9080c46030340442072080c40c422902040440410b201800c1e0380035810002c0001d04110008001500d14505000340100720030828000c103440c154180c041601d100c900c1c107608101c81c40c08003e4038040103001c01e0710138106810180102030b00c0b015a6401400c0100040c0c407041d4990fa46409843c040d6000710641108948001a8250800100b03100320082140e401d010301e9586441c1941c80d0501603822903000c0c001c0c0707002c80514503241780f000d800311072000e002c1c0100c4c2c00c0a600d40c0001420251000c917400810b01c03482c0ca42e508000d0040c0080c2500403421a83e490034040c0d500012105264004d40f002a0140004c00020701c00074020303412240501c80941501202d02c20407810000c094001030740c00310725800003241030fa900828285096451400d40340311262200 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 296519127 1250 296517877 296517887
    0x16080708030f1207020705190320090c03041e0b04051b090a090c0305032101080606130902031920060403150e10060b0d2d1817030601030507 62
    0x40742541911400300b22107541c40050000e180c2c0c2c40130311403060303d419580360302c0000d15192946c40c1140414800180034030a1001c020354841401ca640444e1411781d18a4a000c0340108000401c1048200c0c000710004050103da041680240da0614042c1c59280c950740c5003041424505803416102841140301c44d0426200c044112041c07440020300d14412591803868407405440018022640c2076016500080001c01c01c002400101c441126242504c000d484050407414405a001c10000da0215007440095150000701440c40021483d011070200c001c2d0001c03a01c0d00401d21200d03890640e9404d0001d0511209500400c1000051486a900c0c101d20784100115801240005840f801c0d500c42c00010049144c0c2c484100d00b65040d0507030b0b11075245160804101c64141d441220504000681105410a82e220b1058070b41140041c940c61920340c210140031103030560025010303103652540311741180c00d00382e440701c04181d5108401c041e48a00f80d600c2c0c0c182c40e4000380c50710313070100f400d060100e040c81c0d000e2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 296520377 1250 296519127 296519137
    0xf0504050c10020a051b030f030301061704110612090d09081009140703030504080c1816050903010905010b0a080a0503030c0f0f160515090d1d031608070803 69
    0x300516060244008201144025600350300a51203403501180004030240180020b400d04540d60308250703c07001040c0360a0045519840d90260010401440b0700e581251940014001b10308058602e07546525050240301e507401081603105102062014034078a81020091080b41c0d98403e64460f00d492035820b40308c47d101c0b8000d110540d005020420341c1204554440c6168501492414040380b1070000600c2c10300306681c005130f000450009040c00700620400600543c101c090340c0381c0958603074103540c070201d50102a1031051700300c2c561881d0620706031042098905159000700200b20003030244c9450b41c020440007007440c0c007230242c444000030b40b5400428801d04182d0404080c40c9503036500c400d0702e200d81d4041507000c1d030512030601400030500d2401018081c41c0700c20341c07541c0c1c0e42440d07c2e05005140501c5e0003840c1d044407070840c0070010703607280c040385003000c101250900440e0905d032181d09601510200c808650580726020101007558981e80c2d03ca421210220182c910164a40341c0041d206d00c51 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 296521627 1250 296520377 296520383
    0x609051e06061605011b0c0311150105010e03100f0b041b0e0913080703030515040902030d030f02040e0406140708040b0601200a080d0b0109050f0f0d15020a030f0504 73
    0x14007143d400300c011070401415091003080009001541c988140c201405691a03580018240750901010960440d0812510700018802418994200070490085050500030715040005601c2208242d0720100908001d0b05e100d49014454603803084001e400518502c16801d1049080c030030300444d43c8500c480f21805c040307003543d6210718000301039080c0206070401038107114103130b1003614124010994031405040c2451003980c0200c4c1e2820b0003028005099011140984201c0c50706c0244d0006030b07000900c00002d0030060501040c00c2c0f40100c43e00d8000d020388c0c0d01c028020200c0c08100420044680e128810415800c86e506c617160303d800710100c405000458004140b50f843d6004950158014410048200c0c00904c4418290100c0010241484407a1b00c04a074200b10108100342840d0700d601400d95600020b20781004510b00d050005041c1d4400681001c0c092900181852015100c0300303000b002c2e81da00400c0c114a0a1a1200c20000a60041100d81c0000c2c0c60180002410f100e01e005450107950 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 296522877 1250 296521627 296521639
    0x3030307080603030408061302011116230901121703010b0f0d09050a05010e060c070209010e09281101110c12010221090d0206040c06210609051e06 65
    0x9500e10080d00c0090340501034941c184030034400000d00950410000744106604040322410142910001d0309030460a2044a0b0320340005001c0000580d00540c510100c960400703000c55102c071028906050400c603004099040b01016001243c100c51103600c11058a107e91100301507451039141240180c0800c1c09002000d4030100141c080c4003500f50301402c11100001030020348104556034072441c1c020500c60032145a51100070b1014545014440796901814080040e86880d28940c001400c0c2d60050051070f039000800c4003c035141d002d003004903484803100c0c4c1da03d0764241c401c07580c002407180078480c5040340c60302c44035000a8440e522550303014090b26410350003030001103007800800004640d8400c003005199800c0c041000d411070f80318124502940d41c100c81d50031504103860f14904008481040780705560100040c04001510055024100c8078540342404100048081628100910003201007580c0c1c2817131004075009140740c0c01700c2c0c05950300100954218185d8010950328250842c3c003075074481 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 296524127 1250 296522877 296522881
    0x23010e01080613020a050a060e0306090c030d050313050a0323090a14010c1704080f0307020102250b030705030702060a1e090c0302040609060e0906041709041d030a1d030303 76
    0x5210f075840003034040e10040826001c5078a410114030000102d5200314005100c2d500744c2841030034240011038016080101405003440030030b020a41d41c0002d5146502080000000070301c000103011044041079038407009039028007005040040002002041b100003005550343c64007031141003203044400904000d4004407201c7c0c17814124020807948001440d042c000780c003d0120000700520000307244d603210032004d2603e885c101000c003490709107000f4150965510030000b1302d015070f8001404460110501103a00c0b65404401840032000c00c1d20303030024034100c2e40403040c4191150071002640c80f40080c0d60071100141d40300544030054400c2141c0d0442030700240a86004110016044602c1d0280501100c3d002a5541c0d03005c10100c440c103034000c1c020a0b603204030034000c520744c1c0c1c40c00a401140300b000412140c18a03480705214070328100b0001400504c0061000e803140c944d0b4007e00050030756110301082c46000362040c26201d43c044100000000d40814003032008190b902e1000c19100b5001e8011811a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 296525377 1250 296524127 296524141
    0x302060601080a0b0405010816050301090c0504020c0a050a0f0201080f1015111204060e01110d050304021302130303020c040e06220f06090201090e060904110406080123010e010806 79
    0x150354050b18840103603458011075086910303a8046c480c028081000141894a000c5140d550080c0030364110b40c3c803a03418881d81d80045141c5043c0a001d82c0d0302202c0059850500d0301c6014940383c0004002001070048074240414403002d41c40041c55903000380c96007001a5100080207001030340c211070605c0f45c120302040500000c020840b60b030401005500f1301000e02d0035200700492610a40903c503044220700000d040c00b00d00d90100c520074079820203007401e000750031203016050749038200081c0c03e10801601000060965a860204c482c1440013200c04642c0c07054072121315031080b14540019400740c030070383d0240a41801c2a01c5007050228080c40640001d480c1c503443e82030012400500410f6003031501c007200011403402d001801c1703014811300c0700281c0168140700142203601a40e1184001d040134004004894441224aa1348240d0183c03008002c00d82150024004142c107420502042d8641407007068611040320700c6500c0300001c50001a101d80e40d405c00b1401e074800c00d0062104079040300f0082180 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 296526627 1250 296525377 296525387
    0x9091914041e0507050a0e180f030a0c05030f1b07050102031303060b130c02031305040c080a15081603031b0f0b0a0f02030a020703170105240f030106030b0108130302060601 76
    0x2e110310481c00c1d511640d40d14800102601ca00e60080d9141500b450300f0300ca5580010214140c0082140c4c024001140c1400c26054583c0255968502030085038822a8200041403088841540743c3c1f1061a8490005046a0006040480c50f072100d40c0318000b4081210b40c00081960215000c810b2907070001c604541d1204060f00042d003030680c21650f606420f407411400e6008200415409500558503440c04940c020400001503004500452400b02c8081840d0350280110340e04c45000b04021a0202d0548665096006a40c0c00000e99001d800300681d008420644041c0c2140d00079554192003c1140c0f0400d185150704401c000c1c8103400d14076103940001c4080304450f5009500075800282c94180560364801e80c0e204461009165074001902b41c10150403204c0342d140310300d54103152281d560521020585c5607006441d20b0f50598041c10304c0c945400e20320720840300404404403c1c0c6840e940d50348030107130181c030852425602203070090740050b8458004140c00b429003501a0300a150f030b40c03500001520 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 296527877 1250 296526627 296526683
    0x901090903020705060313021c08190c061103010503011401050303090d02180403020627070506030c0403080409020d140f01120c08160f080106050105030604020c01020909191404 78
    0x400c0d4000c0c6480001c10341c0d92017028500c1400d0300c481411109649204200c0d80c0805010b101c4482411180d120f00840c0b07409058540402881400d103400002c0350710292192081c224008042c54241018501500400d40107075048500c1a0b000307202c041c240404001c41180e0074020181c055106100f0355402d0324200071194030990000d03098640441039682c0d00350710108216019000350b030011080c48011a10807815000082d81d12851025001000d048540c41714010301c03403948120310201c04181010030080480c0c00542c2c1c00104196560b6507141114042d42152a46113402c40c030f85108440403a01c01c0021902c2200c60300341c407500b41d070300740401c1c00f142800c28141900d040000050100b034905041004049403c5c084443d1303602d55150100d05c50840f46c80340c0004c2c805074106a4100202d90700030080d0390700000c0807580583c40307050070164680240160b0b0f0400f580706a4840501041d43d01021600302e040b254580c0912541c09005025000d0103026030303000341440c0b000c00c00c81c5054101005455 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 296529127 1250 296527877 296527883
    0x7032f0915090d111f020d0e0105090303041e0b1318060f030809030d03150e13170408010b060301270f05090c03102d020f1b0f0a0209010909 62
    0x80c14001901c000c50070080b1464000c030743c103e1441058144d05d243c91980f540280402c804480004040000c2c02519092103100441c107014000c01c612079240e00400685100030030103800c0720788840d41e61224400106c091b04110803890303060314010411018034030842d051001003000c1d41c00d040f860142c9900c841c40201c074408001564602d4040340e0f0362840954003004601036a0101c0d241e503000b5041500b441141c201c40c400349450a400d994408013000140700480d510311b0040c0816030384065144010a8124400425420012100c0402c140f54000648251420740c0300070050240b018042c44542d10007800307440c000a0a006100b0461360103445185d100311000900410740490041c110016103038151103180041e04061502c03000c600f01001204800368605801b80262041402034000000d00b550325034070303070120410102811034690b804a480040008c2030280d507564030108660f620b1101d6000c42c0c40720b4060200c500008800c00039030380d54031940041000040782d280040301030080c900308000b1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 296530377 1250 296529127 296529169
    0x3110307020a0906092a0e03011b1815120c03140405070512010504020a050405040f1e20030d0f031512020307170307080306010c0203030307032f09 65
    0x4140181c5452a0b42c4008144840c00415910708290340c0d4810b40d0b81c035000754510304070100c0b44c08a20030115031900c1c00b10041c0b814a10030000c5200d0119024050b0130150240803907908584001280e80b162900340c201e809100c25080c0c2ca41c035071000b200203260250786c40d07002034a4200c030702c80c0139181a88039401c460310b40e050010317140c51010480311460400b15420350701500070700c074108028208003401c03a042c80c0c1c108001300035a1605034001000e00509002c0c080c080c507039441c0082d0400000302100c090315500310840030048180d28120088070300c00901e040390400c001c202039000e220302c10080c0c4110004001e000d890f544080c500c00326084c11840781104101034844500a0a10030605200c40141c00000d60500d09103807030340103140c9040240da0091500c2c0d000002503000080020040e610090340c4540c1c0c3c0da0703880e150400101ca2010b10b00d04007a5050000006102c603054150340f004841500d488010f070300003d50411200e00c1c0303070103466102c000103004024031905450b03e03121003521f0402c0340b030301 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 296531627 1250 296530377 296530387
    0x8030a050a0e0d290603010e07090c030209060f0306100302211009020c100c110303010605030a0b0915010f0f05041a0c0a050d02190201050d09050c040507170609040f031103 76
    0x144c4128403207122000c900c0014100c40d0030b10054080d46605034441000d80003030048400812101c4d80d10a46481009e0780540c0e074000c0290442e200c0d40440d015214010050354a401c100308404032160b0058070102d01c6014034bc1203a189590090003901c0040600015040074044c00d0b100700c0f6600b48000303068241ca41c02c0000003040712015803000d0058a482c2d00000d0018018041c0c2c0c44044030480000403041c010300603802c00c9030200000c00c40381551082d107409a2a030300c81001030000b410ba2001c0d0a90b004010306d08000c00000c40003403070030301d000d426640c480120003007540940d4264036120316400051010481408920849104492013940f0240d0703a619019030110301500f414201a0201d0301900020796019009504200d0f61561604031404a44982c00c3c0e0350010301280718180c9642110707612413104000b400018000904034900140c000e2001d441d00c498014000102c0b9400c080380d000c8020301181c181d04004411620890380070350101c0307440140c1c4c1c030183d40c003480c0c10251400900c01000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 296532877 1250 296531627 296531633
    0xa0515030d031d160627090b1e1309050a0204090506041b060804030f02030d090c0503070603020408031206031e0d0806090702070506090307030605010e070908030a050a0e0d 76
    0x7203120200003a5640000d04028111582514584100c0c01c124443d807165401910341ca26a14000c0103c5109041800d040b8401e16449a6140380c0520320101c645c41c00c610008010305203403c10103011380304071420f80c00c12104c514180c40000c92001c641360000c0f04a501c042200c1a592700c40301602c0d000d1402c0f034000c0c1282d54006815588190f07821143d90700070340e09000410444a840754400700c07800240050003030401000600420000b44058100003003209587d0866000b40201c030310182080c0003d21070041541019214040340f445142e0080c803c080c1c00060403440386c400c0d1416500340304040d5281500d911881808990042c21286d4580581100700f800100024504140840d940c0064481d03080c07144409007007004000d11660081400000b008261a40410041c059540840748a603c0700810703008a0f1410176603400040a5070300c0c000001c00ca030400c842c1041d100314802e5669a1704d081d141c1c009580c5030301070403015102251052103c0b413455030083c0710441904d58042c05095800c0640d813 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 296534127 1250 296532877 296532883
    0x1c320c03030405030a0807091505070c030503030a150902090d080d06080601180b090606090904060f0e030909070c0c150c02060a0c02030105070809071403010603210f0311030a051503 80
    0x960b00b103880d644002000418160401c1800398002010708040058070b02d0290502c005044c4004003600b0007600181a03020810001c1d020400b640c1c000040743d07120b18001302d001c00142001c0340c00d03004504540000141306822402207450081020300703a541400540c2d96860a20b4201a80005038039480d8030001c03410300c10411006008142c1840d02007035240e03403166000f044419842c0241d00a080381001c008a64461208550028ae000c0e20446015515410130100524084042e214440d00f031840c18410401d0002c05450080c030102d8000da0103460380c01d81074889562030203009041c040c1c01e000801c41140080c40d0501030100d1030820b028800780b954000740140c4c4c052400440032400c08221001941000d1050342d070f0040c46030800640b141000c1c407450380e4030099482a0010080c403401d4095140d1400c3d00208029a40201d081c20451041810310f44244400303941321000074681c00711024598842d010782c0150f4204400e0642c6503441d1084804050000100740700354408400d8803118440d1020 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 296535377 1250 296534127 296534131
    0x15110705061306030b0312090f0109090c0908101407050d02040b03040b0a051003020f10020c0a030602031806010506040e070c020a080610090504110f0d0807051c320c0303 75
    0x1400c0b0102866050000c040d0440b940c814505010b80c5c080d40c00160031032815070454201103011610900d81045500040b5a00390140c1c20038120345050211056041e500940004140c0700d00341c064030f0540300032800010444140341030903000190303210301203003105000303400801c078201080c3e80142ca02070f10f8004000d425072055a04032051f4658030b08000149110703103c0c898000b402e0050541030300d841c54000641c170103140110309102d8407000c00040c0060b40200500ca0748440054214101f032640c03802d00100a4004491010100c2c0c1c00201c0294000d6000c0381182c142d8900520b07150801e800d2a089081c0460700410b00380a00ca004525a40565182000000104042d800514051911070000700d0000e05036440240c09904040500c00003446c246813640041d03c090311112200c1f505000028cc408401c0f0078050640400000e40c1303814054040340e081c41c0c4922001d1191018401110112502900129011402c2ca590141c015881c810340780c910300246032280505090081020950b0708560003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 296536627 1250 296535377 296535397
    0x3100e091605010806010207180b03060f04050601051203120703060819060c09050d02060c1e03040906270b010203220f0f080a0f08120106030b0f0a1511070506 70
    0x40101d01035040302449594002d04028609003a45080090000c0c0d0f40f2601c50240c000d482c0d842e0607802850810551001044540040031200c0c641004440442c9420040c0d4003074680c0d01918001140a0070710001c5100840740d03000084d850400a4111a40f088070013515003070425894100c0080e0124080200c801d0003000b8a160f4042141c551030007004881010700010280312101c1c00c00c200c25940c4200345121280c041d15115501d0480d03400c0c80d810f10348a0f80d9560410141140308001025000010384141e034020f03a8200b00c560340304c00e0b200c0d030640806150001500c0b0601d04d15680e400307541e00312401c00c5d601801100c0c01c00c1c0c59401c5008101407c0c10804a48036002001040101d80032036004d402003c511042000c124148000c0d43c1d00c40c000640040c000801c5440040c00300500f860489080b01c0c0084020040b47d41c480100402070841300e8541c500c00d070340068050703010307103000050442160340ca17035030f0058007412031841a50742400d19941d4181e80e00400c940000d40361200d0004001c0314517 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 296537877 1250 296536627 296536633
    0x10240302090d12030606030e0d030f020c07060822150b03160902070312020310060f0507020411040e070305071e02030c010203040c0501080702010e030904091e03050406020d1106070503100e09 84
    0x22410f1801822101c02c0c0c0c2c040d904240c18240c4500c0780b04808074000d250403411f0325004c41c5030350500d0a810040d2003921154030f0244200ba100085407948404030030f0056500036600c601400301410300c4441440c11241c054000100101d16461240a50744841904100a404c0d140b4416403001204007512071540070086884e00000c04408055204003040f01c40380503994114114100186500751040b80c41c01040240070491100c1126a4020002c0c1c8804590051040c00340c42568486058650018414601d140300817001059125010740601441001c040d40c0b0180910071030892092088810300319803095000030010261f1910003800198825401400008078407403800000500f8840000c004c1c200316490030407000c0c04500088101c41c41c4c5102128042030703004443c103206400c100903240c40c418403d0000008000c154020000d130049520a809032145c0506403107065440c02e00056244105070080800a10018010381c0a50f80000c03001c0802c0c040251a0344000c207084500b51505200fa40c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 296539127 1250 296537877 296537903
    0x30a022107021f09050304060c0c09020c010902040b0102010209011d04180b04050f120d02090402091305010807051801030f0503090915150c0d0c0203160603090b10240302090d 77
    0x3c0502e0f00c00c0314407000c080c2d41c10445200f180d11060b442c6d01480c0a02c5041000d044960002e005051207410040c255040085580356028580e50b4000c0c000103104030f0040b4245045201c070380d8018400d9031001003068440d203401802c102c10318a507816080f00340e564080e175200a010030701010040360a048030b110b000d884da050b062a0400301d180600030218242c09074000b01c841203100c02080191826020b162002588071400d19001402074080c034021f0b1504810b043d9a032012480182d00400c0c100e8040030300307407610180c4500601c00c0c10041c03100090b030300c03820000041002406a44039007404032b00803000d880c1060070356000242c040005075055000045000c0c400043c0f4a48040711f15208884411500d10300302e501c90403203403074040340c031b14020500c0f0100400c031042d0b4500b881045110207070200c004410300d49404000d0010a21003005844064003040000d070040d4002c81a6025074a081c80000d00628508056000010501180c0d804158007849500000e450380280e203d10b00d4440d8140648a03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 296540377 1250 296539127 296539153
    0xe040e0123010504060503030708070f1e030e010e030312101e15020109020a0312230d1b0903170702030d080a0e0604120f09081207020a0e0705030a02210702 69
    0x10981030f0400c61240f0b180071002c001c00d980c0082140d082652100813175843d0542d50130100800342c100742c07001d09500c10300c43d203440d90300908a1101e4103880c440c2d10b03011807000c48000111040c86c200302c156a0941d10421098171501300c0030311040d81c0010803000010000743c507040c00034802e41c0ea6010f04100e000d80080c090000e600c0480314404158018402001014450340004440448034031000d0130000168400405480c850480d10034881e881d03e105844006031600c15401a9000b203880b000064030742007202d100c00f40d0001c0c401c080003009980b003480b19400d581f038074808156400b80011400c00c0c108a0b036001a20240030540c6140e105032101625440d00400100c1070350f6549080022a401000030400000c3c948218102c0555091070004020862600103035261422a0002c0c2990b01c42c40d01e03e807aa0b00700c0c4d00000c0118a00c00d4400e020030300c2e65000014200d4000380d840c940890030a00002e81400d8680d0302500504504880c4441d0600c41c03800b500300040d13002d0781d285005820501d90021a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 296541627 1250 296540377 296540441
    0x1020f0a110d050d02030705120403020313060c1a1314071d190203070509060738010618030210031a030307050703060905210703120218010e040e01 65
    0x158540d0030001c0e003002c00514000920714420550301e51111540840400e4035580305006507201d6034844650142e490800741000b0f9600d4204082d4018008142c0d000490068450440d807041140d129440e040c1c40b116084040c1d00418000b0189802d6640c2c2d42d03a650045880313417200300c90340c4d4890009042101d0a040200800c412003021340c8010648600074800c00d4100200040c1c1600d0032442c1c0141c982c2c460301c104441038400c0194207507101341c0118050701070040c04905011900c56035008015001d02002180760407004241c411080300b4a480c1c01009014080d00b61101c80c10240030b0342a500c00d45990026407000c0c0040740e42c0340020740d5803a000d03952040036003241c2c40d01c4408400840c00d0541d80c0e90382c00c0d507400160000800940d01d4022800c2048010030086074400070604074060f02d40074038000c030035154115810540000c0c82c0c03040d00307001c000c1b110720843e48443d80c419015040020520015500c80326041c1e01030360002d981d058200030f142e20070300c1848201c1c015803080303810102c40e807414401 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 296542877 1250 296541627 296541647
    0x7151104031220031210050d1a06010804030c060504080729090129040f181b050a170f0f0c1509030703020d11180a0e01050f01060c1401020f0a 63
    0x44600c9850100f0360550b80c0041519000080a101090300f5501c024007400b100c07a15500c2903422004075625a81042940c459807010710501c61002c040582d01c0c0703001180c006800f81c4014002c00c503243c2451b008542140c000c2c9910500074034906103420b64542d10f604e034005190030740f001042140000e0808041c0030a031605e401c480b000d80240240c408081a164920b080868018252440044202c4031603d40b50080f401d65900a0360070042c10540a541d0501400e60042c201c0c0c602d81161524140440703d85555801c0d650003030a9640250300f4100e4000380f101032444800014881c4003541d40a01c40c04000c1c0d020b4160f6010050150383d607008051001180b4482c00c40d210840043c0308450391918001101c0c400c4907011500600c0101e030f907061001c402c0f01700400590b0040c944458150140c5403074110540a580704807820020040380f0340c2030702e007210ba0554801c01e08600030401000464442d04200340898040c48030a8280300b24a03012600b20f81c842c40001e40c90040120b83e504034683c02c0b965010b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 296544127 1250 296542877 296542907
    0x2041e06020f2a030f0304060306151716020307051e0f0f032b050c04030309080102030411040c02010b0910030b01060203030f04030f21050906090a020105071511040312 74
    0x48814203c59611154a504541c810145800f040ba282c6500f5501004640c524951100640360303a1500d0701c0700100502018000c03070910013004a030301e2690078400d941c0c500c195040081004529180d1600041c000351400242008510081c4a9440451002e1028012020210b000300001e05c0c00002110300705168259005201d8010016607403a07180048211062990070505010b40580b1581100e101100b0300085a100f181c40c0c00100008013502e00024000d0707038001c2e281c817801c0540e55000d850a034071040b540203008076401c1c640501e40f0b00b016009500c0d080d0941c00041200c00c9290042010450119004d041480c1000000c01c1404009410307940501207901c0554918500381c1d00b0351112040c003500c02800c0042c84908158914030880800800014041810007401c03203e42182e030103014280c4441205000f14800b0030082900000c070311520ba42d061311030310300748003482d04c43c0c2d05400d050400c1e02c51141c0d241c0d240c1d000f007200348800401c05584680060005140305400c01005840c0c0c100c008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 296545377 1250 296544127 296544133
    0x50f0c010e01181a0702070b03010b2d180f060a0801090b04020301030507120305040332030a020c040e160e07110106120609060b12030a021002040e01030f0602041e06020f 75
    0x100c0104180380000c0d60704c203000004240309500d0b5264100d15011f4030f54480b0b4011180400003003480c045090003810b00c0300440d282c03008400105904240b05002c2041c0201300d0050030000103074842c1460352490241e040007000002c01d43c405401080e100d45c028100c810018090a00500c0303012081c1c8141c4a000100342e40845c01c544c15a41d8250381d0301e105004440558000948482c1054424000c84000e150b0100420704481c000e45500c0c00310b4460540000d800210441e01a0304011001007a10034088440d4000c041406000f000d00000300513000011515010350591071402000b079049550003005441000c403034038030341910020b040b003210b1140180d040e41001800c216031040e46481501c400e401810001c0c52040c1450038000800d104a50035810190301d0710010b0341c40324040081c1140c01c1d031907000c1d121001c115111440c01c0784142e000709440380341044014804210750300403200c2c10034861a00149010317158070060004400d011141c0c44c00600c0300c0d0f81489040c0c1e040c8000e0507031410368401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 296546627 1250 296545377 296545421
    0xa1d060301030305030a09020a0e04020102301c05090c2121070605011412210a0203040e04062910030e070b03090604210212030403050f0c010e01 64
    0x18005200620000e0200040480881c206030072542c01514850f500500000c5265902d03086402d015001b19810303030140c011205140c4100c2c0c00c80940b44420010800301c504102c8000f440754000390885154980000e0710000d5420007035016200306805581541c000340b0b107046502080180350840e10700c03000440e0403824100e503a010310001d00b000b41e91042c00c00108210b0108083c00846004500b00035001c24103000001031045480c0d41c05541d0210182ca00da00c145540118590359a4410300798018095091a85d40b42440083c1000e40441c0d00644162403401c0d503102d00c81c400c5c00c48181ca040d100c039540e98030710241e115410755075801080380700210580196030000004372402034150040c0706040e100c0c2d00c0d521265209001c0900603002008946449003045203d16a450b401103900702c8000c600f0ba440600440091009800f44000f150300508a185110403028072981010300210306215080c4a4a440030f000f11001e801074503203a000000f500440e10304060309403089004c007008500e901000e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 296547877 1250 296546627 296546629
    0x4080106080a050d030519021321020307030f020a0b0a030608150739030e040c0309020d2406120302060a11160809090f0907050109180e010f0606050a1d 67
    0x2c400722030400c00e090018242d503450720308104261f0501c500344201c61000510000c82c50103140081c050301c020000c04482070082c800528405404007001a5040c1e0181c80d00b040058040350b918070240d48068054411a81c1c2c445080405402c0283c04c000802d0700c42801303108903182000640b1542003d05500085800d1003000505a1008014402c140443e903c91400010105c00c5441c10740400e2050800321450303160030014900395000228a104600700140c10880d0740c404d0117420ba440da0000d010001074409550707825010b00d014007914203034001d100f940e4580000035205103801040f50354005020031b10f0030b140080c1880ca00a005408491804260950750541e52081c1c40c1042042c1107440110781340c9080c00d0100f4003410300e00d16480603009040189140303a03000424081c00b59a401ca03000e084d2201e00554036500c90f4080c15070f00503111101c03520000c01e00d8011060800c405000090301c0c0e0007102140c0141d40d81c50700100301042c00012181c140c00c3c1c1c040b5042c0175480000240f89103070440c03c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 296549127 1250 296547877 296547883
    0x230406090e0615040f18090506010611010e01110703030c08010b031605040b0d060302190602060a0207230f070e190b03100603050c0f06071511070c090204080106080a05 74
    0x8052205070030004000503519455080c00c444088859650350f07903d0f0341d0b6416000d00424202c0c01002e000c2040c10881d00f8400f12140140049183d00401810f0641e08050b0201c4000f49110b200900070f64030f510500c1041402803154400c2c00b15600440ea07502e00050a0183c16a288039600700708000c6007000400602c02604160703034000030481c10b0394400d400175540032245801683c0004040d5000003841d0820801194411811a4821b40344021660b900c103161018a403040d100b9000540c000000140100d001c2c2c0d0b0007000068400d02d0401c2030802d0200300103100c049003502001da00d40c4004180c0185400401841f0000c181040c0703501950310707004d00ea02109017040b031420845180c98811828190740c2c20310540e09107140b015800c0104940d00d060495842051030000d40c095080c00d003d05020b82412000c4a540e5604600034400120030a1040002042c1400070810100c00c14442200001c650700e1608004046139900562502c0c02c01125500f102e003150300124050307120342c401ea0000342c004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 296550377 1250 296549127 296549129
    0x40b070806130608030403140a080306150712021b040e120f04050d0303140c032a2101030b060f01080a050613060e040b0a11070b18060723040609 64
    0x51500360101d89641c00828044240303040390341981c0781884030100781d421000004e88201c0380500f021060401d10401041d46130190641c015100c80c4e401c100003203060400c024484986860003400310b01c1d2240b55120072a03103107011a010342c0183c11a4105901d03802500003000303096042260100138440303044c0c20b10340d03507001c003002c490249080100d280c24402031100c0c03c1d03500421014002c4036840f8014a001001071000c0303582c104401c645c200100e030300a00303000c041c0e174458244088044d20324540c00120b2104074041c26441c2c008e0036020000c030b8820655560712001c000d0403404041105505528061001100050500b4002d0b2142206642203a9201e08c2e40303900f01840660003c0c1c00e45451021a80c079884151059040c1420440005186040f00b881c00d03101d64090008203040d40c907490120001c0d10060208170170704140512602002c9007000e03500300d0300a0785510a00d401d1a6a440d18142002000c4030080049290040365030b22045120515041c000d02c50b403007072441c290078200064a0a012 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 296551627 1250 296550377 296550391
    0xd0f061e1118030c030d0f03050109060509060f04061a130e09060708130b040c030b07020f0d030b0127061112030106030b030c03060109270f0b0c0d0507080618040b 72
    0x41904510b1152428003500c5075141001c1c00b030342c2100303000f000c003d043e000081c00403800007403624000052400144c46800c090b100000e1035001d16480d80d400b00890284541c18050340f16036100c074002070030545c2c0b40c0c101804480d6591a203403903e5100c445440118610782c04403012904002c10045020070200c0c510fa0301101900384204140c68028911004400c0d944005000c21141c1c002d200500007064140801c0f01c0c4149004c6400f1380d60311a080380c9035940c004a440d80c5612a032003540130301c0d0080d0000624000185410103590054010440200030f02c100148240045400207110760740d44100f030718641001a0000345244800c004445001c1c2c4414803807074040641e59176052650785c0c2c0503c011a90171000404a40140d61030305040320080180c00e855400300c3d90416440403900d2035282c00341400ea500400c24408040c0e082d100c41d1000c1c8001451420a080100700041002100d4400c013400340b6019962501d40b490910240141c9100c0c12801613095101e070420840040ca04c0c21245130300040c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 296552877 1250 296551627 296551657
    0xb060306060f0c010204030602070b060d0c0504020318100b150f0414041103040b070e100504031704030503040f0501201914030a0e030709021207030b0d0f061e11 71
    0x750401d0742c6015401001290301e59540000350001c240302041d0040d00304540036807609407a5445010405c11001d8000700000d081240918007042a4981903020350791015010300103030400d540024806040c000c000d203003603082e19076449001001e03050110743e030246040c4d4440326524002400c1c0701600180a03074400c503101ca03220000c0c03134000381d00c1d00d40014480c4102101090307120304141c60885603c40089036401c0003c0d148034207850302440c0c1106072079010105030311014035140c1142c0310301c44003900070000c0c2c20b018801000b0002c00a80108001e0008141d5010180340740c504141c0010078103c4113280e0f1800e50818980800c80100c000b00315417510010581c164201050280707407040c1841c41280d4140124000072800740c04044d0041540e244041044040da05500d890f8601c03a400c80c05400c042c40542c40c0c0590010350000c0c000e6001900c483c1009080038103ca201d5503c1a101023480c4904841203500c0e601500e01034803005840c5d429481000e401480024031000d41d00c0e1580c011a648500041 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 296554127 1250 296552877 296552887
    0xd03020c100f021c05040b160c02010813020a03030507030306090207150e011d010204060201050105150a18050409060c0e0312090f0f060a0c14030406020705090606121005130b06030606 81
    0xb1403a0303040303480444d000c8107040703948402c08000304010310045406980890702003000401e200388001c811015540c3e41d0b01c400c0c60080c0c540c0c004580810300100f107480d0880240004c400542d07070310203903807009511a03510a6540c107042e140040c1502c08940c0107110710340c014401c9a0001d041d04140356002200c408000903524010303078445014040140441c02c04c45801030305460040b8040d0000d00940341e06800921403a40e030f58050000701c0300303290100d01c0184421300501000034420518065140450a0000340098031940050116400f000049034042d41d2494a0287d40350090b90708040218210007030301405002500031541445290241442428129004821685c9950907040036035030182c07080e0345803a0800809040a01d4081d82610380040008d1880b404110002c00c44068400a5001d08861807502d410b12601140181610b5070000d41400091a804198054944540740203512541c11515100501c80191400c4910182c102c2c00d28001d44c500352221403c403a0001025107c00d03a40d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 296555377 1250 296554127 296554151
    0x1050105032e050109061a03040206070809060d020a021c080f040615031401050601021204030c090f3206010f1403040201110304090c0806040506220e0106030c080d03020c10 76
    0xa00380300e0707044070810b5282a0000c900e0708429802030054465480000d08485001c0301600440c2c002290029440001000000c0010b2024809000d460a0140c0340030b0402c2d8001400ba0281d801c00d07400b440041e0b1008000345001d911004058900303030040e080040460409614602c1c2250000700041e201c591100c612049007400920120300850704064020080000c101005018100a480c6580144182403640f1310045800040720102c3e5440041d00c1000707490200a080030f0001c0c0c0c441000010764503000c0c030380c0c50480501d4084030740041c5074814151400804511922a101400d00c03410001805c0c0c900040c5a00f1601a1140c200200415030703ca50791840101d400c15003040740b000c2c140c0000320300090707030210399000105401d019803103441103641e8030000e22084030000ca82c89544081403100484039107502d01407039062000f1079a000b00b400c81c1100486820348070309034000c9461000b00709003040410000d01070031010a83e14039040d442e02d030440510564810115a64000075580c503414071320b034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 296556627 1250 296555377 296555443
    0xc0c03020606040c020f030f270d1203090807060e061501170c0408031c0507020d050315012d110d020c1005040305120a020c09010609090e1608060402120105010503 72
    0x110042d0359044980d0395423a12840324054100b80c8406c1100c0c0c0b101611217000b01c10768031114800c6400988080d01ca11461f844202301e04e045030004c8000d05980782a29808280d003100145881c6000b600c01055814045a04a1410310024000e41e03015410225401442e0790103424034140f07101e149003421040d140c0a01c203049912a640c051501d62100152198060340e0a482e11080e100c207480c82080036036a441300076030711140d81010210000d20f08100040c0182840d0350740004114061524903c8070050110011b402c0c05654946042907280110130a2a140d1089060a04000c0c420181125880f40310010f0b40e11110192070030700c5804148003e00d4228490f005850085400201300c0e9800c0c0002050040e440e8001c0c0c07002401800359845960306410582c038150304841035680c8600c4100e10f860888401081c103040a100180121203070344046d1500b1391074141c05064420003501e00c1d030405104115484842c0c00000c121a4106001003000340d4000c651600300d1324030301c4480c0204403500d034a1144 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 296557877 1250 296556627 296556643
    0xd030512070804050d0905060d052e090b0f21121201030b0108010c140904060b04092406020c1504052e18030f061509020d0c0c03020606040c02 63
    0x10300c8414440401195075406840a07004602610550300607a0300410112048040760054940081080015507c1d120300c550000d584044e0b40c0e0f94008202c2501e03800c03911401c0846901c1d041d180d44425081c000303d010352003400d4100408441c80c20484001401080082054414002c0d041840c101d081d030100c0414401501072000341240240d54068076000d00a100300e0a01060300c01403081c1c00045001c0b0300501c034241d51501c881e122004101480586038005600c41510076070003030340f0703880300082c0d908001e0060f1000d81428500440c1222101071800d070f1540321484140c204091001c07003044900c0d0003280c9200da410080d0752441110001000380c620500c42d6a0045421a00c06522181845e18101c0d100c812030590ba104040701c040f00900c200c0d03120010410041002c440c1c8441080000d07d680c516212240c0710f94004982185415000c85004425a10004509400082d18070700080544103c143e000510300780346c125002035440080d550300004040900859540075000101402003181c50703 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 296559127 1250 296557877 296557897
    0x80a0c020c150d0b1807080a020c0a0605041b0b0405100203091e0a05090a050a0506010f0e120109060e030a0f05160204050402030c0a17010506040507021c050c030409061403060606090d0305 83
    0xc0715175103100076031202c0355904881180020390144040b4007403c01e28022544444080002000b401c03a041d1182c1d0002c0c1400350080701c04030b01821054400300742c2d2070202c0d030081c5401210325454a15010502006a0809240100710340041107000015038070684000009021042103800300c40c150004a040d10906420641d032000b417000402080c1c0c14035401152080341c0b6003009012985a81c0c0c0151180c110149854010410f5141c0b180528286801150692800d0100118803407410352a540101d030150300c003648264000003480340680360001503030103402e081031071700c50b14142c3ca004001070310f803d0600300240b00359260340128080d50303010400c0480f400001070080720714950b0744034101c0d25150300318180b4416508040005d0a9403816128091150030903401078038036502040031289000107404108c030103005003402051008a03042000d000945034199000400f18105441006c05000c8103000c24825444a406c00100e0348601056524544e002d844612055045290540e00c9000c0d0300e07240 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 296560377 1250 296559127 296559139
    0x60901030803090a171812060106030f180b07021e06150103020712081b03010806010303030207080d090809120303070c12090503100203060a1a07120e10080a0c020c150d0b 75
    0x229100b01501720051165609103480110f4604608080c00714922120003482e603203801c81401000114000d4110381c104207a40c6030000741244070743c00a150808141d00003a281c140c0c03488100a210340d010420718210164160151000c448452280c681d80c5070000c080f1703100d11050700309505a503406134060f5400c403540502d12552140c04102d0007450b4200403150803c40440715802c010b02c2146201c1200d050710041c4010346016806c0d82c0702600a035200d05412181e04004000e80d100030340030780c440d0300c2c2c94601c1095146d603258031800c108580000414044071082d0020824020707441e400201c1010000d9000591140e45165620169203101c1258015034041c0500c02303004148015541c00ac40c410301e42201d60051050301c4604000445070800030b0b03030001880c200403002c041041103680c2c0401c00101d103005010000100080350212003a4110180819a09014800607151278040c9140021070f80c8018210003070184005003650740e451040340b1407032200103803040038240190000001c0000281c80 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 296561627 1250 296560377 296560403
    0x6060f1b380f070309030c020405060a0f060e09062709030d06060302031605090a180b0a0303020c090f100605071106270a0b070b060a182003060901030803090a 70
    0x1206202003080740e0681c0e07925082d00004a11600a11803000c0c3c55825a0320410442ca060f420700000388405404964401500c88000030801c401c111902c010700001d54030340c02d003048d403c0207000140c036025211511550344180008038104260001105031151058080c000380c03035510304039042d80300700c0c00420f0146042040203c0d0158140d00218000d45407000341c00e1041000140454490041743c1a1960200c200402080106a211b55415520a40344400682111040b000504401440e4400c802580001503440420b2901c00d4546600010390080905640352140c502201e000d02e90040c0824494041050002d0224680012200ca50b020740300654a031040c04250a503482c815207560303200c03084550107072100e00305194114201e0704d00d41029030401020380d64141d4a4100100100d030003c00a400009820390136810344046110350460000d0b4004164905802130b05405038080545503080040c0b0000d03403541020141101c0d00285141c3e1240c607a0703140c07103051205149001e8880081040c03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 296562877 1250 296561627 296561723
    0x1011070807050109050d0b010605072f090a0b06090d0f0c08030316110a03030e01090507091b03050c0d0506030f0d02010f0606110a0b1b0d06060f1b 65
    0x1407604142c52098803035031399850781c400800000d00ba92210051003002d40500401000340079001800c03986204158400900188159a0f040340048503e10055506c16040760552820400c040303607000300d40028288400350060020404501c01e2400d45230040d01104410814800d4110048802d41c2d0302c001c0600c1035907621f01d0002c4e5644c0007925910a032014144071064410701401c40c81500b40304150140c804485180c8007a07006011381503060300c1075529005581c002820a0140c20044e002e001000030b030081140d41040048242020041d06052500040c070402158200c10384442c40c07815200070a03150303160f0002c01e00b0000c0c2c0300942000e0f031040c400c03c00d85080d010740002c0c10203641540104541541d81404484804280c00b41748860703041a41c2c40c4010038411100c059006103140c45080101c041004045500d901075080100e140742c0e94002804110342c40a1981900711703040c541031402e1400841c00c44d995481c0b0361030052404000c80c40072070b201061078410160805801c55240c8840c80c5440d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 296564127 1250 296562877 296562883
    0x106030503090108100e1506041d01090b030a170d1b08061804081611030f010f0b0a0f0b1305090703021306081006200f0a0501050a091110110708 64
    0x4410764089052100000c1c3d18500a603140700807941c91558002c0f05440b54207201d1642c94588007d503402079000c20010902c0901c1c20a105125050340007110340d250300d41a020012078141d003851500c80e030007151190000c19a02c404440c40b088580354442d0741c85810310000402070440982c0c40131030003104100030401d030b40c1107000c0c0b42c86007034240d418108180c0710540380d08940c0320494008294040600c00c0301c042c5450341c9021181a1700c5807107262008608040000c0c80d2040405105040360344803003c41c003a158460180c11042e03e01910340170f0f520703824154524410801401a07d84000c8080303aa503040c3c5008108840041c00040c1c441800c60070000001806540041504a1440340c02600064400d04c1a84650302c03c0603225495101642040d1080300c0344200207100341c214415120b030514107040e00b402018082c42c0d00e000101254211494000d081d036038000e01c4500c40c10310b068403007008145005408100d031b0b981182c2c01c01801d03512001c203407051764800c2c50100252003400800300d6196000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 296565377 1250 296564127 296564137
    0xc01140405100e030310030b31020301060e0c0405060c03040504051005040b030c130c02070803030106020604120f0c0204051e09060105030106332102040510110c060310080106030503 80
    0x5070501800344600200f030380e02d01c02516400201c584004081002c6482401074540064400d91140f00c0002032803415412901c0291142c0040154588414114a024400d280041a01c259014051b142866850346079000328400c8900031030700021f060914003418022500500f500a20812a0b03040908031aa0400070754000c1c41d01403894000b0a50051500040281d1482001840418200315200441014007460401001076100d4642c02182d00324042c400746000c0c20803940204a1403805041100c04040070080c6501400501a90700781020392002e07500240725015140171500b500d500c04581041041c1c0b8030005510205082401106070300818403031b048031012402805926101c1d402c0004245e48480c1034a44071218a41c41d254541c5c0c100c2c1600d08021181c2401000702403418001040910388944404071180e000405000798a019000c0f000d0100300c1c2d1501c1c01e00500400342442e9074600801c9240d00c83c110210002e807440e44002100409400c0f03400092007415580e282c0581d07a80c0007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 296566627 1250 296565377 296565403
    0x10513020f0108040c09021c0608010213061404050103112a0c1e041a09090105011d04121215300b0f0703020702060a081503010509120c01140405 64
    0x340d50300d01c0503540c412414580a40d8104006100c01e0b480c2c20204c1009501c410500421146038003050401ca0308144110b00c0100789071f50001d65603201030264010480c04540010b401d00c0410216581c2c81b4428800307440503141d00f800e000070440d9500210742124010040c102040c40c04805100c808487c03604500e41e1050607500c1120b4071007403114104070014004420a1080c80c065040030411490203030440003452008100319441a099031010507824201110210541c2e910748004111100e403400c1c800308408019400c10007181400c0c2d540014000701504400104402a110088008a9580001182000e01c454601d60a90303402040044101d03080d100c0020180e40112039251058218204908560000e010242c0756141d03c0000c0040c2c20180034101056802d0004800680310074000348802c420b240c440f080f440c540089204003c2103c140d585000f64103040c24054030040000d10041d03204000fa0103941c0b282401154980184018002d41c618003040c0b9051005218000c43d6001c00036031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 296567877 1250 296566627 296566639
    0x50406170d1d1e0301090c1706041205071109010602150109060803040b0a0203040b160203060601030c09150c080714120a020706030c0c0203060c04091514091801051302 74
    0x40460241d40a4100c8030440b8040c0b40388107031107503451500302d10441100c42240303950380c28154190b002c2400c551001c002128031030020003040c0294040c15400c4400d1410050041c001c1c1d10340303907603283c0507150f901c0d084205104010440350108110400c0c4c0c0c0c1b81d030b040e0190028015607500c040c0255550000c12650318103580f00c000200301403000740205810391380d607030008600e81803811008420f16030001042c9400c50206010100d8001c203808010810403111344905031420000e40109070030018042c0c04281418503010000410b550415141c4040751500c0d544a9214084a001a0b89241154800800100c0d00041d944200205190002d143c040320500b252880b810101480c8524440d120001015074800c0c0010800315100745c2100200c0c1140b40b4002d00c1244440d07002c03911f0081c00740c0310007106a5020a06001022051207a10150003500b03602050240c508040203e001003058002e41c09840e001d40016018001c0540900d00c403e5850004c000d0380c6818241219007401c500d1080344501 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 296569127 1250 296567877 296567893
    0x920120f01360210090e0106170a02210a09051911060a0923040207060903030c0509150d0e03070309030506010b0414040b030f0307030507020a0506040f03060e010605040617 76
    0x3808040c01c441850b1000728001001c55541e0200301d050150580c0102c10400709140200e040e080c8441d02d2802441203407507910494510240d41d40040038000c00080c4014070500010015420f41ea00d20000e104800040f01200c2c5c41c0c130f4641c240036100d6480c01410314071401c25500e5124003c039004906450003400070704052040316081002c20310411100300b0000b06060f80521210131940c90030b0315810900b5030050300044940000c1030598028620030303200a9a256003020a2540601604100c00950300c1e15516044c104400070b01e1400543c3c0c8410701d00c000104884101401c10f0b80681c010103890800c698a0b00d44503c1d006011000740d0108076030364014200005505110802503505546e24071501c010f015000c0c01c03e010041950080c215410b02c5805541b03810324000380020540b507406640c0301655046a801804180a07007a80302c140500f0302000f0070410081c610030f0702000e0700da0120700410500303d5510300501501907500030613841490003a0000d554652214440c00c24404003007515070b45 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 296570377 1250 296569127 296569181
    0xd03090201020a14150a09060c020d050d110d051315020304030e09150907090e060d02060a080c0405090c1206330706050a0204080f010920120f01 64
    0x2a5580000007400350340304240c0000003422031800c6800030b0f90003400300c5840b511850707025860034109460b00c0c10b1440c0d031b1f04054410710243c0c0c00b0303c0c200e0b840345000030001d645442c14002e00900c6003c0c1d035440150303624980b4105100410382164000031002c1010b01990803c101000d8100480381011229204e070342100d201c0d01d0f8603600a89224a0300b64440c20407003002c074024400400300007054444917002072041d200d00f5603654044280a40b9241e0750710b44e81c4504050505804090180c0010700c21400400030b50300513526541102d00b001603920382288652a003a048000501442d0485544146841d081142031070401028052001c091001c1489540340c4d2410f11518000c0d01c1d40b10404220000000303903d144c0201c20102c80111000e1496182164588859081f1141510324140356500040c0801501c503040102c001c1000301140200032901c507940d01d100ea10111040d21301610307032209441441036a80d0b001151541403194060390f01c080d440500c002d0003070510512081480b48001035080c10 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 296571627 1250 296570377 296570381
    0xc0c121206090712020714031306110d120504050c030a03021b0306010803071103100c0206070f030e0d050f070615050a0b120a0b01030617010504140703050303010b030901090210020606130209060304170c0a0b090d03 94
    0x138410583740c2890021880c1c1d00b02010703010050059030244101da840c1d09054604101c0040c0f00303400f9a003d071400700c3e0040301800c3e16402b03001041b03120f0703840072005100c031842c0401120705465101204462415803440424204011481100891071400c41500300d0350380c011900f144524925601e2401030811a4026012141c0004500406600c07030b00c14284418000e074010301da805010021035041200c0c503618442510700b5030f00d0365500059420b80401190804a000d00003418924100c075003040d1000b40107800468004142c51262900d450010a09034003d9004501814403020303815400c1e4000c0030b44d07070f019000640d004c80b0303a1f2800f042c00000d0404c0204009090b26400406180345074a0940004110307040607044a40f655070f035a40d030f94010b82c0c5003580e00100b803402d500a41700b280740c00d00400098054414928807210300400c207580c0d4540c2c0d8002180d0303206900001c4a030000200080940d064010721351700480d10702c9010780000c103004141c0201841640040105c13205d845c00002d003101 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 296572877 1250 296571627 296571643
    0x50a02030415150923071b0b1302100509030f010c02030f03040c151e0e0d02090a060306060b07050c04060303090e0c0c12120609071202071403130611 66
    0x8848641c80b52914449812500114291012612804680c58a400d040700444003c1d40412810035410310300313a4a0f03052810f010300d502172090f04200c000c80307103e8903900800c8481410002d12021108000424805d5074005a44082e50040e04005619081d400c5c017411952041d9802d41c070a101344c9800f2200d00505028100000c1d5141d4061402c00c003441d840c1400980000d0021518400301c0c1c0b0020500080b119600845054203070380d4220901815440e00c0d8040b00030340382890402c52801d0200305c094030b40c0809003050583c142e800d00c82075500c461403e00217006a400041c119400e042000841c00320310005012403500030f03801c2d2802d0141460030001140c105210060224040300003c10100c2c40140308a0303405080c1c01101c61800d2100f0607894142a24510302c94286038012880380415840e0722401e590049058680f0b2015080450f00a0300441c041070f0244000b030707000605030f81000900068005590a40c4045039141c000c2c03d014071000306c4e030901130340340054100440c00c6405480010708070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 296574127 1250 296572877 296572883
    0x902070c05040b0d240f0c03050708070503010b0412061d0d1701030c09200c0102040303030e0c0306180709180b09120304110a0506030406061e0612020c0f0619050a020304 75
    0x5009031215000c0b0802c3c0700842c40048225901c0346c010740a410503000f1140790740e40700e90340003441c0c0c54042005425120094840c00c1004400d02c0140801b034421011101036400900741602c0250b02e52030f00d503000e080c040d04034a100c40c00e81e180c1480c2c1c940000401c030304520303d41d031500c400c445450740b602282c040303092102421403c803040301084032003c0390780310480d002510f2892900f00da400300d200410a0348084100c1c021603500080810505515214580108106101405c0c5111044001075034883c0e01900e11207030441954459079240000704082d00c001d007080705052007815150103031140140151441650349800c410001915a040440c00c111b5004100896506503101e0b510340092582c030319100c01d41c1101807000c001c5615910407001e5403280f48988404607555080041c1240404068407014004010207182842160f81049048840034142c20005072580b04042c64280341c450002e240e810680150401d200002c41d1548840300c0320140604c040c031440d2a07420140c0120703c0112006 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 296575377 1250 296574127 296574143
    0x50d050708120a1e050c03070b01050f0d0f061d0708010501030203060f0702070317040e130210052a0c041404031b1a10081c110a02010819060902070c05040b0d 70
    0x700724810004c1095440c5501445c1a5080c0604940442c2c59540900402d030741084076440100b105180400140c50000e00130707500c0c480407000c2c41c0d5416412004d4541d005002c1354581c6140c0c124001484142015902c0100440f00341c0366440030214000c0800307000c140d0080c0a001c0000700409004081c040c010402d907402008e40500e107854015401e4409800d6881c0310004010002e02d00401e0341c00d942c054002c601c0320080301d4015104000072004034004503018070100340080c6020440012503140d01c04140240c45482282540c80c1e40d0500d010b09074031660180c5054001120300105134440d0344502c0c465101c0c544404440380715640c0e00d0420b6a4014001a03034040d8140c0c5480d081c0380c00c40e4006150b0203160701c15980301c4c1211414480f076001c0d51000690b4071051081c01d02e5000710390701c01b0b2081100192651021640000f050030340c0c01402d003420b080c6400203410348204154059401004100d008548440c02c615001a48810503c17a29200724144019600c07035142008504600da5400015 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 296576627 1250 296575377 296575397
    0xd050309061605010204060305090c0103110316020a0605040b0118020408030901050a03090c03080d0c03020c1207050f030a030506043206040612060f06081207061104050d050708120a 80
    0x108500c60b840318090b0410101d4004201000032001d00141001c0c01c8141c4010610389414501e440c03500c813001c02d000f07040509100c0600326210704c0900700c0b80c00000c5002c584c1e0310b040c10914144c2c40c0400540700140b0070b5161104000c28409035000041c16103540c0419410301c5100c000d1910f0990003180034104043c7c20402240102c0d40c007801c002d0600c0f0265007004200340d00607032540c0540c142d55034004d40f06080000340c407143c0300105104252500801d800c046040080d04c080f032a42e5072038411410400c0701c0000410300c09000c002c20203010700303091401c1245c3e6546100c603070013806405c2c2603800c3c0e809141802c0c039403184a013484085014040c40109010400720705582c02081c2c0a101074426034000d17540daa07011841d03480094050b45141d00952022400c8d2910010403411551158400c0742c0075044030b0301c0401d00c0c1051204454200d43c020038042888a4840300001e010310489e0b111950001082000c18200003011419038125a207110a540400d4211900c4e0145441121050707000214040b030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 296577877 1250 296576627 296576629
    0x280f05120703090803040b0105030c061e0901090f08101a06270a06020307020901060809030412030315061d0907200c03060403021b0d080315010e06160308060d050309 73
    0x40240c0c1d000e0110b15000c50020003686680109a10644044e2405c00200e0014807a604003001280d00b007040640b400d52070714440041c40000e82e01c0d08414000b145100040e0010b86038402c1c5001000340c00300604980540d55a807403030070b546c1c041c0c000c035281c84681008241000020504ca2540d000030300505040c1c81c0114010f5180721131441c100b03083d04184441e940022a07601c407140b03a040500000d800542d5900554010031030320000580c0010104440c5101308446240c0100a0700c3c1192000c0c2260441c2c55082d18095000c0d1032000350703209004454410000704103a1200d00c40d180440e00c00305040441c03542c40280040d0004c200e45401c08100c142040009101c0d5091018490200d80b4082e1104d582a41002a04069040c0c50a070f005900c1018000c2036200b0401c422110000102d5034240c0607240c0e03554585803404000e04e080030700b841c1000352080590017900224101030340100391aa507404440401c8140d60300c0c0030401c0d40000c1c1d100700020064104441c0010a0a40101c001e600340203104e4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 296579127 1250 296577877 296577907
    0x3020712080a0503060406080d09090e060403140a02030c1b09100b03070c050109021c020319150506030c09090303090c0306041a100306050a09030e100804110114280f05 74
    0x1340080c6d0300700e590758000041c104400d214100d4a20140d0f500d08030111b103000036150030341d411411300e400c1036000b0a050200280d0092321a541d4907103e2046103403280c148020680c29030085800012441c01062802d40d01805501070342d00d08000b0880710801c098070ba09045900302d040500900140300010004500854021005030070b140d0b00c11070011408101342d17808209210311500d4079111104400455004600e01480090017070301403200b9012410205484081d880c030b60381d030014650540d680b004074aa0f9142408554070109029010f5280f5007496042d565a07a4030440c2d11402c10300407114010841e00d8086201409150003440c0c039040c5035842c4524000c0004064840070301a8044203001000440c81d0044500c1200002c2d000103c540890401420340c03558183c50034416602101e0032440c5940181c0181d0300701e600a0144c000b141e51680050351040701000030254841c00200300417507540e800f000703291a051104526a1741c14100c12006032002040e00440b00d0119009212a0301448511 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 296580377 1250 296579127 296579131
    0x5030904141302120f0318011704030203031302041112071824110f0705040f14040b060622080705010503070933021005010b03100b0c0f031603020712080a0503 70
    0x1c0d509448038120845c0103940746030300400c090410280c003585810141d42e0800e0842c00550903640d0304080f58585927400944a2100400e4900031580509501c8190340352640280415038400f01c500b42d440d0a4501d070301128520032151500010600e08050300d510100d45031040485600384000160112240c1803100c0000b81048a00d00300031006030400008031041181c00042c0350641c028254250410040c00107079104020088603442c102807898014040203a00c65074065040010100c5644030400018414413075800480500c8458811240c1d807840c01000640443d0103103421100340c140c0d05d900566040c002211250003040c85200e041142d503a01100800ca01100000010848480c00c17903804104400b64008c500140e04c507980f4a81441100d200340d9002d0440f0003032a509619201041482a003a64000d84801060106602140704000c01c4101460103400c010390b0b0701c0c0c0154200d038089000800c00c0c282c0041c07040c3c0e4000543e8180c1c0d045106002078200c4c8800786840c2607180c080d12544c0c80 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 296581627 1250 296580377 296580409
    0x2041503020304170f0409020903012003010602150601080c090109030c06031509200703030603150f0c02160501050918090a020315060d110f0a0602010c0e03120d05070c0c0305030904141302 83
    0x90350120cc0b80314404058400d90912807841c0349480b5418160003e20f0b04194400444004405106100440e0780200d50f450b480708500b481c00ba40d400c0c400700121240c040941c0000c0c4440780350f14010842d6030300754102c002602c000d07100c030303400441d0b0310800181620410314201100f003660703896000c100c006070001083c03064000d00f40401d10b181d507035540c010001400d02640717070b03001e07034401003012012168011120401038601c010915a05465901e40260009100e140d050000008900320b040c3c40b078441d2008880038003005000c041c0351400340a0349400c0080c03c102c2c424040c0071455401c00c0384040340b0900070301014000c0455580155076602010750700c00305181e030001c100b1601e21941d50b101e02c1140060056980003240b03290101d80c4c060300100e18070f070009201c0c2d00000781c00064400e8400585d01072441020001c170b025220400180c1d1b10038900700e005440f90050741c0700403081c84070000007030603903200544080001051000060504003002d596102d1000514100013000d407030844100200d801d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 296582733 1106 296581627 296581631
    0x140102070e070e1c03080f040c0b0a030f0509010902011812080d02130308040e0a0e0a0f110307030309170105010b1204050102041503020304170f040902090301 70
    0x18500030400d00401c15000a8a42c40c4100b441c00e84500020f005459505065410540075804e544819004100b85a0200f484800c900b511144101c1d0010015070046041408c0c46a007030380141000410103440703ca0352411000f5070b10420340507a071603034000030300c1800f00c1c4005005107040c045042d8000d015420208684c5640135900b003403030b9038804111a0b0702c0801c0c00c101002400f0303007013070340444002c11070022080156080080c0180d80d01003441c00196907070f0813079800075200b140140251607080700000c1c0c0006040224008401485040c1030281c5c1800c52021034500384e995032080e00000d02821003040090900034a0310b9411304407000901066041c1205981c240c41141c1008400c0d030740ca803001030305012003941650050b0100502c9801a000ba10780018081d40050350b007a5107030b01c0d420400d00348800e401c0040f910301c081003050190400703103000301c008000d400c0b5001054041d5 = true := by decide +kernel

theorem cover : BRFrame.Cov 296402877 296582733 := by
  have h0 := BRFrame.cov_init 296402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 296402877 ≤ n) (h2 : n < 296582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
