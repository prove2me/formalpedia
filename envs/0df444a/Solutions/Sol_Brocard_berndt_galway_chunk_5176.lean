-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5176
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:59:57.033565+00:00
-- url     : https://prove2.me/submissions/779b11b9-20eb-4cde-b6f9-286a0f450652

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 930755395 ≤ n < 930935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 930756645 1250 930755395 930755417
    0xf070f140d0608030d0b01140a0305130506070512060306190f0e03130302180c030a09030504090e07050306181506011b030c05060c070503070b1906080715030c0f 71
    0x84400c0550318854004001005090b55071040079030b6903032180707860951035410301b80061029070240f100c11a1a20300c0282e000d14011100300c0860040400800c80c540b52041034102c02d000c2101044014031581c1c89440e4555282116240d40c0300741c10b001800684654000410840e000c180000b6884c10145800004181c07640800e400d0006090a2041d0110a10020985402c51350710f540100040307030b0003a26030034044214004000014031044405280301042080810200002c075400640010b010f03180007814151188000010798441c1c0d9490811544508010b01003071905010359504040884210050350101110060721030340541e2440340c152072481c0c0000c0c2141d01403111108505110900005054010f1802900d07098942209807803501c18040003951203d84c050488003902d4008004606041e4950f43c3e080c0c030b0138001015078041c1d500d241280e490400b214010314001c0d100d503402030140b0b80d04102c12000140c5407040107070201030415107482411034106004082c0444685408040d9070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 930757895 1250 930756645 930756677
    0x303062106090819021c020d0815040b1305091605130f0e070f0611032b0b0406090c08060301090c060f020a05070b22030c05040b0d0209010b070b0f070f 67
    0x20091302140c8030b10580701542c0a4101303038086224281041c0080f0b408425950002040780d40e4611110540b0114050350046800c1100b144660448880000d0011644040c10b2010031028500d11003060011a221800c2c4104503005000741d112119422202100052400f8002503010150040d4200480e94601c10342c01c0c018080d4002d16050107d0303408644d1800d684400d4080d003203401e4803428002501c03a0451500030140801150f0100c85003540b00303400d6038115510422041d060300ba0066004c2e603134115103400b44d10349000b00802444421400034010304190030140c03419030001c060f64801c1c1d1400343c038100051860481441682c8080c5080207844800241c16880d060f01280040d100340309600c40015034a01c110010b20f00034030030403564038054080340e00c00c1140611500004000409010b01803066041c0341e440420201002824a0840001a004150806020307001140e045000044031803e00480c140c45c1030308107a10080d1511140380400c0000d114100590001e4100141841c0c41c1c0c440c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 930759145 1250 930757895 930757897
    0x90d08040510020d0210110d2708040503010b040204180518011a01271a0f0f041406041d0430020c01020102040f0e0702030f070302030703030621060908 67
    0x1030003014000601c1080d002c80c0296454a006821000610901840d5072088105005141060440c185210709201641c03143c04050010800202010840200340700800e00012051281d00c5014030812030761541000b085c907003506d10b078548050003a40100010000c03544641c1c118100900c00100015494032a9440122904011420000c581d824104c0f4983c0916203c5526809010240c0755128030081154214040c00c1c07641d8003000e4107007102c1000700a03102a400404403103401c040f07400303890003104810407445078110040204420b400031605120140e100075800e00030900807100fa500300b510b0003601d004018000f88141102c0d9501c800803404001e45940400218074502800007980340302c041410300980b81444504005100d400401220f650040c0b003140d0540391508045c210090514440258803680941700074110710041103e501c84100f020301406940d4400d90140d5a981802d040040594407643c0209410742001c030f020b0f410350030f41c603107440d16200d90080c808118003085043c500b800d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 930760395 1250 930759145 930759149
    0x1033c0c0f06030b1305010e04030e04060b0a0206150a180b01090b190e100c17071406010e0a0213030b06040f0f1d060402030a15091502030403030b1005090d0804 71
    0xa40e000601c04142590180c214910203002640e031840d0701301016034000305442c801e10955203030741180d501041c08207120b1504214100e00203040420300321740d41c144c04040d1781c0c40107000c00c0c01600407000f40300c2c1c01c0e14540140c4481c810100e400b1a0750783c2c00d00388025044202099240704c079503501d0300208101e0f4020040f4070001c080d49410365031660140b00a52140c0c01c548240f00c00001d01c0c20802c04040d03e0300c0c554480b4a038440d07a0711040c0c40002c981d140000d0041d03140240042000c240402000a034003088000382c40030455015013015403402603c8095003602074818810b07580103104014240000309032410803650007a486903010b80b02d0b0800f14009000b541d50b81c0b00240d0070400c18182d54102d0b500301fa062603002002d0f04a840d1040c442c0c00b510750700140c4000358590072401c41607000c00c90180300c3d58505421102d00041c203176800c1e07881ea10400080c5410144c0707150003000300300c14550584a002240d035000d807001c0980000350000100176100b441801380c858a1998001c50038080b814042c0c1e40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 930761645 1250 930760395 930760409
    0x3120a0e1009090e160b07020f030303090106032102030a030513020a0b0928050907140c060f1305070b030c12150a080d0f033201033c0c 60
    0x80c5140d41c441c002d010010500031900c1c41420640000200c20b00041e003061041c00050000000d00e040c0541e0303030b041c1d611a41082e40d00c00300c002985400c9a80502c0154000d40f015030000841ca0f00e1490401c5203d5189a01c80b14070354100003100081c241c001c422030f0300581203450300151954450080410900511030081d400044032500030806608000080c030980000b00c40b03540301c0200b210004032143c6210051044040c90168080045060203000650040054284104040404a0140000d0700600b42c0541d40d0380c418000c0c84000c101c030042498100f88445021142203038580c0f5895502c41c00d511400ba07140900000003a1400e43c001e0650750000070500c144003242c01c2a882591120300c0a52440f4170842241500041a14001034110f03001510340d00c980399280c2960340160020310703545c08517404004442038078040481421814003440031900d4052541035066042246c0c1803083e06010303c60b610360513a100040c101880011180c00c409503070f04144100c181c0d25203141290f01d5079110403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 930762895 1250 930761645 930761659
    0x3012d120b101203020607082a03071713030f0f050909040804170709060f1811160803041703130f021801080a0302121305040f060b0a030b03010f050603120a0e 70
    0x2010385c003090450142402c1e99640361035486a43c0c86802d807207400c428607002144030380f00e02c044850070303107000d1613100300e035420401c52110700c072242119030750320464038802d010605810100816820514429081c905480c08031f841d40380501001e01244280001c4610030300000001030100280701c01201c020b45007501d1084180502406401e540300203902610798030341d050404c0410ba01142003003d01c12103440b03102c9000c0002e0325071440d41c02055203c80e0142002420440d240c2c41c14100c1c1c460b00c0003540310f65aa80d5a900d002c2c100300d031144500b4801c0c100c80640c204144591001400c02c5c0c40c038440e40214480814401d288006809590010380e03107400d000410000241050011840003201c50081d000c1d901203151040507000e03507204d8607900c0264040084018402c1e030800303501492901c4204040000e0040d12100e4a601070742040d1070b084000b9031691060840350a003170090044414090030103003c81c2c289200000c0c2c88100a07251080c0c41c1d0008600c000c045841807040180030f0340054202 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 930764145 1250 930762895 930762929
    0xf040902030a050f0304030524040308070e0a0b070b06090907061d100c150204030c18090c0e0712050402060d020a0504030c0f09050705131e030803012d120b10 70
    0x1a05c2e60040e00c001e0b03079030740038030101904140308800483c2c0c2141d88414518601e0ba5450b1303000e803480040680000f08000c203040d03001842d500c811310380c00060901c0703890054a0b8006031600c1000c0682c0200b826000c2c803144802d000e811171b00014000c050750700d50f050a500010328800e09940302c0e103440703091f0390744160100d43c00003000303401c00b2104d44501d00460b00c64161004030400d5100341e01c1184401410f207440004200000314440795402c02c80940482d01054400c0307a522080d008100c150803281c0358a01c14018455126040081424800c004800a100a16150f000952640a60764940660940002d03202100b24400d4046601031684082d00030741094540005200c012141c0c01803000c0f0518050104101d28060070030b85201191483c0d180380005d0400400504800304c245c0c03816400490380a01100042c0048044c502030508017412030064402c0741c1e5407004d00c0f44440304030380903c2011a0b050004071040d2101c503050b141c200001c2c0101e900c41180f0081c01d444203a0000c8000c041000c10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 930765395 1250 930764145 930764173
    0x509090111182403060918010504050f010e010606090317040806090703030f0806031e0f0d18060e030a14120f0d0c0f0207060309140607091706060f040902030a05 71
    0x7011801d001c09035501088031030305540b56640f034404404401151030050000549624020000d154844c2441e1540c60001c03143c62001401e480f01900c00b1901c43d004082050f440c50001d00c90b2901400c00d031002071200d0f030f181143c0904090304034000a000c5400c100e071401d00c81000001110001e017038440c2114500c1c03804010035501e41d034003404224000b0302000c2d040c039401849108000e000d51001400792415040b503101c4401400c1005519071002d014542c0220003c500520580803100070310341710482c540315107072000c29402e8840c0d00328034144620b80e401c00903691000990080010341c003e641c2e000502405a000c0c0c07801070180e11901c43c034a40000c8641031143c0e10300141141a44140c001d21041030700d420300f524001c8006071000b0059000702010070802c1d05c0f03034000c841554003d41941c1c0e400700c02e10410314180381c1e088a5001c00f0400c418820001541030100000304044281c0181c40c42d070610800192182001c0d000003031065444441010039903905100c40549141d1003811a04c0b10307266000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 930766645 1250 930765395 930765427
    0x11b062a0f02060a09020a0e04030e12010b090a05250c060207350a200114061807081801150315061202030c100c0b010602151f0509090111 61
    0x321510043c05401d01144501c88207000e0070340300580c01031990180504060341c0200d04ca00007041030302005503461981c001c540720300156110a08220303002080d0580418148203500402800b0140040e00d041c0400c942c050b42c03014001c090188203036900601e14000201141c00d102c0f06a005840b1510000302c14081042d0a12100c0c0d48588611000d803802003550103483c500c28202d8074105450500308405516944141c035581004203007841e85184480003400400d00b1248100790501284140005200300c5150602201510098404440c6d40318a00340350000d05011000e810546230f51102d070401c42c9035003801c0d04601c1b10002c00100d0040d034550f0b030f8140010201c0240350186040780c90b20b074001c2080e0303d1801c0441d56090f0050010300f011300f515824000844081742d1160100101c50b100350000a07883c4400c6c0740201200d5004000240700c4660b0305880c09000340c81c080c1c507480e80c810f00401d524202996101150300c204c45c56203895032221905405030003a40d0000013041300c00503a444020030300003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 930767895 1250 930766645 930766667
    0x9031209060105040f180305031306020414150a02150601210603021516110402040b0301061206052e02030d020a03021921020705150411030c011b062a 66
    0x90b01484148044d02245d01240c22042036003003011414550b001c0401d003c3d1004640100c2c295100401170401a00d0f500c08036049500110301c02c6003030101010355807400000400014a00d14002441c0c007101d24000303551016003045c00c240c03800c032400005007d0380c011140c542c00350001095002e481d2501c2d0443e040104240e0000728071480d10406620802c8039441b040c1c07020050402d04542030400c83d030700c502034014402d91a2641c026000c2001260b64440c20f0040d500812040d00c54014401c9072003145401c1c1d41c140e401090040d41c40c11001c64640b0101609580b030440761a0002240c8808079208904500c036071901140581d00000d909444140d043e40105406030440704011200d02c00150205d491804110307140c5140e1401d1310400140684550082c0380c1184034504565080d080803004890650307080310191510b07815103001c0c240606003070001e1078441d24246800004d01c40c2e08500c21000001c204406484160740b1110358042d0b042a48940d80c42c887e15038030050180b55013800007081c030b0040d5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 930769145 1250 930767895 930767899
    0x15010530010f0c211109150409020c070315110d0b12010e0d08090304080a142a0f09040302060a150b03040606380c031c020307200a0b09031209060105 66
    0x1314449650030101c1c1c1c4540e0802e428424905807400465204200304040d40c66208050b07400c013004009803c040300c1c4001c007a03103c10500501007184c80c42c20301c601410b541845841c241c60030130004541e2201c80c4801c5500c002102ca8000501c500041c012402d000004090502c1e41d43ca0100c2180346000001024400e40b440c81d0b03a03428840d030700d12010680b40c0c02648903003100c2c2d61206403070000040079008a040c1c901c040400311038a60702100aa013040d240004221343c1080c0282103080d203141801c4164600c4400d041da21721905081513507000f0340e2454000c100800d1186d445a201c040701881b55000801426542a41916070030a4242000204018031600c1c0c0e10080030682010702c03c0e107892103094019014480701e180440d81c0c0c5090311880c0c1c0140702285190104014004000c081d045110303040001000d401a107915100b2405011600c40c0c610154441050500100924800040e41d00d01d8a511018070f101d251254601d0501d140942d00142c407034030110908008168100017044c90407a601 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 930770395 1250 930769145 930769187
    0xa0f020c0d230711060a11060c040906060318140a0f1a060a0303020c0d111e0f0301091502070c0e0408030a060e0402090a0c020c0d0515010530010f0c 66
    0x2c0000350040074460100c0041040021031082d18031442c2920113480b0050103403c10440c1c50301003d0b80f90f07050040489881c02e2001c404a000c0c0400c181510803800a17200c42c1c00d040100c65083c010540f0001ca0b403150085c107401d02e9445450a451052207419081d9903c8440600d03020203500c0c0400c40074058180d08401c002072100060540e14044d00002c04a0741c0503000b80c000b5240010078081c603500b170071200703446507014031004120036181c04000c082480002c034000302d5203002c0d07041042032004868810a220341c3c18081103070041085a610011106010790380140d07141e501d464410141c00070350344500c00d5014002c040009110f040c6008510402074800104049a2101c10000c0f100b0802ea50181d0032204040c000356014030241d0140640078501d00445540d82c1407040010ba8000d80400c0407100d503004400710030607246a40c0c070500e01600c003c8580c0107503c3d062840c3c01c0f2441c04030b540300003540c40007c260703e04049400c0d8404000680da841051222541a4001030140802d54540800e00c482c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 930771645 1250 930770395 930770447
    0xa0f090b0d0c06050c0307020a0e0a0f0c0f0c020301200d052a03070908070803180a060203071e02061803100903020c040b15031008060108150a0f020c0d 67
    0x9000d01042a04035804030001c101d41e4140081160117030407480200c1d00c944010800c00001d6035400c3e00c408018101c0140200300c901d0981ca04905880d03902080e0b1030201c0c180310b0301000c4a90080400c0d80d82e140c01e450301034010241800001c0c0984030404aa508107151901000148a00d04005100c002c0000380305004c1a15000710780703502d807410007607050082c0070a0840181c80898401c010b503002111031402804094845041c1410280c140d4080c030007503803000802501c0c0941108000f040d03d1030449640811902d0044040d44a100350380000f4801401e4049a42d0030309114204a03820b140c010305a01d0301d482c0c3d1500d03104d0082400072000c501c240300b03040300156440590b0007000d8000740d141d40a040c4481941c01444003428056a0700c0c0c4d400790f61541c0180070b1402d20005140b08980f20742e9408042c40c640000c4904114041e0008445034200a1405064849200301950003d2801e10300040700742c6842a0000207020301150114280500c01f6030010f5142d02c8011901c00d0308800401c00d40c140 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 930772895 1250 930771645 930771649
    0x70c080a1a0106210e010c050a021b09011a0c1b092206020c030c1609050105011418010509061902010b120a02060f0702130903020613210207050a0f090b 67
    0x3403400d20418002915110083e251889152680602da541e0030501041045d0800030030790944e0660b560180001d400810702c81e192550400c5200c1207441ca0090045081c1c4180001c80d0125005000e1400101d56192080500c88140001c0340d4082c0501c1c1c0030b9424000c1c070300ca044014441020b41340e070310804102010460012030035210014003541100c04640e4500c056079090041d4124900c178152600050241d07601c09d1805124000105372070fa130381101c040c1d0400c00a80300b200d106811a904000c075000020000c40300c0501140c01098203001c8401d041c4083c10012907007071044543c525004400814040000440b11140410708201900280300c0300002c4420f111040f00800565411603103c0b10a0b0030140c00c1c400d0007005617201075141c8070719140e02500807500b880c1800c0069801e8640d0f9548080525a06101494111000e100d807003940d540e0645850f001054001e500d0110020180ca46105140c020800781c03000b0a0041c0c420121583d82d002d0b502a042078512619514030300f03181c07010f1094 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 930774145 1250 930772895 930772943
    0x40210080105010813030509060d0b18010b070303091106040801020d0c03020309030909040c0b041e0b090a03110d05011a0301230c0a03061a07050c1f0c020105070c080a 74
    0x103110306a4640b1074070385c1d510001c017913140c1d0402d40540920004100c0544140c84401c0200b080301c40c550130101c5c044241c03105104181d840c4010640308502c101c0c0061100d0035401c421502d409400d440c0c081090550b50130440d034143c852441c5154010302c0024000752243c419000340015500c03a400412038030030468030903402da200866008116420820412240345840d907010381c1c00a002c1c080420140e41c0314154603015034455001010301450749010004071446550100015090240802d820015a030313000c10001145400002c082d8010610582e07660f07246c0c401145c43c400d400034028848a415244800304680c03490300c01601950030100c0f14480061300a9415400702045e250001041d6207059406410390000b2902404040d15403500040e240885803078801740d420140d440903501d0120389040c074940032101281c4c501a0341410009144480000790159400c0c0190a280d010110240300480301d9200784440286000000b103c040b40e030140005196007414490240d8282d010202c1000ca450 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 930775395 1250 930774145 930774149
    0xf01092001081005041d01060605120c12040b0402180a1508060f01030602030907080f1006051e1521010303020c0d11040908090d1b0f0303090902090a08150402100801 73
    0x9003d00d00804011500f8140c6c4601204aa04a000c40c0b245030b44010081c20340752181d00c4040015000328108150b1412202c00d5500041000c000c1031404143d40c3c9030b0350045030010405084001d510703002a0540d2580907450084102001d0001242d141aa50641c02010240d0200300f45108070040400d518600103079040c0258154a0500940e82c40c1d90782e510007a5100030300100305401245070001d412142000396044004411004d46012010f082d444001c55006502c40c512808800c0d050480e900c0d4082032031980c4c0001030307030056002071540840c09520700c00c3e9141d2901714604940c4e035246da20044161141078034465801d9840022140301004284021864041c000b00c0069081800d07601d040d13403000701e400b071180c0d681d98140019000040c40b0840c0c040403c0e0b07250003804149101016902c501c820142403001c0b241c1c050b2509688000b0f0a0030740038014103d440ea8001200289641e0718400c0000501400085540e00704440c210460340c41d00070350f0200e016190070f010b003200d424018921141 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 930776645 1250 930775395 930775411
    0x406141612110d0302040b030a0903030b030304032402030402060702040906020f04090509060106020c090f07020c090702060a0b03120a0e130c050c010e012a1106072a0203030703110f0109200108 85
    0x8c115181d10b45420010410000d00b103050654445000b0000c4c0c03018006000110301940c1070071b203404a40c4804104146041c4200f100203132041040100507503072101506c0ca82d94054070005002011407a088000348a4269040e8656001050000d0041e005800103441211110290b801c140da880d80180d95401b0780b80603142e40503007154001070700101101c40443d4031a85500c1203172244109030b0b006c40c00c101810f455190041c1c014100300b00610680f170044100b0820250014109040d410908000e90702809140000304a81c00c01b06460950b01c01d11481d46c003070800c0c1c104200003442c0210142c5580c0c46041404165400d0416040f603141c0d0600c2521101101141340065801d03855009913203009080c2140da0900151082c07007060303460100700c421b00c11501034582a800c05050001e194130015140601c40100940e0010100140c07400b205440015070701d41032800800d020002110f04140c00c2888a003540d629080001d0103010b5441c56040d01d00c0000815010000c0039100116805041100c001d4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 930777895 1250 930776645 930776647
    0x60d0c030e0c060418240302010815031f200915040e01050636030f010204350a03021605030c240409050c0714030406141612110d0302040b 61
    0x4040210448043c200d01c2d0b03421800a040e4440300f4014032600030700c01c6d00307036110b0821080c02c0c021540c01c00005c0da00701d1580c0e4101010074610400190355000340368400040c1d02d10342d4034000c400110300c0d0008007984c00c4981440900340504600c038001900044031051141c59400821440d03050640115810394405d14410a000c1c1c2c01c00043c418281d028800307180006400f4104030b0900894401c09008004644031074100c0e41c0a98420117242602e00c80b00111140d10401040192000001c164055180313400e1928880d00c0704103040c2002c0128410f250100c0d8055654003408055011898841c1012050260303c4c3d0f440d210b0090650792038101c80d501707402030051541c1c0d0400c0046001c0c01d00013450647d03c010310b4142c951845c070302512010340320685188800b0409404211001d0001040300f40000015801c107441e01a0041c403031054403106c40400c4000003482049881504404250260401851021245504002081c45039a001d0b004928010403910114582c81380c000c450031614046091 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 930779145 1250 930777895 930777899
    0x120c06181415030a0f0c050906070b04030e2205070f0c03120e01060f05040f1808070303020409060803090f060a0f08060a090525021c0507050c060d0c030e0c0604 71
    0x560300c12820341864651005006400314400c1c10084000d44c4039100b42c0360089943c00c21911130350300f980c8049800d801880002e102c00c46580d11134109603140c1e82d40000c2400d03500d0701c0741e04095500c00d040c02c20b4903800060204951101c0300560800b01e40c000340c000b108205a5545880444104940040000000f881c2612200c0864415410001c4824180500040d12001665810b007144d80691011480746130f540c008000300d162a04c039901c43c0003402d801c140300140c6141d141200c40032014000510802000c130340f00e000c0c54402c2c0e0603180030300141c020400982d0b07242c6404a50300d03000104400d128082c0608201401d080c800c0c1a03601003e242c0c3c4651004e2421803c05a80324071006050f03076013000241c00e0020781150107005032070140660900d40019246582034981942c5a000c001c0819503000c0700106030452a0016002d04290b91441c0081d243c20840ca8410305050058085c2c0d54442d901090b0b02c0202e0b826607000525070321310354408008203030303010a40b582c494211881003a8016401e11003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 930780395 1250 930779145 930779159
    0x50136020c2b020c150d240302150708090105071a0a090b090d050d020a0309060f14100807030f030e030d080a15080a03140c0601030f062a0e010c020a120c0618 70
    0x10788108100c1460124201c00c80d886042d0708034030707003a103c7d02c48118401000c01c15414066008040c2042d94007882c3d1404880d46c135040c2040c861050700d1410044001b60050500c0100c6041586000001002050504008080502412900e2001d40344080304101140c2c44450005d00005145201d03100c160800983c0784082d0025041000f025080c1920741c0c01080c0010350306c0c402c081e1f440092180001d14081a40c2088103071550007014149180c08014081c000388000003103010450394400346c132120741800c0380760440c1e0311068100201d4251043c208441c000580000c0803d106122014041002c4084886188007008540c810314000390050241b500c042445002d002c10b8540c80c401c21140790a1042c40c016240c08402d80c0b0a4808080040c00c02e81000040e01505500302c0c07040285440381d8500d01c140504102c143d10ba00d806001143c201d08082d640102c051480139500100f40003139140d951200c0000a035070b00141204d03405030b8910045051030107403840c0c4011f0054000c038031408a0070085 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 930781645 1250 930780395 930780397
    0x2011b031211070b090d0f090e010b090103091a0916061b061d030d1506080f1008010c020c0307170a031119030f03050136020c2b020c15 60
    0xa040084603400c204103401304800b880c601e405807030540c0084c903030840d07006d800401e2280d202c2125404c106071164200030364400401a00d0540702d007441c1241c0c0d1240301200503401048003a600511f107400080d1003014140301030110502c20103100c4140d881850386503003034005060792406110003040c44c62a02290501185900800e05403051200084000110721401c41c090b20115907421a6030002035140900314aa02442c1c51684a800d40c0115042c202071000c1d04902e801004070b107a000000c000513031846c280d15410801000044020020b80d680d191000391200c00307030540c4502a00c00c1d507200080142a00e1400c0c486560107501800200c078031035604039844c081c0c00c0c445280e203209036050145054840d00c030310340d24984030b03448850640d860b5001c0501914030580c041079601c107900751038080300900c0b5180001a01e0860140601050302c00551000074003d011181c895442800c852035141103040c444070324141c03018214550344890020b030480ea9030980001c80c640200d1007507090310788400c3c410 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 930782895 1250 930781645 930781661
    0x503030708030a14130c15170a061a070b0903070807080f0c160509150a121707081b010605060a08270d11031e090a0905010306060302011b0312 63
    0x440081aa0f0a42518503290301308103990210300c1c40c1d000d0312036908100740c1c807030b02c60000d14114084091102c0d4003d006400c2030a02c8205440d803c07002c42c0000c100901d00e43c0700c480a413078460100c40c00c24a000210919540206074125a05e8a5000110308030300800001d80c6e08481e44070003100c1c80c100b002d598040c0d141c0c1100020046006092122200d40c00c41880550000d861100b81d4020b41d91511003001020790f00a4800c030602500800514640c0c1c54100f0030320242e40030240319501001c0c8502d000c81000c1207208c5c0741c40800038003140d500204001c1000402115400707000381c2d840c881000e0001c80c01c0b01c011f882216440142004081001c5d07001c3e0f6040741e07200c2c4d0f82280030aa800008601c82902c02c00c22900154150046078180d030b526604600000c01c480e110100070760070020340c0d4010081080f11130701007480d04c05c8082031900655442e5889500980500070081c000d650307591404201610450008901103640900c14640d503003034580200109039059656170810b883c0b00c01c81000140806 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 930784145 1250 930782895 930782911
    0xd02010c050706080406180317100314060702011d031606090203011418010905030405120f03161e080d0f020d1401090b01050301030503030109110706091515050303070803 75
    0x11401200400c1c0d040c04850010880d43e21200c000b40303054030703112080390560102071850400810103200400ea22241070921900d1300241c0c903805854070800c150302580351b50b0004015501c0009461030044020400c140903e00580003808207101807001050741c421041c102c60308540c01440660b400000c818a50074440c1e004510000f40202030340c001c01d0170b44040805a441e01012003052240010b4076440948034001c001008002c4400d29982e201d80300e11691207012300c51803000c2a0300c4d440507010b0003900104110b44007104c1d1b840d00070115480c12800e2040096070030842200d044181245070105a07011541d0214040340f4083e040d542240040c00740400e070301d0f041a42030203040800a11441500107000368198125000d6140813041c0082c0da1943e00003604001e0305000410019400005690541c1c1030b4080104490340d01d480076103201c0c021408081c2c006070410300d0407003d118060842d440a0616000140700c410205170045101000b10712a05400d40d0041054002045814000e16040059 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 930785395 1250 930784145 930784157
    0x91a0f0405030f090a030218060f0a0f09090602092e0e0f060a0c060617061003020102191a010f081b060a14070f050d120509061303021903050d0b0307050f0d0201 71
    0x8070b8008c2210391450b803151007038250801c400e211071407400c6920070043d04001c035241c0d0300c418104424209211040d20800d20141c1d11030400004001c2d09805580381110080d000005a10864a00b2100c0180c0c60049580340031200300c840e079503544a4404071b048400003400050b110f02542d0b003800084d611000c0e52000304440c120f2034400141542c01000010101d0340703070109040030394004050925901411900c2c4040b00d0034010401030f60085501e079000140082d0420480481c1e05010400f49000308003210051860000819010441032880044d1640a400c07154881c18500300c0c0c00d010b40503410400e91180080c0000301006101e030110351848406200450305002881c0d1320400e6011038a541101d803a0055140c14035010f50011006c000043d91072418046401c00f50720540e21030324040d14000445440c0990441854020841000c0b2089542d000900c111128107000307100c0e42000d001c41c00d0b4a4200500b24405180c0000c02c0002c0c1e4200502d500000541c0204010b0400082c0c0c60403418818 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 930786645 1250 930785395 930785399
    0x804050606010e06130f14180a0e03070510050f01060201051b0a05090a0b040504180312110c0a0c06030b060702490507050d12030c12091a0f0405030f090a 68
    0x4458112801010181b100e01691401c00000403180240381c6103041c0540018120050705101c02110710f50080508038000440c03d00410207641140b01d6004040c040d80f140382d5289001120f01d038803042c410107210750012001d0340c0b0f07a10300b2030903904151250355003483c1c8001d82d18001a44100289800d50060604900c0c1210315000b283c0306440b03690200351080c2c80820200404d06081c091403455103084262990034070625a4080e0800841c1120a4011540d61f010030410414440c11200942c4030841110511034161904070720b400c41c039000700d1002a0030501c4135061810020f055407180c0b0760007011098100007148102c035800e58005441d01c1ca43c1c100009140c40801c050200c1d41c220300421000703180fa0071007803c08518016603a80036a01070383c100341c00c64020900c86c409600910b0410729000c6018440d161003226800710a2804404482c80c24410300104141214a0b04003c10b00701110881aa141c0c0c09080c9400421500501560001c214028000b0300d00c1c001000d0304000100f071001341c15 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 930787895 1250 930786645 930786667
    0x20303280c110106060809070b090a0b030c0d0c0e101211070f0506060a12020108040213020d0f0605090907170f01052806080d0c0606090507030b09070804050606010e06 74
    0x24607030007498010486550460380200028001c1c08003609442c14045800d0401d0800b151390b40c0a10b210f4003100b0540401e86200c82c0d6190b03003842006101103a0103075102e0822020b03022290b4094003030303e40040d141c201c0d0310000c035020340710541c02010001c0103029030b4030300b582048c0c81c20480000c092108030394a00300140e01a00354009800344074040c0107480713440744651914500d040e40242003d0b00ca80c040600401010241c8100841340079070a1800700400d82315407011406e144038001c0d50110441c004605252a01c40d50b500c12080d00c0614101400b45030343e07074414080a15000d030b5a42c0c40310f4100e00c005200c8603008400303612496a445007114550750340700e011907007142c10a035001000900341b0682c650000d0f46d1507206100008007184200000f601e8420f10903034a003051b10f105000d00281c0c0b2511f9051200135401a002008030309420320580c504008000c005001c1e83c00b07428445c20041b0003242c0b51500c140c0fa981d1107160b20800400d41900c40704010f40e140c030095a102035000c01c00700401d488e64 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 930789145 1250 930787895 930787901
    0x5030d060e0601020d090b092205010801020913060f1208040b0c0109110303210702120f072603040204050a020c1b1c08180d0b011e0e060102030328 65
    0x800140c0020a0070381850740c0024108528440400100104428203112101c0003c048a000040484014003c000002d4203442c50410500c1404042032030080000749081c0d040d001041e04d03250840340940901d506454802c1201e40d98064001c54150740340003880064450709102e413406006060507401c280c0d550203020555840b4006498250351501200030400c140c02074800c40d941e108a000e14148000450030b03006040404580e581c401102c02c0200703400c54001c2c0320181c510003605401581c0c41842e03d940901680c05800c085840124a9020f0100c0c01e030881c000104d0b00303065103040f51954540b07400b040040c0070050212503006030708006400d245070b02004500681c4030030b070450344a001d01140402c003c101040d046840c01e05454007a81c0b0014122500f00e03001000c14038038800480c0400808100d0b403a60700000201880e1a6900200c0c1070104141c080400300140e203038102c2c00a84807801d00e0400c000a42300d1034050383c010300101d0b1440010002c1e9140c8210700d10030210004050035080c40030307 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 930790395 1250 930789145 930789149
    0x30c0f0e040f060b1c0c050325142101091808091801030b0603150903070212030903010501170c190902180402161b121401020f0315310905030d06 64
    0x301084014804400a406c1c0a40500440780303003000c6c0d00b94540701c0c5d5191110400c03420420402184181e00c521102e001c2d000010524220b0403242e502c452807101034401080c04000c008040e0807031100002940e03003060080c550514070107012a07120040581c3e46c143c942e04022100d50f44050310744020ba517030441001145000b9130141d100c20300c030790030054185420111282c43c0c5ca8110041c150030000c000100008482c517969043d101c00040300d940c40750050650181d80d1031164554200030000808241c010031689100c21920240c0b020403141c0420828009141c4e00e0000c0920304401c002c00851080398080e141691191000c28212501200014100e034401c40d107e488903c20380518009024455802d00004100d003064010340f81d00705008886a01040a00140120001404000740f030a0a40655076915500580e0b2520b0341441c08202c480966400000c40c013450080b50711a010004000103503c0c4400c2c441c51160107510407034031920246c602c0c01401e4545120404c80c1400040b824494900 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 930791645 1250 930790395 930790417
    0x1318060f0c03060b09190312020a03020d0203030105010c120c0c060306060e01051804020a02030d142d0f06150c010b010315081009021807020607030c0f0e040f060b 72
    0x21240d4a000c005021500881c412104043c504081801045624012500080d401301d42000200e60b481d41d064002c02e5807900018000280060780062298002818040b02132080e0213648284031340074012aa070340024802c0c9400180406201004035016200b01010f81a191804000c2c0035088e0b117075003900c07101c0303075121900280e6210030400149a005940099000c000d10f071803842d1010f213011145100c401202d0303031849241d0000c0d141601030b000700104c030b10740019887c00780b158203000c10b008400600112640f82d0162031425001110011314100c0d4040c0304030319070048150791039440030740040010003414a50421081120107001074800401f030a44500e0740000400d907011900001000c2e1480240ca04419030502c400611981d200410b0032000b1040c10080010746451600000725031200411440d0150403400d01032060f15503006c40c0140c45810b86840910210781090411110340e107000c11481e00180d14007107417185500e403075080000010f84814010620a484205040c6940d0100788441 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 930792895 1250 930791645 930791651
    0x30c08070b011a090f090a0b1f0e01030504080304060c0203130e011a090114071a0403020a0201200c01110109230f06220203160605090a0e01080309131806 68
    0x301c040030001e081102d01c1c803482013420146854041201608051604da00c505026030020301000c0342e0750f1221901113001001f2896144140b4800c510b8041050006800035241c900002c2955020b4040e044c061039001003030a255643d03039142d120040003490100021070200704115000c3c4004031030814081e15403414041c00c20351400c800245c1c5003090221a01c4064001d21010b01280c0c0c02510301114100c1c4070801070313078416440c0303001e15809503000890030b40f040b042400d01043c1940041c050f0303203e601c00c1c0c95002018998245a25850140e501e5001141e0722401c400305603540701e40300611256640c0b0f400480d00342c209682e1418480c40d4401180114007103072520b000b01050402600e282d82030100c0c040c0c0081d0403c011b4015685e8072120b24018603546481c4100219142004602c80c000408061060343c2e541320600107007583e1080181601c02c0503100c00214030506510125030407580500000c42c03415240f402070100000c00d0400c2c0040b010358803140b02c0d0b5600700004461340044c0c4a28000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 930794145 1250 930792895 930792899
    0xf010203101e150815060d020702030c3f0a0515010603150614070b04121d060702010c03020f0a0c03030f020102180f060c070308070c05090f04020409030c08070b01 72
    0xa01c051650000d0a207080b0710031041101110300e2008080d100e070a45041c414a80d02c00b001140e030f01c00384075030707641e00002d00050500e034070712595016082d19882282600c0c09410700e032081001001040b02030301d0722800c800740e081c202c900c241d103840090124480c00e401201e04010381b1f500e0401c000844103507440d03000080700041044010340c805002d411181002c01243c0312002c0c841456040b0b40c000c103820b20030010000b40004200d00192421503a0200815000d4a003500c0d14205440384540490086458010a048030b15690030845003040ca0103450b00b410002260011959403c80c40000c3e019405034102800a446045c0840d18886001e020340310402c81c42d5107070007004c507908103808500b1640305001039624080c417144608a80402258003051250320358000404911030b0091716007075445105000000c2090500107020028050f03207034003140e41c4e5101d050105884c1c3c215250f090f07040c1c038000000d00500d02940003040c00e07400780c5412881064265504ca40d030380d000d100180c4a0207402001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 930795395 1250 930794145 930794159
    0xc0d0501140f09030a0f0e040c030e160501020303061c05070320060306090f07091503060914010302221103070c050601050f030a0204020315030304030c0f05010203090a050f030f01020310 82
    0x2000790081001c0c202d02406180c908070b0151a402208908402c0011402d01c03038920702d01c2601d0f418203084000300308015810840d50301038003c02d40803600740700c1070140d0b005200040319884042401c0310340680156207544d543c4410040c8481d185104081c1003203032900c451012550800c6044042d5115680414212030401d108090032580300f0300c101e1040c2d00810412000381c4440b0240d94121030b400000880c3d07a142e69006403484109504922440640d0440c1445010740c07503000981151810482001085041e003405840c1500900001e0b400c1a07070341c0024084c0041400808442800310440002c1e400003001944071030398020f9803d040062600c0c000e240034040207006c0c0b240100012281064611281c2e000719459610840e8068030466021000074072006224070500f900200040a40343d0391a1240781690b842d20700d6001e08020b080101c080403c0c1c95000204682204c000248109011032038082041178034015200700c0e6405004441010400d420240043d40c000d45800090076110b50402c00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 930796645 1250 930795395 930795431
    0x3050d060b18090406090204181109070f05031312080411090907060e0105091816030e121612030608010c0203190807140d02030f0916060e030c0d0501 66
    0x1120840c032404202c40d000705a8901c40400d520001620300100c0c9a6450418a0080421242c0650428100407910f410b04019000070303143d20740300c3c07039901d600240040305002d8141c8088032020042020041d00b4410140103030003943d80040d00d40707018000d40b0711940d07402071800c455000e05804100068280800c10013004030000603100240c4140e00302d031420414056403100140300c0d101c144400f40740144030b143d1040045504c0e0a40c068882c01d6400d8038000c0180403180101d42c244041a241719160850600c0385c001d080c91150a48024030719514800c1c203488256020071109004504500a000d000441c0072035000e010301419100020000d00d040d0060f400d44000c0d04003102150800c201c2e001e03d42410504a007044002d40c68400001d40d600001039503a10002c11307042c1080d220204134000c1e1480c4a400840c42142d01500744402c545408900b513035a444624140c3c242c00b5080340083c000144980c1a4480c0010000e003210880110fa90109081040820080d40c180c1d44600c401c0180c580428 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 930797895 1250 930796645 930796649
    0xf09010e06090f04020a260a0e0d020a170c01050a050108160305060a0203060411030a0912110d0f05190c050d0e0105040905060103060b0a0e030601051f0315090903050d06 75
    0x511114505040790b000100c0c012420000750f0b2181c0c1c1d01041c441c5a080c41800218408401c8007481c181040701400300740f5031010304980c100fa1035801c00c51480c00002000c0b0b00e600412516030001c0c01c2c1c00b005d696801010240b018000d00000c0c0341400004280c3c8400d014543c010010500d0004055060074402c40c00c00408240031241007404e900c04000003007002808a6011041410041e125210381c3c2c006006854541c0d0607080700ca2000c01800020800c0b54080c00559202d00540c484d0003007401c1081d00e030881e004e4020b520f82d410500881900500842120303559620798940940760455012605484000c007007204000038040d11503c10811004000c0f03e001e00f241ca091140000400c900000c01d24821030080c101c005881c1c00102e54280d001e0341046015045500120303458100340301004000d5408120141d100e881a4800011241844480c01580303100360b45040c0c4e5191503804054029024507001d82c8510710000200161a00c5144140c0d01480d100780d44030b981c0c540340001c899082d40c0c55a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 930799145 1250 930797895 930797899
    0x4080d03020d090605010e40050a0203070303080a060f050d030813050d050a091a1b15010b07051638072102010e0d030507124104060b030a080f09010e 66
    0x80c508500d207452005801c608c000c072244a80c02002030543c070b0842d00f05070042c1c130001d4051194940c04420940c000307007418407500505104111240da00e58044145460a10800303400c00c02803041500070922951003981d1140d40d0300c1d0443c49095955030b810b85841c40418503903000440c0441d0b101e07c101d910042c82c0004010595081005c0d010034144001e0b02e02c03505241c8540d6070034602c0250100c079814000d41d00ca203084188481925a59409980b000c1e038024841140c89000340c80d541c41c6803c0c4884808002e6552404111030385103000044840c08625807103520307134240801e403407803410340b02401c1c024000a4410320b61a4200000c113201e0309413140d0200229070669041001041c02800005094030070011f503440c0102d020748841005680003003030160321020850a224243c040201c1c0c400307241d1130250b01a80c80051003400c1c80c4164a4420f500391008c0034042c503160100d80861a26041b52044100c01001d441558ac410741d10b410a0394401c1502041e00394010641c4d07070466030019140c1d0451481 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 930800395 1250 930799145 930799201
    0xe1006050f06130b03040c080709050103290c09040917070302010516050717040b0c07050307090c0c11030309030f0a0b0f130605090321150604080d03020d090605010e 73
    0x8150048854403c941c0580c110034080840000c0501200c294150010845841a03c1d445034071901150301604003404140c45440480c0038640f41ca1007025805d00502c2c00301e0001a0064440358101521a8800740900d07503c203440340b84c03203000708102c50a201c048904c2c03000300a1380c0e18034034a0301900f5624001c001100301e824000e2045070782500502280d02140c1c4c070402c1d030071009001c0d5a06007107900454221501102e000b04544038000310014061080e21401c078125119680c0d1240240b00340c0300300c0003040000400d00191100080c0324400302c1d02c0320321001001d503800c0090040200c1d02e0078000c094001c00c280d021070561802c3c4501c03118180e4010071016071402c2c4600c1c00074402003203020b6442006107565a5040000d0710328605105031183e8540c50450400b400c454903001320604c10703040c0c0c1e0410101d02c075241d02107541d1812070300311000c44d840c1c031000e080b03c6010010309030000d4200d02d4030300c40425100c50022000400f503110300d60181407030300421100343c1000d08100d002c2459103c803003189120 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 930801645 1250 930800395 930800407
    0x70b070c1401020d0c0602041d1e01060c0816170706110f220312020102070c050619050705070e0c18011812140f0705130911010804060e1006050f06 65
    0x10f4045101c4103060043c0c00c1080003840940342c650000d12484d0700461106503480240f03004000c0c528443d50041e6421014002010303607800b04040200b4081c480c2c10301160780d030041807001500c0c0901501000d2800008590800d419485800159810100944400350005005000c100c0036101e0ba80380034401060f42c0c2d0600110140c9001c180c41620551418550a1448182410703c00910780c009140e2000c0c44200000f03d00f0400703800b03500900421110ae42c02600041264189481a1680840d280300045001075240030700781d8156100b20400d503a6801101d03c089406440e08090314015280e641c2d040f42d40d0109540510342c403807560000207042049812156441c0e01002a01c18180c50514035120000c0c2c3c1d9074600410306001003444020075018085030202c00034004194001169001d0714680d803c8101004050201c420000008003a0f04600b024110340754400c0e040c031603201748203000c0003079542e01100c0107610706000d4242922a5546821043c0041d0500a0040c4a05a020359003c0d0900c9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 930802895 1250 930801645 930801647
    0x3090f0f06010303120e120901350417180a09050f0c0307090512010c0906051e1305040f0b010e0105070206030a02070f021002010608070512100e030c070b070c1401 72
    0x7141848081c00300203900841180302c08440e440015001c00c0442200c0500400c02e81c4010141c2104003002c2c08034049081400382d15084036180d000700110002100340a90400c5100c40d007801014000342ca903010b2a03240b4008905058000f00a840740d1b4820f0704d5109490502044900811a000081224100000c1c0b20320346a035205583e800c140c0d601c241c01d44980c0c0d01d400c03c6601c081168071103903000c060307108050b9004c5810b44c401c02103101c060f6107541030035880b40825035452150460b8500e58101c030352100401000982c003e4445494070307003842010140c0d03c8000405850180d04820b1415550b00111049583c002c42d445d1120442800c0072800c0042daa0001141404000d041c2c8103160f400050300303003c100c109114030885035030082200075450030341d0000034001c0406000381c1001e4400e01c02c0104091400589000c15000040d000380158000981d004014221f0b0021030583c910050201c81181c0c1c41c00d11403103025040b14803004d5154985810305503500c03119540f020b80c940c45d14140441e51030b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 930804145 1250 930802895 930802903
    0x70e09070c052406030c011e050307090e0f090d11070b071a01080304030b011e06110c1e01030f110f03070c020306130605240f1807030203090f0f 64
    0x18014107040d10803240301d040250611060401c415120700b00c5100304002441c0c010380b05400351000703400b21070203080c5440040d641d2000001c80d04d5101240001300f55107051003070f00190f51042c0b00d854a44603ca40d1801c46514404041e2081d0070302014000400061180c104100a8201000e00d80301c408030010612464a820945c0209280c0040005410013800503804501280301c00d01e5528411540e59002070701d840340c10074002150082d10b000300000d54003c00c4110500c840d9400340c10080c14514105003501c0d100c0400d440c00505004881074805550340303440c0d8024030507040c0c0d0071038010350f400a8001402c40c0c10444600445914000300810006500402c0d40c1c4445500040f195490300d03000c1d829220812884002545440f401040040300403401c607141c0200c500c070311424003440d21620103141c802d00d042c00701c0040260441003061128601030301c91081d1028041c0101d013480901e11001c1544200441c0c440f80820740001c18000300100810055415408002c0544503500180c0103454403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 930805395 1250 930804145 930804151
    0x31401031101141209030405011202040620010e150709211101270303080a05060d0b1306051f0803030411011d030d030902010311090105030f040c031a0f070e09 70
    0x10400301c24041540c21541904880c609103103110202003510785171a64641e40e50040c040c060000b2040d2003034a5118400c0c1c0240c609a90603a101d0310017110508000c09414411201e4018440d9203408941048082c2400260329807843c0070001c000034038042101500615083d0300500809a00030b0490301c500130014203100700c0b2588181040c2039407456200480d10159841850903442403085501074030700c0310242c407100881c0d1190b20b900700555200720300e0700704540040703804941103443c01610000041003298120b41c051500640d0070108030103910f441080380c0f421903002803203426110f503d00e5445981d00c403010080084000440c03940c9081d588818040003034407801418403610401d80301300e000e0801c0d0001c8250030040d00b00c90050850540050140c400400d059011034a07040c21000d030302141208562010340306855061850325000601c0302e0800008000351203004840e140400003e40c07403152050748205c4802d2a6140d420820003100c82c0900c007401000910041c018401240e48034140d01d0340c2c2c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 930806645 1250 930805395 930805397
    0xb010c24060b040605030106030c1d280305070f0905041e0f06021206040b121b120303070203030a0e010501050109030201051b120c010615090e180703030f031401031101 74
    0x11901924260803009899150001500c05101003004640c0507408009541250a503a07401d01c5480340d10700041d00c4444042003661060a50089948c1a900700504d01003200601070300159015031034421980507050240c1c01c121100d40203090100500a2100601c0b0050316120000b04000e041640c1c540161480c0c4a402c52801c0200041e02030500010310b10061595801140035035440c9005d551164402030100d400922461506402d03d40604150754240001d0001c0801420001f00750503103003959081d0003041a40c055a480b039254841242800070314003031121900115241e0a00310b402c0307826076003400e800385000c2e07140c54010446a0382c040d0b000b004584e020b003000e9580d03807201c0101c0060342d040144502141e10904550440303182c40c0c0c1d8010240395820100800010307840e64817004d103844038100c40d00c2c000780d000700b03023840006148241607070810480b0300c1401503080c411421a040c10714035401034000c41c8a425074030340d00641500892000c001004d60070840d642c150340d1031480d0b0801100c001c40c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 930807895 1250 930806645 930806693
    0x30f04030504050d0b073b0301020f040306020903070b0913020306030c0301050103030f0f02060415020913050405010c260f0601051e030403110708070909020a09050f0a0b010c 77
    0x90240360049044034081c0c400030704030310f81004e118100150700e0803041e9601c00001c1c0b404081400b848548010b90810b54941200c2064400c0c2241e21205101011800c81d99241d54204141002c4c84030010041c4010340c480c4c4805610f858483d41014248017050f4021b01003000b04000c824104d55504040400e4201030304401038032600c0d040c000c41d24115a02c2c251a8040d80307071000210600d500240c07042c0b40c800300c6544c0c20101c2001d040007281c6513402a90300500d003403040080900d0311960f17078000c1c00c880b19020782802c3c7d44007031241010003034480c20740f000c1e5216552090302022095011514080940d50020b070000b2815030b81c10f920803410b1009101e400720310380d02808100703a60703c9501120408501800751008024600059451680c01641c045022400944004104201c041a080110352005002d45005464040140080c00304800100d0340004401d0300460079a800d849a036001d0400d1140c070020501d00f41503610210762540e5401c50520034400080e00c00200900c0c50903884a10f030b16015 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 930809145 1250 930807895 930807901
    0x1b0a052811040c0c0f1401060902120a0e150f1605090102213a0504210c06060e040311061006180b3609040f031101060902180a0605030f 60
    0x4913000410884014144245803240406022815545148010000c0d00070044540c0da822150100c0c41a0100883c6540141c800a6064101c0b50300c039401c1c0c40d50440990304016070f402d40c0070266680071a810504c10422905000c0c1d068002c80415038010000d0408510b4500b0100010307640ba018504040030103052203624540781060b1300107490200f80d9098807820701c01c200000800012140866501c90b0100c14007469132903084a0107800c1c003a503004011341007550701030b2010200c510104c00c5200305002c440b00240300042d985101d01750060942014180884c00c091600030b00c05401014454416484007080c0101c242c541920941140c2141c103144030705169130031403182c0c524000c0e80f09003140b00002ca205849207602c400c01c42e843c05d5100c0c2e00c0c51408550b582d840e030101a00742191a401c00260000180020f150081c41d02c0014040c0c00e00c0304040e6003162185080da1030b10f400911010f500400ca1000700c5421310715030008030500b02d844085190410348002c0c22804002e04803026a807d000c08 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 930810395 1250 930809145 930809147
    0x8030c0306031c020102040810020909010302090a09152f030c0a02160605040e10080601050f04020d0507090807090e0606010e1c030302131202030c01051b0a052811040c 74
    0x80b48070f1902e291002485030350b0720807401a0003504648200d2009004100c240f0009222600c2113441c0c00d14020442c1016034210b07024050403020080080700860744e14500e11002c641010000c826000c00c076580414941172041c000e08540c8402006d141c04e00c009203c2d07100710380390003005491340035100100340c80d00c400c1c032400c08078502401c0308685684c10340e214034003090303d641c04070043c02031b80c1a01c00006080c0d01e0b000c0b59514640d6442c401d44080c1c0d00f11a00500c43d44c9000390b1004c140c85030041025041084188600040390300c1a116032001c01c007206030402842130144040710003004068010000419450744168469900409043c104000d20a5444040d075445030003510801c50f0a0200c215008a07107400390084d402000c41411030700009100103604880c0c466601141540940039040e900d64400064680e5000100300f04c41c1e21621000d080d02c0c0c1300b0f0400100741031078050402041e420107901b035a046801e50341e407030b000c0281c10111002d03004250100400c3c25640c206540000c1c906001c2c003c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 930811645 1250 930810395 930810403
    0x6061707081909081e0427230708060d03020c1302040315091a06060d0f02040b0c010b100206011a3702011a010c0212010e0a05030a090b040308030c030603 68
    0x464031100f85000101018420400081c21201800410780e401e409006402c10303032640520b1140740b0103040035050074059490102070720031303054810072404110006620a0b04042040050780350529280400411013900d9011407200d4014209a40703020380d0000d0390b20000e4980a00480c01ca00484c0c40800d02c0341790301c2d480c1e4101d80007960800b2607444000b03100d002c260007509401000f0360f01d40d08036a0300a020281114401c41c0142d80081c51180b811001210040242121080948110360300748000240510700b9001400b04104e20400003c800c0701e030504108501219416110443d449074005111151100070520300c1c0d4003880480d0340e1a0300c484c0c80d00c000b41e4040d40d880e81984101081c082e0f9201e0812402c14280302030241c000380001140f070240c8a100e056a80c0c0c40c14000340e940009503003d4108107106e038518201c0b81001080d2203121080309454649140710846541e0700004000107425445a00140a003540400481c0390603c0c1da100e00d06a4007020301800d0100100101160195400300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 930812895 1250 930811645 930811681
    0x6030111160b090a050d17280504020406050a1202120d020309010804060e07030803010302090f15010c0c0b070f0c23102106090f18061814100606170708 67
    0x100c00c1b202c024070452801071001440080f0846940c01d2800881c401800c0c0c140310b1003038400b2244264403681c06e080a0b001c05800040c0050740c2151b5541c8000c00c40d030b2182031540011b8180306660500318141481400f40000d00002d0b0260180c0100d0b100b41300983c0d022003250680c8801340b90283c86a00c07681072070030003041c90541e040550b01c5401d00020410a003580a103040342e0003101c0c1216940e4404940e00a100c00840301c2560f41104004450740c258002c01000401e81c1c02800c000791010348400501c2d234181d024000a4590f01245078041c4100200c3d500040013900070200b0b80e007403113144c144896080811010ac2184035580a00c095102c4c58410903540104d0458030107c0303e850040008002c000746520301070b20a407242000001d0344200d699004083c0880801d0546154041803515071500900c0441a46240c81d0000c00d0ba40c0c0100d4134841d040511a0000d102500d013100c25070186c41c007118410380c0311005101a0000d142210710580c6070030b542c00203050802c10362a540300d424500501480e0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 930814145 1250 930812895 930812903
    0x70504090c200a05120c07030c14040e070b04090f0f0504030804151a041d030307030b01080f01030b2a0f03090c0111120903030d060e06030111160b090a 67
    0x3150300345002903400200c2c40b022111a25500780d8040820103150784500c0c8207a4060010f41c8480c244c80c1009142c0c2c401010030b86241c005031200681c1382c2c1e85101c4c00f41c3c450303440000111405041d9103610300d820310562264050041c0200740c1da034544070024106008512a10303801c1c0d80d507000d1000d13050016800c03004010b8034445041010346003e140103080701d541034409450300110b5400400540c0c981c0d01c64000d40c4a04050800680011042000701410215091402c8555500041081002c0c1040507501840280d00c02040c0c5002ca1000100031403002031201d21041c1d5071000400114551844640c2c00401e04282402203c200480500c044e0541c180070405d042000184001c1ea4007044014600502801041c0c1380e45240e080e00440703640c140c44400c0701554024206013000345440100500f030390340b07029050780e00b00882c0c0e8445404561040d480000210301c10010011686001e00c01e000340c83e92440e404905080c490014000202c05068000741002200304c003040454504010b2510001c1d40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 930815395 1250 930814145 930814151
    0x210b130c020105180118350a0201110f07080703111608070923070c02180712050702030904020d06120c050108180c0904080d0e0303010501091e03020907050409 70
    0x54000000e00801c0704403050b031031440c0454041d0204c00c0d0180a403151134107050003903110260071a214240b041c401c0031482c49034a4102d0303001000604001803240d0040c00400f010a0b00d51440c500040d095603802120b85540c07040400c200715401400b08140e40302c042c0c00000103621009a0702c0d042d03d0042c1141044030340c40c4580c501c100c02d40d4ad60720400350140c451f030f1b50941d0300c81a99402198180d8a400030072951011462511450441c0042003040e4032003154078001e0103415194001c00c44c50803903980c0c0a100800c00340e0400c03400a81101580341c10300794080c000c01040c90801d0009480b03000d100030303451107940c0000c2c22040b118001d03004040607140000c00802e0203c420720300411043d03111300c50503003c5406640060684500f10030118018010304000c0c04090650750108040000001e008840443c1f00b0701003084085010310600c0c140c450340380015690b0b54100720024003c504e20398814000440407004c00036500c0c00c600c141c201101d0781650708280a44900030141c0c1c0342c0c004c1d50403c0c96120300d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 930816645 1250 930815395 930815411
    0x150910050a0b01020d0513140312040e0412020c010210050a061a04150215060628271a0306060729010b0304050c012d1707210b13 57
    0x10564090703480c80401341c00300ca0500071460b40940d0140a00c84004a00444001d410040d81061816841c043c150042c2a00e901080320812802c044e042031f00014902407617482000708000a08202030080314890004214084074040000d64035186030301e000d03a1650f154000301c1e03400038245d001a0003070545440410b40710180d040705c513a22a003281c0b0a40c10008200e04038254007034000f00f48100c42e2000341c10040195918541071050542c01500b100d0045050429882000c002102400607510f800b681d070f00784610540d80c2d00c85c0c4e0405100582200034203d20794200048100300885890b6251240b0f0070175101d9481d040012000d001d04031010303020b0114001e01e00034030802c010507694070000010710000166283d1507070740320b94007048500900c2580304e08100301140d800707559600c001c004500d407000e074071101d40c2116444410031071240c40003040520200c0d4040e15105401030358440141e1422003000c2c0b0700c074920003042d20136985044483e982d540c1001e0751952a460b5501b00c0c45980b040d014001c0c81 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 930817895 1250 930816645 930816661
    0xd12110a0807060f0203011a091903060905010501050301020a0c3c0308090601030f02330a021207050c0111070f031a09120405060d020702150319020301050315091005 73
    0x291000b02d04850141c0703400951820201540301740c0341a1503607072031813203130840002c00e040c80349901003007a00b0303841038260b0f501c140c810b00e550210030007a500c00da0700071551000a02e003450a5130810381195101c1d0b401803188080c607030760080955462542224051a00d110109103c4074140c2c184501b04000b2425500110350402c0a254003600841c842d6940800d10742e11076400a480b58028080142043c1510050b00c001d0b00d01060b601082c2080440b054500c04080d644107034018021040220b00c1d8600440c1c02c0714881c1e0144010382c40b00100c011418640046c1d131b07485030340720340c090203c40d4188141c00c0000d03c00b001c020000400980703a00c2c0c0d07950f04010b4990820200280007203c00131601c42c0107100050001d400421000300b90385900e0012402c15050100700072450f0040500a50801d600b80714850142c0d0344c032070a100c031280b00600781070750f40d0030300c1201d02481219400142045900400040000b6100000d04201d01c903909002c0003115243c4039100d508081482545455541c04e10080c01201 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 930819145 1250 930817895 930817897
    0x60c0702040219111504030c0303050a0e160f0e0c030a05100305030a0203070c1403060106030b03030f070b0406180c050607150903080105030c100207170c0a0303121a0d12110a08 78
    0x1104c80f4204403100800c03000c40590005004440c01400a1040c0403400c001a0103a08007070b070030882480700883d0502140d415949800d60000e65013840380e6481e8000c105c101c40d40e0020102801c444886a010341c0303002d52031003181d4880900928135040c1d81d4000a2003100c00b071480300300616480b000390303a42d8012218000359a0b0300080e000f580c6240c001c40000614881d0f00c001f02031a014090090300f800c1e0301c1c2160070340082002d2010190140820440320b000c0304110001890342c0c500c22030f44208a810281440c008a030000c494154120300c48001381c42c007054002c0c50001c100c3e030044440304d0b030b90445460403400509201c0c855040080c1060004402c0641081c03440c2d058800030380440749014281c004100303605400d81e44400c0542c120000a0000605030340444a00150150449004403441c0000c5840c00a2603803003a400600180d000700040e4502c0e0280000e850324040c0c60aa125000400050340380040704801000c141d0020001e04265000e100303600da10031b20610564458205500f40f100d06 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 930820395 1250 930819145 930819167
    0x4020d020d020613050a0608150118050607080d0c03020705070e0a0b040608010906200d05040206090a03030206100504090b2701020301060c05010b0301020a14030a0207051006180e060c0702040219 86
    0x4a02d01b080404100c0754860502544111804403207007095850b40300055030361112168a241e8a00842c0001052a0311080028010079200e030010941e40ca00c0307505110b04580401002c0000c0500400c00c080c04244005956000c2c0c400400c41c0000d01d131105902c03540207003481c401e05038025003803c1d00080c00380742c194032100740280100e10621812007065101c446000039915001c610071014032000707070302a44e00c0d031080d54814400703003010345465561340000301c455080364400c8005900000070450000813241c807410041c0341c15242800b440105035118114018014064041c81641506208140c0f034a441607000e00d16807000215075030350711060021b0a400840318103541c10341c01d0440b01182810140300b2070b648090300d903617034007208000d010a041165102801405203d41c0901006001ca0f0052241d21a0505030110000d00c0754a0014421a54108084903400b52450018001420310303002c200540e0006621484070354614551002400034004d0948a030301c020304046609030096004030b00e6404c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 930821645 1250 930820395 930820399
    0xf090302150f010b090105070519031b02100e27150a0b03270601080d1e0e010305092122030f0305030a060306092102070501020604020d020d02061305 66
    0x18050005804034480715000d660030521900d28100404c5420425000b0b0a83c40405250441c5001c2075621610b1425040199141c400031004614000305a04540301c0360820110003000a80402d550300000e030301039060b46010b02400f400c003e5032841603a030b00c6d50050042d550000302021700041c041407034051800449080101c84415982103505207820034041d001c4889216040b03146641c0e1500c030484400e0010981342c1e82060000030f004e1864018080c0b079000e4200c3c00010020b484101c0401803114101443d40c45041500180c1d00383c0d208d0380850b43c0c07102c0301c0b020700340482c45840b90408685445040c26450401500300b9031a844504000c600400200c0c4080341c0c4423034001a890000d40c000a00c510008007501100101c810000b07001d403010f103a001844000009007103580f6120130094407100d407004c80e1070440e50100203401300b16403040341c0240c200b2407009010407030401d80007035034450b80a400070b481884124800000c5540f00100109010b0f80a01401c0d03c840c80c80f003404603071324180d0040c28 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 930822895 1250 930821645 930821653
    0x32b0c021f1814040c030b06210a020306130506060c0a0c05030c1c0f0303150303030b010305101a0c0a120c050c0103090803040f0c05040204151e0207060f02030d0f090302 75
    0x600c002d0040c00030001611001411146440c0c1040e00b00001003020440c040c0a040e147c00340220290364100181400b046c84071241d080d440203202042d140103030014000440c251061040c0092501d613010405240c2204840024958a41d84006255402800040c070042e104150030349003000b609150b60070072100f0030f40c1101c8031200e000d000c2041e40184045d20386003010208503072070080341e0101c000e00101e81c000e06002616450308403101e00d00da54107800540c00301e900d6001010312940d15228582d8810301404481071024104004901c030030b41c00c006207910610307000c0f40c451540300e0305000c0d403061240d00000c000c100c10501100074180c0f40a480c401d4425001d1140c02d855554040d0048030a190f9101c951a03182d661140e84100d58103191038400d40d0f604202443c003003440d44441c4001c10160400104820b6001940200100601740c18203000c8441c840103480302c400079030002071072015940142014000111801c1c001c91070350261039580c00c41c0505007010307940201c005910064007580a5420b80e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 930824145 1250 930822895 930822917
    0xe07050904020907140405031504020306100b03060607150501080105010f08121b0a140115050d080f0a1701240206090c040f02130b03010e06032b0c021f 67
    0x40c06810448000c2c1d008070791030000446241c841d8210080f00f0b48411112410561118042450030703030004920071400b16014240001c0d890308004581d40200840e030301c40030181c00c22410305124000605030900914005c11001c0c02c100f5904024140c1420390b401c108a1986d40d4018039003c0c207828840d008017030b006e10710041500d840200701100d404041c850010320f0700052800c0540d139400043c40240b414001d681d94107000800100002030310400a0740080350782c1162b48030040f80c021960348850710441210150000184010043e10084a0802101501d0700c4034000240c0710340b01c001084c28810b40c0b17440004140f18034580071b1012601945019001e03800c50701e50341a039a6400980d0801d038241e01075046603030b0134900b03500605130344035246001508201d007002003561150746a4008000e1070384040018828030b0664100d840e40400120001d08013880f2480c2440c2000c100c6203100b140c80c032943c085005129005588a01c105540a0132529803074800d501092039842c00c0440780c800046d004d54070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 930825395 1250 930824145 930824149
    0x10306110a05090906150c1e0313050904031110050906130f02131b020601051008071709030913090b090c060912010b041811102001090b0a0e0705 64
    0x1a41c0c1000d0080d10384526207125141003103031100e802441103a000b101c0c45207403800f9070840f80107400c414000c00300510b201c00d0782d90600210041c549403090205d900c1400802201460b4910300c10480b4403c3d00c1c140610f4503903081c2240c141c00640240e4060740310f140ea0b42e2042002c16031045201700c0480d002e66134591520700203004a03040c0d881c000703070642a05410b49000b5190280503c8850640d002001440160550a5101c0040e6645110303016800032001040b9a0410340b032044003450552030000c00d68901004090649005000020b2224041e00009210001c04104032510014014400c860910030319950101a01500000b252481c4480020a162040000f48255000001000070303042240ca4402d000500c0100e030100310796592241040d20351a04c0e14402d081c6184e44852a0210010032070800250082e007503ca0a8010701d401c000f00f1615650203c900314600442c00801d20701965007110481c09880109400f80c43c1e90641d138188413200c00c13550b001c1c0b005103c60000b91440d0680c1c03141 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 930826645 1250 930825395 930825397
    0x50909030d1e1d0c1c0809040f0e0c01090e040b010b161a0a0b090105010e131b0c0b07140d0c0203070c0902040810020c06070c0201021f0609050c0a09051903150501030611 75
    0x601d0b005e208002c090708400048010020b4480084058400240b14145140750400d45000c0e90010217070b504000310318039403540e01424075005410030000542c4681815612060200c00503c1600201500420414560760090b01130028143d0030003c0d8002c4800e51003021082d615040d155040d10602c1c1080c0b00c001d40c02c243d0a000e048070416115a00b2a88282e01800546c1507400341d00048541c0e6203241350000d01c5205000140904180d9449180d40c0b51460003070200c3d04041c1c2001c090000304640744440ca00c005080741c6d5038030341d0014017041510703c450090740755028a010080101040c01d101048017101940944210780050045035110065120b10800301e1240000201180d0040400070340303042d0013118105d01061042c030442d07a402d80c0580d40c04d03104080c6440b800d201c00d41c803410100180d8400b8054250400113484d80340d0315142c0078800c0506985c1a51140318000c01103100040b46805048880c10000d44e0080252950144c80644202c0200001d003c200c071420318106404241c028050 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 930827895 1250 930826645 930826669
    0x70e01020c0105091815030f0a0b07052107020a060606030e030409021b0d0201050601170108061303020c0a06021608150a1e09030302030709050909030d1e1d0c 70
    0x80c014006000c601d4004549603401081603e4000d41d08000004061121101c0107204042c03800e4041410400e100400d418024412002d41c0c01e9880300c0b4080b400b095a43c084070b60482c145040040d56140c08180218031050361801c07003190301c1786d0034080244440d00404c0e96000c16100310004c0000c40c1d1985c105400b1511802c4079203000d64004d00c414890240a0390051080e2302810140c5608001c98442682c500542a400030005035120824050156003000c6988000f0001d20303240350a0b503050810203903071807078020412044010081d19080915000340103e6810700d0300a003030054901e0f03c0324006961034040d071100c0c0c80841c5900c03900151503000861240d0420414242c0c6c0c0440340c60b100c0747e13800a840c0d404a0301c80d094100240d85501d107480381c460b1071440e502c0b82d2405078591516100c003070300e400318680c0024041c54045080003c4075001104440100b0610f00d8001282400124030780c200c8507202c11816482171800c0b10b4071a00550000c10301503403207609070407680c800c82c0840600052032142c03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 930829145 1250 930827895 930827897
    0x150e010201150b07081201030f03080c040302010e220e0724020a0f08270415050108220c0e100b130312180b04090c02160302010305130b0709050405070e01 68
    0xc50300c240310f40c03c0d10310024441e0500a00245051002c1c502c03142a00d82401c2c1d104440c800007203c08002090341060700d052380101c016602500b804d1a540002c0c00013007681810302d00c1202d8040900c200f101a032407240c40d01d445608030030001027205149140e91021240501560710031040c00710302c503860800030f02d40814a0320368040c010200003681d586d44a1b02041c042254401e00911000621007800d07032452095030003040d0740402c0c00d001036090100b12900307880e550034802c403914002d0200380d800420550700012800c4039582541074441540307130300141000e401000040b441a0004000d125041902d00555100e421404280e54500400c03c140c440d20b003030f07801d64189102c002c1000c1812650045546003640c100280006d402d800d21107aa24495042402812004641072002c2d940d10300c2110ba081c2c580f80000d00010f1030f041071241243e0320b1880000e04142e01c442c001600d40003e10078440b02503034001d0049030141800d02000e40040c5207401440d001d1407a04000440040c45610b1400071540c0c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 930830395 1250 930829145 930829181
    0xa030f0e120c0d03140a08100909020d080d0902150a030b0a03032c1201060f0f0e1801060e0f06010201050c09102a03030212011406270901150e010201 66
    0x41424044103810841d0f0541c280018407541c1120203030450024403080e25260342c0c0086614102c1c040441c0d900880e0050078034a0319040211005890f10300504462541298055448021070070080000e0310800c41c0c020f40144011400441c1d140c000c4014140c0c40045880a003e1881c018080c0b108d40207452002800040c2c0748180c00c40014002001c1450141c22181d0450f6400b0340703940400c03400882441042c0c10340e95102000c00982c08000381d56405841e46461985070646803c3c40e1107042500501030400380080e1403459031220720700351310800041400f800d00349898940f105040b0608081114028055400c01c3d0000f10740004001c201c0e9601e0100810514840c00001e108030fa00c405242c2040c0c0407840000900f581050880c0c440c0c0f001d8501c00e56025a581d800c102140d0302081040c3d00030440c1843e4120044ca413659000b054880818088070051520398180c00d108100f51034106040c0d400003001400407440d00c544642c0450094003545030003802c0d6110358012801ca800b1080415607100c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 930831645 1250 930830395 930830413
    0x12603160f060c050c1606020309060903011407110c04110729191b02030f03040809060d0b1e0105040519090203070e100302040303080f07110a030f0e12 67
    0x40c00540680300d5001d00d0218840788500e9945070b049943c00d0b0380c42c1010940c04540c88400400802801030105103221491039410b00d0030740080c0d5203000c0c01d4076561040c000407a503000c00d82c5095006820340c50311000050381909080c423018020300131940d001805401017105040c624206030088412100d401800755192000329151030708100807410907005030101d20b115502a405c03407200c869005202100014083c100f066007141c080380c080e481ca0031500c003500d4104440c9240c001c000d5407150644c140900340d8a54642c40c1407070b1980310304c2d01d010380c0c04a07000c500380481c06d40a5012111803001607540343c0400c0300300c034008404645003c2c074041c00560b0400092119080a01a520080d20560815000a501c1e41521800d981003202c0c032000041d46100d08100520300352100d075420888908085183c42d0954034010903048005220248001006010401107449401078141c0c0c040380c00305071480380b455454020180c0104082c0d000004900071301009151601030450b50f0f07000b00903001405014 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 930832895 1250 930831645 930831667
    0x215030c070f060b0d03030c090905060d08210a0f050c090d12020c1201020712110d0f0509030d0809010b040b06091003090c0e040209071121040f0e012603 68
    0xc5400a000c41d10540c40380300314911354560b03500f0f1009040c40b0351130200b040c60a0420041c10903150754800402c050401052001c90744510048540d500c0d001800306035142c50740d1030041c0008010324401056180e120342040501c2000b0350008001c1c1c94030038420301540d143e05c24426254040e182c00789500801603d92540094200c000c584907030540d07401501d070b020705500f0000b190310b08007160f07115140c0d400084805c10419940c4005400da02c241c1441c0c0b40c1c0d8840720503181d98441c081840e601c180300141d01e442c001107009234103480b90040c3c0141100c0c07412580c100300800d0310302c064034100c0c107030360034003c0e541c40c00e01c4c10740180008460054240da080001d403404201c0214118130400d01410b59a2484602144042020101618100c600d12001c0d05091042c4500c104004001c40704000412101825404001c0345480c0015400144400700300d4200002800320301c2503902c0109680491400041d090090581c1c05040b2040100a59104c06100d1644405500e0315000144980c1003001071004031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 930834145 1250 930832895 930832913
    0xf0b0d0641150304300305090a02060c1f0203090c040906140103050604030f0c030915170703141605070f08090918060a0605031b040f0c03090215030c07 67
    0x1e0340c6485000c0c2042100500401c0485103849524102d0100020811081c0034002180d604080060328244400c0c41c483c03e05c80c0c0080d00d00e04809010107403102d02150000c501004084c1d5107075001086650f84081642007140e40f0300903454111410390330101d40c0e111402441c804d42e88180c4892000e040d0a0007c0070030480106881c1d1011100c60396a110140c00095000b0350140c0654800c100806141c01c2500700900505c00410b00380302002517080950001942c007965060454055062042a80c0e03403110f030540e0308800c40c101142c541890381003080ae0466042d0007664820b54200481107141d181e448603500d581c100407100c800492000c018040020742c0005c3c13080a8640184001410070409030002182d03094240e0300016905511125456a40c2e014000540c1000c1e41c0358040000511384000300c2d80325603072031600300c18030b010440342d140041d1030325000100d4101030300400308000b640c011000740081c00c2d03a0350181e00540c82c503448203c8016a48080b84d000380c100d505241d06003820f0340e50304016 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 930835395 1250 930834145 930834239
    0xa050309011503050d140409050a1d0c0a03020d0f0f151805030301060509130e0102071208060919090203010e0604120f0e09180a1208090a0f02060903070f0b0d06 71
    0x1b920070400028a1b1040d4410140520420540405d580030340ca4241d070b45041242d4a015040e40104035250160707500d0210860450340d040d40c0800e001202070500c4c114280c030011015002c00d0701c4100c001c0411808201106501c464502c0c00c004d01510307050a60000241300b01700418581c000c000500040c1d014501a1950401c01090b0200e4040f09400c1e8105407034010300d240010ba900415200c08220041c049030300b042c40c081c60708040a00d800c03000100098405044013070301c0210700700b0b1404680328941241503040c0d0040c0003800742c681c241540300d03a03d00c1c0c2118259009550340d4080480c4500c02c1c0d034040e6009040380d64050260700c929042065000014040e20b100c417034042110103005030144130100100d80036280031481800048409000e951000b004141d171a0042d5111000142903240e444440940540e2259201d007a0b00c8080fa182c40802e42000d8900107501c0e00008404459000908285c10002414401b440c0e85402103900501400c0c50380800500d4401c0c1645516800444410 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 930836645 1250 930835395 930835427
    0xa1b0306051c230d020d1416020324010f0e0f01031b0f0303050c060a1104090510090e030c0c0a0617090111040b04060201060b030f041b03080a050309011503050d 71
    0x140b001d000400f6440003100034007148400e90000d1101403400ca406000400100c1d402c1e003014441e1a10303440180c1998821010083c1000c89402201e00542d10100440c95101c4150924680c1840e4140400d0102c0c503024410300b803c3d81040040811040900601d5034010f80311002024031030b9085a6548140100010002c69410800d40d80000d00518001d01400110f00035100c02d903845072048850b03824000c0c001c02c02540e00303040c4880a0721080e02c420880f0304845c400e003000255910384040c010002581644142d8015052000c102c41a0b80701100501140d07283c00f048600303512415080c08502e5400d44a1000460385c1444074409400110030060791040c5464000540ba10b10b000c01c004ca184c02ca80c0080142c654040360900240c1d4092040c5006410082a000e0551411501c240700e040300c01840108002c00b0751000180c28481000810055644802000c1c0c070313000101c0c0002c240e900202c0f07054901d036003031020701501d400c0004114810b07250000702400c03a40e91002d1307048e9070741540c40320519 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 930837895 1250 930836645 930836663
    0xc170a020d0809040b1203220f03051614030606041e0501030b070f0203030405121b0f0a020108010519060e0105130b070b1e04030309080d050a1b0306051c 68
    0x8016a00c05005004540c403a05495403950450f4041c0000c0352218107509001c0d018071240d032440c1690000039140070304c413112451102c15989144d030100d6444586d0002d00200036500d00031040080110305100c11420040a0408113a80ea60414603142c40300d06409030150007110101c0c4c5141040c1c4c101d03510b00400300010302000081c0446840496009038015907000001c201400303105980030302401d8040c100b51000314154103058031056120b40712000860344580d0300090f0207084641140c01c102c0600301c800287da045000e007102c0a511030300c80b060300303c5c0001c0c12640041014605103814200d0b00c84e00020110015041c04001d03039171644110041411311106000030385001b0745551720701000d4108000030580300c601d94170705156a80070192503c00440008842d00064182041819500a400d4500401da00206080065242c0700d1511000082410102007141c910403c3d004000121034625403200c2601c19103100310304884060042950040c3c0d9050310042c104944a00c0c1900380b8000c031018 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 930839145 1250 930837895 930837913
    0x30604090218090706180e070c0b150f1008070c1718030c04020c0604120302041505070210020610030204050417041d1e0a0917030703020405030105010906030c17 71
    0x8039003001c0c18820914260002c4100001088248031078001004d0b141084070105280000d142420f00c00341c0540b22030994080e0000318680e00c20901040c807590042c03030340c15040c00c1000d100e00709550588402c40c05040171154000c12810640c0030701444070202e40d28089642c8a02100302c40d00e011001040d501e629402c2030041e5900c203020000d00d80c40104504072404c0c0801078003894103003040d401401c0e1256105015454020b900410142d40c45581311001564891181c1400c1c2e000b8041c40e008400700100050150749015045001000018000c46600d0108c408252003240e40b840200c6400e015007042800400050174150020b64001d4410310200034074405010038111540c00c140d021034030501000185541560050b00255088036003814007412588009020304200c140151869220540d602d500ea03061140c406076030654190030402e03081d664180080c00501a4005002e114801d5182000000d91803c07240308440031a6442000503082624000d4a00d4405500c91800a01401360b1061 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 930840395 1250 930839145 930839149
    0x5010801060f0f143115050304054b030a110f1036080d090b2a040f0302010c080c01020307080f060306242701060206060d030e060306040902 62
    0x28002c11100aa041c05480303910062801700002e00d00c14040b81c03c0340181041c0528508101185603950341400d24956030b880f01c0c0703840c601d00300d00c00c0440d4001c1e91000d0b40c649040d04030001100b011382c101000120004100485803401c48000040300300d1258020404074810314021092500c1030383c00e14003503d101c00ca010041a080c130400c41051110349a1343d44001c000142c0080c40001c810090b121b00c0345d00d031705654104401007000786c0750141480c840810700c600e00d0407071504401c0000d540022030701000d0a0040d81030500440c26510804051014080020f80d080340c0002d5508413118841c1640c0c4e903c2ca590015208200900001e50f540481080f0821517490300740011402a039403036480c0b15461400400104240d00050801c0e8840c0e040482482003c0c0c0d5080d006030b8003407100c404030041c1c1003029400100e00940f910058030a84c2c0c401510300c540317203408510941c101d6600e6000d48900d6a5444100614004140001400b142500740e12400c942000c1d4040c5502c4407024200140405070381e00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 930841645 1250 930840395 930840397
    0x1602150109051b0c0303010e060f041a03060903120c1308060f040501110909072a080d06050a0302100c060f0e030714010501140607020d06020f0c0705010801060f0f14 73
    0x8440d040d161100103001100c03583c1842d20314400d01092005003054043d60320281c030792206200f20805400c41c0008500640d941c1041e0401c5484020000c0104020182c40f101141c0c015540301d03803290182000041c0c400e50080300325500c3c6101c00b00c1044844c0c0c1c849000840c144c101d41400c81900d0066800407922020410850b401515081c500748503c1c07510f0300e460360a42d1004031010b20300312028440400780d510355100783c40d041038407414001d09404160408000791200401c584021203c0380721040709000b0300d8001400a011103440901c680b0f5150001d01c01192000d11000390030907543c080403850144111b041d9550107202e800d0205400000c5803190081e07800b0301b120000990400a0b0010811624030201460300002c1c00090281d0b614040c400081080c5540c80c0d00c1c0540c00001d03d8408555600e100f10048542c06441151100e400500b21a0142c002c4400e14199104180c00440c242d030090f80c0d100d040701c2c0c0a980d03900c0300d030a203880f04640200b0030840749800e0016000c0700100d6000410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 930842895 1250 930841645 930841649
    0x10140d060e031b1606080106030905010e0d05070204050c0a080103120909090804050315060102210918240d02040c0c0f031d0f030a03051c050108033016021501 70
    0x103039003075400580221850901035070000d51305407003145441c2040869040703480320f41113034514203000a408100e414510b01410100f22090700f04d0054000305c2d82c03403a42007405004450b0081e41c0c200f06564a50076120428401c240704080810036000040000881c0104805001d6586203403072401c40b50b0b00d10350360098451070b80c01107403840e0020506000b035040800040d45001d01a880b04a41810700d00300203900c590710b81108008004230504a204010205021a450b004001e024401e000005501d012690102030b2070b441d420500d54448414401000d82d081c1340c00200007040300c004030060381d08020081c00841240030510850700001c1c030128030440004005140652100b40c540140c403240c8404c59405900144e1245008100d0340d613041d20000340c001c0c04113a05040269641d001b11000b003059401105500800700e08010002c00e2048000c00603044000034500309501481071880410003103c05480031f812030300018800154001800140100407420500544060300c925202402e50a0800d1f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 930844145 1250 930842895 930842917
    0x11100c0c0617130c03171216030605090c0d09020a03080315010905030d080c070c0819020306071d040518100509060f07020a031812061410140d060e03 66
    0x402d409101d06a140001e10703400304010404501c5014665280e582d400b15500000c0d101081d08070003809072402610407035001c060705010005440c82c000c0044c4421400303140800740000c1c101903001559040c8400d00900620503c60000e042107031040c903640041415400603607014008840010209807039000440c00f817000e58527403807845648000050821400c40d40300701e000e035001d1000c42c020654800c914030341005811030740d686d80c0c600e02d003043d0868010f240c02a0700720b409054000400646003280591903a8404e42c00e4540130754030310809995150190f203019440f035851500810040c54558403040e40122880743e0480d84002201d40705142c10b188030302d540f0f4101c0d6100280048400d04005e0280d00c01c00f07081070460780340b13403101d1700a4481004a000800b80300700c101307140403a00c0c510254038000e0480e1003001e401e50400c0e030400c40c014141c050710980b40390700400d01180d02810440703000b030150342160400801c2c1100c0203007070050700350b02410b080d2016581c0e41d03452981c1744414001858403400c9c1c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 930845395 1250 930844145 930844157
    0x20904081e030601170c070212061008070e1303030905071701060905011a25031e030902100c05031b070501080a02031306050403050706060e0a0b010203040311100c0c06 74
    0x300034481c81d00200301c04500d010071006104021190f039203c5450241745442e512803e11544813858100e28500590600a50141c459101d001c80a107001036160701c07402003241c3c3c10f00c1846e03807002d5481d2141d0690050301d5001d6521000a16107a490029514042d842860300103040038190312824109015034002400220401c81580b03003c40c424002c600240c85244070400144d4540002a504407503840c41d20702e1400008034a80070308914100501c80310902003000c2c0c0f02da010040c540140b914209190344042c0390480706500c40030900c41d20800c04680d5010b044140c80b00c203000c0c401e40e11010040c408961520041150b01c0c10122000d20b00d0382c464012600500589083c0170001d000c5c00802441e0548080c414400c100302011032000c400516500000001460303110b0b402e084500f48074540d0041e101e03c0c14110000303003c40140924a10038100400200715605200c401240c6a200f0703071002511081440c044058685042c01600c407240c02141042741c0151007070365424001d40159031214011480c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 930846645 1250 930845395 930845407
    0x10807021005070239010c02030a0c060503060406290d0b12070611030703080a0b01050c01090c08010b120a0605060d020d060618020f0715020c011a0a05150d02070f02090408 76
    0x3200c1e0102c00400380d207149040c207031400c0d00b1942100c0b41d20103a481c0c1741002811f44e000010354805215030310035145c05c40818036440c0d8540304090816481550b0f0036008500d420800102182c916400301182150103000d643e600c3d055405040036500894021210309a45100c040e00607602d00c03400c400781070340c0800500302081c80c2c814050401500e00c42242c001d80c20402c00600025031245001d6440178507680c0c0050340800d81b00049540d809404a03110f140c1d880c1076201c0041c0b00302d0403801d400300d0785545c0080c448610280c0c20300c0540014400b00074410341c000d1303021b5000a60260415039103c01c010349980b03000c00310303070700066421f41d100c18040d200e2030754655060207901014403060041d13146c004420741c0340c03078042c0568002030310030340e00d0280010304040c9204420143c207404403641354036480000c0c040c2d0030401c40c401c3c0030b101c042e445141c8a110007050024050a140160600c81c1d000019041c1c10464502c0e001c202030360242ca0115460391411041000590754925110b01403401003140d5a1076103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 930847895 1250 930846645 930846673
    0x180806101a190905150c0607090b090f0d080f031008190204050702120408101a0303070b07090b1216021b0f040b100c021e0a03020108070210050702 65
    0x240180d0000200a18408000c601640881c022501c03440c820703030103030000310742500300883d030200b840e4000d9036200f0541940114001c14000103840a4030414065880a03181c01c0800e840081e018820300c0d0302110288101c0d840f0b8034241c1c0c0205802100901122035007405942d51603215440040d0881c102800401840340182c00380802c100544910302c010307c0607841403d10240300c038441c007000903c2251100c0008512a1003403091420400108008940303464940c1001f5845881c2c050842e00d0f01c91400d611701c4440c10140c8002101c01c040a80074601c1c050143e103811042440040c001004d11605c5117000403c011850020f040040e81982e03144040d0400011486020b201501144110b61207044200081d87c0d0740420103800348001c840a0f2008042e03c2c0101e4064042d0404481e8041090b242000c0300360741002c49115810b100325207604200111417042083d00381ca03900d0f03164100c440c1010520055000f00e010681100d810300480b4240e0048802000581c0c00489580d40145c1081e042d8100c09 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 930849145 1250 930847895 930847921
    0x504120903020120031209010f0b040204050a0902090312070317090a0b010618090603080904060605070507050d0f0f0f030e041a13060b04080a0b010b090904030e01180806 75
    0x694110320349004114a150002041074440e025a8981658125010f80403040b003041218001d0b03072000d911032070750f1803c40300150003400700b0b40c03030020b02c0c03403c00c500d40c111403400340708440c01e030b40c001440c160301c41d401c1a50b080001d40100740f04030f030180b01d00c0f10b21903a06400c002c007400d0710b248260f50311001385002c6070001c8820140071b4100220b070340c440c0c000500054030701c41403581500d89500c1d209190040003400002d030702009074002c41c150303460000c000c42030001c98801003a203501c05440500440f540c6d420111500d10441c140a0700d01c0d00030312801e1000e0301d044002920458001c42d07840d900480c440c0ca4580c01041d122608032400110741100708101070700312101d04090001203400704907071880040410700540c0c48103107080c85079050420080d1819482e60281014140301642c0588032501c0300c810603034410004809581c402e80000000540005100803034420f164040c2089409850300d42e010345070890a4a0964148000c516039003a11b40b12144017a4014000a001400c02d8140f5a04425031303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 930850395 1250 930849145 930849173
    0x1e12090102120c43030317071803060e011803020a0809240c1c120b0312071a0a02040f050607030e150a030f090f15021c02030610020106050901061107180504 69
    0x8804220b10400100360000a0703a40c8020300503c180045541c0c0e01d0003210201d55506800300d00300c627a86800b000b400002d43c400701206800000030850210a2000351100c060031f001e0080040c2d10542d0310f84001510000030700100400a841401203010410000d80444040c5589070720089010581640d00b01c1c0420654a01c1e406e008801810440c030154018410003440322007213105611002c003028151020403810011001ca201070703070340301c01d4180703080a00003420032500750f01c2150080114400d103966100b1141104c8003818070210591602e0300b48003180c0c2200c001901446084201075940e03440d2410108002442014080e0741c0781041000078007100d200600c1078a070585001800c10000d01000c1201140c1b5030010088110300003021104000313480b1340000d0300700744803005030b01003030025558003e103014540846660312250b1620804a0072a9003601c40d07a640041010010003000b8002c2110513840301c0410151112103071180140501d5a02c01e004502c60144d0b12020842809041051546 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 930851645 1250 930850395 930850513
    0x1003060606030902130e210906300c1b0f0f01050f0f0606180409021207080d140304030e13020a081b0309070e0606070f050a0204202a1e12090102120c 66
    0x5081c0810394600ca07025402c0b00341140385079811000c840d03400802c018070b81c06d814001240c402402c3b81c1c02040c0030304410b84907400c440200c1004140c826401c201414403070382c405003a10382819909c1d40c1185911030031104864000d1f60b82c01c803030f101503210101151400b6040304010040c080c0340c1140c103480d0850114111081014030700d02c440041621030200c98121390149031a00c507000da040c1c0040d80d80106860782c40302480c0b0002d01c46404c5a00b04501a22a060030040089900703000b00c01c00c1168030040b0741000f440d400c035807414480214030b0b4480503044800030b05481c0c10724075241d5071030800e038032030802c00d460790b502c4441c0010451a1902414100c0e1038681d500c91360030440005107806078060782a80d80030620b40701c0144040d482c81004003103642c0c1ca07584100d03499050780300074120324900386000b04126409a05400a641c2e003c400c1290a40481070340244081c81d80516859030381d40040c20740218074014000102489540c40300100009003022442c101d0715120300b40004003c60078501c0c209 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 930852895 1250 930851645 930851737
    0x80f130314060f1b09040b0a0b0c070303021b030a14030f070c0e16022a0411030a15150c05010e1c180b0f031003060606030902130e210906 61
    0x2135004c40c010213584060105503404034a00c0041c0740015400c3d4400d40040544110215000d00e80c24070006019040fa130180e0280d5515808000c0c0c1031414a4003000c0141d0141e02403080c41c000910b5040004c00115071440540c0c1c2041603501c030145890348500ca00b030b0742500180d80c0c10f0241d040c0b202e1400d600f0540c0214841c200c10821180603444030500c20f0102d1f0854100d10108102031000108400c07600001441040340d281c3c01075600703845030800d6900b000c0040c94184008a6840c0c51440082502d4910f4103480c4000d180d550215034680401300100c41554840301c00b010410f0301002540c4a082d40d2640d07034a1003001d4440c006100c5148411030b1108500e5024080103104e212408440100a0140c0d1041e034035078481440120781c201740e60004201610b007103400100e0a91503031014941610032500300c410400392440c44002d41c0c402c1c1c05400380540146240ca03042c81c5014196000b03802ca0145403508090460300002ca00742c00c0041e412103c002d040389400760000780e0840300c4080040c000c00310 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 930854145 1250 930852895 930852931
    0x1302040905100e07051807081306060b030106030c0c05030d020a1e020109051203070f110312010b033304020a090f15120e0c060a020c1e031603080f130314060f 70
    0x403c84c0d0000b8081d1818051400042740e110b4035035044080210740c00281c10b1102e81c1d41d81019203203d42c0b00348212400a4986103034450501c1c40344107501803040c2c014001f1420301c003c1c188004000d41c055a9000d0500c41e88030081110103194840c44021007240c1e4000080c401c109080103418a0554600b40445c05420400c106006421440d0540d4410142c035103081415400d4020f14614860902c51901544c0020000a04014140029403041a42c00034039100c07803032100c56400c0010145100c591004203000c030400d22904103680542003a446501e01b04056942c1d88585008400c0107030410311040048121032000d042d00020313207000165014104000e43c0c03c801e0380c41038a03442c1c0c0120036031003141e0000702040850310800004007910001014601d0695031851450741458410040a0180c01802c00c101180118590f18108491b042010306181480e0340042c2d240ea54400d4820000d002e9400d8000f10200340d404848981020501000b4107241c10400c00243ca410402021160310000d00c10750 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 930855395 1250 930854145 930854179
    0x14010804080d150519090b03010b0f09040c03080301240c050c01110f100f0606020309030601031103190302061e012105211c0b0105031302040905100e0705 68
    0x4494112502d51030008030495000001c0b441031415611455003c52810440c1c4180400c0e00c81d160115429000c0c01c2024541420501d0700703039201c0ca1503444c1c0c040104c1440d080f4604150104945c0148140306009a42e0b480743d0325545160020707001a903458801c1881800c014103443d0300409100080c0c1842007640045540d0b180e66095100861410084204171101a81c81c0400c103148404440c0b030182c4280204801c2c19a0023040c900d00309160244c203000000905074004422140800400390150005a003507455000e51500d01c41206a010712440c6020218420100b0141a107203100ba8083c4c01607003003080c80c64540228000c903e01341e508140004101e505585e48503651107100075174800001200d03d0804c9401d00f450866901c003400301440c060b00c9180c44400082c0807242e5154100360480170900d9540e42154000114140410820004241c0c41c00010103200c0d00c0500c01800070486d40303031036950642050050320110480641302c10740a4100c29040c02810b010f07200aa07040180c1101e1801 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 930856645 1250 930855395 930855397
    0x4020f0a030209030a06020d0b030c040e070614070b040b01051f0e040c180308030105090703050108060c0d0e1005011724091501080319020a050a0809010c0f0c1401080408 75
    0x600c03018160b002455001c0340d201440103010864002d2421912520f0050310000544109401103100707000c4c0d441d110880d4a441d1041c550041c0411000b02905800c1c07a0058034030740c0c3c1000102c2d10170b050500903080000c2c0b1502d60103206234440c1010750210751400d414030850006c0f804d920351607403a42411784201c0c41d87c0f0241091615800310340224402298110507106451141c2015144c00e080202c04824885044011070480701c050715680029901c4000490450f44203004003802c039000600031071004410b0002400700041c81201c00241d170840311402a00d00588030b01009607598a50004000000400c80340c0d030f50842d40c0601912002042c00859801e02c604002d0b090703100548800440c0071158100300171841c6c42c0c20f40000352101d5842e031294a075070360072641403101c140d0004403455662501c00b0a151403200d0f032040061075000c0c0c940c0da401e030813500450b4000d81004000104400400c2c8a05601e04060303004035241203040e0300340070740c041c00d0705181b0128505110300e41d020301c00000d40d490 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 930857895 1250 930856645 930856657
    0x9010506120c13051905030637020408060a0605040c0e0a09111213060615080f28060509010f051c0203010204031a070908060c07081b01060602070602060604020f 71
    0xc02e5aa0344081c070b01d03103642007603400d038201640001e40520812044c4600701d9040c0e01740c2d0380407411681c0c5035880610700340070244961680c10040e103010340511000b10108847d000303144030800d00136060689a071000e500c0c0c90070485491aa4039203c2d2000c02890034184110b070203007041031070a02c4901400001051411400c4d20842198a80d01d201098950320100260743c114090008102c201c1e040158011481909105c0299209440c0010014111403042c20003600000c440e241c2c40c016590362000740f220110002e100c2d2000208034170011b0b030f544846e0000b11030650341079080010041c2c100020b015115005030001503c01c5004407041c4020ba5500071100e05d042d04041100c829400d40d0b2001ca400390080d9480140a0303d0700320002500170b242c0c840300130310800c0140d64402c00550703503880c025030700c2105640da00b0500d501000341d54081005e100040c540304e1100510a01c001102043c407500f165450340c400001604160024481550b050206c207412510444003542859000a03031114a0b100e06 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 930859145 1250 930857895 930857911
    0x3100e011b1d06090a0f06050d11030403080106030f06210501110f0306060a03110325080103120c02012a140d051b1f020c0c04021c090c0f0906050901050612 69
    0x40745002132540d680c003e25000d0300c015040e44035005c0c1d889501400c1d0ba0468482010000d0405079481100225001031703901c902d07050307a5000041c1c1d03c0c040c01a00103000c8a07203410001c0352680004603050341c84407022030704060401003c000307510360750803ca821203030746202c803040e48042000703542c85401c01581503d0f0841c10495180369200d070707452815800cc00f9044c0080012250100030003000f85120104031101b8a07000200704103ca0f0049412145600b09020043c40c64040c039051000d814031882c0000c0c451031041c14260140312034200d100401c002c41251b51040794490940790020000070070041012000090001c0c9000000c0640140060042d2000d451750b004980901005810080110306c1c141c2d03c4680c0007260308803250701603002951080f0081c8400b0301c00d40d41c0721a114106403003290040c04c441c1011a01841e058030081d0058480c1c0c200544000412560110b0781b03105014044004000001001900520f884144549900160311861091506204a0340e40f40c009034045a442410 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 930860395 1250 930859145 930859147
    0x80103050c010807020a0b190c030219030515120313061d040c1e020f061506070609050c06030906010f0e0f1906180204050310151403100e011b1d06 65
    0x240880407880e06c0e5000d02e01401c0300c10b150040c40b070f6003041c1d0b4098420108100d1802d01c14007000d240141c050340f00d0b100e492826511010b136003500c41407007a03000a4002c40040101000a40400002a041032108041c04031a82000035401a0b081a0645560040c1020f003080c0d4062492112091700103400b01d81e2480c091a250038001d080d00c0c0c424103c0e446002d2103402c08a402c0780c009000250b0300c90400c000f0015520030340700481c40303d500d000540c45840314000d09c000c2c07801060b40c0d03919028010345041210a4400e5040207421a0780d2000950b03c100100c100500300c3d0340c5002130a021b101490342c4601481201d0400380100030b04401010381e8005068203030f01c1500f0b2128140c080040004d9407101801601e800705480d40311407190002c0085940850844060707208100151048618004134a412047c204104011003030316a0080c0042c1c200080c00d60b1000c45a080305003060300e1854420740340c43d0759110013801d0075102e00116019400e20724607008908030803c11010310000d01d40304519114201c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 930861645 1250 930860395 930860401
    0x15030207060213030f02030d020f03041202041401180c140a030207050f240603030a0512040303060e130204180309270911120c0a0302010e0607020415060f080103050c0108 75
    0x5080d0b0102c44468410782c8421008640d80c1c1004016a00310003000c920a000303030411341d60024030000700ea40454003000081c514280c80d00c40740f04404541d128089800945030514610082c00c00100700f4021b043e0ba8114140790920107000da0100c426041104045c0681200f00952402c12002a14203a8040c1d0a00680d1281030b810302ca80f8040b03101c0c440034400d10864041e4910018001c8102c1c0e944600d00e6140c0f420b0b6160f0508040e201e015520344440041c0080c0510b1941e09500d4903003940144c000d0a0010300c15840e03c031000300c40c440c11a5110081c0b88003800000840c2400d1007510089814200a42c071130a000b55001010420584500c0c0003900350840c1c4400066000808429542c40e1040708106400107494002500d540a07003185100e8190020b0303600f080d040c0401c00c213480c8100144154207a6056600564090b164214590340208040c040d040c010b0f103aa103d426014081040c4800181d0300d401c00050140301b241c03c1d0201040681b000400c006040050700c040c41441c24209202039079 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 930862895 1250 930861645 930861653
    0x1203011a22060f0e04050c0d0915050420182a031302030606010807021203070c021905091005090105040209041509060806011502101119052215030207 66
    0x1aa078114180c007a40c1e26400040039900303e142c0743c08500705a00c40010160002c810001154000c80385941d0407041040003e01c1c890f00d0754840742030280310390f8074220f015003169186001c2b10400c40702100ea1544080e802c4c00c0d898109002c1110b0710714101d4010554060300c10544030034420103818182d4441c210710114080c502498003000b5101d140400880d12840c281d078080d000e4215a10042e4040e0080c031000c40d015500c51208140300b00c040e41c000380785a0100d41001e583c0d55100500140c2041250031020006940342c8a20603c1c48a460a22504560a050800c500701e01d0140c01c000e42c290000b0000c2201d61a03841500741100d1084030016101d000702008640541507084141e049641d44080100c0c1c022170317540c080802e403002502181c0140ea01c03229010004400d03500390f800581d02c0082c290024403030b00c2d0481e203600f50700e414402d8203040120600010300400030b06007201180000c180000b0600c140000750000e844260310b540c081c81d16040e40301ea102c00c13000c2050010143c000070004144 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 930864145 1250 930862895 930862927
    0x150c09101d100509090129180a08010e100612030809100e070e0109021315020f16050f100c0821040b010302041d0c12071d07021203011a 60
    0x4000d0103050140c02680d560b400410310307400115864455400035001041084200700c911544074012062100f510200b5403000702590000350380d0f100070f03581551401101e030311141c82e290010070341100085040f42c1c4403441d00d400c0c216201c592071400b92800c0f80401a01d2407941c1c002da68290075040255083e00c80b1188a4100b01c85003c0d840c0d503050801a04003405c60b00003c0141c02c60708a0038601005980340d0116200340d01c42c4020809029888040900030a03d000101d05c0c0007540a00403105212130304c001c0306051201d040440e100d00348d0740710341c00c01c03050810490000024800312500703400c0e00c01580000d00f05407000030020b850f012011503080c4c924191901e14400032810000308900500d0203140002c0700d1003003400120b002d6070904104049141081410b0061410407902509a0b14000350a21001c61300f030b841c040d1000c0c810400000b4050b0140e038012184943ea08401203503130300e027283c030107480e00c0f40d0a50320551261003040104509015003074000c10f404404400c041d07031040c51816240c81 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 930865395 1250 930864145 930864197
    0x1a13020f0703050406120207020901050f1c08043b060d1e0c0b07020a061407020418020a0503071a03040213050901060504061d040204110c070305150c0910 68
    0xc40303400080741c605254020002c1c2c0100c4450341e5964500748040000c1000740c1c01000402500301d005100140910324207905964070074800075080c00c0c1c3d5030604e04040020f154590200b9030701c4001c0041e0a100e403271580c01030440c03062512160000c0610300700404078207540043c070040600034001808030b9419595000668107482e0003480e07401003090600c03005094000b00c0d90301100d150340d5488000811920210603542c1d144d4004003c0110545408001d49400400c0404100d480780200700c09401a6a180700b001846031130700c8551211b04419105011200e81540c100911943c41360a0400c6440740c1c031007032071080702000d26084c1c3d143d484510200d500004070310f0400002904000400c003603094154044811514100c0717080c4685943e9403082d10308011240101d481c1448800300003005802c1c0f607000380209011380c0403041c0c980260410076a061000a400440780d83d0407100001c1188096600400d8114071035800e103900e0310800c3c00004214907410603590003400354000f43c1c544042c4424a000d41 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 930866645 1250 930865395 930865417
    0xc141f111f06090506180712060b0705070503030306030318131a0a050a0503120318120a1d0d0f0c0306050916080a0c18200307030509011a1302 63
    0x1039825064914401806100e10a0076806250600010f00c40405009035401084040d0148400300c040c103122446044005220100b802000c2c04103001005061280c800103140d8103520036115401c1c0d2030300cd800c4c2410703a80050301c40c2e030040c0148038290b81d0120071200780011410b00f400c1c41d03a40010200d0074186002c100c401400d45440000c50b0f480344580c1d1f6181c3c210000316440e031001c41d11001041008041c4d4000c294066000140c00d64000039a04011074004500040d17140340101d40c80b90403443d0086618600803071640104600c5010398001159510b64103202e1005400701c95140b0210300d20220310034004c2c0c03c94021300c4408040c0482444002c010b545c211005100518001d0b813100d642d01c7c4130030140c082d003080f1610001000c4001140600c6070a0b84800401e0010386403000c590400b000d9134000e0407101d81c0d02ca100f200c0300740e0350310352010f5108441c6a5042d200d280a03840a003c488005109612590500001400c080a400c2d030040703082000300c4040c0e08031444500900003c2c055078891038 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 930867895 1250 930866645 930866653
    0x20903151509280b190b0a140d020a0c0c060c0f020108041a07020616110d050309030d020a0e0405060f011718010e0604120f020703170d14040c141f11 66
    0xd03d1020b45412901040307509646128030100424044e08502041d071040d00d200b62800e00034213021900c503900140719140703141c0c0030720304082da107078044002c9038014886a0081460011084200071201c03d00e80010b041d80d00382490300803d141c59846910b8100c15009040112250000701001110440140407041e01c0700b4030503040c038003204080d59507201030343c859030004c6503041003070031030780c421090317000091040009005040044030b002e5642c6d13000500705081078001440015010300c0540301a01d101c248541d5502c20808403182800f04550000c5c010f01d018090780303120400c0d542d0304161454142210484031000076920200b6255682c1210381004140d5420202c4081301d107100090703450f00403409288450701c002002c8000b52034400c040c001d41c0c00907030411501017000c41d0464285034280307441507407950705e0801038500c184200c07101c003203030000940d03a800c081c803003400704014000024004051034028821000c90001e440010701c24040740340ca1460400140c031552080304038110000aa400712 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 930869145 1250 930867895 930867961
    0x1215020f030a0f0e011e0c020a0b04031e0c1212060504022a03090a14040204031e17031905092e0c02011a13140109020903151509 57
    0x30001404002190814660130003e00c11300060045c03045500b281740f000840713034004901104040141414908190079405800c0c10180451180c860191141e8802c3d610a5282c8090500041444001c03140200400174180b11a0002448036819021001d0b9503040c190302183c82441560301500c03198100d250007078008a0030382080340c241034444002c40c452500002c003940c1341c2c00da20340d40c2e0700031544026444440c00108112080b900500d00c5050344000d0030251516803070b03444a00c1003415035080700041e0614202c0c00020302c600030521003180425084803510f1810100c058403070715400070320301140003599100454280039081103041c505c41104c01c109005443c1c1d41400094030079980d48890b86841c104059484d2151061042e8400360034081c2100c0e9040d11401c0600003c01300c0c4500350311482d80d64016496042d100180b0441c020304c05660f0150303440d01c900b8185814641c50301c1e0080c080055001c140569003140b8071b0030b1000b0071400e071a0f802007581c0f0071003403240180d03942d00203000411160030b103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 930870395 1250 930869145 930869161
    0xd05071404060504020306090412020102090406060f17010608010b0901120603060b090c0a020a0609030e0a030507170309030601171009030509040b01020d020d030203070908030d05160503011215020f03 88
    0xc00c0c1280880d01000810354880501040e0703c021207090764080503113800100010703021003c0c03044005892000500b852a000081800c46c0d00d02c3d00048082050000d1082074258400882082404041000d5146502d005c0c005043c03414180102d000c500004034091890743d200d401d0300744440310420818011182d0300c1c1441002003419048081c02801114006021181d020003200e001144030783c01055101940e0b181d87c80105202d0308114104518a003040d0070750341e103030561100514005c50180947c20702e412109006028100071410b0150424007042500795408544541180e015503000c00942090032a21401e003210946248121454541100d00f4164024050550500c1c190340400056118000583ea00e823892101540140c2c003080c004000e20380f20307401075500080d140c00c00240b45a25032910078116005a01c505000540c2c0300d003001035803d001030100d20060030700e090041c40c6504140017004161120b900241c8000c12546130381100100030b5044402030206506060303101e040406d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 930871645 1250 930870395 930870419
    0x406020a08010807120305070303022a06090d0c1e14010e0c0a0b090f0a12052b0f0c0c090920030d09030204180b13030906081b090d0507 60
    0x2a400c0c00003004000003042a4000003915030544050300003442000c8a00c2e50b04607181e600c0b01500300c08058091110301c420705150050821140708000381c4840a941e00f840040c81e04500900000c0741d0740c800800a0603172a00b2001c50403096412100d40b1340150500003a419000f0810000100000c2c812001031b8948c2d1300645c040200111150181d0300c9902455003040f006a120b07009081c40c40008200703030042450281810b020f601000361610607902e81d11126542149104841550250010903017841c0c20442081810030140740c450a11f0420466042d004100903030144220341400081c049550512a5900c43da2005001e10234041c04080414900f51a220381800c03810f5009030520509a8001d00e804140c0200811455a0b620800361440e001c1002400110040103000f1315507400400214200c040498420750981c40b8004800c8680c1c036005207a4142e6500900400c000d034403e0000003003202c40c482c2e00c80030100e030226456200c80320004020359a4030800805902c2152000a643d05281d1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 930872895 1250 930871645 930871657
    0x20315190203040b06010c0303061a0a080609040b01060c1104150312090b0a0e011b0606030b0c0a020316141c020705041e050903040906090213060c2315040602 70
    0x1a9011118045040d100800da01003a90028004159080060300551052402401c803501914010412a55031404c2c0c030501c12502542f249200c0c400140640c00301d03003145000303400007030030740e100d000381d00d00343e1078080c2608818060f2100b040201d17940c00c028048800e010b0b0300d900000a00c10800303405042c00031502c428881c40101c4171104841f085c40c1500b0302501607002100c03800b000042c9402420030007250302111440e40c26051000c404002c0044404644a03030445500c40e0000240c060b0540c1402010f0700340043c007c0ba8410810841c40b0341d0554040140d490030010364480c20503800040c6880400080342c02080180761186490303000049450828041488400c1c0d0262070b42c4640303a6007030000b960060041640d41504041041454050950140d540b100109050307a04264a440801056400560100c4101c540104002100e10340551341d0308004e01013424100e0222819540707681d031104241c0b0000030940345143d005016007509010720841032200d51400c0b01035240524104000790000703 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 930874145 1250 930872895 930872911
    0x21060f090c010e011b23150408070b040c150f080901091707051216031e120518011e0c0e01140c0309150a030540020315 53
    0x2062008030082100180d0a506958003520b03041408010f540d5060940380400301c0749880c84004020821a100900018001d440b10700d4a0700340141300280f83c0170f5803003032204440304144280000241031004a6003843d9003d81c00c0102c594503810802500310b1f842d80043d0603582c940b00814803841e0300290801000406860700c4045444004070682203da0b4010010890141030786040c100900e01c07406009014401d0086a440625405550605410024a6500102618000f0740425821202c0701508433019810a01141302110000701011040e00c13080c01a90341c1c5402080c400342c445280d07141d143c51000001d00c031055a0399070062000c8000180050b141e032410880d44d8020340b00703413440711180318140d45d2420a25509170300f618481c3d0109103030740341c2884100040c445a40b945000c2501420429102503250100d51340040c050b9000180345060320310590b540262002400e403040d69a07070030008810380c0c505090500b058141c0b0b03072850002c5c3d41445421103030005c200e0004446c0d8030074000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 930875395 1250 930874145 930874171
    0x361e0209010e09070b0903010f090b0108061509042003030a0908010b060405180a0b152a030d0903090515030106170402010207050127031203200d05062106 68
    0x1c2d8481e501c80302c0700d082d02c0e051241d40280b0020813140e51000c4c050400c00d8401000081d4032010310030000102c4040040480c4d410300c0c1e00004118502051042540c400d800714900f00b60f032448e8500040075100001c0005056807028035041c0e2100400c810101c007010f602508507585c8400389100075100103441d03c1849580d42c2070030000080f6042c080140c038110707600035180c8110a011020200304446d0028900e020703040d03aa120340c407400d56540b40680007250401c91203541c1c03482183c01c4100f0134104012102c40c174951003035080e216180008100c0e0340d080840800022000c555107000c480c03610a6506c11079205441500d1902800c2c55400254121529a140c401884403c8552640490320840d0042d0242c1c02030f110400555005039030419a03244400c0c6504034003555139501744a5824543c2060b2280344003055080040c54242c4501405140d46441d40030144c8180320381c00c030480c030505040d028070031748a6000c61420f03150300f0f01c20240d19480e074141c0c03007c107108285540d075250800c94003101d400b40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 930876645 1250 930875395 930875399
    0xc10020705030a1e0b241824090a0606030c1b060f09050d0207090b0a05030a080a05041a130905010815093405010201361e020901 57
    0x80001204011240050098210300308030391514102c40040345032114121441c803510000007100c0c0c0c80b03d1440740f02058040c4411a04da0880316441c2c0d6000c142007401071401c06090003500c64035407045035200700e000000ca241015001c8a030715a80300c0365412030b6080441c1100384106110140c00c42c106640295404102258540c0c40495a10031108042d158100b40c4440900126000e50410901010300303007004075400740030382c0e03a062230b01e40c00e0100d010061300100401d0120001500404c0014641241e110750802e0404001076114041240003c1c040d80000400356011406582658010301017000e941c0c2c085280d103541c400c0254070080c031140e10620180001f0900400d14890705d81079400190042c20b58541c08030f1880c5180d10054407405161007400000740342d0104500d1081e50a50a004a04010080b0340b42c10f20b240b107841d50085819039051045000c07c614051640901001e81d040350b6195401d038602d41450038442246000d00004a450404c2e81d03401008112040c18600c00d440e0407030542e07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 930877895 1250 930876645 930876647
    0xb09030d020309010c080903070e01260d0518240403050712031209170c031309050f06010c031803200109050f0d030e10020f10021305060a02030c0f0c10 67
    0x40303c0c8071a000d01040840f40380030049800d0001920040c1e0015040380d10130354440300780401301c02e402d130700040742001851415002c1a400c4001c101e0000d44a1005003100760b12034002601c140202c11040d82480a404040450341d5181100f5140b070b092082465514680ca01002c100c20740e03c9804140c50522403c0300000302d03d04000340b90405140c040d580d80c207160154401c001c001d0403410074180e42e490007034407124440c4d211020003002ca04540c0402182e982d07a03148a1060048525804240d10318589820007250302e40f55a0303050791042d024038060040800c50f01d000e13100c800414442048090304000040100160034490480e54000c6003204090001e520004454078003641c000c10ba0000b0f51240100f113242821151020420300c6820700301c903014084008242d00704105561000180d00440c0d5120202c803040c80b100050748c401c460250710f41188040c180c0400c244522035075000307140c00110020050310a1083c1c0c0d0002e02044161444c040b11800d0256445420300725031841540c19110440190b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 930879145 1250 930877895 930877897
    0x6020d120605120f191101201608010b010c0f06020c150c070201090b0c0d030b040e010915060b0304080901080a0f090b090c01030911100c020d0303060e0a0e06060909160b09030d0203 80
    0x6194000c01441c2102c002100455140d074003c603101c95400c125003048004002e0030b000c021050701427900c01c0c0c038a9034904120b203420b40381440759045c14440300ca482540424002d214600040307400a4000d03a07500410b6403110701e850001c000145044002c80d041c040701003000002402d2440c000d0303a4000c15640c0b14100b0051f03e104080342c0f08007503440030075071600007030007508817512070a001000041d00d1020b900740a400e440790007108860340d140c0240a00b44808091040e08090061550310714254641985c0c0d1180c1c503c920034031507060001c0e0300b000030000520f9401445c5000b0020000b444141c0d050301d41030200b20016640c0e801d01307020307801840348554440d03c45c417100039811103d18001c3c40c503210113200b5050643e4900100b0061000554005a1601140507076910b1080e640000d4141c9000007a109074034002e03141e401d950742042c06001c04010001006a0410300c122545c002c0b0391900d00015140c04842041d0300020b090a9000007106c500c030b0350250411241c01d606444400041c0c40e800ca860b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 930880395 1250 930879145 930879193
    0x100519050a0503181603210503060d03080c0906040b190311180a03060501230d021018031403040617161107030519110a06020d120605120f 61
    0x142d003440050100380280241036040301c540030541e44102698160100d044100c0c3c1c10a1310540d00907103880b07400b901e9445412204c045c1c503141c51f03821800d0040028400c40c48104015042110000106280c10005c070129150040b0003848140d4440da1150b41e0380f486d130050f1403d040c1c161040300d03041403014081c0c06800da4080d1159401d0b4940249601c0542c100c030788201155400810303030f181c00710003d081c500c00c40e4041c0170903404104420b203c03000f901503000f440340d1a0f00e0080148042c103038010303140c4140b100e1800c00c0038103002c1484c50b400b5034030210a0078030b98409024181010514111000040004c2054512550380c4003041610388410a100000540d2640c6032002906e1680015038481c03035106542d041c840041d101103594075140c103407405401d405800058078400c2c120204100b00e5207007201070b01c2d0081d110643d4841c9046030180d11280d00e170505074140058103000e0687d510480d4010806898001c00340528402e0b0b62400725a40c042c03002d1149500e03c240d84042c031a0070745110309030706 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 930881645 1250 930880395 930880397
    0x2100603080d0f061503050105031212010e07050d0f0c180f0605030712061421060f1909050d09080a0c120201091203020d141c02090609100519050a 65
    0xc9454840e40b0000000c164a10006841030b83d160341c0880c190404041100a5003a2a0307030100307055041004142c1880556900d02c211001e040018cd0301001c0c1034000c45044549120240d452603540340400c0d03d45102e01c4c3c14000003a45801c1d4050341128482e401507204554a54590f0221414543c0c81c01e90000140540b40348030442c00001c00645100e400110303880032051034100400e2560991170425111560454060020912160002c1d070402d07000f1040e01916405910715400203504c0d034141c540001820380050900d1040000e01d1030390303a209494070000203008040203000700604059844180761b038506000034201c01f100095250b000101070040981060414070980e00d41040c035018507114041c200e0520150140010b00351502900c40480a030290300604080b070704828004001007080d450300f410100c01401802e4501c04800c0307031011004000000160f407a94030f00e0001d8010b000d488107855000043c0310380c900503641c0c040050b00801030328045038040c0314401d02c02034804e801600d481c10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 930882895 1250 930881645 930881647
    0x11040b011103310f0e09031315020c060909060108042a080606040b01020706030b0103061212020d11070e18121e0a0c2a260106080604030f05041e060210060308 70
    0x80090032503003c0013600078041d1822203182c20500c0c454800088c05a5000b0002c3c3c6541c0121000210307014801407041d60411901c40703140c1040140000d200d00c2e400b800b4036040002c518001400c01101c41c20102078501c0144c030318500d01c490440c102c4101c008a0040300f04500a8001007006410940034440c040f80b0305030090700346a803d14008170000d1148406842c1055111301000800001010104040c2400340c4400c1246005150010345040d100d80385000800c5148114540c001e03a01080301406d450304a403a44400ea11003a062108502d4240f4035025180120507090b00104460300050814262225020084040480005031079010b580d54100105a1000b81d0340c0c0029009180c020030300000d01500c060350b041c0c0d41d080703080302000c541001818520b005207002d203980040035015040c40041000380841820000010b880d81809400103045c03007042000740c1007050290090710060040d585408552400c0024418031034000c0c4d2150790054090850011283e0203031b4040d05080e260015411 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 930884145 1250 930882895 930882899
    0x1401060206041203021c09260a1407020303041401020d0212031503030d0e01052208040302060714010e0a2d11010c050307060e0607080411040b011103310f 68
    0x2055111440381c0c5070000c00d1703400c001c070b00600d980510180c80305104c2d07a031001820b400340e0b1500714020003e540528404c21411401c1e2250400d41c10101d8100764154509039010f0340e030552016140340074128009606000104000c20540e00c40c200302c1e10060000d0382241c0c42003001e03072801d0343c480d00a24004100b2060400008100c03a44640c000e2a0400b006021245002013881c1418206d5001002d440e074240d44a01c140503001078145e00e0054100c4e822400c091345d140c180e9483c02d10f94810f038440240a50008a280030174082803209c0074903c1d40f5207030000d001800d0041c00c510740303c0840c488200c42e034042c0e40500401070115400c02004d1a100d051000034140410b84602c180100008601030401115030f0410002135424009402402d02c18080410301e002000365482c10b042c001032000041042d410304200102d40c00740c800d10b007085000d803070002d00d5010003c0121034006030349850f5145d0340720000b80030160300e03501c107602e0541c94204e503000d0205100261004000d46010700c0b8003c1012404202 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 930885395 1250 930884145 930884153
    0x1020a0f110c01030b060405030a05010b01030f11161a010e0f0c04030b070e0a090c021b0f06040e0408090402030c12070801080a030315050409120f170f0601020114150103140106020604 81
    0x1010745c0c0039100610344d604041c0e0303c1002920f00400070000303c909075101c4600304038a5806001c0d5210401b415001480000c03d06900d507030190160303100c0081c108040c42c10031300602105000008001c0d6104200c00d516603151001258409410384241d07980c070401c24009140e0f50002001c0ea400d883e40301102c003c2035140c0f1881107034070300040c1c110f45d944200303060b40c0010b15180d0341c401d40c42100015005808001e40e4005194150761084204501803010a05005800d81c6c41a00f1a0160394010b0a07112154865040046860185505140c0c01910000512002516182c0131340040d891121540c1d1440da50343e20304070740283c401e2040500503800b054003040083c2c040e0708840c0c12015000e48013244140c0c1c03680007030281d5404100560728040b5206401c9185a80304802481d10f095504081c000c142080200070030316031008150000703003100030001c80c0a0780e00c01e4114400002e610f005042681c00d18541c1070b1540c0101414940c0071900d030103000750a1007a1034044c0f904841090b0040c14007565280c131 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 930886645 1250 930885395 930885401
    0x5060301051021151e0b071a0f0402130e0606060f070f140d0305060a03030c02030c090c0d14041518120201050f06030105040222110c01020a0f110c0103 67
    0x200c005200c5040c83c2440b11040c007032002c07820b07420145004129a00d001e1002008070b041c58101c01010140719082c01500c002404884003252051600241d0320724090070144c20208155a0070b0541c000b021045c440740080b06c00742240124001c45107150444500ca500034100d4205020b4480140c2080b000110146004000360650341000003040b880c01e245580c6100b807811000800702c41e41c045422052022010411100444840c0e508042004e81000340015881c4002c0703200060030080e04205030411034406110f15000100050411402803d140c030b0660b02c5600011044454140b03010a00c54045088010590041c0d03004550a041c0f42d42c2d400f04900581074a900391f40040000d81800800500900c40034401d0102d00c4c2d000007450305000012103044940a0f060038866030412007403102681d1030b03405400070f07010080c0480c286480c452040c40e02801003911a010a0308000c500414294019001041c1d140c0c0c05654400000e24181070550784000700c5d80d40f101c80c1d907000000300d82042d4003d078 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 930887895 1250 930886645 930886669
    0x70501180513020c0d0801080a020f1819110a0e060c03120103030c1a15090a0b040609091106040e040f0602040b160c06050901020a060b0a050d2402040506030105 71
    0x8220040d164550340481d0301400d04035144582954002181c919442003800140e01d102e9440c0f804180da94941081603079030f200b0341d2402030301c1284403824160341c40d80e43c05002c2c40a650074036007589903843e0880200006805240a0640786402c05103031507900f10040d4116000b5608a40f512000d881c13500d018401160004507028034144170400c01c40f10014507140c00719000718869070b01e824050404c0d1400e8201e601004108a81c407090200038003403442c18440c800c403403030182a01d250500382d490300c01e024080e01c00d1781e45954020b4a4801d0103e142592604040b80290282481e80c2200c05042d043c400d90384914421007076011b40840c00300300060820f01e0708604c424002d41001d410a51912028459507100014107001443d0740c80210b07040185002c1544014071a50030b21500300205240040d44840d80f04d400108011b03a100380e1040702c2c1e0389219603140646400307881c1150302840e500e4460384107000d00304070352031001002031154548001c60013110152100541140e081d030740303404c051154540e035031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 930889145 1250 930887895 930887927
    0x80606040506040803030a110a090b0c070306051501081506032202090a0605030d0c050303070525080c1005040c0e060d02091513020702100f0203070b01031121070501 73
    0x4120000326a60707a800503001804413400510307503a051442e2920206c1d40709482c050b98554040c0281d19926800241060031141400c00f2295107421841042e41880320356040100306902e4441440a0801598420071582d20b0a0301e07000d5842e10f503070004031f1501e031407500c002d640b0400820026401c1e440e107407002d03008009940d04070145c100c460f900161545408603020007040780c3c4c40200b0041481c0802c01042401982d04208244008644810b0785034480144003c092040000d0400a104103218120a0b050980c5189440d2010240b6110000d540f00b42c115402a110325601289005528401e190055610019035485207190401014580384014586503010118005400160300e4085401c2e00c41c1c00e6031509110ac04008034208050b4140045804090303501c18800d1600580b107080c609011a100d60908004443c0c80d814100e2543c4680c000080200c3e80280001003009054070040e0301c1c3c0b03101117030710392401c00c2c01444111030f50070104451040f96005600c204850350140000810286031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 930890395 1250 930889145 930889147
    0x10e060705010e0a060c0302181c06111b0d1209080913090210020a26041a03010e0c0304150e070f060e09060108090d0509040b12060702120f0406080606 67
    0x3611140d00310f9810400c2145160003501d0340208105061140d8a40484035080c210b040882d21503002c408030901c0300d525030148202030030f40c19032000c043c0103082980c1c2c0e02503000c0c0702e4000d1500c00c0b00303500c0d0002104551340d0055508105903030200450304000410056030f4243e05040b249003070700064030170f250098035900010048401c10341c46018049007d4500400d000c203003145540b040c80401400d040c401ca0854000240035030001d6942c607030703c00b0010000e10f1000d14140e201640703808540700ea6070011203200280803959001c6a04007001e0341c101c410141025a265841000364030b900c1c841110011f04070000806070944950a03076004091041c081c004031500d0035210028010303012450f80001002c00c0c8844810030243c0f5100305000c0d0301c4130081c030b4081114109445890354031382403601c2c00021b120740458060000d84881e0700c4500c0300103004100c1100c0b124a901d0007510340e6019500d010050140074503020b2506103110456001c12855a080c84c9000c1c034281040303d88460103004164001c2d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 930891645 1250 930890395 930890407
    0x1060c0303091e05030306090109110906130906121e11100e03030c1f09030905060f0708040f140909190206040504050a06060f09120303020a2303090c09060906010e06 73
    0x410070500c0c1d150303240711390011641d90600c081000210101684142c000a050140c00c3c052903800c030064404001d8180c07001901d40d003007120b04007240800e40d0008000d6604d8100002003c001c0e0000488880c0d00518034031034107024207405542c071008854400307840a007031200c800b00300741008510801c4400c11413510443e400c0c4507500203800c40e442a003036030100c0d500170f40b90184261a2014590b1012175a00b004204d1112259005041d00041b8441d1500c600740c04182e4075120030401c0704580c2c40c60383c014011a034441e1145203008440d4024026030b0443e401d20581d08010b4241f40d00c0e003030302407444203004008500c1000300c1843d0310f00b0500b00880c0c02c03040a000004441d100ca000d107601a01c0128004600b540c02c00c14020b00030345100980c50104210f200c0c08102505500b6180e41100741c0600e0b0169454aa2503c00e8401020340c109055800c204003000004c8800c9500181d805050f0820580f580320400004200a10030151801a84002020042403080d07004e00400008510060605400c020b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 930892895 1250 930891645 930891683
    0x7030309052803050309030705030a0213090305040801020703031406031f110c0a05010b1801060507170702130903080a061a0a1107030506060a0501090e130503251a01060c030309 78
    0x2207030950044811380c5c004104400385150030300200003d404150004c1410790b0842c0c001565541000d043c61035020b66480c07944052500c15000c03100500700000c0255524079039494024010006580165814046a070105410340380c04602d01c4500c101140d00700c000801400360386402000c80d0b401264981c8001c104400b2219424000c3e035509034015000040c0c0701c407210061046038450400c0382002150258014006503410405440d0400d4102c41c0c44032046080f81e145010314818454080c2d4080c40e504545070750700d05690842c5411074070903582e00180d0b0300c0c1c3c3c050440a0759241c3c000c00b034800100500c1d89200007031050141c0110100e918000004543c98070409003040c80c0c98100b40d5164004e41304001702401c110046000411080c6060002d0034648003040200c900c0c081e141203a403491101c100c0041c032004000b62010300780005001460b0104c01c40344102c4122511000b05c6001081400d1440fa41104400c0241201c1c560784418107a261103903012401407903815801c60701c0035140c4244800c2c3c8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 930894145 1250 930892895 930892969
    0x40801060b0c010507080105090f100302130912030b03070306050915180c2b020f060301091a06210a0204030c0b030910051b131a090a080703030905 65
    0x14a4070451040e610700810180d0780c00e407007000344a20188011034004208640ba003c555070303071000c80c092116501c0d440304a01154608400d80c00650300c07030b0002440390740008155006420180c8079000302001d14075506010790544180003407256042d040b0240400c00310b115038104585c00007890b0180d030311004090f9404401800240c41650040410401c0c41c0780c08a010041c1641e0414100c8484c083e40400000600c4104088031412030464003152491045445400c58944003213001400c0c25220b41c2c44170341e80c07002060200c001c81c40100300003081d49170900307000b011500511705803009404107000c2201d4001a00d000a820301881941c00c00c40000454042d41401e4007030a8400090f41e56410202c044c146012000400380207071924010501c4054180100c1700150000783c3c64041d900c41c0c04402c558000050a6880a8000408000d00740000c030f8492000300100c20302140c01d44015600c038000141d9a21075400000d002c0345407460107000d14540aa4504030012034042d54036a200ca51020030448 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 930895395 1250 930894145 930894149
    0x1602071502070f14060405060f07201801030c0303110a080a05030717060a140612041b060906020309040504110d030f08130215030606071e0308100b031501020304080106 74
    0x682055400303101003e03010600d02d000300714007a2001c41501d220b40001c0e402c1c1c411482024410360f40000d1400f41c6010300400d807140f070fa4009900c5402d0080002540140b01800403905200b1102203882a45074000c9103007540c16260003060a450103411590203580f0a00c406103503244520a8120900020b4100002000b101c1380541e6540c0d281e0402080103000c542c9482646400c001e440d8040000e25124991310104032001c2c0c2503613101e111003440110301984200c0c465080000d2a00d0300308000d00c01484c1e243c40220280400040001d0780e542d10456034829940180e00042e081044142414030305900510b401a015040b1020720603a5000081c103146600c00080b00070941d50310102c510302e900905030961010046450f41212107803035000902c43c44102162000703e42010000c160740d0b440b6a000e0b11381c2181e104010040840903202c00d101c046580c0d14081700040c9200d03000800e505c0c4443c0e102001c803031500c6d140c41e0640d20741808412030301100d040b0f0340303045210034400010851030074090307600 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 930896645 1250 930895395 930895397
    0x90109090302070b0304050d032c0f060a05100303080c090402040816091104051c0c08031c200d0f0c0c050c0a03110909011b0f022416020715 62
    0xd103040039454003a00305030310340e070012548003010700401c0041240401c00100550b6103150000e4036000d030780c0755540503910b59140101c4603c031520540e0a065400641c0c43d107412011801c032100d0b80da13007560003401e40e041100d104030f014090507001c100090041d8130303184c0c010b041c00807054101541c013001b241c103e0300180e00542c20359208174110900e40b144061800081d1140c001c0074052220b44100a144500c224030445005001412041103d2842c0c0e0011100c41d950100c1c2c010089135039007150503540e410643c07103418010500740c05968030302c6441c400c0d40c00303080c41d20340000d06403c0303c20100040c5030014015045030a07200d09290200714258483d500300c1040b142c030380400148903418400d1610b42c083c10480e0243c566030800b8030106071161800302d00402c0c115454485a03850f40d8050340540b94000008013919241e1100d4041c0c2d9800c80b0514000d144c00c0d80c2200c4100321050f0307080000201f4050400c07500860740020400b50b00d01c02030710301c02001036401110038059545000410340304d5a981c1c008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 930897895 1250 930896645 930896651
    0x101e0302010e0d080a1805031905100b03070501030905011409011a01080415020a050705060a1d0309150903070f0305060108070b0c0303070507030c0501140a0606090b180f090109 78
    0x110840da04078582d20340c2010151034016000100390745241c00b40c880c05001606008212102c01950300186050001500b806030035998a0a0002107801c806050040c00711624015040340b1190441d13103110303e489038417006006000c210b28004c0154004d101a20003907031503540342da002c5800c2c44841c01c1d0f014021094000001303a10248a050344480040c4020304134104100e450501002c80c0103c0604880c070151202c2c01680c400e40318206451501c2801c0d03004045006142c00c00604000c1c541c401100c0c080f03000c41a1642c541c0d010852a01e03441180c1c0001d612041c03400901c0c1316001d286000d850484005411101d1164030354412040360001640111081e501944c014800b8440c10b010a500801d00d0400d02400d2120340400315840340802090b505c01c2010110300d0f00e00341445103032480c01c4030b60400003c00810003158040c00c81600100c40d000400c60503d1000685180300d00011401c461030001043c1c2400003010b800181200d060700641e074401c4038040003e107a40c0c0c912118038002c2642040c00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 930899145 1250 930897895 930897899
    0x90112020712021b0d0b06180c0d0b0a0303080f06012606030f0105060a0b160602030f09071401091a0c010c021c02060606041e0b0a0207080f010603110603101e 70
    0x2803614101d5000b03100c544e004c41035580010b80702c0e00400c000341540708501b8205561000040340710300e50301914181282034444140300849030650b00800141d005042c2c00d104e00724204c41801285049072200500260304c260002d480c00403014811504401d0501d404a40c001007400c0d07004059601c00b01c440d4030047c016041c0900ca240400803a0a51600c101c000c1c459842c1000005000700d00a00c0f0300c059100700010303590000d0502d88071011203203074002e10454407810300b80e51050f56651304699055151050b60804580e100010b001580c5403c0140d488102060918003020607086120240210700c0400307018221010074207010720b4200f1182c0764020201414100d8100c41d054070400114419900b208040c170541c2d481d850100c800703482030385410608039100003241015081030340d8403429060310041410705d1a0ba47c046008000c541010b0300700d44d044074407507288501b200c1c0c0c0c40c0700c010005000400e108000d424190082d550296014540344007459072142c0c0c009815000702d1001300024100402 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 930900395 1250 930899145 930899147
    0xc0e030115050a1818030f0e0a0f121a0a0917280507140d090603050c090f031005040f02091e060909190605091c0f05090112020712 58
    0x3640c0601c010051038201e40c0c0c0c03824002c10104042c60280d038640140035010000340381c4c20f40c3c100304c40c90a84080c60b00210a081d0800401800800c800340c0c0c0000c1882481c02440c3c9807554a40040da8100000454605d00d8540703588400e0301a54400c840c64003428554a80f000184070545100c0c0e018480080344692061401c13034181d029040c0c4075424004188a20044c18810204015410111545000e50000940c2080c0e5031030084d1600108203100d040c0c0000521940494407030f080c0f090035201c83c5001c40e180d0700f0a40690324200e47e09200060280181121032600c0200c3c100c00110140940d60f11600030000507040e264111000d450255000340703441c2c118113044024070f0340008045d05031500002c0640d940583c41601411b0710b8414420440800c0a4a0b01401500c401c4186c621954046982c1c81c60600040d01048540c0c00e901d0103250740160304a5804000c403000b003035090b80c548801107080c010039030759600a143e0860400890701c8880303800204034401032082900030401d006200b80b064070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 930901645 1250 930900395 930900401
    0x5120a08010b040e0408072f01030b0f030c2707020105160309110111010f1404020f01110601170115080a1103070b0d02090301091208040314090a0e0a0f0c0e0301 71
    0x4880b011200702003108000c500c1d400350038103412651200e03889944200340d04011282c44580305100780e030f41c840302c2000c0c5100305600c0c1411a2007142030b01c05204144d0880c0810403401035502c5c030325800d608400e202035014039009440d0060310704102102000c1d10f41102901c601114100c0e16940540e6566040c0705440c00c0364101040126a10301d01844100c070240c2d00c1c0103042d40d01d80b0b9402c0c10b20400d640f40b90314121003900f01016808036114100320300c1d104001c10607035031002a5000e9014801c8040b2401d00c07544500c80c42c1c4003034000310008040700c0e442c20068601ca5000521201e44035581c48441c07030815412111030100500c074850007007488481508000e03c0113207a80000078866404000104500c5484c1010b0b02c80f01c00a40c00d00586541c03e000210380900680321004181800345003030b2000b8103401c5480c5134029802959046102e4042403d0400c0c0e44c890f240400d6442495520200403143e002103140303078072046000010500070f0610f1001c10585440310780c280003148200c100041c1c5418244 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 930902895 1250 930901645 930901649
    0xa0c0b1003200d17090a0f050f10110105151009050901050409030314040c080f010504020d080306310c050418020f0f13050a050103050f0f070c05120a0801 68
    0x9000c0300c10680c074560700d0140504601d1241c41107501c2e024824800b43d41e03000f0a5004550300b0154512070b80d0400008501c507603100c040940d12680c0b19400c04105420700c0d44602c0151791002d407846d05e0350500c8504003c01c0b600c550340b1120821507400c180048241080c01518016031030180501d05200900c0d04005540800c0030142081102d00381c810022369490088050459a00b610001110851400c08a001d0100c800c0d00f0326114941e40140001c0203105a00a000c446100c0240c0c3d00328050041d0301820b032403080e18007030b501c1b0281d42c00c00b4002c6038003e0b0065800003001800500e40101003424448003880740040203140755103014820404c112a400b81a40401c0785281c010301d0507040c606146d40b4601130041600307402e940460304462141403401121020050b00b94506c2e11440d5410180c004c1140c00d01946020710003041000a041d4064000c09001d0391a94004141c6030b43c414080c0d284040c401002d40702004a603404080c0828014401c0041c0ca030307140c00130782d587c40c41f403100d010f032100b581a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 930904145 1250 930902895 930902911
    0x5010b041409070b030907211412040501030228020a05060105030706080a0504051e0f150403050306100e0d03080405070b04061205150a1701200702040504060906020a0c0b 75
    0x141d0100310b40d0160201d103140688400e03440683e226160506205c3c500f0702a500250024105d0310819072844801c1e0000d030451074410880c0c000a000c0d0b07507059689503c15450310710302c02d25061005205941c02034000d82000d0300301d1001c0185082241c4442e201003c0c0807400500560000e110070350900000344106409090140c00909800b460094003e1a07004014000c20031543d5038400301d020490700303000310341500345e6049940038a80d11003105261903566040001403c0d106008074029401c60260903148519010b0300c1d0203007560741d080140001066980411030400c00240b003490000e5507041c2041c40b0042c040d81c0c034500c80e0320340344c0303002c41c42d01a40b41c00140c0b11440c140000c010b503c1d48401000d45000c2070075800301300c50325103244040c0740300b030190b04440e1703c9010303c90045414802c03c0c00c0508402541c2000303200030300b403041154000c000e0b4a502004030307490030010000581007541010350098451100001d9440040e1122030481e0000e402503070014280e154003205100603003404a0300b0100d4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 930905395 1250 930904145 930904181
    0x6050609010f0302071b0608250804110109030510091401020702030606121507050a0f08071b02010228020a241d032b1107061b080705010b04 62
    0x100300018250030424803440b4200b40d000204101003101d459440203414801310410b800c1c00d82c40c0c2c00045d0680b9000c5072540c8900406038600d00d003140c0468168540312603a511a10b0b610b48441d00c81012a0580b18505414405035072000000580100140180e544628000040a4a141c90000413400303002c2100c0c0b07030306d80c0184000c00140e5004100144c20070000c4078013440074100810440e0904200590000060130440c0800101e190072a00500130644150f8030303034079013003401c44c41074502c034000f031b26602e00103120b08082c042c092099030102d40c0c0250050048805050360540400007505041c000c1480d0041c100d4000300071418004c0d6003401800310002d20030101c0d100c24521031502171058603010100043d1744003c62071400c0c1d080d4515072a11010301034502c10400007040811911850740c0b440c0b485403545031050700c07d43c42948803c900d845848060001f180c503084089441842c0a03185107419010300340e2180c00180754100030700001d40716000200b5507184500801007150b20b02c40b40314031001d003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 930906645 1250 930905395 930905407
    0x20c0402180f0d060e0d1b0302070303050309010f330303081b090d05010b1c0203300a180b040e0f070e060c0a02030f030421060b0603010905060103060506 68
    0x10300c40d4401000704100392806078030003880d0800110420034598029150780d150031124070340c80d00301103502c3c01e04d4010358540098100440852402c40015100c003e00160020798062000910600c021072f009031290b0000300e00705913903040c0f850880d20141c03045255030345000801e20351988011064283c2c21221002201203526640f80607246600040541038200d40004120b0102044030080e1440141c01400082c2c0103500c4d464101d00828506d02e0381441245089005000700a1041d82c0000300c0c3c0d4090064940704003072034017038238101407841d225445a5140070004400c00315540041c010212403a80c440c0f0700d10fa441c28035642d0fa10238070381080c0c8280c0c004010034030104c1200036000b50005c002c450310b801541c1d501501201c88421f413400f40c070b52004000034601c503490710004e0701e041d000c2e000310180c0305080d0890038029070700d106500c1303000c450380d61101c4d01284c0c4610040c03050881e14020200410b98040c21030018a040d8002d07004000025551020300c0007035681485800041c1c9010341c0d41a160007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 930907895 1250 930906645 930906667
    0x14010e01030f05031921110d05040627030f18050f0f0405090102130803070507030201080705280206090d300c02010207050609070e010303050334020c0402 68
    0x98140009014180560414010001c0c100101c4041c40030804800e0003250440300000d060f01032142000f69820015882c04050450394402c04a00d14024103041c2e281c440c007001c0200103044000d009498143d55914a8141d881c9039802d0300c0d00150321074041d03210054091034040c01c505d01c00e40314901004040380c94400600d501140d03010a844080351040c0000e441d402c001003a4054104030b083e009420003081c08665001500944403c0d255183c81310350541d15a140d181d81e81c062480c0142c0103610640c01040954001e112003600200246445464890600860700c0141408c943d140b4641e54202e11044d8503076030611180e0340180400d40607000c03440382074030001c050845c0802043d0403848155415894554071403c0c1109006a04406006031104410068001d41044030300755450b0259100003410a01c01051140a80717122aa5242d0b07a80d08580b000c0321590001481090401d540306031180c0f400600c0300150021440c20391060218501041000b82030100802d0350714003450062280350404 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 930909145 1250 930907895 930907919
    0xe03031e040c09020304060f091b060c020f090907120515070c02180702010f090b1e090a060b0f12010c020d020706090e0a02120a0603032a02010c0309050a14041401 72
    0x843d03040310301503201e031200c5c10410b000700000712400188502d032001d02c8081040591000d1551f9604856402c082955240250381e0645000c81c002c0d84407281c440750181c00d01d8650700f55508884510111400251180c03c10300c0c08030310f184400c0e0380d00c3e07008141a07c01004403004141c0d010401e0320f004002c8801c1c0d5808034141150b03603009480011010000104054400d500030b4401034207070b200910803134249090480c400001920b07000400e9480c808045515842e2011081c0640712a40083c0004290354644000501c0184202c40e40310a0710040054143d65060381500b685e8480d01c00007418200240019283c40700040d0030718155040710740104407c5800c0102c800031509810400c680c1d90740c81c2410f00000344140c8103104542e81c50601445000c042941c024010307030b40300e030712009208040d80290000794000240403807074818840080a006512442d052021a0310a0805180058844c8000755001c070b03140c1c00c5440c1c3c0089074240b0b1611761409003c0d1100501c138502d100d03681941440800400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 930910395 1250 930909145 930909149
    0x302100f0c020d0230100501030c030807080f04092c101503060908040602070f0e01091508010204181d0c060f0f0d0b030d020c030d1808010e03031e040c 67
    0x1c202c950305030314000d54480060b401c00c3d6118681c5c441148030501c404030040f200e000030603542da51044110150410b025032144038141c1e80c20940b4020030514580d101d05165000341d000f184c9101060022410200c0d204018001804107040b022603032640074220f8000c0300c00c03229074404454050410701100c0940c0070542c0d8000c1c00802001180303200381c40c40c640401580c0c65000501c540d1a0801324801c2c022480b01510680d40c00d5802d03507040c203a680c0d0000c02800c4039405451700e11000d00c0c0041051665035806481c1c06ca1040c0103a4107ca550f910255003240c100d648130002c440d0000980a0510600380300d01c114912100640e10303200c6042140d560303940d65551308218091900000c401c0840f28210044d5080c02030344100d800e80c3c90742e1f1b04108038003a203a1004c45d24024400c027010041090b00200311fa5040260240050500e907803880e404581c410300c2051001c4010f00000c10109000800780200408820b00000440d62070030030380414144035452071280c1d110040c614007407100241c018400b07401 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 930911645 1250 930910395 930910399
    0x30b071416050c06160b0903030106201c0806040b190b0a1106100303080a021806030c0c060408041e0f033206101a070f030309050a06060302100f0c02 66
    0x107074001915055241880407249550301a0001c10710305900c0b00707400d420921807445807856021546966450301c0e82c1e40020f00030b249c040303175404940d00101c81901640c0796403414448211842c458035500c40c20392100e00007900d40b001820002c04c0084c5810a030184400141069400d0381d0003400d43c1d880e00d1328041481c06010801c900000380307450524400c5084510180c2170754255103079400c18000600c08860316120841c08640d80b030b000154000c0e241e00c00c1d034092124070010302642524400070003015900084c5907043e00801171024866020003042003034801ea2040c2000f5603140e0405030b0001142c0305006003888040003640040c088a802d00845600701e0340d01c00c509584c00030400d415490b21101c11381851600c0180c8002c0103c4815000600380d002342d0036218401051515034a1890008496140d48102d03510200081c02c0040c44101282045030301916000480c00f0213a03640d20305081c018042603540503100c44050080d864021000c111642a40c14074078401801c0b26006050804a40e02c0a8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 930912895 1250 930911645 930911677
    0xb04110d0f0513170919080f0105010605030c030406150906080610050301110d020f0904020c1b01050a0c110622240c1514090d2007030f050102040b13030b0714 70
    0x140d951903408240c101040e102d81b8032640d00b5100d40c07089230340c0c01e8003018420813582030100019185005900704d90040d014803802c240703160742d1512000040c0500151b5107008810052000821518900c9584003500c821005012542403140f011a078103a929003042c1e120340d1402c00c182000c09201c10403140007000407140035840307003a1042d01410718000c0c2012241c2140c000102c2d02100d120108421018490b062f08030144281c0800045606000305d03104140410000d180c404089140000c000c00c0c0a00000d10f45032400900d0701b010303280200010f18a1100c0d0002c810103002c803a440c42c2c184046230300070b0000c4104c2c95044400003840c1c500b0341c0c080034005c00c42d421394200d000007140d04510064094840d246006089c1b84d981c9980d14140542c9600015514000130000c1c00c001c1021070340c0c00880d007001410791a003191600210345000860445181d035080000268132001800502003030605040c0025440f40707075040c1240400002400c0c50b0030003842c10f41d64403600c0c2c0400260742e0701250030a51030b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 930914145 1250 930912895 930912907
    0x405010816031709040603060b010219050d050f09040f050f07021203070e180c090f030a050604120203040f03030c0b07030509280c1e060f0c060b04110d0f051317 71
    0x18140c2c800c03a480c131038020341804004820f1144680000006000aa0880e90403a0b1131000d000800500c12030000d089410550b00c90036228800c2020f00301391840307110385a142c10034000000c0e04960700196045641612407080002e0304281d186031580c41041d40c005850005680000444507100080950382841082040111179490707036440c200051410b0710145046041510107a5190f0300408151440b480140000008904011403100300d11580000101255100c039500e018030550500c95510852000740300000b90000d0000142c00118000e0326103031040001c034205062101001003240703050604020520484190010341c07030b02c802c0c1001c08010030901e80f400000030f00d0340035468058800040c1d01070100315048081702d1601000c4107603c1e22096555501015600414418220004181d101502e9008030b54150011032610800402c0006c040c10050803200c1c0c0c80d0010b002d080c00d25580c80000c0490303a0060710981c0d8201c1c3c140510108801c1c03e95a54510070090702442d00480000811a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 930915395 1250 930914145 930914183
    0xa020907090302120f010b01090b040306050a02070c032109060c0b06042c011407170a020717070312060506300c130605040608040b1b0c0c040501081603 67
    0x450041c540c01041c186040714000b03140c41e42ca4417503a2040886500c1e01500d1102d542c00b40c861003044a489041550500307140d611201c1c024003000b00004116070302046044001841c09869601451103044c0c103070282c81c01140303152080c20ba100024400d12030072038400e2150940120386a88031035407004224a542e130302d1401040c050521000c904001032192081071400e541034a14120a060500000b0881c201050300b90114160080d520000410080c060544880d0f03c8110107950100343e244001d803a2022903070301c0c80754a5100040151541ea000324a40c010503509c8240c610103049030b01418090b5908050008460f88551031440501c8880344081007a03110081009600380e100081b0840000e10340144248031a070300410030003484889088012403828010400d99054079195503407049180c0d225643d1000c07441014016460752101d0099803a07070300c0c46c0f500c004d08845002c0006040350ba80c210003404142e40040c2c0150003d5081505045190a190358031070b8201d171b400c40410112000c0c00c01c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 930916645 1250 930915395 930915407
    0x50a030209190c031d030340080d0e0d0e0d03180b19030204080309040905011b1d120607050901140309032503020a0204150f0e1006110a020907 63
    0x2160b8280642006084003120390194003031500e103107250101d201040410005d2945a01c000c50b2201d104250a501d15400071515200e101e140601d010b04401c00840c00503410b4245013204441140e0310780e400540c07400711340e0780340c0101035800c1400c0d40103020b0401c0e45a40a002d4105500d04035014588802c12a014184100c1c800010550400901c4200b151180b0b000e00c41c69001e081c0807881c5030301501144452034468400c07241180e0f4010081d40c10200d0180401c40600303009d5105581c103640301c00c2c1080e26108444c0400c120421191104428091003c14446140d21201034892003070b00c0200c07220030b034007030b02003820b6505c07500c0303490900d50b100c08035001650300da051103158110f20344001c002c000a800000000700950300e401412040f40c21070705580c46000d803e444d0310050040e0003a460850042c242508008142c1410210320000c1e0f5803101020908041d003035010500e003003180414040030322001b4a00070003a124619002d00000c01d044452a43c5e00700c4c1850003806044108001194684110 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 930917895 1250 930916645 930916681
    0xd0903020f1c0b0a240e071e0207062a06152402010f0b0102030a30240509160c0b041a161d04060f030302061b0301050a030209 56
    0x44a080b1010300a0900e44540c16007156100382030361070001540000400252080903043c89036516010f46403c1039140c00e0100c030040c15850170f100380030013170380d000107000710609414002030f900821a032460000020030040b40640e21040000c00c440c2c00e6500141d844c850504a650040400319804d0340c035200c10ba0300c450345544500c080259460201491081481c148115201c00307074024000c1c2189103a5090032a46510b503400e015a004115501c9942e00070307100100b2800e5010b91510414a802d85898070046600e55880301180e0344285c0407400c1401d5145404440b9141c7c159408014140804108404406030880f200d000003046d0010301c8074443d694820b140d91b446007401032203080901d01214940c10b0719469502850602e0b00003940c6001107401444400065510305d2103540301c4800c6123154844048015401035110301000c9181e1403459032039801184241c0c02040b10349040d0040c11502c580c2240a2010640d0030401000280d80d40c500d4902036907011035500841d901d0382e40c56031400310710403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 930919145 1250 930917895 930917929
    0x40b070801260c0406080a110a060c020d020f030f0a05070f080a021908011802131b030207140a050f100203040507300b0105010207050103090f1112150a0b030d0903020f 74
    0x8040400c06000100f07126500070721230001d000f858015101007140912460103860000707009082c0743c4025103001c9051004803400900b2014541c40c5c68001709040040c04041800c2580c88044480d00b0400b04101d80f000914a0442c0605246d0401c0303261622200002d001030710030450b608540c001200030000440040000000821142c946061211901002000183d01c6100d1740c4154008182041c091a2000c4800c0a202c00800c5610b01e03050b0002e40107401d040c0c4000d2005e50742140620005c008600d04140550010940206519080ca25002000c166000700318014030600c40044d10000d5010309452002c1105280600700c0f03480301584400780d581603041e104801444409200010390014141e0368203a0954200b2502d07040194141c66102c3d00c01081001c1800c0c010010841b00c0b494104110302c01440080808594100c141c900803610850304c41c0441c844080c400880a0b611440301c50b03038410340140056a0344602e01074020200340c400a0b0080c254403156106650340d80b651007114481c1c3d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 930920395 1250 930919145 930919151
    0x801030b18100f09060c05090d03030518100203270a0b07030b1e03060a0216020f010c02060c16050a0305100c03060b0a021606112112010e040b070801260c04 69
    0x180443e02425070210140c40603458000141119441402200c45081015000c80030b8603540340e40850003007030300924903403102002e0300d007030301c0e41e1502400320648c0300c1290140543c880c10800c810f08034803400c840c10301c1c460b100b0007154517105440214140c80d035070b904241c0003403065503a084142d0140816215031680123090445035107415107407101550103450203404441880c0e03140c0c4541c0f4104e118651084600200800c00b01006143c4584510603000c018545007902c2030300340c0d000c00c600b034004010013441d90308042400d48029040c2d060711b80c0240011900b804550b40746845054407802041c03c46100207132581002c030300350b034003e801c0303a801480c01117030156031103219030b10003919241c202514103045c5e1003000000441c1403140d1285d261420b002400f50032014400350020444031500ca00c0841c4886050003c00c0e20560707030001070b9000300000398026909103081c3c603101400b007030010005410300480c00d0060105c440d4213038a0142c82100c400d8880d00a00d10407108924000400050311ba1241c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 930921645 1250 930920395 930920411
    0x307120b0a1512110f030102030106080a1406010f050a0c021f1209030509191d07200c1216090e060a0902090f130f050c100801030b1810 60
    0x111519611903080030004000c400c0c42c011003154a001d00d44644a0800d0b0020090360200e100c8031000c4031198030084c009901259400042403da0b0000d074060000300b600c8004001c024940350191050006a4021100c0c45182080000c0e1400d01185400c90801c080401c101502d2400740040c80308103600208551b1180c5000341050700c0c420002000308000424a5000903071100707143c05104100d03541a294a4144451441405448800e00740100100c2141c4000061030100c07054510a00c8200904118a44e00e84600007421001c0c1740030a20a101002980b0300351101c070301042000035540c0460346031104400b00081d40307107811561346101155a003c003030005501d0b00d05034001d40840440905640540d6101c4019800700c42864001a41005034280040d010042c81006a03501004602030001c03101003d44441d540c070004c09070111450ba2040502403070341d24100c410b50348814034624001d0050760459468240340c01c2c01820851407200d1503041002c170110701384000100805580340030402d000e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 930922895 1250 930921645 930921653
    0x607060504080a090618050d08040e25021b120c1c050606090c0307030b0d1b06030609180b06060f0a1815020d11030f070b0a0f1e0b030712 61
    0x10388483d1a82d004039104040c0041c9050142070f801004804400d81e80d0805403030300040c440041d80d003104c02c41d02c03140f0400c000b00c0c51034815000180640392400d040c60401d43c41180720310043d80043c2c40311003550b0084023044007008180d4030b110300481d001da60050f20150102451468103074220000349e1b000c803650310700c2000d031910780a82e00e0001c1d004804940b501d0b22503200f4010350500c00c0c0c94201c400c00c020400039000754001c0d00840412080a40200e207000e00c6074075907415078007459414900862400c0d004011440d85805010050100c41b10104100c0c9415642c00882c0c420802000b0006118440007802070368500742030703501070412100000d0b590040c0302c00080c80b04141c664041d1a05c10100404100c00c0d242080d000304070b03a01500180704c011071420703058401010308a503008030b512042098a01040d110005011400d100d521000f0050629544480a940f601c084003e262480c3c1900c41d061016114042c81c0c0200ca029400036a840800c0c3c040780c28040141c00031681c101c010369901c0104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 930924145 1250 930922895 930922897
    0x1101020d090f0c09180b100317030f07090b0406181d07030608011a0904020310060602010b03070b1602090c040902040e011d010812160b010e16020a0206030c09060706050408 76
    0xe02e01c9003141001c11a15240800110b40c45c1c6520b9030344034107141d001e034400100d02c101303c0354100c444440c1c48600c5030f42c0c030351700d13142c040d1000c0c40000c40705030000c400e004519812556460b0070030854181000482d00b07004140045008070301c9041c0400400410b800d014a13280d00c4548054000005100e910799404802007d003001c0a651010000746001c4001031460790622603c200140180c18030700311a920001008121403000e0800e9a0500509042c8468910584560002041950008688440c40d03400709410070101c2c5d80507411101c0104008284860016402c541c42541110700079965220b2040c094541e000c2c640100410610000300441d070b039104024114125110380c0460081102103c43c7d000c06420203202d840c11070780c041214011f0b02d40b409005001000700340e0804580064071074440c0b190809017a8400c00c0804024000d2000c07182540034807511002442c0004d2407660f65940c00f08081c0c1c0b0008050640d150008508540d855072044102c6181d40d030083c00c248500e0a107424100c5203 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 930925395 1250 930924145 930924173
    0x20d050c0405120604170a110a140d020c031507110a0807062301090c030b0a090c08060a0e0f061305040b0105090a180609020d1205072904031101020d09 67
    0x400c02854440143c51000061001d01c656842088070b98004d50710400c0883e29048003c80030103003c00c0303c01c1615500c4040140d408200d0007490007004541c1082c03000c4d0300f8803d000c1007940842d000a5070f1620280c400246480c806036125400031140e6480c2035044030134001403130600050380619809501030000020144c8100e034003841c4108401c1c00140c511142e17402d0800039880c0513100c5e102c0108414481c0e52f100551260007030401045149500c4005030b88107400d5004103404d9541c80c51001c40440d4407844036036104605072480800c140c1801111f0100b104010a030143c0c0403480800a8001d882d9240d92686000882e1002c1c006030615180082000200340149401000f0003800914000d1540c02112100a182803100c0b820500c2c2c0c2d00d81c1409041c0d500010303a0080710110510340042c5800140c2020000d10381d4840c0c0d25071006d46051220b03200c48180b1102d8110001040c1c0074440c0c0b000300e0301604182d00d4203101844a20403050369000e401180c03c4020f00314500542a1301380003042802c094 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 930926645 1250 930925395 930925399
    0x80301120c05060a1b020102010f090606031709061b031b0f0f010c050418021e030a050601021606050a0306180e07050306010b0f0f040f03060905060a0903020c060d020d050c0405 78
    0x120440c1c0340e4060110070b0040c0360301c904c005100c07400fa2808906031401020302c8240188000304074412100c071428140c4140c107504640700340d070f500002c000f4011500c00584440388205401c92402040d90006045800344416254040480f0103110122480420480b10b035000b1040518420b1200b1070080d40c0c56119104003120580a40c405c5002c0b600b9062241e0f10060b03100781c80315820982407540c29441c50104140314011584c0c03c000990b0381d01c61038403800d5481007113540c1d4251303139241c80f004a0050791070103060241550b00a0895041c503002e140c04c070b94182c034194640b060b200c00d6403080c01c030054007040d40680c6500c5030017060700206214a800005a0700003810031a210070b1b50729001d0558030103091041c484110410b00240ba0705551810040c0410050740c402c3d42c5c02d05c0e03140c00314241e100002d07a00840748155920105010048103003c85c5602c49800c601c00c00400d0580e480c00303501d40c0034580074607114035070000d60340b10048010760503108010128101003016103420034a50381c403a805401414 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 930927895 1250 930926645 930926663
    0x1b030712120c0e060f0a020a170c0d03051303110102092d0d0506160c05060c030a0f020705070302060c0a050105041a09030301140609120a0b0412110c0d0c0308030112 73
    0x10340b0290169214070103202010700359070b18003080141c914030b4035007044030702ea000c501070f4204400c007056012050741142e0b0604c05c0310702d0b43d442041c6070a6240c480c130b690341d20040c1400e003401c0101d8807440441e590360207505410800b020106030310b44540288600c104650b803001e8408550015822074520540070704a85007461102c50715410104006040d0310500144554002e0340044c03646510008200b4050265041c50285100705590322400c0083c101c501c15411a008020400c00c1026030041c0b41c5e0b08120840118030300342068a815444d0201e6010180c003480c000503d1541c107110800141e40b00ca5003140080085050903e800a0f0f50a400b40c02c4079410b0a20038085a0300e0b12002c0220390485403000f400c0c040300e40c204014001700d0340000071515440f0a6140d0941c24121f014000300f54054402c200e640440e02d00b6140141310001c08806440801101d00c4068082e407100017203100c0c450004445009a00d1382c0b924004003003d0f4141c0009000510100001031070081c0c06d8200d00030288285215 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 930929145 1250 930927895 930927911
    0x21306030c121e0f0b0f0a0b01030204180507090f0909060e0303100311010203121f14010e04110705030418051308030a0504150c020304050f10051b03071212 69
    0x305070600402d80010b0680020145071140c1d846008a070666000e00c144a503000e040c42503250300300c1c02c03032003200d80307907199003018040081c41d1000d446145d1041d07909007411070400d07082841c1004600250b486a0448598440202d58030602400d1030500805020a000c00f00f20344070602c007030241450800855500d4106a51000e80050200a070307403050350702c480c0e030075007092951300c8800005012805860640c00100f03c500c201019100d6964410294058100780c00054001c0302d50420301103a0bc143c000d021070511030422681c1c0310340f00c268800f0702100d020031802d030504240d080500c51078500605501c40042c0004466180e09482e502c82e039407072102041180d581e107500708801e01860788020021641000041c0100d42981d02182e005801801e04410780030380c0945d1030003110b02044d64000564004641001032b4540038021001d80d500070b982d50425045148406045801010311840004c044014405000c071000c00c2034030360f01c40d0032600020500d400d50202601682ca8851040d074950300709605 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 930930395 1250 930929145 930929159
    0xc08102112022d030f031b1813060305062428080a120f0c0501060f0911090604060c03210b0f3c120d020606091905070c021306030c 58
    0x43c105514500e0014520741a903080310003107160300040078450304004400c80044c003221204041e000402d0703081251001ca80d0901c1c1002401c008070140e845140e420418248002840802c807140c0008803107060040c0c0040480303425a50351710110762641c0103d24840c0d43c0c01c1c41ca400868800da00c0031001000d0610b03030303100c46415488111134140500b200c084800d02d410054403801564000c281280340806280e021542c4003400d454280d40017150180380c0000030f05c10340703440d40f003408010f044024085240c102d5060101c0c0d501e010728811b41c018410b00740c402d54245030086039501c10200702c84501056005d15040820020540220114010158a007500e07205050029003503d80d2100101100c810356500d13a107401c05048080940d1000c07099a5017204c681c1d4962086440121a150f07001d40301608080030000d14260008103c640f007840c0c1002807110901c2d8100070070358a0740e034010b000300d0240e0b20b5030f1090399400e451000c0250070104408014603c00380703036070207003054900ca00c030114503040d99101 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 930931645 1250 930930395 930930463
    0x10512070e0c0711120601050306090d140d1401060309210c0b09010f0c0309201f03020405090a02130803040b0f030a1107080307030c0810211202 64
    0xc1044100c12403010821182c1e40201500016102e00c90f00d442c150320301404070f2141a1641000e030303410341c801401031150b0b20301445410743c07050001004216510a0640c001c180445000d80b45414150000f0526100200c0350040c4c2c0310540c000b14071003140c2d42d403114000d008081e252400c0d5400e5007061702c8021048081c0c20b034480c2e52842c55691140341c0781503444103249040050100d203125035841003800300c01c5402d03008030451700c0d030b1540780042c50004a003402c02038400a07200d002c2e4140f0b04825005007035a80d090454141d1071500100030043c8090700ea0960003403107123402c6603501c000d6050404c006000300390004d00420100c0703048261015541c410382a5640940e01608000e0a0140300d420760482d0217030080d55029040e9080414440e4071020031213442d903c2000f082e070340c2c600c0c00810403020039058024402c0c0c502c11490841da40345003d941010070505203005901d10703441c102a2800c001c110301d80c544009550086043c00b01c584030f840c4040d503a1000304402544580208038515030b0010841 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 930932895 1250 930931645 930931649
    0x2060108120301060807020703021c1505040c2714060112050108030a0c02040b040903030b1009140d24020307030b0306060d020402030403180803182e0c02090f01051207 74
    0x10902500b540d00340030007550780d204010a01011440b034817600001503a00c02c6240c1c8524580b0114048101c5124203101311941051410a503805041c0403c4c030000840c2c078607400c1c0c00c848a060803540200d18034041070f01c10a903184000003242d400c20b0f0203085074182003609a401140d0980fa008200b0b2000c064410554200340720b5084d01e07810512007070214a014050803081c0e180300500018a031f40022002904031420007109500199481000d0aa241014242da03c003102d030608010507039901d003240190910500d100e11034024565500003604119424007000701e41d4142030501705c16001c0504501c130080d001185c6c1800064101b030410401030802164860081e0380203000d500c04003001d9000e0001a40c0050811001c01c8400001603495100f00d030840e40c0070b0090704005c1d6030380d88030401c1c94491820216400611550408500c845110008018425010b00340350700c2e100000d40d06030040d02c0a1074861406900b040d010010422540110165241070324001c07260300c42c04400344154699208854 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 930934145 1250 930932895 930932923
    0x60a1805060f0606040305150106090b1c18050109030f0306060e0102120f12010b07020405100509192003010e130507140607080d090501060b03060607021e0a031202060108 75
    0x701c00452090341190601507440680686210300d4156a41d4850346403c820003049400c0b01040c900520101c4e5000035420000e10001c03002c64105564075036100b2003141454000400d07240d0b501b00b121809004d5090030202c0d0381e0000d00800c04007106050241c800300929040c00006880e15601040060003801c001c0e440d01030603401031002d00142d51910415a1040034020005071040c0200c03448060702c09031490180000051a685541c080d04c180429550090404040481455414420358541448e4160f00c903c58445604a04a18440c07150050160b00d5124078001050f2181d2182e500c9000d0095040f29040118a03229a4804000503040c152a00c2d00400c40d8200940800500c140c1400b00d000b448001011285007201d50340d16695180e000c145107008181e11800c102c0c00380402032103030800400000da0302918525040c8001a02c0c0d11401c40028490010b00d952040a030541c3c1d8201c03001c0240181c09800e8682d16414200240080b61141d003005216050020821690100f1141c007000301c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 930935251 1106 930934145 930934153
    0x30610080115140609041e0617010209010f1101110d050906091b1003020d0e0606101e08040f15060603060b041a070f0c0305060a1805 59
    0x1402c031501c10150015104018440706008003424103402107030401c1c0d4960580b000140101650010200000e40c50104000340020030b070701c08000d9801440042200701c81240a907800d03482000701c143c2c0014000060a1106070250000b1403030400d03004004109804009000344050700041e9210303208540712024007211031070900080b500003e505001d02041c0038070b481203642d04070700010507078020100d148491500c18482da060324042401c040701844103243c100a4161740702c4040e2950361040307280452448801b4041c03400500c1100d401c00c802210078103110f4058441d00801081910600c3c1d00841c100000342100b8019040d0129502c00000c529040804c020b046400d90b402c50012201c0801060200c0904803480d82a040035400e80644e40302c1d40c5103000d01c4600c0c4030400060110140400120070041c1c00f04030544071300401d80d07040044106104181c540c1854119001c3c200c0d800c = true := by decide +kernel

theorem cover : BRFrame.Cov 930755395 930935251 := by
  have h0 := BRFrame.cov_init 930755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 930755395 ≤ n) (h2 : n < 930935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
