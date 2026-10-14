-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1044
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:58:57.095826+00:00
-- url     : https://prove2.me/submissions/0e78f37a-5b35-4c19-a473-98ef4cd615f9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 187589928 ≤ n < 187769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 187591178 1250 187589928 187589933
    0x610140607140a1101080708010e0709080f010c0809031e0d0b0411180a05030c1005040b0c01091a070c021309060c020c1306030f0803180708150a1503021c 68
    0x952502400c0010b0039484660800b0400c00304521001e0455028a4000800d0400180c098107100e810f003c3c208264485000140f843d5110324030100080c8159000c5131011a008003170360340205142010000001d01d03a1002030030340b14000003100c41c08900d19044504001044410f454250010500310f1544d0b601c900301c041c2541c0d41e50043c0a0082681e101d0b0540c0d5640c08040c1c16062401c220401e405407401c91000c2140790f9001c1448802640300761403015101451840440710744c4a85d802188075800c0200b2201d0090780c0545c00100000d1048064121341001c20b05030550410f012070321000020800b0900c0001400e0881945603601c17005680454075103081c0d91041c083d02c8a00b01305200603848401d0321005460045020040300c5200d1004120460842c1c45110902002d0340d005480390000101040c0112a1010003000c005202d10036035034031589031203540d911100031508241e64000100c0200304400514032415500d2180c54410386803c9195600380f0a0060400c090071001e8003030046460302 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 187592428 1250 187591178 187591193
    0x90103080a020f010f0b040f15031e0203060916060c080f16052509060515070218090a210c0201030c0e0604060c050f0a0201200109140f0c030610140607 67
    0x2494049117a0101d1010002403d220460746150031184095040c40e0590700c0c1c0c0c214031044402503d8000a01c440d5000e03c58042101080400d000250980b0031a41004808180460305036804440d14580b1800329540f07450031131340420711800240988400300082000d0703040303040003890140442e400c0c40610440384d03183d2038145518880700c1802401c00e035200a4140a950b16600050318a09404014041c1404041142000ea60036400e8080d2400030340a0309640d68176041044000d50301480300c1040c0b418425140d1205190074003220403940214402e210701c8484990340c09c0c4a0040e50719041080038540045018094240b000e0091040784500038000f40c9600c002003000d4500340d00c1780c030b501c030744035141c440d2070030308840c3c0d6902c40c035041400500c0044c0e038001e4840c12201d4884104140c032401e2240414010310ba00d44006107062320011841840c03401c00b1940e00b040030041015070704080d002c1c6040c145c4485048810300c1c20700210100520a80341c5030290014520702c041d090768148100c1d583c42c0030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 187593678 1250 187592428 187592441
    0xa08060d02060d020307020106050303040f060318021504060f03020405011b1506140a1202060702060d0623090603010509060612010b04180203060709062a150623090103080a020f01 79
    0x80303d19400100704800d880c5c090107000018030098004615240c90820b2640142c0340d580100c0c030801d600e5007203280c0b07107142125443c0c03c000e07001440c1c042d030b2a01000004115074001c0c41030f8804104d5044100384040d001c0d20a5130b0845006840b800d003400d2484801c01e0304c0014a0408032488183c882c0b01d80182400740c801d1001401c0100103098422509500700300d2102c400394010700ca0f0302009c0840d040140c0750081500c0580e0340c15a0f40c01d032100c4184030000c2c090b0540e40c024203400c2180c1800d0324030355000403106507001041910405665160b010601d4243c4004a8000401d030744008041803081c10407400e80d0104c01c0d000000019000c02c1000002c00b44d49180f001502d000254541400c01c0d80307424061141c100b401414404000b9180c884090407000b141c000c4282440c0800c0010751404007003410807001135034000c143c990403244032850b24005007064003e40141b0250500c815840900d106094400010020200c440c0782c4e181d40e540700304540c0201000800c40c055502008001007090003250b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 187594928 1250 187593678 187593697
    0x207050f0c030c03030418050601021509030a110d021b190e07020d0513050f0f0405040312061221031803030504051501060e2b0507090614060a08060d0206 68
    0x10401030070601c0806261a907a143e034180f10b900204002c10029090160903403107140c0c050408101c5944200040c1d003081440b220501852540b44100300307840c24040300400c2e99800340e4940440d848442c0028a5a91443c0c800d010b0140e40041d0403500f02800c50400403182000c01024005407641c0c070003000c041d900301c03680800601100601032242c0f07113405004000042c01c8928000342003060b0088a00d0a42400e0700c101c1d4080c1601c1c1d42c400800ea1141d038150300203004081c01c01e01c17141c2410700e03000f0800104c215070038601c6031030854007280f10f00c007041c003401e2690b82104182048400c108070406105179010603050a0554410b01155491402144142c50500a4800055524003401c0c154202080020b21459184041e001030010640200002880d4801954000c0a1580c9aa040010840c17810b029034010181090b00104110f000039190040e4ae84898003408402e582d41c100584100d01400780c607910080600c40441d52a119001840d03028100400210307d031009500820099800b05458 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 187596178 1250 187594928 187594933
    0xb0d020903010c08090a080903101109100306180f020705060f070201061a0a0518030609070317070807020d050304120c050f090402030303070e042a08070c05030301060804060207050f 80
    0x1035011440d0a2160f064114881d0508521a240015203030741c55400e80b060041071a0000700c1d510040ba10708128000c4055001302007000b82501d284103100c680d0700001251881343d07000200c82e80030113100380111021600030650f510f903c0e222400c4d4072030181a00b254103241c541d50030700030000403507001c01c00c00b030051801e14412155410401c90090a640745604200745480d51340154242807034500c81100e50108203460840d8803694a00c400c030b0b08025a40c01100d07418854813007401b10f00300c400700e032200440c0d20603030038100c48400e142201da0b0030707000340e46010706822800d000d06005402c0000420003c0307031044055914040e00c59140d6407600e01c241c1000e070b5483c081014203101ca4184680c44802c0b402c1c00301c0348481c1c80c0c030f0190300190381c030700c0020480382c10031113031000642158335a60032034051010303c819444c0d441044000070880712040035032031000041d030600100b801d040c01f503070742001c000703030808003640c0b45030f08150b0b06541000d4081c0040300c0a9508202000c00b107a410f2100302c8486a40102 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 187597428 1250 187596178 187596187
    0x60203010e01090501030f020d0302010e0f0303060103060602060c0706021c0c0306050f03010203062107210512040b0a0807140c0606130e07030210111e010c0e030d0309020a0b0d02 79
    0xc001c0100581000480c64a000014030115420010f40f02400785c0c1142d001d8440030503842c0417400351400b44014000b40c410b201c0310920280010001e5442040e00382c0c0d0400202d555410b0480c4d8901c015103410348208070801c0f40d04007040158000340564980c0d03400701401c50083c5440360044404040108000903130740d0f0014466072074944528003800c0001c600940c19414104002021034111010030921400b940340780c020080c0050160500034100c01c20280081d1505080300b1540c0c6030076040484440c050710f5401d60b031030322041d825201030342c401c80010b1307007400200c960075640b00354050021b1040c03241c44404099040342000080c1491280388000d0606400c042d0b0501801180c1c1800c2c001e00e0b503040115070f03908500d000a02c901140d40480381e282885a50740c0043d070719203040e4070070809a80034040c022a620428982c44401018044000b000403220a060840b0b030340680e5080700da490b4018014810341188250000d1010f180010001c4c04d41940d45d08076500550f0015036001140c40c0c000c01c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 187598678 1250 187597428 187597439
    0x709051e03011e02040819023a0510050702010905031219021c06050906180604180c032a09050601020c040f1406090907032003060a06140a06090b1b03030406020301 72
    0x404000184000345c0441941c0580c0040e400b0061081d03400100c14903000348058003120902049c1c40900d04000140150010741446038948030070200800403142040040b0f45080d20500c00c408500c0c3d009000ba5040c8a900c0300d1114031490044c00b05102c0e9003440d4440e10100b0701c944010000c000042c40d840c0340d0022111043d4003a01c00c1548994400d040f21010481c09850701c40c104d10400b903c408080701140d8030100014002c0c101c1c4a925100c404050315010100039240c0480b00c2600e00459122100c011046180c0d00b21288040c850080341800f00003c110014a60700481c1e04200140140c9440104185c00310b0200e6100e540d1408204d40c64902e1500065100f400e60b81d04500142c03441c00251400c0b06460795a100075100080080803000704040d030701c400102070025014401810b907506414502c0011014103001d000b001c41750070b94440e1044007490700d0600300003202e000da00c80c0c000451a000306442150485401001140d01304142545061000d02c000c620441c410000183c9030750425 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 187599928 1250 187598678 187598683
    0xc21040e10140609180403030b030601080601061d040902120615040203060a050603040c09150f150f030518060c0307030606090e060904140f01050109050709051e03011e020408 77
    0x1501441c2032051105040c0181c41c104038030540085000d6603007a68861a44000c9810764850401c100c80302d441400901040542c0f5070002d0204840840481d071540e601c0d140c21680701c0c8428850f00300801c1c10005102500d01d0451104900d08200030400112002150042503000241a8851210350804000c010a004000c050f03808480d000b80e404508514121000c00c1500b222805418414040480060200440c0b4440840901030030f810a0006504c81e100708040f0480078041c1400c0d0210120000c03880b029120781c2031042c2e90082e40c80300140200c110003a0014000a4013508030f07114542c090503103240003001054000d0325030074030055403864000801012107816400010030012040c0302008000304260b441900120206c6036100107490b286000c48410900100c00400da01901c0c880060000040d4801412610300420611095684520856201006010b03290b407101d10150302c00c1c079005c4004190100030720040c00004804091080a11010120104090050760006002d11101005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 187601178 1250 187599928 187599931
    0x510080f0c0907020a020d081819060210140f04020a05060a050408010b0907080c0f0715020d0f020c0a06020904020909041b0b18090a060312170f010b03010b0c21040e 73
    0x200d02c0070700340b50002c0750300081f40103039203040c0035010b1000801c40c00e4100f801e41c1141100c1e03080007090b0800550035148003100501c02485960054001c10080400d1118036018041101d0500507800c0c00780c1e503444075802c10030030300a0001c0e80c0140c20707481d0106540c2c880000503d1840c49039100e44c1c2e1140e203421445425a9407403a841c9002c1c480c1b0009010701d40e0381010030141c01c0b14103144000e0300c030702e811381c1400c1c100e001d100009040303105c810308181c00500c4035600800c210052074606000000110040105a11074410801d400364400c1c4407410109039254050110842c0003030000d85800100c0300001d05010080d038007076541900380c0130060016000108a400206042c1e120507007013904801c080c0c41b2002104007494040c1d211200002d10b51031950f80824080d50f13206840040c90303403c0041c001e010034088402e40082c94400350100300d81c90341d00d01d5040e040301e4001c0f01c02440c1d6805c141580030581c000301c41d5040b041c454076011019091220a03010032845028079455103c600d480c50078014000c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 187602428 1250 187601178 187601191
    0xf05060301090506040212010b030d09090b01030c020d1404030b0a0501212012010603060608121e0a0507051504030e0f0f091803030a050703060f080a02040510080f0c09 74
    0x140508280000348042450740d07000741c040710500d40c0d4981762607542d4090074514278101d6050280c1d82c40c6480d0702c3e8004002070281c2e81050b00401000c60004019030440b000e0750004000744e8420450300044610442c80c010302a0f91441c80a030400d6a030750b8031011441c0042d601189225103480c01032121003200c007e076103450030140007200c81424103900d900f220b441020740e0141035141d9540707006d0310948402d0f090001e0403202d00000c00403503a60f030900c00c0003090640200821409501c61a03411a14000c1c1030700d000110034160320031000030f04004445143d010007001c00c01e109007403004901250051150340842400310059008920b0246070043c8001c1c8601003d9100d4100c00c5580d00003501c0700000e4013161841070720051941c0c2c0310340309445500201c40700d504529100c00020401c0003e00e94000c14003030314068134140071041c0c40e080100e4440c2c0310341c002d5219075070105c07482c20090300d010741000390450300c1c030344207100d40715211803005042103581503400071964012650f003074007030074807422840c0d2282 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 187603678 1250 187602428 187602431
    0x501080318030d080c130305030c0610141e0a030f05030901120203040b060108150303041409010e04210512010308130b03090304090509010b03060106020d1701050f01030c0903150f05060301 83
    0x4090a01c084c1c420761014210710f201e00404140b030804410f12680ca1009190000b0403691141d403004507107540d41504848a000c0c40c4680c07800000c03a280c4c0910a4445240c00400400007c45101a100380005803010016401080a640000400c11002d00c90311814010b2003c1c580d150703243c01c00945100020000360108901c10010800072030383d030802403504504240313800f0119031a00301c0d100102860f000301c941d505010000300007400c91101003030383c0260b213425117040d140750384c1e600b0100e243c0e410101d4026114541e05404480040c200750704030061f20b0107904011b0b00781415420003480801098000320f840d00710018100c03001101c2603a44000400080b60211700c0c0d41343c40c0d80101e45900540c4a54400c0584902c04100d02c2c0000303400c81c8264000203012a10706603034401000b581d4003013854003100440c11404503006c490b2242c903003036416200301818880440359040011001030440401e441d0401c10300e03800210000711138010f0300c1c40d08110b0726004505c401003001008111280a04201e109a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 187604928 1250 187603678 187603693
    0x406050a1413030b0615030c070b011706011a070c060806031603080a0e010504050612160f09060806192402071409060612010306020304030915020601090507030f050108031803 77
    0x100e4810054007a01d0b41304000c200c00c1d4581c100403c05440c0d44280312031002c4008020495244c480501805d1814055829405180da88150cc40c0120240800c4c80c4c4080d003001005000914005603084141102c1d80d0200d49011a213884801c0c44007050342291780000c0314a81071069528040080c0d20461400005440750b59103165510002803207050040c03000d00881c0c030020102d5a0207007041c1c5000300005000326944400340d9540d81c3d80450100c9241c0002582c001d50245094400c0400042d17078a081c2c0c5070044460b08000040c2d40115000b440c007644171516604c02010443c40951080c01082052240036a07041101e1100c0e5250000300082001c56201d40003c10900c000e0141c0900e000304103441c18003840c0c40703000214480f4031440180342d82400380d642c000030030040d8503401148541d0013591020400c0751903500d4041c0c0e100703815400ca030050f0300103001070190180b20360042c4d4100c04141000103035100440da0300307015a0f41c241c0c0242810307000070030400c5290840590364246046e0403000381005 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 187606178 1250 187604928 187604947
    0x5250c0611041a0c0a060b010509060c1c14090f060d0f0507021903091701020c030712181211010318050a0c060806060d020c3a02010203060d060207020f060406050a14 73
    0x6400c178000d00a0100b0f521703004403c4240e40958121007100304050140350780e40200c54a4155101c440c40c0c1640e902c0c4400c030740100c20141c8180406500302d85482c0c9464038000240003041031462842c2d2100ea070200c0c0420408450f1081072141078000005960086a285014030019003440031300d20131391034030741003e801141c00a41e0206034041070314081406012121b0042c44000d009004403621100b6611001401c13130140045c040c0c801a01c6a410380da0021400c0c4041d04504200c0e00d907104108648031104613400000d007070001c4c9940ea905041c0340005910b110482c00e203040c0040c0d014181c510713405c0344035140c0a0240c040450005080c2608102c0b6460030080c0200c3c280340300e0149043d09442d40441d2207001c004042c8a06c0d40c80a842c104404002003100118203940030080d125489a20300d6101c3c9514018018002d6a101c1c15000b013003104c224602c2d480d410060751001c07001700c1c1c1c00310f00d41220505070f030b032218007810146c51a66640d607103400c400071000e40b8800d001807a005c910901400290346 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 187607428 1250 187606178 187606183
    0x90601180302090c04030b27011803120b0a0902071b05090601050a05040807060807021b0f0613032001170105030a120e0405091b010305250c0611041a0c 67
    0x101ca605807820b01540c2d55542030042507000700d41004210f901118107010030701a000700045008169403d44a080b0000341551302e01702d80b202100042c02400344130b4034401017401001d601c26202d00031600440c0c0d0464540008001c404a41c000441141e40415850240021400c406a00300000b10b40c0c0d01c403150405000800030700c00201000e04002000685503c1d4901c6171044c1c600401102c01110302d884d440310406044504200c0b46403005108080c00000c9200400080c80035041000d03040404400fa10002e0050a034408003050000c521403050000014160800c00c001880207c81b000000362041c0000400c07218010941358011081000184100e541c0485e00d11341840e0312007140f11f144240082d0640341e00e490509080d40c05860304040202d015400b0841c6601c0c60700c1e8007000101c1e032101a005608079801a00e003c100200d001121048020102c24840700d042d00394101110303c40c2040e0f0380d10b01554504051001b4960001c9404c010b101c04642c10009110203055095060151032944075a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 187608678 1250 187607428 187607477
    0x5030405070902070f0f061d031c020f0c03030a09030e0303190507030c0618020306160903060c020a050a20060a2c1305150907050a05030c0d090b06090601 68
    0x15820b03907000800300100042d001089003000e61150210404100320308020b40103003100c0710742030b10040c07a04808107910b6202004440102c001c010314482c4601443c410600250003291424560303a8040181c03980c5080104007951180886140104a65000b8903000300081111501c5c14065401801414002c0c3c582088110f8840028a41240ca9607000e0500300c900e14412032015080e90701d080141c0384403450302c2c8440021140294100c0b4019100c0c0000c071040d00c220310142d900000c0c0013000070300020b10150402c401c0c00d1004d10444564040b161115400d1480c801ba080f50640100321021001c5441d2000e102460202103030030741d041249404000c1c0028607052115145c0c80004903440028503100c48141d00c041030302810500e01040b02d05441d0340200800d44100c0001d40c00d014140d8502c0c50328400036440b0f1400313a99514103013060b040c820707119904042c10131000b444043c001c0700e046d800d07588251038042d40075030564412030520005100700c20030090070319410081c501c0c94188525a0902440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 187609928 1250 187608678 187608689
    0x30606090612020403020402040602100506030727020d0203011e050f060304060e071809030915270803190f08010e0c07060204050409060b0a080c090a0c0509030706081005010503040507 81
    0x81c0c01407805420142e000307100d02d0f003000750300520200f004034006900156144070540301d441c08004070b882e900100f5a80711f545209031012105021034003080014403a0729600030701500b00000d4140144181004166013098100a4440041c03020401d45405074072461030062800740c0c0d0400b804120400490b2592000500142080e034441d5480000000c080051200a14244403810101d03103403043e40802508403000d00741d0005041a0002c58070f28a007504000d4803402c107854a1030080d241030f0401d01c00e1012034020308101c0d4203c500000d840c18051008003800da02c07060440c0c0896244000103840c00c46e00b8035040c3d0402c030728107005228038540240c400707401410404640d80c448600e440c02d28003a110700d400c004e400c5400c0000c428200100c5030070007594860100c03a00070281b034480904665811289690b07a60146800002c24540b152551044002c0341031407400e20302e40b0401c0300109140000300e5000c10006401c1c0c00030460f0394030038480071b080902000d280c198a10b08040c1c075500d68440c49401074 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 187611178 1250 187609928 187609937
    0xf090b1003050303071b020a03050304050f06090a06200f0705010f0e0a05010e030a15050621030a0806040b0603071709120702090703090f050a120f0c1b12051b010306060906 76
    0x15140c0084241105800254010488e9103507035103034640701c0e03100e4006108080c020413140e185140c90345440780c1034901041c0040c105403990303440c0c458229218503040d140308400c102c4182c4031031021038042c444080f900661000a10480b45080001421a902c04a041c4100680f400b1a10180c1d910210720b4003c50700240303401302c810144200001c0c20003134640c40041010001050b0201880030381d4200030b200c2ca800325000110b00f038a00003275500001d54a026603030b003038200300001019203004443c569000003015100141d0500710030040b411907070040d5401e20103c0e08600b500f4840c01d200c40581903001010401402e40c02039001c1c0c0d145181d015503c8003d2141d460880010b02d414400d90210000703a42081b9050075003a1a41442500e90b180d4800580d103080018502c60b11040c005d50802075940c0c019550f6507000c11580d2190113019140b41d064807820362000da0b0001c0c0e10908000d540c0c08050080c0050210b65900c2030140c0084900c81030864145030a14500b00840391b0031003881000c6481c1c9041 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 187612428 1250 187611178 187611197
    0x9010e041403130906031e03020a060f0207020604060804120f020309090405010e06040804030c050d03080a0c030f0f0213080a03170903040504020d020426030f07150f090b100305030307 81
    0x40280c00c41c00b403800ea02001c2500420300113400b9080790440c1003164060a00e0350040f0220603100c1c4062401340d400907000d6800902c603a0005500b650100128210030800181080702660000d42d0390f5001d9405036002812050a00040c00100303c260105107003a801c0c0b01103180e51100d0041c0d143d0284800e0f030f40c0f25051060006003440401c0d0841d011001420040c1c90031440e09207455103054004d0300055442c0f48007240003140a06001c0c100d4001507426031110562a5698140c540280200d01c1144081503210b1031880c0703a8030390324000c01d02d0f50920700001580765100100304440510117907001e02e01302c2d803152101a0100390040c211040820084035102010707514100814650300c12a801150064400a940c880c0c12030a41e001d07005881c03680120800c501601c07030166040c4000b0742c61089454104208188400c00d0380d00081c22414802d0711043e94007025415980101e5081d40c12809483e500c031180d01e410803200b40026030340a50310004c030341449402c507101c0f59074900008007000103010301e200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 187613678 1250 187612428 187612463
    0x250b04031d01091e08010603030207030c0e0c09040e0120031501091404020c070807080604110904020a09020c0a150203071716230d0c0e010203072d050a0c060e09010e04 74
    0x4904601616428000381f00250707513480e0082d0b48803518441500c1034405440c0110350b0440240c3d05c580201d1411401505109000d030410009101040d04000550b588d100030781c41070600300e00103060005c884984240c880c81c200200040e85440030404d1030401420341070500c412a10040c0d001c3c914103042c0c60040c0c80742c0c086d000303203031518000350060a400d02c07e4070b000145002c00002c0713107840f95100f2180e10000c40780301e2082c05503d0303800fa203000b5800b4110302d005102003a2680c0c0902f910350208403c0f034a0044080e11100f812241101c04041043c0c0c0010402600c55040740c1401401d800f1044055580c0ca0400f00d9840e50549007491281082190012a815910000d81d604030403118440b4440c1c0c0c9124a1111800800c00c1490340700220f00011a0540190700100584001796006100c4a0180002564004c41805110201100700d03040b40780700e0010030001c1090901d40b40c41101c00f0380c0d1090400d840506a007801c10130140c80b03110000c1c010700104066948885c1c00a45c08490b01c0390300025036 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 187614928 1250 187613678 187613729
    0x20f0d05130c090e0c0d020d0f080d06060e03010c1704060e03040306050f0f01050a0b070318030611120f0402060d020903100203091e06010e0606250b04031d0109 71
    0xc1e800507000b0128a2408604160f00d0f5005140300c3c4842c2089a10076108401401a05441c1d600d001c1d50006584044d20301041c04544841c84041c0301d6600e25141c88080340c541d000f26241600110000381400f95403500740d00303091003030701c081e03540e2800c180b00c642e400035501505e95900108000c01085d1a008114003001003002560040e5510800a120a161120b40f4901425084a0080c0d8081001e4000130740d50401610040075600a10101c604d8004241c070151403007011b11440780800b117406000000814200c2c03203000d6020042042203030b6202c0d40300407000e650000250440c0d00600100c01400010394030b120032181284100741015031200780c690006402d0070308038044441d000303000104002c1e00c7e0310003051640081c68112124842c1455040c0320540c0e80d8001d0042c00725010888010460700d140c4031010304031506420111960070001842d100ca041000050119018002d40d004d110070907400c0502d02d4403104011206d20b1403c0070810000708101c805100d11035000c0050307c8040d2600315407 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 187616178 1250 187614928 187614961
    0x5100302040801110904050703061a070c0509010312020601090c0207150201020702130c11012322050303150607050a06020d020c0102180906030d1d1f020703031101020f0d05 76
    0x44001c00107984406449040e9900401020303204074035042c00234640741e0191050b80c05030360b50009015500c004030184102e00d640300213019200c1e41001800050203036128400d00b40614440d084c070241d986041603004e4604a81030f04508009414202030000d1164000303091070440301100f02d000e075410700b800303400c2e0b0080c4611840690014820000e420041c50a500302c621500c0c1d203540d801062402d15086c0500b240c0c411480168104429544246809036504450790081c181000c04c1d0035130604038910746900c3c3c031000000c640c0b58001104120800e04c04100308604203d007650560f20b000280e40c0d4042d114149100000c00e0345501090104240640b54151003820040c4e2000b1075550356070344c040140d25520f40721454865205000080c92605010412241901c00c03520754545504100f812211410148000300e60007a213094410b0002c40b4540941090b410031640241c9202e07815410010a6100d181079050f81c030784e0041000484e6024107804030ba82c0c147c03000c1800100342d110500d08410983c503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 187617428 1250 187616178 187616189
    0x1110721170304120f03061a0a050c0d020a0201030c09030503270d0b09060c041a0702060d0f0917030709060507050c040e060a05060306040b01090c030e0d0e01030f150510030204 78
    0x10040008100402e803042d801c0042503150b01c00c00c2100309008031b0a45429000d02200720306c1d4403040000c44405400a40b40030b01c590f003011806e213149524024071b0481c032800440300503444069044150f58151041a880e40103600c0c1072b11000d81103864481c4e0701e205402c54130800a01c010b00004103a92540825082d00b04000d0609181c900c1905180049640c02d4601034424014039000c1398100d8142c1c0c044a040301c81040707501756404032001080d0100d1704000404d0b43c00100810a42e00c40c803d40d4840d004001880b0500001c2250150421690034000251a105118000c1040c401d085412841c244201c0d956032804075514510707403800f64104400003611640160400680440c1d6400c04283c10780703c1c07103807030104122650b2503104055a80106071006041d0a2201d00144031180d0030390424002640c0e50306004c0344070700c841c0400b6403401da94207503600000742120781e10040359030341800390004410b14180181700d200108064044140e11902c90300c1d100b441c496141041c11402034065400415 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 187618678 1250 187617428 187617473
    0x2040902100f0201050f07020a0206031021030e03060708180a0605042303070f0204051f0608090c090603070510110105010801090c0501050a0905190902071101110721 73
    0x10500002070b01d2000d103410008055400c1c076001602510700005c0700e91241031180e0082c5512055a002d000700c981c0050884400c03c1410f00010071883c04000605102e4803026415421034072041c00c000309401c980c1c2e1515482508020184284180d10021080d00482481d005200e07600e0100d81d0103140002c010300081003e82030100304407d000142d4125526608410000220388255044231358a0348101c0f80010042400507218002506281c1d2106510058111400c80000100080480c440d4020303031114000034000e804102c2155401c0c06103031103084064400e05e07a01e0414500107601c408041c050580035520300c84040c0c00a034811031100303140c1d41040000b0801380d611100d03494081c011410081c0c0348041e210390700052a5105804540e9610210755815080c241880d04108800c2030407950140c004054803c04110b030907451004042c1c251180035110410442180058815504403071001c0c2c032504106c104014101c00c690490540c80c0000710060340340c482602d00a5442e0961500300700500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 187619928 1250 187618678 187618699
    0xc0210110a0e06040f060302030a06052d04060e04154104081210050a060306030204060b03160c02040212072303060f130b030604080319020301030b040f02040902 71
    0x3621904018101c11981e907030345a10280b100018018035100e244181c800e00d040507082000001d200b0f501a40e00480e00c141c002ca04c403582c1d01c4c0080c16489582200300a0f8201450310010111600d0480300303c1000c059405001d03e40c5800c200b07081c4440020806801d2109505003500c2c20340d0540d0040e501e400e0703454070102c0081840107a05480d032400303030119a84054084510002500400460f034803840c3d0081c0b2003840c000c0c4842106000280203803414030580302c82070012403a40d441d000f02d40094001680c000501c02d03d10700401042d80c0710782d4065004407408200307006512882c13603034401028200d4200903862607030301e02c080740081c030502000381c2c50701c0d0050081c000f4095202c00c980a80280c6d0210407442070b1440d84203500280700276992030b1f81c0041070a07000703041405c20320315801682d0794840c0b00007040d40302500070a040c6402128101d50b07480000042008c81c02198500d40155000000114110b43c1159a691581100900003901040d50405010111f43d1550020b022160f400303412070252 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 187621178 1250 187619928 187619951
    0x3060501031a150603280c050c0105010f050108010302090c07060f05160f0f0c210f1107030305071112070b090103060509040f1211032a01140a0c0210 66
    0x180c0b20381107596020070300c0040442e120044002403852100e1000300201e103152142d0b118080c503800c602600c0d8201070301031810480d91108511440100c0c1c00d40d80c452540d5403440000c0795085481c16084a003000065650600259900084517815240e054581000d9521080001607450054000003080d850800002000450098125034020244125464a40f410f208001e458489600d00f803100050400f40040b0000c038480d40310b000d5098003c800b00b04220002a003003882c444103c8440030080361301040c803100e40a600205411646405070090b280d194210359000f4003e00c14680c0c041c00b4031041c0000d0320820303030300c20588043c00008102161102680c13540b07aa603158008041c182e0100c1e24110000400342000700d0030911459004804242840207540c0301c02c4010362510729a4100b1810100b188004002040100301214104a84c5c200078a03070a020050108000402800703240d0600001a540121502d03c440e000400b4036004941450241c1080749040e030b24000e030b00c85e503d04042900c000b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 187622428 1250 187621178 187621193
    0xa051b07030b0f040b04030e0120010905150106020c040507170a0507031b120203040501020702181609180c02100f0e070504060e0c0a0c0213050f010f0515030606040306050103 77
    0x40364802c9290380364039a5402c200c55050101110094504203070000041d00091040038001c000050504003421280c41e1001d0751443c4030a545000959030799509103280c2807142c10000f5404840145848450a6042040c000c0d155405204501d0040c0e4072240071924040c0107420041251210482c051541c2c60104421000b4050607a040808a80b030031044a507601c0b9401c12804207105561148450504e1440c8110004c0d4402002502c6031355080c000721005a40341c07120018402c5401c01c03501c1e041c1c00c0c640019030511040c5181c100034010340c04c50411202038031548050080ca41441d0024648042d02d10903400c010703285c689035802601d80400a0054079107584011210741d150b00441e00f0058854050008541050040140070142c0c90b00051501c9000e03002070400390a540341c0102d1610a51340401d030310000000c0c1006007192281d04101c9605181c2030110300404041450301c00f0b0b0b0385410003280c4622071900c1c802490603000400101e00e070b1124000c42c0c0003550b002c5000c1005603541e040460703 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 187623678 1250 187622428 187622443
    0x110714011d0106050f01140405030f030406021221040203070f0b1305030303010501090e04060908040306140609040201051b071211030d03090804181b0201020d0b22020a051b 76
    0x1110000701036480e03060307014400c16081d1903002e4403600002c0f5907003005498850065444643d003031420040030900ea10107200612400000e0401144c42e42c0c103007076010741441c243c4030000d00c4042d01840554940c104044898080e2003c2d6080d10110f41c507076002003418921140c208220f201000300000034944501c41c001c0004000c100140c0c80301c1600c80c010180c0301d100a02c1405d00003020a030007480052481d070748050300304dc0700e4800001c140b4407035a00c5031482c2d0032980c825140650740303064426014403008055a409042203415410307d20f0650700181240c020740c401941040f51404103065080300070031240e00a80504a178000d1881c00c80d01d4401c001d269021040e074003901455001004580c000d004040d100d03a03111071030b9810142082d100030800c0298015422803251941c03900e10501030740d0304003940c07108a980e0000d6529848000c004040e61120704030a80500c42903500d42010401301440f002e0b51000280c400f5903034410090088480d40103007545218641c041c0c0e980840040c80026065 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 187624928 1250 187623678 187623701
    0x2101050a05010c0c0e1305070b04050a09021e031e04080c120408060109020d0615030b0f01020307020609130608070b03070f03060815073509030a1211071401 69
    0x81689030001100c14140960000f04480b60109052009030101021641d000d039840f5255914006c20741c07145440d120003940b001100c41000681485641420019100500b0b010b9505500d04030f40c2c40604014140f2240400a021001001064006041c402c151030700002c440e2501602d81010308040c040e90340207050300c9500784220003982001c003809105440403504084044d0541c0da20384402007010390300507107151484580d1010042000390380c0180340752180a041e41c0c0014080003803070920152200b00e04880341903500510615005035600d9040301c1044409491180c00980442010b01c041e040c185c10402c2a8010200041628212840518071500803617546a80003840700d10107600b2101140030b03010042c0c00c41c901080c90800d0800c5149d030000d03d01c0c40c0207060f03295a420100c0c00d1075038560040480341c0e0454101405560038842c850303048980d2402171840c0c0701400d94060b00d1000310444d079030611500e983c65109071516840c10382d0400ca4001e03a20b1f0300994411700704980240784174100e1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 187626178 1250 187624928 187624939
    0x11011406120d0903080f120702210f07031803080c060406060509010e0109090c0510030207150b010e13110a080a15030506011701020403080703050301060f0e0f15210105 74
    0x1105441c000c001216650030180d0307121070031014256102d4449603807140901181006040102e944041c0465038800c5c4207407078550280851103608481110410400c1c10841541c41c4148003012043c043e0038106d0b4026585424002c0d45407514549019070902c15600c0a092081c0218001103000c9000c134056100e948605000c11019441e6000c00100d400280981401d0080140051101303000c243e0100d80000c0c019860010042d90b220000741d0241c1998200d500026008101807080000400c0f5990045442e050140214864040002e100c405a64800d61244400082c281c000c0c1d00103921050980610403502c41d6500b800681c05401300e07009a81c4030348402e1400071588110300c0500502000d0301d5124002c4e0180d640f80002c33203045605080303000c861555081000000060752280145001e9100740c640c55120762500d2400b1302103c035054000301c01d20224500c0c01045948000240741d40c2a0121760082c1d071250405101d610900a03c55a8441c1850102d829100c114101020b1070407500111503 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 187627428 1250 187626178 187626199
    0x120a030809070f031e140d0906080f07031e021204021005181009080609100510080d05071a090f100b01080f06011413060305160c0f020111011406 64
    0x54040e5900c665200c2c1d10031181030160280001842c103500d103000303049482505d05a09040d52154200c03040b50700c00c04116503114030540c0d000c0d90707000115180204002e040c010200d180040e1009074943d40200110201651042c0d0240810b0802d2038206644110329411034498400044005c001041602e0a9200d0143c54192490701480b0700110b41040c0c02034145180c00c81400d04c14021429000e042c02c0301445214403021805100c1001943e104444040041180c00d81440c0e0203411180c0140138840103100000061040200010309a840717104c0c24544030341c2c3c400850a180865408031040c2e0048071124409102c5d02e402c0c00200080f6014140082d9415181440400c00440718017161f05804112880700085150a012000329408801810700070040d00e2810204580c0e0760042102040140d0600000d22486601d0300c00c841c0e00402182200181d01c003000d4000e00f10806500d001800d80e903c8204801c1164880c84100c03048041c400008c2c094100100304080b8400720856821b80140070010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 187628678 1250 187627428 187627441
    0x503040f050f0418060902030f011e06090903080106140d06060513060201020a140d090602071a0112080f030601030924391106071e03110a05070201020c120a0308 71
    0x400d44c00440d41e0b482e1032890401d003995031400038180070941a80c5c940a08001c03503040000030f0040c410ad05802d101c06400c50101d510500086904a402c404503051a1030340781341c002034105240a0544002e81026000c1c1c108040d01c600151040300c540270191418030340002941074210001e00320003003150300d4103480b841c2c8a0a00b00d00f02d00507080c40c0300000c0c2c10a00c0200340380340c0d8500141030f11020124040380b03441858841c03405030b078062501240c01d0158448581c8001244540481c09040308402e40103002d40b2945904178070b0300500740506100705000011980d00c0c1c0c026401400800d130301420016903414451440340003a80049091481141000010116201070410307000e582d918481d8010026485401a1001c110051807180c0a01c412800882900740080007440d100e40311664418441d841e4021303446806000740c1c4001c02c1418180183c1203040c0c00a1800c0c1d427540701e02031a180351601c10a000407071401c038410842c80e40082500c145d500ea00400800d10340d092900a849042403600c414 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 187629928 1250 187628678 187628681
    0xc0302030d080c0d091407031a090a02010e0f01020f0d030c0908071805091e07140105130e070207090501030b0603061e220204020d06090b040c0e060f070503040f050f04 74
    0x455058040e20f20400000d85000700d140e01c00d01d60705000f00502c40201c04a8006c10749403407601c0d0800d803a0525581004020340400b0308005074823501c01f00161681c40d101d0341c0040c1c81e42c00e42401c0284170348445150103160b41d2003089121038400c0400708941510f0710748600900280841e840401c00100c000b00c020a03019000500d8204407020104014a400740d008420001014007038907124043c0101001070101d1030b0901d403078524a00558005d80b0380d07185842c0d1085401c1c2145c0c410030f0b050001c14000900c02a500d01112403c450100c004658a40d8a210b412400c041a039005403c81d186004008010321800380c40c0e10f0311601c1d0603400c0b104241c440041c4080303141018808168038020b42e80000d05803129105040c4170441012000c2030f096045503002805907000b02e01400075507603856000f000040018019000d1650f0180e800b003020f01d0011800922003000314500038022080003901e8045a00c00108030340c0ca2582106c25a9201e80d1190007401034404030f486a98407800c546c54242419207045e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 187631178 1250 187629928 187629931
    0x306070f02061305010b0901091406101b050102040b0a050403110109030b04030e04020f0c0d0f0905100e06160c03110604060f0c0f05032d03060a05011b020406030c0302030d08 77
    0x580040220340d89403440012068a50380c01101d480d506c0da003596000340ca82902c0103010705034111003c502c01c45020500010018000c01c51842900b198107841ea4843c1c2001c1c1010350340c040c072050310b20714101c982055806403190b40e005008061001070032034180c1d40e002c0090f1080d284900c0c003007101c4403c082c00440d203a04140c080600040c60320710104d00064011741c110000040040d0015040c6605480c45190a810440b0380e0f0010303410101c4900145588640c0c01414003005090142c080b605040101c1d19000d8030821280600843c0040001c0d55a80c240c1a03030000000a603080d41c2c4a005498503404a25541c4822030b104110340c41e41400e585080c0c4152010f031a915503518007140782541c022200007080c040309462080385541c1c42c4010620503c000d0501c0f40000c02c0f0101a07c54550307454403c001814181c069108041c0207105242c0e484004481c101d0f03a0910300178414071514001c8103840d06054100a40c094603140707000082210840e081400c59000301d064031041d01c0c2d1306809843c6240d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 187632428 1250 187631178 187631207
    0x302030c18162714030f102d0b1c03050702040c26060310090c12021f020607030c081005211002040f06020f06010608150405070e030607 60
    0x300840040c03501c0342e000c0011100c580707480c40c0c030701c00d1102481d4804080c01800c14155004080c00c5034184905030030300080c140c902d030058000785140c584500300b550712035a40c0150120310313a4a4260141012044441c013400a03a55a4505510280c145030102c00822a03481164000c42198020484200d200300540c03403e2501a118203103041010307400c01c40101540d218540074080b0011030011603c035054003032004294904c0000c039043c1400c0c1c0401d8540b200683c109141c480c00d0007103090008030740360a1b0108984111000c0d00c09504613200081801c0c40b82d0100000148090055100103540041c07414003685140c3c90030860102d90748002c80c1c05040c1100c07140c000f260070f03c00400050502103810302c4000859035401e40d1f0754560081140c10101c00341580d50030340d40c000c1810701400645400340d600400307090000b00890380c05c19000310307101c0c401441154103201c806400920940d02505060a420320b0080c0100128a0003042c044c040b0f5901d81c0d0076500034070038030000944490290302610b00451 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 187633678 1250 187632428 187632469
    0xc030608150a05070c050102030703052401050712021c0f030c080103021027080c0a0e010e0f060103060906060201050a050a020a020c09061903080a030e010c05180a1a040302030c 78
    0xd41d24001000500f60142084040211000840c130100c0e01c20f10146005e40b189640105180c100085818001c1030b0846880031780305a501c2c0c00b4010340e03800008840455500209095208401c50700c142c3c10482c0c1c0020340c15115074100c411010321503019560213800005502e041114541c0c104046907540d00900000b0340141024403a511140e00540c0044030b540c9111241c0320307108a00c0d545600e00f44580c0d50058a80b980801d103003c00b9868031024013400740400d5482024a5854030881d0445400003610b40b0907907030900d00c0803800c2644650800800741ca403410307051140784d917200310090003003808135038070504646054086034000c401402120550720541d40213103607800c18401003050840010384125442582c28040755040324401c07000c24002c42c0150f03070158403002c0d842009401d440184d030011172a640341000c2846116084820340b130309081ca4944502d20840c018000c0341180c0036580000200b90104011b010101c00104001c100350780c8240e05032043c0028440038800c681211500319085d00703 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 187634928 1250 187633678 187633681
    0x6090215040621022b1d0307060b090603061308070b0c0418060305030d020a03140106030603050d05070f0b06011106101703030105030307080906300906060102060117070b0d0c03060815 81
    0x261940c29000071711117040180080c00075000310440901402207501c9180c075400102d014820700007a03106a01c040a415100320900f0b140250002c0c2d04d030750008046207031000e0f84015030310500c80c07540250f82045074011007100c2c95050011940010b40c00510560f0301803502c4048080c0340c404c1ca405060200ca40c031000030340c00c100d18044528040c1d00088003c0c0c080580d55038000010121b002c0709207008010540340000c006055041240c00d01180a100d58140030017042401c000661760345d140c019960304030150111a403110700040745c544803038500d80c1007184500c2050140e080b84440c00d400442c1e480942d1285a615410032151b101e0000f445690fa244d0030074082d44000ca510038004041d40c1d000100a1841c114050000b44e50030011003180400b080c80d9503040d01c00000c95600825009607001e00200524500800000e549070414041d200b00c0d210090407101c00f10500704402d0000d0105c103846d41d911420800302040080000c01e20380300c0080d0608000107000800410400c8110a0880101f81ca9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 187636178 1250 187634928 187634977
    0x50705120a0b040b1506190f091503180f050d0f180b0a051207020102130b0315120c0301110903100203010501020a0326010b0c070503190609021504062102 68
    0x130f505000780a445000e5008441e402282d070b41000400c0351a4580c1402c0700306032284500240391207014038070041800b0105006010307000c50141400d0b6a039403103260202e2180f00c82e50800b010010251030082c04000002450303001c000340840c000c3e0b000800341d550400c1d01050154100d407a200c90f00198214140300087c1400190844802016115200d04146250001ca00c00c0c0720b80c2d014007100c03041c0042c0d5010503d203055038071509103a4000c0034025103550540c04c00d81c0c985c0712071400101031a48a40303000900030420034814894082c000d00010001c110352007800c001d105507035202900c4135209008011244204810902c02d482c1642d4040e80104201001039070295400c2d50003070108110048030402e01650502c622000c9400303000307407102640d22000c03003010403850074040343c000c184030303803c040e0b070301c02c941d410141525810580121001c1262040c03400440c2c1c8903080c80510b04440c9100007004580c0980001240b0003110400c101d80350002d5020f40340c242207001d504851064451500c3d581403030f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 187637428 1250 187636178 187636193
    0x405030a02101e0e0a29070e010f03090c0305061018020c19060e0318031501080d140904020403061e1103010b0a18090f060905150d03020f0109050705120a0b04 70
    0x1c05090100c60403101c480d10f848514000c6d0551a4403030f503c400302e20721601e855441d59a5001521401c0010440b231001e00081c1034032001301c00c400101951094000c041c884000148002140c1100540d5034a003412130040e910b182150142c9889408440325002c101c809920844501501d0040a400242c10302444a040c4414412082d20019111072001c000c0303c1c4180b000b44410358459401e00140d13051041418185103e1020034150030011a004010303034040420006000007251a2080c80440440700d4614180542c1e4002d90f0040c0c070103d004002c1042035440b000040769008800c02d0524940c94054041d2152041000092070b01030004004946440014200c04103030350809400c2003a29000115584c1c2e450342c018405107072076100c43d4003100d846101d000003030408101d0070310184c80c11642403001c0114136044036014001d982c0c02c031010316109006294122000500a0225105c0c90811a07a55043e81c000e4500c500b0500f0812000440b00090b031340c0c00c00d68080c582d280542d54075250f850 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 187638678 1250 187637428 187637441
    0x1805030613021810150201140c031906080717030a170c09270a0b060714070e0106080a0c0804030c26070f0b070503100314010209090405030a02101e 65
    0x260848814400d0076482d11080c101a48180138104180c810b203441c003903407140141a9500d1500075a40f502024545280c9005507196000e0035400c8401d59a03241c612407145642c2540326a000840d192410204946d50302007503200071a0030030b05034103c40f1401c20001588a12400b544507010503004121890141208a151a405009182c495044c051804e011815a01d500038049103002403140c40100d424200038112a00205d0003c003c202c45082c61010448074455804054100114040000100c0c8410440c03c8090000034400d0601543d5515000d001da50701503d1400c045410040c1405000703100320040c901c12a00b40e5070b07402003d512a201d408042141d10008803d140170411740d034100040660041200c0e03842411131800b00348803401c2540305080042c0c04581080810030a0088819040f407000054a80104001d00341d00d01c910308490080c81074280545d008013402c0104400d03c60b01001605034034920360241c9011100322100403084800c03004030000e0211500f01c1c00c2070340303008660188 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 187639928 1250 187638678 187638683
    0x1081f090c05040e010209100906020c09040f120c030306051008060f0a170f070504060b0405011101200c0610030305160303090f050d1e020601170a020d030f1805030613 74
    0xc150103a22500801c013520744065054200369000612001c041c01c0200106c2c4c4208170b0342c40d14044007418500000e480d05542e030900c512400d203103000b003420700c60110542c0390382d00d03032202c0d01e010210180c8a0190005a0074101030b80420700c0d0860000741d03030030952041c54501d20142d68900050340c03044100b1801090465005400103010702010911501d01c426a054080c4a0300080070550043e058003440d000280d0440c500503414030500b003103907074104000e0701c0a40d182400d124844002455006006007401480d13070320041c01a06000000317000010051101481510030b40d01c2d50307a5408030f804403086092000900040c030811094181d02207100c41480d06510a20b03003c90181450380b07502c49500c010301810307551600302880c45031138030750000b480034001e4100b81d0004d160940714950107501e0740b04c14460891421003508000c1c040350014441c1d10003d650061844010400e80c0c140282805620f00700c0401042c043c100c8443c0f601c0740d401c0007100b1980c00800511450f07882c1059004d44211500c0304 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 187641178 1250 187639928 187639943
    0x7050f030c0703050d11130f0e0a0b120d2f0604080d0209090c22060251100807032006030f04050616080703110c01090b0f01081f09 58
    0x1000b0700715081e005800040d215020000d0300c4a000101c0c47e40c003441c49900c00e144840405401704443d84d0303401400ea80c0210700c03500010710403004501040f0007201e01d0b14012207a02910600804490300600d05180500022640c0c5c900381ca656200010140c00c40310b8042160781c849070010b000101c0c64001013130424070030078015082c504500e000c40c5900c04140c0e60103454400100d1038513a00d000d01c00001e0200128115030900e00c1c1c0c074010000e9180c0308060601c0740d030701460a110034421642c032502c546483c6111080c1080108500c03900074007050b52080c0d07288a844860021816418000d089003040d1420700020f04001807840d0b4405401014a000c50400032811211180c1555280c801552090560b02103175102441c0914000d41032203402040465020700b5070607880102544006460381c06a80303400c0000d450340003c1000ea2990203101025800c640c20302401c0010006461002070080c180a04040c01b6a6219030080b502c0b405580344a0007074000640c001c840103143d80d0800c4002a000700c00703 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 187642428 1250 187641178 187641187
    0x910140124020106171c03020a170604020403021216050f0a0902031b040f06020610031a040212031603030b030312160c060c0f020c010e06030604090201030e01050a060e07050f030c070305 82
    0x10010310f040318082225251b080041809940586800541200d03101407500b1442d111a12074060550441d401e0104030040e01c81001440139126a4115005181c00034101a00e41001e18101652100884d900c5180282c003c1c1c2e00140e541000341d005440118014a2880100d080c100c5da50020f403c0103061003104ca003045080a102d442007401080a401c0c400c42c08c0c0480c906195001c2c0c42c116018000211010444400300041039000001c0030780c0b42000080000c0c15101d500000300c5040300000e00307151500000441e40c41082c0c0d24203d20350418070a840c18441022610101501d80c02207144480d60b014982c0b00045103003080f030902c0084a40b03d42040c00c80341071591038072011241c544500102240c1c0002d503040d01541c0420404503405007d00e000c1a10821101c00300c0c500d400082e0585001d40d032181403803411a0b001c4e80111030011000c030020070182c0b0349a40d42d440501521300c2050100420302010401e41881017080704d200220091b02186940c40d115044001c1780c0c0070520030707000c1120030f10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 187643678 1250 187642428 187642439
    0x15041a060d02130e04020108100e0a09140106060519020325170c030a0806040b0f01030e030d09050307022b020910030210080a0f0204080c100c0b0910140124020106 72
    0x40642018142c4c0d0b42d42c001e02c03807405200241000704080d10310140c10702d110303070f0400280d0144400d10764030459085c40803071903821a01e00801041c601400801455081010104500b68080d002d0700015203158501060008410810b907224030400c0c075582102c018540c040f2030300d071108da507a03011100d12034800c490803104604400c0c80140c02000c404811504005004c140c2d460307210850b02c1c2c0060003143e040102c511400005411800c400b0309560600d84c462080c282605020f01c117950100f80c1810050100240d946422516940080c0c001ca105c1d92240e0786035496415021a1305003215910381c00c8541c0c103c410340801440c070300000c081002c500d0b6580c20210050701c410411a4080200d9100c540c0316003403400358001514140c0440e03050040c41400208011500098500a840303000e444908030641501c2e012110011440405400c04c144202070104506c0b0000d100c0c0068200c41c0001c00800528241140d62050203209203040304445e0703190030072114910007a4a100c010a40000600c00303035a075 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 187644928 1250 187643678 187643707
    0xb04080303040609052a0a1d0a0504080d111c0204050109030b06060708070516270b030f07031421071128050324010b030403050c100515041a060d02 65
    0x2906c0409403100e081d030b00d18981c0c1015021f07400584110070380e04918103e44c1c0d1020002d050010000726016031681c020605100c060400c031422880da80304180004030703202d000d0140e203601c06200b12500c20005501900102094801c0e9030a41c0c00c169900007100385540c90b50002c104c00603008691002081181c40005009840203142c0d692052014202030a6000340d8001603801c26880882e19108003440403480c85002c102c0d0300641c8070000b00c009900e48550f80460718050344440185000c1c0304558000c0b081c011351700410030b01e540c0301404a84007007220009480829400004800103040e040c080303840092840100151860005032500d589041a80403580003e0a4400810b0166500500612040c203040c04407403004c180820309001c1c6c0001083c03032542c40d180d05104112640b03c020012030101807186040b1041d40288404607901c100020000310000c00c0d0541e501007081c080d01ca40c556103414140103180e0345c00c84009040c0030f24150702c02441001d0f4000c1d510544035903800c115551180101 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 187646178 1250 187644928 187644973
    0xd02030708090d0908030a1209050d02061b0f0f07031205010e01061704050601150504031407180b03150a0b030109060204141806010509040615180b0408030304060905 73
    0x296a808903507040c0b410350b483c1080110741d000001c02009107810310038403200200301d030352028040c68401d4400c601100c07407500030014034074000d200e030249170121040a035001401e503002c2d20b4001c0c80d80030f09201006101480344100000d04c1c00540040c088028007041c0600900b2925000c1c0c14440c208004021241c0e0480f40241c0106406245900050103116070119403680c4516140078030421904058807110f640d0041446510000e40503030152080d1544240141c0c1c00550348203407000048040c0d040c600e5200e00060050142c43c5424902004042c2064020407142080140141c1956a21401095001100100044100d5403140e0090320151800d2050f054100c1c003442c001038485040c109451956031401030000d101c0c414400c0d0303902d21200001041901302c00c0900748540d0395a40319002c240540390591005687c103014940140e1000d0700700040c40c01048417a03401e071000c01d49900294149008900640300c003a80107000140014400754015401c65000d902294044c030f42801800840154 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 187647428 1250 187646178 187646191
    0x308010503160626040c0f0b07030c02090402060702030f010204090b0117150316080606090612060703020d0b060301060e120f0d050d06080609070e0a05010605090613030b010f0315110f0c030d0203 86
    0x210b01008007d52028a488900501102400c031854002ca0303031002060741104500181c0b1907984076020600719690182110711240e13024003980c406a0312109030034000c0d00300b0f11070361841906001075031141e980f10b000006d141c0b8042c5441e104807600c514070384070740325007c83c68040c1d010b1081030340170313150f861398841c15000a1486100130841c034549002400b41c91000507007002d00400c0e10280e5281c0c12500070400304d030700c1036540c0b07001030b100c4500d030075801c000d4000012080e030006030020010440c0d5610104030b400524007600c200d0b40400390300080c1c1d075940000c5002d5460782d81000c003590014900c11802440085640d4801207451504c4242d442d050403400d2360010f900d0340c0000010085005860041036105440010030041e81d850108060103034452001d81600c50400024402000420030300e031702c4c020310f0f004002c0c55450b40c1c50f444c0e01443d01c6030b140070030790b41d42c040950481104e24040c00740c2c0d0030b0244880011070410811140c5014107422540080c0b59030300042c850908024118800ba522848 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 187648678 1250 187647428 187647443
    0x1050339030c04090605030a020607030c0c050607060b180402100e0102120307031b03020910141204060f180f030e0a08120409060603020c07051e0a03050a030801050316062604 77
    0x140f404d02c90008803405035200c0d9001e9002580f01401690301c3c0340c2600d00f10740d010b08040700d040c1a940740442c0726140d2500480e620800205a4400384aa00c2c2d001003507120f0151184591009406011181c040302210025403046800b0503005440e81708101c2c0042e0402c06004490200d58601c1c1035600310b42007144d2880c002580c880c4014604094a0070441c80081c03c0d040840c508000d170000b040d2507010a80a4105110780001002091614a401c9030742c04900c205c442881c43c01d01c1d03d0140d01600c4e50301c180d03425079400c1a0300002c20030880c6240c1c0c3c0728998004032410b19120f42e0380d01a551440e501c401950300c5031320b022000039006018040704c41d040c41902d0070903039640e040640032401c58003540c00007030401d403060140e00300020000600005030f540c1101c0390761b900003405102444140031500380513000341c444200002003110018402c0722041c400d440b00341d00b581c0c8510070316a07911080c400344203210031840404c10806001d42c8810b0744858074903010034100b804030b4a030b5055803441558201d80e00d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 187649928 1250 187648678 187648687
    0xc1009110901060207090506060910094e050604140d1d0d0606080d0e0a0902120106050c0102040906030311060705040506090613080106030b011401050339030c 70
    0x61900310840d24412a0200c4655042a0b0000e40d910094055454410f542d440494081d640d41c405407420614001c003561040209840700800000842c03050411020000e0f020700300c40c0602c15681080e1810b540300c10900680400c45440e41206051980c0c901c035650064480045403040c00b80ca40f040c0d0181002003814500030003000c2c0b802c20301c114500c0800a440c0304044070a20b1031105652440c0045031582c1e07001c00c4030b040c094000e241039482551944904403683c0280b9800010706c100030b0b00210f0300700d0800b40e5954100c01c02d0b4070440b1048440e011030760005101d0346000c0e8002c1c00e0b102c3c2280f0001130030107031100c3c0343d90102c44290b0800d90108400069200300c200c8108001c90780203495141c081d0a2030311301400b007545130040004032441200b010900c7c0c0a101154a101401855803030b000380f020590782c5c180882c0c154001e00500c88880c09207240405254003c01c01c07203018584907858030310000074111a40150455804043c2e1000c107a03803100301c0c1a500300310050350007440f03418500d540d89c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 187651178 1250 187649928 187649933
    0x15051608010b070f140c03240105030a02060a140f0f04030b070309050c100c0b07210b01020a0f0204090b0103140c04060b09010f050c01020a0216080a0f060b01050c1009 74
    0xc2100591251001810403c0103400080052884007001ca070300c078110220104400d982d407400c140402d10784542511400764500c060144c185044040195581e40c10080d6903200c406240c1c0710307000440040d4000f00c042103e80e0f280c501c84c2410300c00c0c0c1c400f2402d5040c10010410038401880d848100302d520201400300c0c0900c18008810005074016003030b82810494107038a999495160030415481c188550440f00032101e402e4018518111035035030000b0101414030700214041c00c82c0b148074103000d05030903c5100f200c01c9085079103d0081400d90503001040d400680d80d030786140600003440c1c1260416111540740c40003070300300059107002c0c510036031031200c0b621042d40d81189000320340382407548124107181080046928440484066440030300c0c01502e841c45011051314203100d40c40400c44190310008028000c25404148914110b03920f0308501805543d03103000700d82c1d0300c00b9a40c0103000c00003440802c00000312a81d000940544060400a0604200c2c0e184107040a251135010712100f901c4040701d204 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 187652428 1250 187651178 187651187
    0xf0708120109021903021809090105010602190b010905071e0f120213030f1a090c040c090608160201230f0f0417030702010605130207050705040e19150516 68
    0x90400318a046003006404c0203040b111098210003801410f03400140b1104608580700031210718400a0404083c0f030822084040c0241402d1003400b005014808041c6041803207000e549a0341904014500156400c4c00813100040c00081c02c00014404c101000c03960f403201200b180003024003191134040501e0542a00a841d42408801c004480da06c10450446241382e14a0180107407030f00081f030a00158014604954080300d803800311f002c0014070000f0001c40c20000100c20040503400c0c0c9090041c0400c00109962542341805180003062f1180f0014003800c2181082070720418881c8008103011921080100140d03810b5100c07541080c101004016840e590806580d8000184007080c0d865860503454007008080307120010716020340e001010940d41c500c01d4111002601c070050440382e24050700c902e45402540030034030859031030040c58000102890680f14401c10404402d018103281074a210700c511480114a108076910501007811100d005041c0c4552441071551202d51040c400301820042d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 187653678 1250 187652428 187652431
    0x30806031e011d070602101a030f030304050115150c03091724010617100b1602030d080c1e130807180b0f040207060209041401060e060705030708030c0f070812 70
    0x2007030fa52000504004030344c3c0c0020801c021154905000684001035002069441200044aa4144240908a00e0651020006500480c800c038020040702031914101c0c616100b6902c00c2044a007032039001c045410380100120000c01344a17240c001c22068442415041821030389040000307030303800307410301c15034400c07820b82c0400801c4c500e920045503d6150002c0100b80301b8020700c0c0700f14144008000f00d0744c0c0451116100f405031000185582c0c840d420060030240c40b103400c1406a1280c0301d506c0e100720070b9034094200703103010b00300c0030403c50300c1c00c19001035030350541030044261a0000c80400c410000070b2060203080b03005d020101c0c080c041c22450105010040c0d00340c00c0119240b10324005100e000e55030b880e402c00c080320320140c402580710089800c0100090007000b07001d40d040742c1005a02e000b51420701c120709060707428640302c4110f0240701b078043c44203601038401d0040c2250300821a0402103548140610340c4030030f5045e2034900d040051591030345c0541290401300d40e4840c0100307450118208100089 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 187654928 1250 187653678 187653731
    0x61012141611030406050c030c060c090f0d0b0a05070c1b06020105010819020d0201030b0402070b060a06020a0b0c0309160e04170c0c130f060f090b0102030f030103030806031e01 78
    0x81038004449004183c40c0d10481c441c0c43c050000c00507407140707803030b90a006441212301c040c002c2ea02d030b624110911000d240e0245130204d1144a030050030403518608608102041600603800e8840c0c5d41d2035460140040001a21030001e21000101590008070300828100f140c04046120305811841c00b40c0180c292481070304800200d40110400702500340403005101d00341601150100701d69419400160010b10b02c0c0c80c0250f4001d07000280c0c0406014007010001d000b05020f49004010341d030740e41d5089031550f2091000400710640340c408610000b41c41130185810081e068281d13404100240c0c04030358519040e1b401510741f81003000801c000e00400c200e9440e170980c180307010a403514030008003081c0c40c2c12103007005600c00c4901d0300740544d0800b0523600003001c542d0116020000c031501e8109240781c0c00f100e4450389440a05204112455510100680d0781040c2c0ad050524116400d541c1c045d00d10803402426907425101d12000f0744010210702070043c80529289d400064412040161209034480913000e5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 187656178 1250 187654928 187654937
    0x1023040503061302090705161703061306050f041d0708060709080703030f030504060f050a090611090d12021f1a01020f07090e010605061801090608040503030610121416 74
    0x3681c0540c40e04505c0300d0b4040402d1400300d50750903640000c2d0720700030700b183c0c0c1c00340ca0700c09c40340e02e1000300c80c54a000640c00782104940c90b07450030102070441000c0c0c0e81540141600201090b00517142030800c1d400400d0b000a44000b20301c050b00b04a070366545080e40c2648003100740d03404002444801900214840042e2503a90064945903045071005042880c1070a036420405039900000b400703000c1c00b40d0240e4190440c2040a1000341410032007480075106000c1300f5186680b405182034441c051071700440d0110382c4080c0c030540340d072022900c90b003880418032034104041d4059401c50900d440c00e4006045a66440c81c600015400c1c0070708168041400d951261324150340c40030b008a601c01c0030016418048450789034010030300700a401350103400b40085601581d04400c02148408a402220303c2d5003280040c01c1ea00c002089680300421510100b0550703000d03106030020000310300305007801c111000600005080c01140c03645035040301d100300c910860030443c2c058100000d102c80c1032100445841e02681d6882d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 187657428 1250 187656178 187656211
    0x120a021509030d0503091504120f0314040f0201050d060303050d06060c05060c13120b18030a1b0c0e040f38060d020d05010209130c020c102304050306 66
    0x842d90303a150400c980f0084c010040002140c480c402c114890280b10001d40705805410545415003900c4c07241d090302d401003500180c068203658424030508884103143c4070b9106803078440703840b10000e10400d008243c0c1080010040307011583c0140c020503008501c1fa0307942035617580c0340140308070840342c45070400c50410030350009410128500190580d0010720504c042a0b81c0c440f454106121180c1581c06403140b03085021480d024042c4144000c1c2c0f06500100c840524444025100c5072248502d007038000204003030245034000a4100720f441c0d5811403007180c1c40c8200756140d074440c1c0d19030242102d00712011350400d4036440400429000b071f02c44c0c100b41080d034540d400013811441d4580d4041c40d01c907850354491110005803d42c0d41c210f480500d8503005007491031640c1362400e0440c080d40c00715030030701c2c000c04080761b500c02480d4041c8544454400d05a018201d24060241044141c5101c4200102044007140e0024609003c1c195110001700071a0440342c2d03250701c0d00c01450304200004140f080307413851814 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 187658678 1250 187657428 187657447
    0xc0a05040b0607240c0c02030622060207060f09060e1606091a090405101a03070f051308030c010608100603080708160606092316120605120a0215 64
    0x80c1560f202d070307500c80c1440108000120b0303070010802102d80f0640c003032400c00700f80720707074094010982c914854026802e841603942e80000305480c580c01036429030642c0030300c01c0003540803034031940c09000d14034421030010a10380000441403040d40d41d00c1c0d2040c0c42203070b07850822903076421042045000542d00728803500c0402e454460090512002d074410002a105032401c01454202640101c1d8016140208100040d00b001000071090b03074000d010b150b02180b0410542007002d010782040c3c030321404170399a03441c0080490340e07022500e81e0049104030307031040c4015001241c9503c06101620051100400003d000c500d0700d40d03054034154050b00914000c1e49011002e1021840030340c01c544d240e641117600203070703581c40341c8805031300034019210060421403424101040b00321407500080c146c885491800c900300441080b00d0b0071811801d5500c207540125040800301200d015403900350b509a40740d03a0005240303913501c0c08111070341c1d2201e84907103160700300165000451912104c2e04160840781d004441c240280d04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 187659928 1250 187658678 187658689
    0xc080c0f0d02210123031902010c05250e010b0403020d022b11010201051003020108090703080f0c1e0a0303090609020402160303110a0c0f0516080c0a05040b 69
    0x18004003001580004001040c0c406039011a40030002c42c0c0d20860002c5030301c0111255919080c007070701000b42d001000000021946003009094900c0040180007120321350040005400c0f0081b60072410300c4460f0f8020b4000c1442840901c0c2e02c104c07940140c0407004041115410074203216000f400c15011044c1c01842031160035400d03141500d0741601c0c075101826150000800300c1031303003696200d44003554014040e481075540603110186803040310aa150000181d00590a1300d104840404a4071012401080035600c1001c0890304503c40d4019100c0ba280caa0b250380c1a1640400e140c20501d45001600b444d100b50108212144201405000420510300c02c42e95900e8410390b01000e070402d91640020000e110b000e0340008280c680c000d00440d075555900301d0400d1410440c030304c02d03000700b8030f82480303c1c18107401d81d001c644e5202c4240d40c0d4070f0030702c1005580f81e440302c41c000320080c1c0e07181c0f00d4200000c01c08a10b240700300028001c6100141b00325880113042100d100c0860b048540910b0611100907410344a8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 187661178 1250 187659928 187659937
    0x6070806030c0a030332030709080c0a050112110415030e07060908100f1b1d01030b030d0c0f0602041712040b0301180b0a090906051e01120311060403050a02010c080c 73
    0x251403103500c2a04282103c1c1c8803640c2d003100146c000c81000014040003035000f0074880704a0300c00c90180c3d003641e00300c5d5080060000305441010b01146200c990b4002c6025141e006500e082c01d5854864189038451210030380f0a030b0039079900b801280e030f100090281004c0800c4030000500b01450103061203410922115103c00e044030a00c41d00e542c54005038024100daa82014090860340c9500d500c079941c41040081005011a1080c45415081603114510394403a000e03000544502900401014141000448062482841c141c80040b0b8890300000042c4083c0010001400e40d0901c01e8218151300c11480d0403c3c10050500305041d03002c04c0201300c94030058003540d0450b41d291070560022503c40c07403580090408911129800800c1c803601040d1070540345c0c0310304000c5025403400c112030740e5030030380741d5803040242c8160503000c401c0c03030b0f004021070517100351000f021622070302d0031180003024520f14a00d00072040d1000ca011071008102e4000c041d609105400440c0c50501d03150600741425040c0325800d114 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 187662428 1250 187661178 187661207
    0x50601140a0c021c1202010908040b070c030f06060e010603051e0c09180106110f060a0504020d0b041a06100f050c0307080f031e0f01121406070806030c0a0303 70
    0xc0c0419558401d80c05858820030407030700581865040c0f80c40005800501103d8071040f0b034036081c04458400880d1051158030b607400c0c0d000300e44624142c1081e1010460b40c229040844000c5040240440042d00c1002d10b82e00705c43c4101000329100f070406040060610b4160080c9013051320b0031003081140500000c04022030b034602d8081e103c0680b904002c0200c14441e81d143c43c1d4001c90780f442c61000034218521031504844a0755108403410300c4980100382c81f046081d550b581e2035400580441d504500c6507004580107440100300c09612411641c810070340041c1160b045e510001094400391001100d4104180c1c0030300b040350050114000c84030080c002102e00e851820810001080c7d101e0440c40030400c0321611034000315400c0c0c6802400d01482601d9104441d0350701400c200c03448010781d0710141001c180c02584425a5140c09a081141c4041c40307284020703040c0d4221600348603484038180184a0a0f02403482980c030070499280c044141340c6003000413220a4040d107090344040010a6101d01c1440040e131 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 187663678 1250 187662428 187662467
    0x6031f0203041e03110c0303070b0f07020115030b040209010b0408060406050a020c0109050a020a08010504030915020c09011d0c0901020c12030717040806090c0a140301060b04090b040f050601 84
    0x1c0752428410960009030300b503d28264590741c0300d0002d15420009030302240102d00212940b070116201030680b2030295a10051004419802140c0f008510005131075105d4520701c000107662603801e020302e000c0011035005840101c810802d0005508081030381501520541400702e21b802d01c1c001d081075a891300100080c201c10364500100d6124580c503011141403d605030b0007448010502d090540d19500b2040c822445509038090014040c034040c080c8a202d45e406031501800c0c20f00d0907010f02405020b0346480401c45c082c07020200800c0c0d03141000d080c00b828a0803100901100600b40c0d5412170364010b0203400c071140d01403090f250b183c0e80c0043d81c00802030082d030790403540f0741803c440da51450045840043c40380002c034600382c4021000d00050000c445001c0110340300e5845e01c80303c4549400200d101c2d140c018071441c9080c000c4a0001030740790160507010b0000107420390f407a40d800019810036001800141e031110528036030b0340b030f082c001c525050b0308070031003085035090070310018260b0b60f280c8030788401d0304 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 187664928 1250 187663678 187663681
    0x6020c0d08090607241d01092604090f02030702010509010b03031e190302120f070f0e03030d0c0201060503010606110a0318030b09150109050402030607180f0305010c02010506031f0203 81
    0x50000c1c505601074210f1821800c80d5010303484100c0900100d100d20b07081701b0450310a43c030514105000d101042a040050400350090b43d50300001400d400e01004216801d0402000841d203803580b00d085070007a6402c000584a04220400034203681c40900610316582c10000c2c2c000042d500401250181d881d81d101c0360094180c07c1ca036450b014002c4030200185d6007801603841441940540080c816941054180e200c1551440340d0000d6100050700d864000421410580402c140506100000d002000f42101d0821074808201d0301500c04203620140103035113400013000f680c10240554030140c800c604240c1100941c5011442d5280704002c0094100071101c0420403008006511200141d504120142614503054030078554481c60050041c0e500c0300c4801c00051003c102d481400e008680c01006070540361100b00d82100c112078800610441603882900020b00e0142e00000caa0040d84114004551030f50b9040000c0c2c21154020903442c083c1d0420255000000e8411002145880c00311a005859 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 187666178 1250 187664928 187664933
    0x30906042306011e080109150507080c07031b1202010603050607020a030206060405042402070314070201020d0806040204090c020c0406060207081e150c091509010507030302090d1b06020c0d08090607 87
    0x80c4e4582c0d01200c4203501e45200c0740140045013518030741c402c403840c7c8107001d180c51780310046540341000c88012802e030341c0500450001034030942150340c0d2130b102800441540f0030161218146400001e43d03200160b07640e42d0040040240520041da4060f02c640040c046503103240d00c004c1d440343c4c8021700140c413840d9100005405c011f401000c80e41d0304012102038415407010a80a0310003580025401c0d00825100c1030a9203460036480211000d16030f045e4003501928010000544c0d2071180a0505030b4071903000c2c0400f1901420302d22030260284180d6000748911010241800222080c641000c011500003550510802c0c000107941c0c1e01481801003429140c1014104541c2011a8014903060b4011751005100b40086268003800503040121aa40c00080c0e644a002c1c20034820700f546140450400e01c0b05101180c060390103058140c00250280741142c80994454034040d841c0c0c4420140b001a102c418880207504000c5e02e80307004015500c100d88508507031112034a600900795682e225201c002783c040c04 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 187667428 1250 187666178 187666229
    0x142a0a0e09100e0f10061a0702040e0d020d1d100f050c0111070210020708060c070602090a0803030403080a06030b010909051006060f0e0a0b1b030f03090604230601 72
    0x440b1504240030450714510403407194850a1a281c0090b00f40704804249070300c4480d611400d811a0301d01420300c040c0052161041f81036400081c13090f170344595610200403011000740300c40030f0040d02d2503000d07024030003426201800c11a412030100060202e441101581929034a111108100c0d0f6410084100700c00c1e11000ca94510070f0baa000f00c0c80d5402d1140c600d0004201d0b5024250b407c2c0700312080030810075841402c981d11844e13071007603290b01d44c4070300b02003807812070582d0044c4101800340d100907140c072007110003041003089154082c1e086648000100010b0580c003407041e94000b41401e109020781891a29107408810040c020180c2c414ae071500f501d002c10108200c490001044080d041c40a25568400601926924080d841c0032038045400072110b480c00080140c180e6200541741820b01a0199094800c1003194061104610040000080c4148a10f014511503034000b00203150502e01b91503c1c2210f0305210600801c2418030280d1b0b00401c3c000402c0c203506565201b075044690082c0f1483e01035 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 187668678 1250 187667428 187667443
    0x40212100204030b04030f0309050706050306030f0a080403021813020f1815011e12110403080708031906030503030a05040215070c0e070e0307090f0603142a0a0e09 72
    0x5048920000d000010032800e41c10b158031172402911803c181c00404c4c02c081d8141d81448100078042e8004100601805002d80069604004042d045803501d001007160580740c100f045105550400c40480e0800443c42d180b51100721032130369590010703942e00b030110204c0c15640c206003009100da50031420b1048180c8540c0c032019800c03002d840283d401810300c0150249000030b4810820300249056403000341140c090b020280000e100ca991700c0d6800c00745a00c01c0d10040c48595409803683e41b080200201288006001d48515401000f82d25aa81400942034200512602c51000034908006c0100041100441a01d6000010b102c000c1010340d9244005541524201c081180c804000300300d01082c080c1d401c0140043d1141800c00003256101c400e800d071408032050f0102030b41030748180700c28800c0400c150013801c0f04031b0038424089101502ea86c1c4004002044060f42c2841e544800001e005e080c000074132030744840c0d94100c80d40c80460200c0c170220780c0e101902e000c0ca5a40102d0080400c60000c0e0030040d40 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 187669928 1250 187668678 187668703
    0xb070c0b04030806100e03070e190c02030a0e0306070504060c061508010f0b1e060d0b030a03030b09060a061d0117180706050a1e12090b010515040e040212 68
    0x316007031030070780340242c00c080342079a009018072106181c68407202d02820085c02c05401c020300400d841e03450003644214160005295404000514900241c01e1459000341d004071003054000e1900c85e030a00074010490240c000003284207900810902c0b82068115003110300762442840d091802e82114103012001c3c196801c2411914441240300041e1004194400598a10580d109202c40d0804004120b41041c40c0000d441e1b0255160341070030030614100740140004841c4050200e003240c00f100010f410070740c1074402035010903150040751440703260518609500c22011a58403a4450604800601c001e80c521030b500c00300c800070903410305168040c0100031035240030010010f4180c58041060410145d05074400501c0303104906010904500420940f5282c900640c2c8071420303500046440900c42d5146120750007441100040340303c015419004040d03040340148498411781d45803000348036951000c0d05018a90301e00900050114941480240350803540448a810f40c04000c200315a08004442001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 187671178 1250 187669928 187669943
    0xd050604060b0103110304050715180e0601140a08010315061a0408070f0b12040c260c040902030c0415170c0f0603091903050f0c10060801020403020109030b070c 71
    0x2008100700c220b8001d038900300c400b0f0303805005140100f0a0900b05000c10b032802082500b20306c00c180034011985001c5c0007901c4540c94034100f84004c403801102d490300d41c2d0b08001d54250090741042283e5070007031007000d0911000c101c807500d089112540148010410b000080c120189440b05009109180e000300024140007168462500b40a0401d0f401c0d0780d21030700c030f066624001c1e01c000080d02e02a8189070700880700d413491702d1860400b4806c41c03d10a050010012119501600c5e0041820388505c0d140b102a89034003009401d210400c0700c0881e1401c24130541540c4980c0c20990068016140808c40550418084d02c0c08a24034060540c40d10260607150098009000b004510003141080028003d811000c143c03903072401c4c201c800007448140d200481d0700c0344442d070121904041c1e41d03005001e00b03031000d13000740b40450620550065490a640c400c109001d5554810703211041c5070b5426124890003010200000c40c6002d00c2d52380081d080384410300c40600070800c514000b90300726000d09048201590702191 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 187672428 1250 187671178 187671181
    0xb0d2d0602070b07050909070f0212040f2409090f11040e09010e0d1b080408010e0709050901051b1303060e03070c05060a021507032003091603080d02090f060a0801030b0f0709060c020d0506 83
    0x42424480c4424030621000401000ec1010401d1805042d203481d254a5a0f039000c21604012040300500341d084848403129507685140c450100e100c102801c0034200c80e6038606018241070241c00c2c21344040203070701205900100d40034182c0301c0e00b000c0480c0a0705040360f102075900240d818128040d010716031241d41c684d400c0c9405014031050210700c060a0b00d0050344100016102c541c449422102c044803611180726024101d603815000000107030031508000c036110034074079031655124020748105c41080c2071294400b090b0207041042c000d01640250030300f0341e642424101030140080d42d980201040351215000301c0b01040c1c95a00c01c2e084201115640c8000d0003030150103110200040e4003c840340c003e5805415200012095402c8490b0200c80e0030102042c1084841d52586009601906083d030b406640c20884982640b6280c000d06601c0ca225240d11110350f16508000d5860900104440c48940e020420400340a0704809440103440b843c2c03504409201e0280b0120f0040220002d02030083d121303140 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 187673678 1250 187672428 187672439
    0x7050409090303021218060108030301080606010e030f0111090f010509030a030c03021507090320130c1b11030d020a03050711060c0114060102010b040b0d2d0602070b07050909070f021204 82
    0x15411b140111007808460087e0b030303119413540d00d901080c0100b01091b08020003007402580325502c5103500c1d000041c00c0e0780e080409c0520583c02c56031064449e0300401c001140c0c10005182051004881c250700382095451b080b0841d0022351070b4246c454006060048070204801814820072200f45118082401e0107502c1c14410381c040c103205510721040b07d0b0264041000940507031190300c19001c3d42c1000e000a4611010002000094030148401c0010404505030843d600802150b40100382c80c000c0c440b250700608a00c0034181403481c0480d4034025507004442c035070b000a50200403242035503000420316405251442c00a580e500c1045210000341d030804500c1c00222813400c00950241009800801404120005200940c2c40117003000d81d00003040501000420340b001d404c0315400c040d040b603408602d0aa4128500130f00183c503401c1d10002e40c04500a410401c0c40c407032880d04141c480c00c0c50342c117010b00750000a040e142c0092a500c200f198042140d00c41c00d000304150381d82c45100010396900c894964 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 187674928 1250 187673678 187673701
    0x230a0f0501052a091e1306090e03040f03120905130c09210b101a04090b01091505070f02030304061106060a1401051c2c06070504090903030212 63
    0xc0c0c50015403d03c48154540d044403091580c0d504a00c2110070302420b00880504000101003103044e00030a008a032158500c41d541c60f55190303600102400d8001800c10700301350070441110764610783d66880d58404c010034000044a84040000c4030b50051820350107419100341140c0d0101d0301c0d806036410503202c41d2000032982250700700000858550740e481c102140e0390403c0408151003024803806e0310564418410225555000a5500c401010381c01c03152135039240b208414000040d1b00c4400e00641c046230a000034101030251703c5c070a80e000d10342a02c0c0d0604149400000b01c841102c890107000c2d0004500c020054861b4010480a03001000d07a0345680d40c8100191800000c4005000d081c0540070014404d1318140317a030342d000d4030035650300d001445881c0740040d00c0661001510301c07031090b51140200340d0a401d5024250074810303024041c3c180c01c004556900100404025080d034190003070001c03c030940e544002a44e084500d214004107001000d41000d50083c842c2d8811002300c40e80e02020403070f0050300c2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 187676178 1250 187674928 187674931
    0x90501030b15030c010e2803030c0c09020304110d051e1f020f030106110a05010507030209090a090f02042003010803030601080709080604020105030c19032403230a0f050105 76
    0x1003070b8068189000420405403104050b121580c007003800804c0300c0c100c3e4200340f103032440841c1c60b1102400319520707401000c0c068102d02e0741c800c800141e520132643d4104410002c140c3c00070f00d1141c0c815030642c01c2c0b81c5d65003405040004001c5019002d013000002c244841004080d640c141c03100c04d05140c501211601c1c9488050545108244c800414281441e94115100311100c01070b60744c21050550b401d0034021601d081d404070600f16184110826000444e80a100d294010140c51300c006030707588020f01c00e20809842c0184101001868a840c3c030380410b140c0b00c41c10300c8440e81213400040b0000b031031040c40f800403c685585880000301000104540c2c900000542c00f408098a803080107a454000490340c012490040d2421030300410301103001540140080c0d86c0103000d2904c5d1506000400f901181c8283c200100300303000075201c0c1d542507002611112030039003458048200d080114215160b090301203400310ba04916080381c1c00017484040f0810b115940c9010760182c0b00048526050820342c1c080c150 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 187677428 1250 187676178 187676191
    0xd02120901061403030f0306060903011b05041410020d0e040f0c020f010605090606071509080a031d03031b09040e150a06050f09040803060a0312110f0609030f070c090501030b 77
    0x180d8100d1078004146c4032026904c04040745545c2c0c4070b505201043c1c021280040d050342d02c9002002d14005110b50401c0e8254a80c0c1ea1942c0311480c4c40c0202d10100580c802c2d20f4000c01c10440c03444a00da0b408210315020001d43d04001e0001c0700e10304007041c0188040d440c403030141441c00701302c814169404101c284c21101410020300066840710208142480f040d52002d0748940100103c400184001000c103d0107810100006401c0c02c0c59201c210190b4441c00c14400020356a040481c00d826940f8100e1510a000d18011411441c10318490000400d19a009085081c1c012542c1c0d4690307a42c41c3c014000c45104141501c410b8400c08203030005800050350205500b50134840d010400f41015800d00001420080601800f0748598071110800e80c005810940c1040e0140c4002c008170300c820452a281030301c10355604099209601c50706042840407440d41600340c11140a000724020000162510725100140701561340701f89203421030303041400f58021801642032000000c00d014401200500c40c00c03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 187678678 1250 187677428 187677449
    0x102040f0819020d06060b04090207061a060a21020708030709090e0601030f0f0f08180405040c030803070c0b0108011b08070819090203010207080d06050a060203030a020d0212090106 80
    0x20303103401c5520b4584090a50180346402c50114110152905803505115540181000a10203860b8204400c2540c060781000c24903a40004554040011500c00c00c950514039040b41400150200700240c03551080c0445102007003401610fa140d9415408802450300b030a05508542c1c0d50040d140c00310440e081190b0407400b05001840000b41708041740900036034601c401e030203420180c0c255501c803a261510b058080d143c40700e81002203030010340e01840c00d0680500600c02e031600c8180104500b01d0342a40902400d0155080c03009000014442580c0d0310b00703a03907205403541d850b0303900c0360804c070390915134860042c200c0d24081000180760541903100344074100304641e08096620300c91205442c01442a01c0040005540c0b02c00904140c4502e9620180c601000c0d002081c040340780d800184c00c4e03070005941540c1030b10b00004c40200e817240c0c501c60240200001c1e650803400928244000e502c13400700402e16581c203500010301c100386109580c1203078507514103908144001d0500701d09290084c40b050040ca0000c9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 187679928 1250 187678678 187678709
    0x8010e0702030406050d02090409050601081212010509040503070506070c03230d0b061e18030d050f03060f04060b0702010215160c080702090c030406051e0a0c02150702010204 77
    0x509420155520448054004516041ca000300c11035003640112655001c0c144d09000e10310740c0366150300072320090710301070b0b40148031075410503844508058000101d030206403020040708001044054010341105d108030703500300007952241015420740c8070f103a02c0104180240b10801003c00c2d080202c0050b02d50180d522015060880e0384880715a2603115001941c2200a01182c0a84c8a280c0c01c4110404030181c00642050b54005003818a41c100501c0d0405900c4041801c091a080d60a1100300c10710040b0000c0c00340903d000005440c601c1119020810008000002013690311080744105400c40c0142c400c00003965201030400b110340102c00124010f000311030425401c1111030805d240516401005000442c103044c07020348026401b480c046900f41814000d4902503520b140015100d03501d4080300e035a60b0700c0c2601d000011540d006280240c202021000000c0000a042c9000d500803108400090801d0740664140e184c038200c200004000014441000302196041d00980220740a906014111 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 187681178 1250 187679928 187679939
    0xe0c01260c0c10050c07062301080304050108092116021005030906090601080c010f0207080d0906020d140304140a050d0201020a23030703200706090c080c0a0b0d02040519060801 78
    0xd844d4295805646513806101c0070000c50165030205030800300c242050b0743e000e8841c180c2c0d480d580d9026408459180c1011404100c02c4d60844044c075403020480380506840ca41d9024044070f44000c2402002e02c160000c1510362041c1c3c91007441070381c2c0c503400800c5110000385924006101e984103c0314441075003d00000b14603a40f5000034224142c4110710003400c60074000000441e000c1c01400b070000214070401400245000003400345c1c01c4001d103e5951250401d08101d07000e4549117902c40128100708101d484c4541c650a05d1050b03c2c0c10951111200443c094031016503841c00e00c1406000c0d0043c041c44640b14000b40e015402019411041d0f02c0300c00c01031915120108070101303202281440c0755030400015400c10f10030380c0450401294050045070b2034005903413505042e00022400c0321281c0c0d64101500521020030201e00060006030000d1004c5030244c0c02052034040c451084154400d40450385100c1440c850301074401400000c0c007414000c416410b03000455600521030f00700466242c0c80003185 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 187682428 1250 187681178 187681181
    0x9020a090b0d0b0606070605040b0907050d0302070e06040207120806090a09050703060f0204081b011d01051801031b03050a0501050109050108131b030b09100e0c01260c0c10 76
    0x4628030000c19090701c40100f03071030380706a00ca002042264007540822144000541038810103000e90b014a2200b811483d2103840c040c42c01c40140c112a11400c0da400c1e14800190380080c1c01010f0381e00c0d80e00300e2140d60b110032010401902695500403c0040b481c00c21440040e40040b03854420300c41240d02c000645c44020b4842300300d032203007503004d0000c2e08850014030100da03990b04040c1d0a11542800146040e94403110036040102d19050f200e03003580c01c07241000c3c2540c0c0c030103100c0701c12920101c4a8144064540001788c05442807100559809880c2050403490380c3c000d03884a07030412580d07412008041c00070980140248000c4610001440c680000807410f940708200c0c03481a5101a110446c0b00d84400016100c48800b400003198682c112600480ca01c4000702c12a074001c3d03210703000b000c42034100319040c141020740310381c108141d041c40e0490340f000c0144c0001d03094000440030f0030100c441c011880c000b00708000381e000c81c00d0765110803501400740c881c130400d000b8441008400140c03250340054464000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 187683678 1250 187682428 187682441
    0xa05090106060f0e090c04090513050d0306120b04051006080f07140d0312020c0a080d2d1e06081e12040306050c0c0a050c120303040203030714100f09020a09 69
    0x20f884940400280e0605c149041d40003042c488801f0b08282c0e6400010b007d640c0121001c80344210f00b047d2500030080100a030b00c0d1080c1e4241801d0018605042d800c08038006c219802405d902c600b1004201030000500c43c001c4804c880041c00e10020751580c203000d54515048010040a1080c02030002d0045280c80d80040c40c01030043c5150004191a1012510243d03043c013050490380e402c01600700d21580070000f01e60720503c07a00c40c0c1603c0c2d01950039004100d0307498401c07411641c0c1441010f00d0581d02004072180c0394041040001500b01100c0e05201100314118082e4080c01d850440045120540090648459070b01d0902d00481a90364000058840070040e0845454850910040c80050401d81140d54056600300140e420700f0300c80b580d21460304965000a440c1504200411101030510380c900804a100300c500030762450a155010030343d2841000300141002004182105c0c14400620410051035031004051000e491035140784002003600d054103d100e08064900015500e025003e042e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 187684928 1250 187683678 187683707
    0x306010314360304051009080307030801050a080c010c0303021305150301050901290702180a05090601051027080a14010c0c080904090320030d0509151f05090a0509010606 75
    0x3c500b000d24100c103100b140308950301c14400f40325000c41d000c600c060041000d000414000d507102c441e25450081448490070f05500300038441e4021480c04581c0c2d0340c1118074041071650516005a42d40056415004104034681290ba803103c0d41040c001e41e2884900c000d141038030780c02c5508943c0ca0346d903440301040b0f4000300c07010854690120300e10510040b901401400c0e40134000b410303060500300c9602d040013140d10701b10f4001e02120350300c9c414420224820007501c0d0141038261002d000c442c1e40404042c010b59141008031110340e4906000c40c0c807181180c60039600a04070032084404181951410f865030b845883c40c1c0300d4443d0b2a2103000030201d031245500058035a00004c04628000c0c81c1000c2c00003404a02c5415024800d820b110109444040501100050751101c003558944049041240907288040d01c418415440346161201007403540c81c0254102084030292034152024000305013651032960f200c103078842203002c00c0003201e03402600300c14030403d01075000b00320440d11500305036200382c00901603 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 187686178 1250 187684928 187684933
    0x302040c110d110307060e0109050d051606020c032a0c030607090b0c12030903040e0c03010b0909070c050a2a0602030301151e0c0312061208030601031436 68
    0x259844a006400681a4091580c01d1313070302e000030030b85501c029505994000b00c3e0581d03498100905002e010b010f880d92141c600d16041c7d2030000c0b41009620540d84210000e4812503000401407100c040801c120b8180c842c0e01030302049084400109a040c1e00152620041c0301c2c058054040c4a41c43e01142c0c0901c51500c944440f40e1072810048044001e07013141c090307092584a8901c0c1603943d9032404000d1480303054030000851381c03581001010700c8140009018040c0c048400c0c00184044050002500d070308100540e1110b1042c1c0c0d511808031818610f00001810b140500d05030802071008614640110446400303401400b90b6036500ba603412103c49108410050f0401e0006000e4841490b4200003015290b1030407500d0281d01000c984410b865410110000c5111401031508140e081088218074050b402e104204082c030303082089030340d080340540c01000f10700000001340d400c0c0c5c00795002c05902c20b018110405146001098007170300c1c0f01075180501200f000c0310540d0344807006a07030000c00b650402001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 187687428 1250 187686178 187686193
    0x110909010221090309090103240212040609080403121d0f010c11030f0303010b030711062824060206010504090f020409081c0225050c0d020f0d0c0302040c11 69
    0x64101240b501030401e140c1d90104000d440025515001d0090186020302c0c04e5400e80b200840d811036200c40c1da0090071401c0f500620611f02d80001d40084103500c145c00c000040f60340d40e000d203400c1b2400d204d19040203115078a6040542c4003640e000c501c105201000c6071205040500c4101040800000e02610900184004000c1c0c4005401c0c20403c3e41e540c0800790444008020b07040f506411a0426004182c94420110070001a160b11103c000c41110766030014001604000340c01c031031309800c03a2003092010300100c48000b5418904e5400074207981c0d101e0220440103003001484c0c0c03010215621483c0c2c0103109880c00850146003c2c401c00185613070002e4400198032681d4240005400d0004c821b0741c098905101500d61502c1070804880015004c1000580d100681c103403849040407160780007569a55182a4030700012000036404000850880d03038803118516501c000303400400c000d60040d4201c038241840d041045580c0c440202660310840e414004030200d20b8080740d1600d120030035010036502924 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 187688678 1250 187687428 187687477
    0x1d01020306010e010503190b0a15080610090b030109091104020a0c0201122f090910031703100603150b040b0a02120702060703140d0203040b061002070b09010f0302040906031109090102 81
    0x5000c2090580d01400001c9c540781d491035070103105000d01404601084401c01008024544082d2079016442c2c40d0030507108140c1007550034540390005000d036064407075076007001809110300c807a0043d0480d6801402950784101d580c0005201d0400c2d86800c03400714200700d1890452088a015020310380c05840c103020100c1c2043c0025412494034040b00d0110004100a0354025880b2500964481c000d401203503034181c0c4c55481d164410010002c4954a914000c4c0180501c0d100c110010900b1a817280c41d0110fa0b00004040d001d08004c000e81c4052299200094006070b0b00d094400545600c00d8a6020341d40802c1034008bd0b100c040c03050040c002d41c4041e0401c11f400c0001e0160724001100b0034030602d09801c00144900b014202c0c1e00c1994299010006030041000070b24004184070305082a0303101800d0054a03002204006001e40103145041c002600c0344100b400d803103907041d0b800504600340d007484210703524109408003011048105014a0396940020010003050085810381e19040403856250324204 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 187689928 1250 187688678 187688681
    0x507030312150b0a1809061221020d033c060b07080904110d020f1b010c020604110d02041a0a06050a02030a1b0b07020c0102010f09030c0b0a1d01020306010e01050319 73
    0x40170300b0340c5c03007031740c41c0d03402240b1800306104403009054083c2040d4007510315030030300c00710202041c4228031003c0d150000d948111940032800030360000752801d0100e0010305184011041000988005000c801c5030b0064030700e4441020b0345480c400000407020010161103140518441c0705120000c3c15260040003c03062605241d0720205e81c484071040c54600b0f00180c0c1a00c88260b070300481e40001d43e2240400c040c0a55005402481495413400000300310213a0349003006901d03207000910142c00c00300c04060b0480d8a8036800c651031070481d401002049020a0122564024002119124010b041c02480030620a0040040720780d0340c0b01c40e07002035007400c192003021200c09a410b2001200c254038840c4072000070b810500c07201c2c050030300350300680762024056000908403000c0508500000e410001e11402081d0400e50031307020325400941404141d40c568042802504580d02d94803d11090340c0c5010144c000e043d130180d40100e034266140019540381c0c1c00111a14041900c40082010b11480d141140c00510f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 187691178 1250 187689928 187689947
    0x612070912080306090a1b0203040315061805090c030328051204080f1c0207020117060a030b0402060f030906040c081f09151503060f020412080c0a0507030312150b0a 73
    0x1c5840812060750800c03a5100c61f041c02d07100c90000d40d1010406108001041910b40050041101d040000782d240810070601050842c800c443c6551f5603002043d900d4500f80001c0344003400150890b40e0b24210010122401810001503600d205011541e042016110358110b803404183e4144000ba02c0d111516150f4455205508903142c90074208582e20241000d9038229081d142c58078401a12460140005400c0d03000882c1c900da03407403c02d10304000080e030b1240140400c0d650400501c1800e59201d1010500510800c52a14103241c008403c01075810000070b100d9200b40e21504450000643d2040d80c20b507915451880c42c0c1000f20481c000d03a0740082143d10880029005a040391210843c0b07003000303822034200c1440b5000512600c24181306010942c0500b810120b140b101c1146883d01d03166400403090443e00d4000c00c01b400005201000079410401c02c0802500300c002c0e038080c15501d18015008030042e5803030710341c9503051241d2803002c0b9403a100410100d82d000220240b501005030400c5444000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 187692428 1250 187691178 187691191
    0x90603020d032006010e040b06030d090b0a03020d060e011d063106030b0106090807050d1209030b16030f020703020c01050d02130e04060b03060705070b0a0605061207091208030609 79
    0x420b1a0f107100d421400c0202c035000307004441074503e5078100781c00c002080c1c090040090f4000d41c85110039103803c41d0f01103503590480d15080442c0780c44494041044001e80301e034403003000328030741020408100c010440040c0790495001480038480c02c1070a03409840d0403e4101d071510346c00b0707042c911004012001c4510242040c0311008207032246010440d1280b0880340035070000c0e25071204490041c0704031030300016071f00d02900c4403c000b440902d10f40781c0052588042c0610043c03680107102c203160750305405201c04078040e5a1000d110b000a10380043d01034840717680051010002401c0ca40d1005504a0724400ca801c615010b40c060201d0780d01c41801901c555121504008042d0b5082002a1032954204502c5000e00768900c494926070074503003807080544048c540124030075000303101800300482c0c0060803901c406501858002c4d10369220b500400043c0069031220b81c000f5400200c421400008035a0300380b003040107407034003c2c0441d100e021000e124919050000c00403c401c00100d0140d15001c000207074004c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 187693678 1250 187692428 187692467
    0x703031b030521010e010605070503190504050d0f051e0303181905010e07050a0806011a040b03040b0f0f100e06030c04060e090d031404020d020d020307180501090603020d03 76
    0x109500c0080c500740350100a0314905036801c10050041d85c1001070142d004051520b00141050201d454841d164415075907900c1000c0041c010303007200240150103640013485c00030070245c0741078014201000c2e614110201186e207801040c1400492040d203039800310034440040000c50444d81c40b6000e5500e00e004d10381900c00c1a10400001c80100034058070291100c030b1060001083c0c41c1c0032008041c3c81e051700c5400440c0704051f404002d02c840301c2c000540604440e40c0016200c3c0180380c802450f803040c03280e900b0a1172290800400c00051160040c0c516001c1d0103100021a0156900c1014910500c002d64003e000040c0b512400c20180d00b007103101d17540085005058880c000c42900020b02259801d03440302404180c99010042105004e01003070308071401d81e06043c8500080300e80740824000340204020b03c1046c4c030105080541d200c0100c00e685c00ea034080d00b1600425200c04c8072204e0003002d82003800c405820300c4004100c0303500501641c011658050301640d0341080540d81600c40f038040142918200 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 187694928 1250 187693678 187693687
    0x6120c0e060d0206030a0204050a080109020303032a030403090618080714150a0306170c01021207030519030b030d050c030403080309031c02070210020f100e010e06090d030b030703031b0305 83
    0x140e489100440c01b41000d200300603a124501802e000300c0e00709591000d18280d00d08640310000da10301008032130f800030702c0000100040f04000d070f1281d0900900d100720072500348080200020544c0006050054603c26140d07049107540c0070038481207280c06030146040782d0b00003210800400380078042c04190454028402d03501c011013200c040103150803210b036520010b9101e0710204007420852407000c0e2501d0400014100b200c0001d80040c0d900e10826600080142002032850b00f407600c179109951b0040f04200e2910904104100001d01a1070b00c08034040c42401886840729080b40250100c4800e0300c0c0000165080500d580c035449000e800003803181c1500e010402103400000c0c0c900c18041d2039511800001078503002c0500500c01281d207880c4a003019035021610202d0714640001d050010b40840e0440442c0b20316203001903a000d4445680c10780c03024422507082c040b1444000c40c0c41d100448041d42c0800c80d410054041542d01c503c1d521018020406c81c0c200c681d08446000301c000c0e01e20340a0700700f06160 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 187696178 1250 187694928 187694933
    0x31410052223011b08010b0310210605040303090b010915050405040303020408060c0d1d032a0a0807060c0e060d020a0e0a0b0712030b060a0e0409210306120c0e060d 72
    0xa42c4c106540704800b0508031415a05025008045680034150b8481254290b1034007000040b080d5407036004043c940e00c8100c480c0404120002c00600c0c0d09036005000340403c0c1017500e40a0090443d050040710a40100e5002190380c0006104085132409480d00c00c0b0030084c541011310004010240c42a001c0640030070022828500400605000d582c180107415603804410000c401142c88010f408d1138090002880c0328900303240002640c0d00c8201944604008604100075a14407140700078031200740e40660031842c0140030b50840600a802e00500d030a01041c81c1c241021500010640a4154007074414060100c0030b0b10306030b014081480260400d600302c502c82c1000102c0000a1f5032004814000004001c002c021401e0300354249022181410310066568000151541c0604c464020030441c40c0394003000c0c1652640c101c1c0c40c280d60001044206095228420000d0444505000700842d04101001807060380c1d442100c02d17a5500040002c2d50982081c5070000c0c426006040c02c0d500000c20000c5501 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 187697428 1250 187696178 187696181
    0xc0d021b01031a040c0206100b040b0306010509010c17180603011d041a25020601030b010506070804030f0803090601060e0d080f0c07140315040c030803040c03141005222301 76
    0x900c4061b80080c002441d00024880c1c054000380c002850170581840100074051094042c4c0381c00c031000b400e0550710350440c07800484d06039202e46c0c8060040602080d8186c039500361b000c01040c012511800751900e0061440501c40507100078402c00440014080403600c45207980c489854119120360700300024043c0c00b0341e40c14115a801e581c4401d480320840c0c641c00341c600306008900007050382d50001e41b281f0341c515100d000c0d202c0340c148078440c010500000c90000b001045030455000c1d540c403450041c080f244d14201001c05400480d841000d6120740070010a049015000c280d000c0c0710000c0640003004103d07030b0792035010303040b14000882400040c00100c1c200b140038000c0d1000b411040402442410311306080510f8010712019100003486220140700106960440080c16a5037080d4200e40e40d880394030300340103808510b5101038682c54007981c40300344c0700b800030418851400d00b940d400d006585650907203c0840208481c00c002c0074420745d0810001039200741c0d666102012801c100426140784035482030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 187698678 1250 187697428 187697441
    0x203030a35011508040b0a0e0c1201090209060d1101030209012c0a090c020307120908030301060e03010506010f020d030506011107031a0c0a09030b0603120f0c0d021b01031a04 77
    0x1070320041000e0061000d540c00c44201c1e009110289040801c500303068841c1c0880c2000500300c80c00460700c854141113800f01c02c214051400e040a01602c240140c0000214003c05c0840030481c815810500404c4c100d140c050041d03968940c0050032038128012a0b00158020361200780c40c90306001100b00c214484001c9880100c8020b00150032080f100020310042169940d002e4001c490541d281c4200450140e50000544440c8e60303101500c80440565640180d0390861141d201003001d22002001103001e541c00041c038400c0505c10f038000d0200761500001900d1100e01a814940185d1207045000c425502c2500540d400c0081030510b0f01e4012060300c3c41c58207040043d00107452036030012240744500e080c40c40040d030b84111600181401c004980d5001405c02d0340340e01c400b40200406401080c450342e01407146c428410b040e03044581c1e40c1c03010100c0122090b0490203a010300c6000760a90301c0d21850020560841c2050000c0f04045c010080c100154000c100503041000c0c0510b10141c40941900c6511465 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 187699928 1250 187698678 187698767
    0x3010b1312051c0f1403270d11070b0a0c15230105180402090415050103060c020c030c0123040b0304030c1407050612280b0a050d0203030a 61
    0x1d1051504080e01d0b43c404030f000000c00c000b004140d4162065060744002e82510a4001c000c030696070fa03c43c940301c1c0026204144070706044400c0144014016080000c4820a400d107a449000544a070841e40740c1d100c80755031044d050b003190108480290648540302d0701c8802407080740005480004c044400003280c00c130401e4150b0713005c12600002904055210703114010802101c20011510800c8040324420310b014000900a40c0118040350800c005c0350403042d4907818241c1c04101540e56401c00c00007511540503640301500810b041006142001b00b021800c042040c0c4808035201440c15480f50b480d00c0c03103c0c800c10100f00074000803807110000001540203030701079592010400440c1c01d1254014001181c00c0500c2d50000707030308103c607860750780a440030700800f44108e41c00c90b640d01003a490758100c004030101300081608080d0104011551122140341130641c0c2c0c000500e900c81044c001c030b04940e003202951584c010321002428034854650004007003040011404008510802c030f440c500304501c02c5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 187701178 1250 187699928 187699933
    0xc04020307110607081509060d0b042108070809010b010c0210030e16050316080606060a09120b1503030903120313020a08010504030305150d0303110f0c030315120303010b131205 78
    0x900094001484851b1710500003210504070074102800014000c503103640000304000041800107050040d031500103401143c0e40090015941001e40000b0140c403004ca680d0300115500b074010600d00981441040314600c810703110401e501e0019000c00c40c1086882401c0010151620f4501c0e8905d1130a01844040361242d0b0002c4d42c80d181400101810480050582d20034210310840820540304006011034101038181c904540c0d0b05103212084522210310b40150b1008144008080100213181d150300c0e11802c003240c1d041c20981e610f0000c01d80c5030710a0a4010380e06070700032281303644a1140c18008580162080c00c9010104644c0d50210301d03c0f01080d4000c01c0c040c0d540e00e0400080c150103025056101c00b41d00c00700d03203201021900090a9140c2c4031000340c10565180c0c0c40102008100342100d113801070f076030507040c2c85410602015950f580701f200c008100303201c11010320040c0d0030400c1d4902c081c86080d5000c1c42c1944e0170000d1100303890b041a171040d90344140f200710001c1c2c1a60312a41d80c94845e4001c002 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 187702428 1250 187701178 187701181
    0x210091203080612010e01150801050403080a090f0605091b1c0b0a060e07120f021317010b0306090c040b030c01230715060305010c1103031303020a02040f06031202030a020c0402030711060708 84
    0x238521554029400b4020320b90600042200180d4820945607000140860000308031556050a60042517402e01c01003285245c20148103800d840068072080003062040d07103c20b501817841c24481c0c81d08650f12561007507128040108000750300320400b554072489640700003407015994250145200380c01e032114400b02c5c41d03140c075645030310f000c1f405000004c1c800c43c031f81507250442200070450364070118401c032811016040003140008c2c1c029000144151001412103400c0d0505c803401039206c00f05e041d4064821480c000810b82c150070302050902024030140c41d031140c80310402c4440007100c41001d00c0c0c4194a0403c004044c0010750380c81894104c1c1c25180000074283d425858071508540c41c419115007031210061030018192000011203a000031851190803080c54075140607441d014a40200950150424803000d001c844603034007240803240030301000080c80c0b003500011f0b40c4902c90803c04070010782000a1f0f2090350f003829001507800c10f4407490110204403d52044900b49441580d50700005a40d940 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 187703678 1250 187702428 187702451
    0x90310092102010614130b0a0b131d0711120301060f121505190f0305010902100503071704030509060d0b100513051003060519030210091203080612010e01 68
    0x308074291011540002c1103400e08040c8421584413410701c255105140c04200741c00d03020300740d0b0443c00b2107010250405590350b840e0a01d03503449801c09041b140319403580060004000703140c422600444840d2541700310071a201c0513000c441880901010f0642440360841000c83c3d40e0f03030440203500134a501e0750384400800c11000c00820b03582500c02505009820007083e12150094001d81d00700b02c450440740e050465000300405808828075511a0b41180754603140001800300641040500d42e01c00c4600501000340d46400b42d449001c10b680c0000050f24010120702e8540e0b01d403400c641c1181c060308241d8100703010303480080c40030b40c4058010180142c44a60400c200d0410001b10b4980c441241030131410281e80d10007a443c0c0051500c21544a00300000750715600c5406a03120b000078060117800d215070480c41c0401002c8c2c1070034501c022401070408210314050303030744180c0c40c4400b0f480642e01d040b50700c20341e0398804032291140600100ea010510951910742d00e0703401d200700d001c5038003180700205581e800b80c1c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 187704928 1250 187703678 187703723
    0xc0f0105070809120d110606040b1809010b06040303120b0a1a0304050102070605040f0507050a0b0f0f07050a08040807050402030f01090b1809010c1b0309120f020d03080a180c050609031009 83
    0x140609000700d082c014014900d80d944296082f000400900c0e400d51031362110700003801340407210611034219100240c04000e155000081d0002c9803030b80c0328180001d04400043c800400c920780318101e907010390f040b10500050150780095400a000d040003600b4940c40c0c1d01c418044030010f450403214820030310110410084144030200c004c110850300c01c0c00140c50a2000d0455208074040b1004200001601604a565000945803410740110031962101c11620300403a16074001d0180c550725200708400000c1514050080364413540b44003451a900b0391a040300c21015005252045600c0b203001c2c0c1440d00e204510448607413041c481c00b0b00118007002d05a6000c2e00032000d90180540c07031f010460761100440e400904520490303000740c10006030440d41d03042406803c1103030a00254410441012041403640c010103850040c00c0c50f120800c20000750010341500b10400d070400802d0700c1d1403090100000c0c60500c01508081c0d101605840592024a980b40b0859213412070807681202d0700003035a00101c003507 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 187706178 1250 187704928 187704931
    0x92a04060c060e280f0b0109051f050109150c060e0601090f0b0a0e040206040b07031701211b0b310e010b07021816020c0f0105070809120d1106 63
    0xa2001c3c4c0403103a0512110500a6554114010840d10b10702d114005c21140c1100403166540102280b07007296161290306c0043c00301235079100001254a106000080c001039400c100326032058664503101894510b00348075044c088810102440060b035003190204019000b601c10850492014141943c1090b00d00c000b101e5040b038001040320300d0001800520b407198590341040c1c03001e2000002e182e9459100182c03407803165403c09081e51304041a80360402d90080c4100b10724a1200300c9205050381c0b1000c0d913a039620244071a8052019040800e000032032420f09110444030150603012540981b0340c84400820303070003c110071020041c034110854210030008010f80d2171908401e141d07215907207460741511178100c06000e407804407600020860110358517503d520098820841d03100703400e4076006d400c51006014401c50b610241c01500030440582c0b500781801504200e0584800b07080122903203418885410440c0360075040b03904140016850f45080105102c6000d09950340e0009081d80443c05003030810 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 187707428 1250 187706178 187706201
    0xd0f0c030e0a0215160f03020102040e060d03120f0204050411040f05090c03160516050c0109060201050709170a020303070f03092c1306050c09011d092a04060c06 71
    0xc5488440140c0e80c0134410300301c00341c910f0241d9844010441140c0c031100540b000085c4214030903103802c020140c041d000380080343d0845485540f2035407408148821004140d90040c001601540d80e07151280d12603003c2e01c07002c0210030006040c25164404241114002c2094100c0880046070801101030310b00e6507440a000d080d10a051103050003420b0708101c8c0030140a002c0c3c00030042442410080c03103101940c1221003040d18400c4600c0d850700389662207100c1000c0140c00503441560201d0400e0050045501844442d5220309034580b401e95480c21419402c0c000c1030b0f8500801d02d034000507070780070009400d81074054001c40c6043c0f6031030b181c080c08030065035100086131714403043c80084202405421464403140c10220303140030b944540c409201a4450600103060515240c1840740c00c0d101c400280100000030b03243c1c01ca00902c0d1300d8240c6051480c2000b055030007200c6c0c80c0000d450501c01c10b840762401c800308032000080c1101900b011041d400035044a40044c3c1c48a60860a2296500402c5070070f46 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 187708678 1250 187707428 187707433
    0x914030102070c120f02041d0d110304060f0e060a0801060219030c060b12010e0106180203040b0103080a0504031403130b03090601090e0a0209131103120a030f020d0f0c030e 76
    0x305580d45070f001c044030f1842803241000b42c0100790000e000404e81e03614120b990080c41007005800d004421200c0f41c03803118200e4414440d440d068000140203181c06d114a42124008605091030400e04a132725151100b100320806c81e032018124800d8889501030042ea2185468145c0c07298100b0074020302c1c0c00c0e0500b0154403807058401220010907009500c690900d40c100202150440c14840421046a001031203d40198600740001d04090010b50080c015581e242e04800240e01d008440f8405130b01040c1d0700603080c0345a030801040022079080040030303c1c1c0c456003400340c00d140d070ba92180610b08180c541c643c03010f50000584c1012100c80d03400044054005a00c81c5421810710b048440d660b0700c014015041070540e1a036045800d1213003040891642c40d4010440707031041c9461101a001e1258031007044824100c52201c2c40018038010403032041003000300c1103150900d42c440e5800c4002e08001100244000c0d400c108a01a07587d0501a0000303103c0075400c0481e804c0c4403410024115661049805102d8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 187709928 1250 187708678 187708687
    0x121609030312020d1b020d02010c0e03030306120c060c0721150e010b030d03150e0708041e0b040503120f0c0406030207140105040c0306060b0f030f0406060b0a0914030102 75
    0x42d40000560703580e0480721100503100d001c0a80c5010060021040c075603c81002a00d100c00c0f00340e0700140006404109034024000d8100164003030f01d01d8070403004c04941c103420510000f0035508250701480826909031048440603200500414103940c0b012030a04526005034009000d00c1e41310351b40548100c0710110542c19101d019844440100d100f4008084469813602c00046201100b50481014480001c1c182c8400b084c580300d01400070140404281041045c986000503062080403445100f140241c4840300c3c155160754409900050451fa55005207001a1241000c50191000c940c416842900115030318280148094241d0400403c03201e01c4007000303020480c03030002d4001907808407035050a0160700c030101d518084c1d0701c0f019425001c1000758644410030090200080d140070803640138010030000c250300e401c0d06502c544a40c0c0c103800c500c0402080462055000d191006a01ca8010440011504d80396000a102135000c03851800001d0888042802448100d121500001c1c20890085241 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 187711178 1250 187709928 187709933
    0x70e090c0a030e0705061b0f0c0f010f0311030103060b010e03010608070501111509010501052106010b070203010b0301051801060603090506041407090e15090a0b0c030601090b12160903 81
    0x31846040c4034042015158400d140c0d1901c4100446000740800801031038031407008000086601d2840044c055071403142074a0440c082c800414802e43c12100605050407400342c030300044d10081c80c0200031004056503101c1c03101450b0700040107540614802c000200b211203a4030300041c9021a03250400344240d16280c0e04110080000904004a560a003030160b03600400c4c0d44843e00301690005100d00740204030040116040043d44030303a042e075004940b0809541c224218a0404500c102002c841990100e0014084841000003810300075200400114400309a071001c0f80c25600d0507581d086117a0709900298540e24400e0050340702415072807a08101007081d50b1501541c2d110098402307800b00004804908107041d05221001c090081200c061000d90751080c0115513038481d4840150013000b946010070202000130030a00c8880750044800c02d0252071300d00d001c929580c009024a4140401c03a01e00050aa00540c058142e071f0700205822042407808940000e051f000507030b6031004003c420b0700d09000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 187712428 1250 187711178 187711201
    0x40e1e040b0c0c0604060b01081e06060904060510030c03061a0702040c1116030203120412030e010e030a0804050a050d020618010c0f06090501060608010b09040207020d0204090b070e09 81
    0x900076081586010700d52681e03070059100e0311490560051a0043d50b0400c014402540c020310407802080e61101411b03503419003103030481003804801540b240c80c2c410110b69035250880c01380c12114802880003420541c2c0b000080c2102c41c15000c4100426120018401042d42510860008110042d0381c6154501203070003c00c8640f2540f41c009105a5842803c0c01ca1540302c2d41d000442c4901d6441150314180ca40c40400e070001d406031000724400d116041082c0002c403540300030746044440c00e918a040000300380d80c0c00c0c0c0c2c44c4000041141d04004070851a0140b03039500f0806007142d035000e00c0030075668034104418031004003115080780340909000010ba5005850b140b0480c0d2070085803044d4144441103210040b5681ca41c02000a84260f01d88580c1e0300500070300d98003d0300a58402c4008100d2941c0d0380c007081d01c0c01c1800744111529418280800115400c00780c0090044910003400340d1130b130103860750010303007101d0302c1500a5800c3e00709a003c0040c1ca6070001da82c0c58020408031090032151903c941c6001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 187713678 1250 187712428 187712431
    0x302100c1407080f130305030c010b060901090e2e030203010b06030609040b1005041119030606050f07060e0f07080d02010203060a1202061621090f03110109031205040e1e 75
    0x10b201c0c16000401c4503258604d03806940e1481302203542d0382d072041d030780e800c003140d49401503030450303056529101c0d20951520b49403003100e1008030103854400d500e51402040e04241040104107550a610b0301944002901e4150b4040641002040881941d5401c43c010b040c00c542c4428101c07406010204207010640c0d0380c90300d4035a4410fa1191402185a03204a102c00c0c1d00c2a0a5010750b4005040c40c4e100c030407620044000d01001c26500760740644441d440c0f54100e080e00c009204101c00b1507400c0100c192903003155402043c0c031601505022611110184000c0d2500384424000d07074858008a005009008045c0904010358042c1e100130350a50901070b0000755550028440c1002e00784500103001c0864451400f0342d4580500800341d01c031417182c54200b07088070702400c0c0343c65915075000303140d00c0051501401e082c009841602c06031903071243c11561884070714801c0c410120306020076120000001401c0c2e2403408803420003651141e40b82c510f403045080c1840d00160001128403d5051071150001e03061100c0d5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 187714928 1250 187713678 187713683
    0x20a032a080312070221041404150308130f03080703020601080313050f2205061c0302030d18350403030203070b04020609060c1c0206130b060118030302100c1407 71
    0x200d000d80c5620038264039054071840146c414460b030790500304200c90241c02900840341c050800a045031a040c0400085036139100c1442c640c494101014404103807004060081448140c4030080151b480c2c0c1d101c5c00c800c2e409a401140c0079440020104101981031040a00511b4064001c42c1000410b000c02c0403900d400f80130f550b00820080e50305080680d07641c2108016100c0f01c40500800e00c010342000000b0b42822150310b03008507414a0000036004944400718002a01a17029500f0484081e07a0040605242184501c511144020b907201040b03400b0080581c50012000751158015103600e000000c00801d50003041c10346007800300f080400c0e0040100c6000d2383d170000030b040307071a959880000d0450040c0340c80f0a0700b100020400c0c40440d10001219200241600800c20610030000e600301d94400007294042582c02c560000d1200007982000340701c2d00010141030108807494901c0f10064416a00d0f070003600103900902c1e006101c440c01d48a040085240c0b4501000001004001c510f03040c803500c0c400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 187716178 1250 187714928 187714957
    0x305100e0d0507150230091908131d0f04020105070b0912040b0c0c0604050f10030608010c1d010206010e160e03010e0304030302061014011b020a032a0803 68
    0x5241006030b4007640b104c1c42e404100f4110b45408008844e034551503c2014040134031441d6136041444d14a0110000703215010400080c50346c0040e09000842c20400d004040b59400001c0c01a2010a00c60852400185c440c03c1181c98180121400350700031a0400741120700100c400c0818440540d0f8402d080341d0159030003103c06102e64403180021032405249080e420948031002c034010501c44440d4000b481045015011501e0740c841e03840c20420684107602c106035000c485004070700d00b46e0800c040b80f01b2179640507040010711a65119446401d4450840c15040090001907180f074591605400801e0600720a00c0100a15030402c1c03403030400713008050803030b00e060494551403003000c0d07128580e0146d1040028000340411500d41d0000c0b5682d400602088015008800008400c41004012002103564881c03622031a240e400780155038507200c00209500c002200d82413400582c95910590004501c54500e42c0460600060862419446502400582c0425035010411a4800070a5503a5403520082 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 187717428 1250 187716178 187716187
    0x40b07020d11090103050c031b0f04090314300403020d03020c1608070306140c0f07060920090603030903100b0a081501140103092a050d050102040305100e0d05 70
    0x60000101400076082c0b540601e440c400401048000314590041000c142c00321391011700703920b40100d07284034103200c5540c005503183d0344110a441d10f9049030f0b045600a040a484100750380a420b24030b640b14110b4000610715094400980c40100102c101c0844110300e0494040c1c00e007554001e4a591340750b0000410103130085203010b005542400081843c10b50100380000450b41e41d500b240d204c5000d0310003a40e9962400410250400b00d90542c144203030b81c1d8150851401d0060040d248050704580010b50f07407156035001c2c81c40028420481a0704000201c3ca40d401c442c80748204200e80310000178105400398200b0f2081000039100025842c5141c00707010000f00b20000c5540c0810101c40d050b600c580010b125030a040c1c4404024041c2c1e240c10783d40c01c13032018100e8500da60010340c20388074280380080c00610090050009401a03452450b10454401c0e0032600b190380d20780024520740d8403034034150740c2c83c1d50000d800c00410400304000c00d080c400c1d0341c02c01d001c44c4120140305501c4c1c01c001071400092000004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 187718678 1250 187717428 187717433
    0x307120605100309050606010306030f080703020c040c05190f050d09171b06130b07050310090e0106051809031207021c08060315010311190f030602030714040b07020d 73
    0x10440d6024000280c092080b0307000380d54000300a09400003094409010343e601044440d440b80c005d070000d890704003200c100341e80ca687d6204121a4071004c000e90440c02544149140c1e40c1e514000c54100ca415503517941c3d204d401c0d2010307001c984040c115072103081c4800000d690142940103030590788075400002000607851114106080c3c400141c04d144d44001c0400140030b03400b00f400808a0300c00d07400c0d60b0220303a55a5030741190149400751a2034050603080c0840c0005030300500c01c0005550002c102c0c0300c1000e0640c2c1d01ea000000381d0740f210407041c1c426510744405000900b0008800420007520007035050603420001c0b8002d450344500c103940007007030415174000b07034441c2d008120764414100406003400221030722610052803030b00c1c10340e0850310174000c046100209021540c5010b050320b8102d0024603c00b030923002000701261980c902c440941400d20744c005213541c010525600150b00600c005641c0f80382108008010a9021041c104a00801e0006000d1b200c070410558005e19410b9624008150300c50 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 187719928 1250 187718678 187718681
    0x601030b06070b040602120702030408100203090118080a020d1404140d1a0a0e0c011706030a051c08060d1203050628031403040303020c130207050d02010b01090f0308030712 76
    0x554010b0064680f41080c0030401c40983c0c000c1000a10140210ba003544854008980b42e1140d80324014182d0b0080e0790340340741c10700f15900450300700d03100d0400040c500426410000200c1240e45003910f07807500204842c01d0058060020030051070051038040c5240000c401401003500450068610380c1c0000c010344401d503124100d0040115410a98a011303a1400154103242c482d130491380541290b040680c403d0000c3d074000b0b07512200d207038140c441290b000c0e0f445580d4000e50344021700c0070358140700c1c1c0394042011940138041e0000e410b84001401e030400701440c10203050103c001c0d007068000d50340108070a020503d82c1d600e81d0080115454041110b0302e0760400030f035422200030004048440c1841c8641c0c0755146914817103040300e20902c034605480000300d502c2603c9004030303c00600540c1000b400c0000601d03140c220b00880c00103110005040c04807544442d40340c00903c0e5101c60150f9503580043c2030640e0442001c00040c08441e1080c800340b405d40c0c0e0b0303000342400060181402d02548403102064030031035 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 187721178 1250 187719928 187719937
    0x50a06081906080a0c0501030c14030f0703060b0c0303060901080604020d20120c041103010f0b0d090804030f05060f010317030414060a06050405100605030105060c0124030302011a090601030b06 85
    0x1007000302c4210f130070782e0706182d00110701c14403070369000c20724040da0000c20303a01801c480c80f564001c003102d850460b03850010304107240d10700400001c101039580c0c601083c1c640b0004c02922402082d60020360b1a07151040600c84404010b0b00035070f51a80c0004100710042c0e07a9180808021a0b111400148508400080440c0400c410600542c03007034091225181202000520403001c84003150240032111440001c02000c0c0300c00e00540b0311201303000030f090203a040c00c8801000000300b0300c007001aa030034031525071040c680c00540044403050f0014194905012040001c9504840f04141c200007035491550f851a580c04405540d020100002c00010184001c0410203000c00d101201980d00c0c87c50300d13984420003481c0d00d000d4607128502e0900401d40300303010407002030152412610b80c01c0ca1a402c0204200842c0c00003c0d41e4400740d0340322070000e2184003510b200041d801c001c41030104003441c29494040d003510701c0356541859120b01601480782c60f5658007001900f10700d0070308001400d480d0000200b16907200713 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 187722428 1250 187721178 187721189
    0x61214090c21060a020a1d01120e0a0204060308030403020d08090c090c070b0106020f010c14040e1009090c06030b04180b0601120204081c020a030203091c0510050907050a06081906 79
    0x9094104041e139280d5070000c28416901d40c0e2401465051420900052000c05220a00080d860032149002d501d080e441010110426421250ba001440e130025059804580081783c00340740c0441800101034042148a17441540c0d407c3c03200061400b404a541e8031964411040d108000c09808103080341040b0048911030707070b00080b04104568503034001a40e02c040038844100c0300d40c68007014030000d903c03035103c000e8a0420081c1c1c02c0d02e070600d010703020504680040c012a426641d500000034405005216110199200382040c104040c60003502404460f00054402c0c012424030200500c1c04103d00e41c10041c3d07940c0644118001c1e100e04004036401100c001c802c411051000501040c5141c001500c080c0703003900c0d01001c0800041120040f82c0b105020040200540e10074401c070301e0645001d1913000004140480e0044051006450700740c940907090f400303101046da4030014031615070f50902c03c14001e0101500c04541c964035141d4028a4410024040000f40203400d016114110440d0800c800821 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 187723678 1250 187722428 187722433
    0x3150e0408090d1b0e0105030705060301090b0f0d0f02090a0203190e0f010c021501090c08010605030603030f0a030f0e01020a0f140d150603050f0105010e0d06060f061214090c21 78
    0x310180130025424280100441c0b0501c01c0000921484d0008880c01502d0000c2c12142c15030b440d00800001400082c0011a0311140114540b4030503150654031024440c0601800300e1010014010f0040f02d01d006065105840d004008221030b40311500701c05901401d20050010390181c24200c030900348180301342c601006500b000d030040001c542c00514402070f0b0070040d40080180e6a20254401100c54a01c0f0f02c4010074071a5004000190042002d1036014101030103a1f03240c400c0304044100b0760b0780302d00c1c0003c2c0860350301c1100c11294012407183d035003c0c070880170086181109a210150801c10342890304170400c208240c500308195050015145400700090301807140721803801006d0003219080c010140000d16240c0002e41c02d84200300c2182c100c480c1030712110798080801051011002e8002c40503500540c5448001803411842085040101980c0d03945104100c48164440e00341e803500f40f030094544d800e00b130038000203080c04284400704210848861000c400c0103007510041c0c150b1034203d64400d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 187724928 1250 187723678 187723703
    0x103080f0a090b160501050606030702071a13030c0e0a0b090c070f02040f05040212060420120706020102130f0e07050c070b0705031206040c08070305100e100603150e0408090d 77
    0x202011354159046100b40024420f0360b9405040c001640011180000181d00c1803808000d424181180c5039600081f51640500c1d05080226841501040d42d10403900080c1070360040205814201c034054011008801c103001d1071034410000b0b0041c1c0806040c200d000c54000426204010613200c3d11400503034094401e102c94001c01c031040c40180b02c21201030b8001d099504454100c40c030045500307441141e006440c0c0001c1042024003907158400c001007160400308070742c2c0510910104102c404010a03866001583c1e40c50f41540c2c0301a656103580c04220b507206000030030701c0342290b0215210360001480c6030064a41d010310450034a130400300da0110b058a0000503410007440404030003000d20890b08086c5080765195032003070000300c0d1843c60005002604100200b11100c1c880e070026030700403065001d0054034070380310080c602e003164051301d11a102e15400b2204001c16505401290342d154609010060a2858048070f52412103004000808100c000070710350f102070b42c50030030124580c0e07004503d44102 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 187726178 1250 187724928 187724947
    0xd0f051c06080c06070c0311180a1e060605090613030f06090317011409040809041404060e070501020a14031e0310050312070605130b13030f080103080f0a090b 70
    0x201814042d0300c03814050146039a0042c00c0041c100c030040d50b07204051240d45490b50b00c489440e20650810346520080700780d1000103400910150900646031600002030303401c500480758075440f001d800304820080c00d00c401004080c2d080350644059a40c16a09544e80700c1c84039184800d003100580004180341c00c1002c4400c180250b580c81420414402d4640307400e902808107001032804400d1103140e42203071500301c86801c10b051000c0401c0d0480d205803229070824980e280098144d0b00140d019200c40c035503d0b81008280f00540c0503071101a4103c2d07002d8540c25042000003503c2c1d001c02d00e0003900b1072a41c5070ba014420042002200d51003401d0207044002c00f03038043d4070940c056000782c91218001c9094440400c0e00d18000c6001c969040301081903902e042c0043e603a21028000080a501101c030700500c01c0404220044100c4c0d100f85422042c0e1848a000c034580a84010740304803521080043c1c41005000041c0c0c41c03021070345520041c10019403585680102251104640d400c00c04800c070011445024 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 187727428 1250 187726178 187726181
    0x21005040213091b0807050a050d030c08030130020307270c030902010e040b0603070e12010236030604080c0c032505220c02070b0307080105040501050306090d0f051c 73
    0x30f404c01142030703610030240c2e82d521031965010203010707403507010242d80c4081105180c0300111a180324400d0034090f9181c081520b0344000358100f603010489100402e9880c0800045446440c828070302c0c80d00010303030b014003150007080da16680c038062243c84e141c1e003034090740040b0f21007003603c0b55102101c1021300030f021359804020702070314980c0d8003240400c1d0907101501852400b40500030340440c01504a50440d40c910b40101d80d120055401079030094490229203c41e188280001c2c00c0887e225034401c0e51007285100e02c0881700c54603601c51201105100c2c1c0d500081d40e00440c01c10740042c6c10410080c1c8031580702e0480350030072200d640000e43c07512950700301c500c0003080740010f24070800d03240441c001c569590328240800304c550901018660004803001020f180b550fa800a01208070600c12110040d8689805a4803548140c0e011800318081e9001000340d0318050040c80c1c0540019005400c15061004a982e40c65680c0421034007440743c58400801002e00c01d8042d02d1041c04059940780345888590108030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 187728678 1250 187727428 187727453
    0x3032e1d06011106070f05040f031a10030c06050a1e0e04230613060e040b0f06060c152e03210210050901061a0901110d02100504021309 60
    0x40110368000103095580200d55841003100c4440203894255a41582100c5140640c440201803101c140004104010403000c800003441c400c0317482034030303020000f0301e403110102004040701440b0848002c144001003008035901c00f00c0310036003881a154440300106a5860000c544282c0b002c10600307112403881613200400c4022150160b500b0040c4812070490310b1890164072a840c002e1041c1c0074003041903406d140c0510340e00558103403000100952500c01d582c03c080c3c400c1d40c003543c0b0011600203202040281c010210380003401150482d150040703801c191501d07459540044250f141c002800148824450000c0d40c00202c0045180002000c0030321050301c0a6105000039203581342100c100e14001c2c80c1d642c48020305490150000c000e200c186000d0400034020042c5010b50954071504c001641514803103a200d4802100481592103180484c0010201d50b0103c501c0c540c0c65000b0840641c0c3d250b00801c421049185022000c2584d0b030f41c5002003505c002c81c803c031305c07020f1514240b0800140035a11a000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 187729928 1250 187728678 187728719
    0xe0d0303020d0c180b09060c031204030e010504050d0209040510020a26070c0807150606030b010e09100b07020a0305060a0203040b0708090304090b04091713090e03032e 74
    0x20030160303a4009044076070700d00c4c0481c00c803080400355505002103031104004e04007909000341800d1400c6400c1070a2810758020715003210b0410304800500c800c06d50041c4d40381200361070030b2910340d060620300400203161f46102400a801103118034007050500034140540c50300b0300c8400070300b5036a803510140001c19041d940c80080b1821310104a8482c0e0258615020500403180d41c1d43e5000d00100c40c0d00d410740c0903031004030200c4204141d001320404102d03640c040c50004001075180021a803a02e40c00240051043c003a01501c07030f807041002c110708641829042c80c00c0d60034a07095540c64640b1440030030820b11b09500068510312030101000a2000310390011413181d40701c0c980000e110789603804140d130b4202c2c0590f4a40314540043c0402e1082508543c02000b10350002000403031210306a07202d100b1850051f4808041c208400241c4c1658407502a5015005003610a1b003004900d80c1950315545030300015242451482d00c190302e102c4003181840303405d0922002401440407013595034291040f9102c20700f40c2d8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 187731178 1250 187729928 187729931
    0x109020d080307140f090f06070b090709050109151401020307170304061d0a03120908190e0a050303070609050703080c01090203010f0b0d0605040c12060e07080109080a0806010e0d0303020d 83
    0x91320308482528040d02d00c504900307100d5600780b8040c3c1041001c41c0b0742c6480d1043c0c2203981884400046420825800e0144001070b024140d01c0b418100072500b5540140c0103048030038103150041064250f8000210101d0313461286007410864500c00403800c61049040c040d00c203808403196030611305079030001503000303e1083c00100007070010315804021170710881c40300d10040e4101402e40c0000c00c3c0a220700c100d600c0900100092484455615001c507904900c60102c1402844000e490205401034603842d1401c50860780c1800c4e05180100080d80c80c4074a50000341040d031140300400410104024440166a00c003400c85c5d00d55850b9031580e0300905501d60305038440d40c00d042c01c030f4481c0f00040c0314042e4600e0024000c4c03038404c5820340341c8a01070300340a00304503145500030300c0002e041500900b4140c0b01074440c81d1f000c5a078407a50407640349405090b4010302c191764540800400000e4005089510020403401c1c440501d540322030060703420b6078004a1281d084642d8400040030541c0c103074014000070904400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 187732428 1250 187731178 187731197
    0x21060b040f170304350607020c0f032a0301091505061005030609070c140f0601080c0603010608070306030f14061509010b090d0c06030c021002031015020109020d080307 74
    0x101e0340712030300303900c034a10702d10f60800c120920540340c4004524240c000c02511401c020156414a54000961103201c1750003508130006111340e081e814480c00700c0300c0c4001c443c5c0c0028043d2038030009440b04030710494045100d02c01c801018003c2c0214200007007168008000700503024460400c681c10401e0321201031100c07440c2900013800d615294002c1d907440940c83e66240d06507901e20050041c2114003030528000d01911078a07402c00200c0c84c0085424001d02200500003400500454510701003040c1c0046900781c02441c01441e03192606016a03045480030f1401e06000c0d120800280c00414040c0c1025140201c0c800c07000c01031140c003618400200000c40c1c1180e40079a140142d049181c0550b201c0640c0c0702d00340d07000410100d0594805040200d900505154002c03c15580f0800b040c0741c0383c0d210f4408030752140e6403034600c42d8050050320590000c5a02c01d40c40c40c03900c150b0325134208040380150b1000d80d00e0b1844941070140300354001084a64068201ca400001600b0401001d80080f02c410001420721f04 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 187733678 1250 187732428 187732439
    0x1c0210020c030301060309020607020409031d0108041104020304032006100b09030a060c1b0609060b100c12051b280c0909030e0d03030b01030515030a0321060b040f 72
    0xc00c440741c89444801450559082c0385048024200310034050ba0301c0f5905000b003e0141c0daa500c64615039503c030b034461442103000300041a400d0b030b00c00d8025505001200c0d0070013011888803d03400306000c2084070016503070794441c502510b06040242c00d40c1c0c040a00b08010107000d0200041160181c040b580c11041c1c5143d80b144e04c5007280c81039085041d01508880c02c0880011344075044207010810904004400030f075070019252590104036030030f40301c00d40c444042c001402400c0c8030b074008880c020344024400e1143d2402c0500700c80154400100f4141d80c1c034048182061044003541c01034800040681660302c107052400e680c0e2407911200145084102080701215020521130104640c2e01101100bc5035141000302802072500b40c00a4091100d000944581c61340c0d0001400c03000707442520300181c03c4907007400040859100502c0704c0900100c0d0658000e25940005548400da50326140c8400281041102441d0001140500c6440103003070000211300540b010010303109444880a50503070055541 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 187734928 1250 187733678 187733681
    0x60708040303031515022d0a0515151f03110304060203040c05030f100e1c0c0b0703051e151c15140c03070513031a060a060f0e01020f1c0210 62
    0x17003001e080075a018002c64602c202c3c45038103c1d40f80e441000040013280c014005d07480d003041c540340c000b00c681d90040400c9034400483d4294107600003201c15a150305001c94040803456804d040c10341c0c07032034400001c3d4000791868403e070000c00020900c85103050310703801c0510300300019405c1507034111501c1144500200e2030382000511002d44803040750046c410440f100310544000d042419005d010303406000004014440600c00409440f000c540e0344903410320650401500455014054500b014100ba051043c5894001c826100d034a031b4000858055807a14594800c110034030303800f11034120117407031340041800d00d0007000180b0843c0500741394685410034249110407940207903650140c072411200801e0203281c00b06c014592141b11781c100207103040482c010700c2007201e08503401181c40322040f207200741820341035202c8141c0142040d9180500c4600b003a0015003100012a041d6040007081003040816030b10070444651034810a0042e641203041c1c810340490720503541c04110300980303e00d04503005000e109 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 187736178 1250 187734928 187734959
    0x60409020105090f191203020601080102130504020918010306061503050603030a08040302030f0d022a0c090606120901020a022808070606030b09010b1c0803040209060607080403030315 81
    0x507902c203498580d089042043c5111680b00b080d80203c801d08646045458280c98000038026524560b03001240502e0024641081600a603100d80d0040c800c03c0c80240901c0d01400a5039001c1701c000d81c44281550208041000d203c0c0404102140500000705122660340301405440f03400e104c0d4883e0301100c00b81a4181e4400f47d0302e140d09944200142800c04d0303c101070541e0800d2203441683d241c101202c04006180d000103076000549940064204c3d0500102190407951011a102c400500e00c480c64005031250180707003c0e40e004405480006003e0b6032190300300c918100c1540381c2e81521742400304000e4003d400104c9641c2c0544500c07010940c007070440c15102c81c0106d480060003803030301c1c0da6035a400340650044641102c040703440d8000030000a5008584c00c0c8a10440c20001507400048810010364180e141041c00781500c40c0724000021640182c1126803107034060318402d049803950004244030307100f03040c80030f8020345010030044201545908081041110f8909031034030303a5210000808086c40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 187737428 1250 187736178 187736183
    0xa11220e010812030c03040c0e04060501091a09040b09010b1801050907030b060a0c15090f1a310804060203040608060906130504020307081b090901143417060409 71
    0x1307200141010041e0001141e000e0b219100400381301d07039945128070380c5407020b80d011210152070b4001440322000c0ca10507490f0408461001074804411540032504010b405480501503000d40f400250980b20300750000302c1000300103131043c1c11150f4010b8442c0360039034ac00c0c01744920884499003c101100d20038007442141c030900400d100c0c90405486003e444c1c20303400c82800c0740e1010424200310104145403041c0302c0c00394020780c8a0780030600c19260004030f2210111100417410910003d102c0c1c48400344501740c50f002500b0000203141d11580204086505000303100030101040010089440c030340c040b002d00300b1100e581d214665503440e16010400c2c83d140c1101c81d1500540b40c81c4080c401001c05400440e0028009030507101500d8803814040d0402d4003821071805000d050140c429107600b001e0030520341c0104440e000304010702c0100160014000c01034049003110481070120b02070a07002090841c9000354032000c0400c6e2120f0384401502414074040300c403045051640c0080c0b10382c10240201200701d80e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 187738678 1250 187737428 187737463
    0x150c0309070e0709050904082104080313110306010b0a1803020f010c031205010b0a0e09040b06190e09070f060e01090306150504050a1409150a11220e0108 68
    0x3800d080100b400014020401c0d0f08000b800d16000a040d03c843c9440c5000b6401072201c281c0c0c43c0c40b03440d088a461030484c859012021003000030403020907105820340e50865419100c0c200740040a041032079043d58030114550b0706000d45000007c09880e03810051904020907103a0300589030203280f160198130128800650048400c2d000f00c440c96104050b1003040a209080c03907410200146400d82c1164426001004180d000061207450250400004114600c0c102c40c10901d03480c0a0380c42d4410062f02500940c000c662840d40d0b154192100c00400d030141c040d03803890f400189030a81445907204940c0c441e20205030140180032a42a10981107a40100d106071154046a86141d5070a4004e2001201500c40c0c20a108404540c80e52103018031406840e1010300420300070482e4044000b107080280450625030b01018018a0f003142401c403071035000c1d21503040000c400f0441d450130340c660b1003003010f00c46400c3c2024a9202150743e8400300e4409483c0b45806030300300740c2e88968030309940301e044069203918030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 187739928 1250 187738678 187738693
    0xf030103020906011e0513180c03110f0909040501090f0b0601080c070803060909190614090105070906080702102d110906070804030615080105070201020301031e03140309150c0309 79
    0x20300400040080c821542440081f9694490b0603c0b400044415011030454a511611705040c2d8940540050312068000d140d1405910380a005507610851a01c24000c0d48094002000c1c41400c2d800462920707042450401550b48518200380649001c0301d01c0c50200c0c04550104000050980a07100c2c40e551110300c0c6031446d00c5042c01c2041c8040c1c020301c600b100c0d10603a215480e6400c0f40350100010503100f04008980741c440032070984811000100a50f4050389440304015215501c4a0b00d201203030003504001440d41c80d5210203d003400070009000d00c040b4105080d01e4140d40c5101050b1810b844c4000c2503100240ca2441c2281c15030f00c0e0f000440d403c0c40300c1031004c0c0f0018039003c1c2c02858940d2080d240c080c9015580ea032881e0645120000b13080000e09031a00403c0b41c02c1d428010b0507031042c0c0503c0214559810341c0e07280705480c00200980103980343c150b81c1040816004980c992988100502034030748a20f000303d089641c500744c1c0800d12421056140c00b145040d54004207032405829484c2c040d0141 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 187741178 1250 187739928 187739987
    0x3060e010515010e13020a0905030705060c2d030a0801030524060f04090c0b030601020f010507090b0306040f1e1a03060c0703051308011505060304020f1e060f03010302090601 77
    0x70380c011051340e1688000d4610b2079844004984c030042280c0307005a10b844968620700000c150404a0a0344a580030b03240811250120700f1011031940510709901c60030319002d40e04902da0022030041481940503601c000100c40b0031050304020210b04030703442042283c4400e00c5a9a41c501555500f607960080c0f4041c00300406c0c041c0c580180049038007400507000003250b24441e00d64420000c10355020780007000002003401720707559040c0030907400705561000074020b5060100c80200540038610a122280b280440480c00c5551a41c101030032060408105004801c05500310583c1da8184400c03903030400b4903105007003031340d4884a1020030000302c000713018102139911503140f100668010380003201008020888101e80e42600d01380c0c180500316580000410481060040c1350800c1c0390b8205d40e00c64282401007200603914500412038441056403240100440322070342d03004405a840240358031a0010070a90b014031890400f0350f040ba4000c84404150740c0307401d001074490042c0000c807070b814001400b512402 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 187742428 1250 187741178 187741187
    0x3030509041509050f010609030b150f0907030501140d05070e07090e01031a0703020c1c030b040f050a0b01030c02030f0c07030b0a09120e010507020d020414040b0103060e01051501 79
    0x3403200030300041280414840709854241076070700110307419540c0f03405000c0c1c00b0403203c1c44035003d8602420b15048640c1551100d82e4140d8004188d09100d00601510410940320034002103440b41010380031607582d0806d40b2005d006060240543c09850401c0c9c40d0003210b0380782900340c000400781c104002c0e1000c5030030610b41e592200c0d03000300035100340034811100044070440c0e41102d5000710300400311840d5068007109041d05a5502403d003e040500521601101a03004100c924032000c070f0460110004035010b01c10340152042d011019800340c9840517001c03092400381c00c4144203e00b212010000c0389030706d000540485950550501c0180e02c2070008118040c14040200448145201190b0905079a9134801000c0d140880302d810302c41d5140d00c08034081100d8036a903c84500b855041454289150800091843c001c414006e88100603c60244040d916254014201c0c25440106c2500c2d5240500303000030220707000c0c403045803406c2c6002c200302e0722001e06208050140242180c42c1750b145480d0001103c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 187743678 1250 187742428 187742437
    0xf0102090d0b1008030f03011707060e09070c05010f020c0c060a0f050c0309040c1706010c050607050d060e040c030219051c030509030a060501050f010513061103040f032118030305 79
    0x43c000d011000ca10341c2001c1000c0c00e01200c050204e6656076041c2003c8110001ca1100e041c03001e503200e41014040250000e90b1007030f0450069038501d4640d601c03c00304072030b60314114401510325440d20b502c040c2001080e070020003198217041b088411900c41c1400384001441040c00d1200040c80d00302e6440000c620550081c82d000140d50205c134184000752000604a808842d500d0010454400ea9106a903003801c0d80d07552b00080c03d0030807090800071a150b1a486000040c010810040e00042d210408481c5910035000303401807a101c1d901e50300c0c10b4a8a6545150a404140d2068440d85140805400c0401805064803000742c03462200034a0344880810f4410820b5080b020f00030240914101c41c0c070f040005443c038601817032010032254580424041c511407150319042c1088001c000a1030b004401506500403205245080d48010700150700d100d08501a540000c0d040c51405400001402810201340080d5280b10581c801484566a001d82d1900d00c1c0503424082e442d072a080403c007080c014005071 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 187744928 1250 187743678 187743691
    0x70804050a061506030e03032503020c0109080d0516140a0509060307030501090605060f0315010e0603130c0e070e01030b061b100b0f0913080d0606020606030f0102090d0b 75
    0x48928440981c2c0e101d081d2032158001e0916400301490030020184d050207894120314914014614605000e61025141d62000e5072640749640c85450a224903880f0740c0c112540c0e519554000c003c1424146010446c95012610160505c0d0802002c0303004045141405000c00015484216055209c00c55003a129003006d106d00701401004e00030000305484a01c015031184511381d900041940c14030031042e0031101142c11140c0500000d0084001c00b00a0608407a08200001c04100c2c0603003010340102e41c03400d4807800454020402006028407402d05100e10b07a8024428500c04410320f441e200e00380c218039801c542e036000064448800c0e2034654000d61100849607005000b00749480d0202050700c001d0000080b41441d541e004010071098426140300320f00318024200c03031124580603e40006006200d0140c00444440340600040042003440b508441140102d0340090010035550a8085d4a03090b04580460085c00f581d8070014881c5810320071100741100007801c40e821902280c440000d103482c010301a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 187746178 1250 187744928 187744933
    0x50906042405010e100905090a1e0210021e0c3f1e01020a17090c18040501050f010303050f0a03020405040e0105010f06030b030c0432100b1207080405 66
    0x940007802024007825001e400f092104465500340711001c641c90b928240c5c0b1010080345040188000003001003103a1481d590480c07902c10140c4146926146412001d87c402544017420548409017030744c021603c0e000c503004000c0381d409407007400075140f91524084071040d40e111003040d031407107565140b442558103401d0640444c05941ca0501c1d403035281d6001601100c9076030354001c03a1140d10740f01c040d48043d1000d03882d0300000d6090441103403000d04550003078000c0600d407a0510000401c01c0c00c04201c0c144000600801d000007a42107052000802001905c0c1079819508000003e10111401540d5030304981e415518540781407510b6100c0d0302a50401c1414a0800d902000001200c0d07030b81780106c250506420000140d607525000320a003c004103940040141030500c00d6502e019a80860480c8042e03500361804200191000f04d07404669460400c19503d41c0480c4041170724010f911401e26100e402c0f01e8040c0e121203a1138002d0010075015000409054080c60800500828882d420107074000384039104 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 187747428 1250 187746178 187746233
    0x302010b0307060221040b0406030e030f0d05010e0c03070e19050a0b0a0e10050403020409080f030901050406050601020c090103060e1603050607020c0f030c1e040608100b0405090604 80
    0x70b0030004241c0c0840300607030118041c10b20310402d8000c040381d1450300724001450f00d0f20744107051817903001d0f41c13048501380b50b03a8800d11030a000c4184119000303081c907601c0c00c60383d42541c8160031004010030b0140708032106030003000031503050480c1c0131603000d0000781d02c07030265080040007046200e10b0040080008080703414070000c0c480d220000c0c0076014008400719140c0b600e003508001003115443c00d0798148a070b40c2060307403001c4594114046409607901903401250702212418900980e21a50201d68400d510000030403040343c6e010b43c0400e025922a0100b070000d0303190745004a070b44003100b4484592001e041c100420020306c10364401e8400185510079034005070200c05c2500c9807445582e00640305500141c00b00029603a040c00242081101200e501003992800b81c00700382d5612405259501030400d8801070f9143c4021044c0340103100c08028428012240c03144d0b03480341c07102c041d50058003420741007200e449454a03007801507911800c403040091406a41c6c07501c84581c890701948012040c841081c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 187748678 1250 187747428 187747451
    0x101b0c05100201020c1c0c03180e180d030209060f070c0510120e070620120c0f060618070f0509090103030f0807110712050712051513020102100504030201 68
    0x300c4040c0804035400060705c0d8a200c00e4031508208461040d03e20342c2030000251380d131325a013100c04960010380501c2e01c1155a6901c50200c0080907860b040140340c003003100104400d1480b03044007481d071700c1e4039002910602d20a10000740c0680c0900340e2130560202c004e1194a8160001c14003074006540585042c501c4143c0d0344000c6a400070181a1000000304000911a05620340303010f044600081540240495844c041000304480c81d0500142078844400c5000e00d451601040340c12490190f04492a9a072a84944001d030382e5403000b0301c4803207a4080c0c0c50004159103060446c0d08401c0b00e9012052402d03039540003037210580448502c507001d21805001100ea40d403034078100d1070b002e94030030b07241c000c21100c02e040c001e840c410b0300805075820060141a01a034041010586000311100e0b10189820a4814600281403d00076002041c811600b0100c000a10400180e007880404003079112003485d498884800480a82c1004c029000d60311442c40014034032450b50029a1040c0179100008105c00040e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 187749928 1250 187748678 187748689
    0x6050301140d0c29070305120901091407060216150e03120f07030e060901230412110114251502030906011404061412120c030301090b101b0c05 63
    0x80c2c004607a096140c3c1e01d0302c11314003910328480c43c401003a000824141980c5603030007000751145c80545c1d0602040c050115007255802d4212160481d4484101c044080b003843e0101c1e91004240b0901005103d00c60264012091507600c180641d80c030f5265143c0ca0b150030750340546032290500c80f900d07090f00c1040c8050b0001c0c0400f0001d0040401820790190b52003c050038028040e1880891951261408012000e242c0e038001400e09a40409180b103c20a44000348003e00540910303403117084040c044180101c100112414105d0420b5401d0b218036142d480d032a1400401c2c1c1c095025462002c0d0064a0700764560441c1c900c20300f644910841032400301700c4442c01c1813410307a001902c038088070b9484100180301102c8030700b484440d0000d080d102080014034241c03800c4403070402c502c2c03014001c40d00302d8158080c0c00024070007034a56040c6000003d0760f03410485281613403030784248200300340d82d8500351030100306103031403242030005503200d6540e181da4080c4144030102c50314022204030b8581e60000000111902c40 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 187751178 1250 187749928 187749953
    0xc030403050109030f09050108390405180402131107020d0515010506130b031e0106091503050c0318010f050106020705040e0f0303160315030c03150606050301140d 72
    0x3074000840c500309245005000d80c0301c2d0450701402c0c4000c110007441166404402190f0203c0820381c040c1000a040160103914003900030b280030050980d80e007464070104c0c050018800c03201d0558070b0b0305141003051030361417200300c090302c0c000d40c021005010343c455921982c000302c2044c0820320f007a07450516568001165921005000c07606030304031100094aa00d0a029210300404090b40c11501d440c0200382007040c1b140d100d018060b84008080003003404e0003001d204400807008414400806541c40d40d002501e4600d0922a400242d40d0032403403010700c02e1290150314041e40c60050400c1c00c603142c4558054441041c0300b0481c101c1c0d961600310320825100c1e03004c7d543c0240381c5034010304203181c208020b000130b0302d82c3d816000d81943d10640800313480c1f050000449901841c08190a442801c0e0700000b10040c0c100c00141c0f000c08000c01d80c001c800c2c8506649a4001c50b8400c2c000e0051105d1414208025181c0301d124030004164140300412115501b054540c2922500600b5183c14940d00d036038400c5050f51 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 187752428 1250 187751178 187751183
    0x90506120103060b03010624120203010b070b0112020607171c0501050109060c0c05090601090e07051b010506090f06010908150414030f030a090c0503010f0b10090311040203040302030c030403 84
    0x411000400900583c0e12501c098072905a0007409094180362124901500048200c518040d640000b00482d03407040c42c030800c22400030481955071b941c0d2026040000d4104641c26550910b8680c000210040108200c0240d2a030183c250f034201180398441c3e50130300112858100507580c08025400d55101a5059001c0c030100c5001c00003074079410003000512252141d0081e000740134005180b4000308004a07022011214100c03161a0b65541d490012a5400401d0b803000f0101414602031111040d007000c0603240464030803104503500050000041c1c04d8440a075906a04400110081440750000c032008a80c4044181015640d9a9a40a40d1441c14040c00d07030380d000c0c000e04101840100441040f031043e400d00d41c0c0008501b000e4681d000e0254510010740314029250781e80c2008400c00c00c072000c003800141001402000500490610000a00003003000c0921807051100c003c001c1d107014403c0c403415a078001d601c02c444100e4150501009500142c02a825803205100d0ba20750031b44100014000b461 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 187753678 1250 187752428 187752457
    0x305010903021e0f0a060209061603021510030f15021605071d0708010e06040b0d080703140c0307060b0d170d0c050406080a02070609050322230d03090506 68
    0x450403c0c01c205100540110050303d6000b801900508000008070001c070980c000000503543c2c10f11000166441c400e55008200d0707880040e500c5402d15401185040f0000c0390105002d0b20741d69001212035010b91b69000080c59090320380303a400302144105412200700e240440d001850085581d40c231640c445c87d03000084881742c9c0a07a005000009024641c0c85010226000c0e44000e400c0c19040500b16000c14008c10b1507001301000020a21f64664200003107100c006480c0300504961402e0501ca0303540400026404200e91120481100c4291811a11011401360141d07080440d10f07a504006000d41e190200d91050b10b00100c0d002190050601c140864180b458481c1d50701885c0764200165100707070307400c0c00078810144010000980c00240c3e403a404468001c005a0f5100c10f45084002040580d00c040c01c944004116041d10b10b4000303044400c211070420080c3d0b1441c0d81c0e40030b8088000011600300e240e0303080c0d043c0c040e40203003848030302c541d2aa4401d00f0040708040e200c4001c00c2090304101f0303803140941c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 187754928 1250 187753678 187753693
    0x80610030615030c180e010905031209100c030515240703140a0201050402031b090402010c3e0411180a090e060610020609070501050d0209061315020307030e0f01030204030501090302 80
    0x704c41440f07101d90606c0b10030000e200b40205610390355107a01070b4100e2900c03003104440008251600034000501e4031211003404000c060002d580c0103000700402c0301c011264001c00e80c60464a440c4c2101d01c1c450302000481c60007e40710290380360335a10381040c8801c40074802c0842285105040c45d20182c8103a1903e40d000162600d402d00405240801f110710540a81c9500000e0349025183d1a00680d8483e4080c241020803621a04c4d00500b03522200c0c59910040b2519100004000044c030b81108943c590100c002100252000421013210030301c1600c03484c20803040200030701000311100080c01c0300030010300381c2e488195074030101c205403403690080240541025040016900e420618003010b00042d20040000346000081d04d0740e19000d6005450520001080f042e00318003481e0102c410b0b001300900b480d91100c120f401074018818440c0075500840c1072441d03042510314400020b8491481d00f541c1d60702d601100d80c2c0244042440744480d0f5a041540800c800701c0441d409000303c5013001c0c865401001307103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 187756178 1250 187754928 187754969
    0x14090714040f23090103052a0402160201081608150d08030901020a03060e06010203030402010c05031b03040906061e03020913050118110915090a050904030206070801080610030615030c 81
    0x15402c401c07030524440c0c1002001400490710010f582d5441c068810107a4110540002d130508c02984030b44000782e4464000981c01c001c400d04186100c84841c400c1e00c0742200b80d11a8081a00584015030487c0005503c2d84006110100e080c01130484032000903042f00014049520fa0070390a030f01c2124141581d0b90000b40c001c4c140c0b0780c103110f008018018111800001d0900d140002e40328800940041d0400032811404024807106004507400020503201c00c0c410010585445031302c07034100d813080d003102500d030107800a44240903201014603020140201c016809106201b980250050540701e034000885400b00c0041103030300d02c1564040c02e0001201110a03c0c44030682058605c84095210601014062480c0c5900d6440204c2d0300844070901503910b40c60350001040c1400f925501840d441040041403000341034000c03c8840c05140c0559800da0700b0303a01d40318881d540704016181c1044c609220801000840c03143d50110141a0f8840c280c8001c031a901e44911101440d5900144180d5540d2402d0958 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 187757428 1250 187756178 187756229
    0xe19050a0806090d051306050d060906080a021e090403050304030908030d05090118031d0301020f030f060a090903080c0307030b0a180e1501151e0906030614090714040f 74
    0x4c010042c03412628048000315280003243c10703840340701c0c180400800ca6899048c210340001001d0701c9010420014159540f030030903030b200842c240a1340110b06610300c1841103030031001250f00ca0600540341808903140c2d80c3d4229410b030701c024401e41c2002005140410107a00078001082c0c00c541283c8040740b0340c1404961242121540503062200090303001078403000a81110980039607641d940107103100c841a01c000b181c0607204034207110b00c10482c004100100d0b01c600104035405103605448100344039881b00b94090484407258070140102d0441800075880c1c8100f0001185c0c090654580442c480c8060000b103549155650000c1c89036103104032810001808510800c10b0032407581005005003041615a142d10710418069580d14118039103000380d165000c2c3e28a0780800c42003c1c00d8641c41c4030f40000082c111030641c0200780000b4201003001400400007001d00c42444030082540716103803a810000d40d050000a0f95022283e4003c0c0400a06140b40e107100400410822008900a9600241404 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 187758678 1250 187757428 187757443
    0x110105070f050d080c0a0206060103180506160305090703150c0e032b1b02040902031c05070501111801120e0d0302040305060a0504080d0203100f090902010f050a0e19050a080609 78
    0x1816170003408074400f015800207185822903400e00b4001541c0100340380004015003a001d01400750320500041c0889180803407401008000e242d41d00f04190340759403080075182d810700d00c4060000c041c85440340e403003000180d00001840149003080c0710400c00c8400401d0a0525000158038054011800480348603414005520301014070b1401407007144085040c2a0340d0040407202038004c5680e2800c005c03c6481c2000480103091484403001041c0407203070030043c40395110721000c507040e501341448810301901041c16500c1250034a081d000d102e41851004688085020710305401c1c0700d40300c411100014105200c0640941c0e461b95016076600d0960030891f243c02ca01400640d400d0f440d041c100004144610162200c980040d507016a0329220300e03408840c1d00130540c00c44084804c8456000402c448254080e00e0450300c00e8950b80d000d80f0303034034000f96003502402d000c1401103040c0000c02d08083c904500000521800c004d010b2860544990120701c0c0540c10b50010850382d84181c0a0000803d020001207 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 187759928 1250 187758678 187758691
    0x10203060f03302802010c0804030c020607020301090c08151305121305210c04050c0d0908070b0a020306090f060d301d010302040e0103110105070f050d08 68
    0x40000e403a4a000c0103801100704080f0060300160b1070210450542e00ba02100c00304c9803200e140340c44c0d00c001d83c604904038140c041c103010050340c42c040d2100c4055004042442c45690141c413428054603654080c03008551110304220b030b00d55030b0385a01600045507182d081d009412844020300164448a024004450300901005481c8100d0010000065030000f404d10540c0d081d0700c00b42c2c1d1a500c5010a01200d410a0b07048540d200030102a2480f0141ca640500d50402403810b08842c09042113005000490303d05451440ca2880b0070420b00403e024030f80c208003c0341d4800c0200754508205511000b40c4000141e840d80c1030150000300f0300c0f0091400e41111034100c0031456540e034050a00400142950218140040003484c0440d40860031041c0c4646940480804c6520755075000b03500d44005102c038200b4161a000c0c179484510810b81544244251750548800c481031600907400c5882d21803c1c216900405030400c0f0f0304100000000e41c0e5040e0015606100e2002454840f40e40c9001030000320001746030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 187761178 1250 187759928 187759933
    0x40c051c0e030703030213090e060a061508060f0d0f0809030d2613050a0303050a0c0504060e12030f0d05010501080106030902031b01020f07080c030f03040806041220010203060f03 79
    0x55012010202c12120030079407504006a607002c000a94170744511450740101c4040385402107070304010b0b101180152094100c100d0800c2a6911010101c4000180b50320080c001440040052001d040880c0c0c980c00c4110300030540a0003001940d40c41d80320000d100701c101d070180e0012844d00d0123030808020107452050b541c00e160030a0021f4042c4d01d4103160131030040d55200301604005c2192a8103001c61000095000400d44541154509026016250545140c0301e51413614021441062054041e90151101d950b50801000180700411025030400c4440e1107090104000c5180d0017944400100034000030030fa8003056948c50140098602c4405070b0003802418149840107005039001308027940c2c00300554164a03402c03c039120040345090106001c1ca91540705101e00454001000075102d403a4400441c00c5940032445906440c0d1240918401c880003031340000c01140004400c0c1d0100000c01030b25240820301482d52201ea107050110040c54031491341d5000044c44035905041c2000341c01e24105400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 187762428 1250 187761178 187761191
    0x903070506030105060703030908091c0201020708010c0f0302030a060506030711070905100b03091005091501050d1a07020a02060712030f110a0e03030d0c09060f080c0f031302040c051c 81
    0x300780f17140b0407010010f04040c1e907080240300300710840c03041d14822940134006549034004440e400344905034118060340984079402c00003032111014020301d036184400d684c8240000c618060243d0181d00003400c800c1038552150004511519031101440c8110f4140e80c50341c181d050b52840c11030420010746c1152400504040070000182d0090080c4002c490f8120341680e035a40d41e80c03180741d0610701410341e01c12246081ca814420f01a40008058000c1880c290b0240d000c5d90780c0d10104115103014060007040b2184400c5000f03101038a00303000a40c003c4180c0180e0711548400e034001900c551144c0c0040b5800b40074003642c0e503880380d0b1500c5000100b04108500304084051561200e03058040e42101200300f0417640000c4105403001e000303650b00e01982e09810311070410700400c040c00c2d10019010700800100440c2c00d40808500c81d103a40c0e8000c1955920440c500006075034050310079440140503041a255043c11a0b0050315644502c42d580c4003217542c2d95413a1924280d0741801c80341d20f0340d0070348c401c14100701 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 187763678 1250 187762428 187762439
    0x806010b0403020d020f031006080d020708060c0703110a0f0c060804030c021c020901080c0111030a09060c0807050d17010504361415070801080a030f030e030f09030705060301 77
    0x341100c0689804583d00341181000b480040c0c5014148442990507006200c0300643d0b100179500800c040d54801019a0706050400108071307551031042c4613089681d4071041c00310b40c01c5240c400c0200031640c040c0ca00b040124682c4003c040c40e11054000844d00c98405804100c02e0001c041c3c070f82d00c0a4159890209150f003880d8400520300103041501074441d10b080500c400100c140000c42003000c40e40605180381a42e0365420141c1c407284091040e50100711034100e0031159030b030b021084038a88425a1100001e107800d10000701d8102d0290700d0301300c80408042182e140802c3c020820403405000c21b580304290130141303412500e1081c0e81070b0300103401941824801d90201c0b5201b00c010040400c200c130501016001c1001728490280500009440d0701400b44003000e0107240840c400d40205a40800000b030b03910341e4002220124004d00c581c10880c0c20030518080081d208054814100314a490b002c1207402810703025600759070000d03040211500c0300050b9940c982c18288045801400304803035907800e562410 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 187764928 1250 187763678 187763699
    0x10617060703050c04090c170a140406020306061606020d0e0f0a03050c1009030c120c0b0a09020315090115050402120105120102040f0902090913020a060f0e091f080601 74
    0x81e00000605842da070001e800c4a69480540d002041000c1061040107482d0501412030b090403043e0714100c0844800044180795180154071035019030070912801540e5a0312118020340020740a01c1e44060100410b061061000c0c210101c800e0042c200140d58100c80e140c0001211000c0f6400c11042e0400c0d66000749444000c5800542203825041c800d82e12042000c046040c00202c800c090714480c60180420107140d440240c03003031150b100f642220903503800e022056994021280703000701b14949110009104d400035070001e400c4184040c1c2102c469820054136803104110860314104503a645100c001e000104030386014006000c06c0d0340442c0b4100b124070181c50306443c14010f003801035159201c2015003e0f02541200d00070120030301604d031038584400000d0043c1d401549090321980b07021012800c51281c50045250f0790764028070942c1520300d0100203840ba40b030a4001c0c2010b02c0480d90400c02e494070740c1c02c10b040c4507403c044618409400744000c2640c0e241c00039002880154842c4005000d541440d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 187766178 1250 187764928 187764931
    0xa091d0c180409080f07050f06101206090c090b03070e04050703120513031a0c0a0905090a021605060106141306080a020f0a09091a1c020d02031b0301061706 69
    0x140241c4018207650040340140c0841c000c01002d00b0700008000d0440c41030750307001e842d50300e100d14155004505c4141d84980e8a0300709a442081c20850313035404001c56038402c0c2c0e103000543d11422004c943d0103072503201c9401100322540803070041c40d140c00b0054910302d030502480c17000c0c03c184c55441000d814992a0340d40c2d20681800014040400c108501c40b846024609803254990090400e00d00a5240d18003a074030b220f4044600f0840300e40000100d80684c280000307848058406a0383c61600c60b24000411050320b2010340030058003a401c000701022101c21007040c1c07091034003c1e8000d186035407400400600005945c0148a6144001e001c040c42100c904e0401100701c4581c1d2034406421348500c480d034002441103c034070314a00340b40021112103039600b04a480c01110038005040028110300c04400f5164142c6000f85503100c000c600d084066507048607070304042c05002401c0368080540300c0c1e020a151021034440b143c40d41016000000c9145024001c58000d403081c650306030040e41c0c01c4003c15640d81d00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 187767428 1250 187766178 187766197
    0x916080312010b0310120311010b06030105060d110c0106060c051204030c06050705010209091311150909130501020f1b0a0b061e090712050109020f0301031401060b0a091d0c 76
    0x100003010426445c0c21044620182062695042c1c82d0002072502804440c220300509003203500301380461840b85000c0c41624100c0300c01504043c541850f21100b0001014209a1440c4003001800b5881d403002c1c09116681c0509a20780394890541c00508101c0c1c0380c0030280e021004170324401c04c8213000040000c0302c03030003c845160401948460301031602030f019000c1c84101c0743c1c100d800d0070100719060001c071009030840c5000740c00c81d0141100e400305000404814800c0c3c142d55a40401c078015181c2401c0c500242d20a126030758024641c40c0342da840f0340c26030748282c2c10712820759000f160703228020030811881903600750550000c0509504580d41d5003c0d440008009a10503414120080d610211001c08c0b40a50240103001c0302440c0f600354000742040b42c88410040c0ba075450300c00046503245540c821544582103079005075045a295030340c0d251b00020f070622000c01b15503d49200080c8040400040c2103240e1050f11018140d07420071040243c840c4003010444240c0d08040184000440c20404503940e109 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 187768678 1250 187767428 187767449
    0xa030504051201180606050f040e072105010911011e0c032a0804061805031b010504080d052502010807180305060f0604060e01031505040614091608031201 68
    0x200c1c4680e06074014050101305001003a0540c12003020007060b54059401d8500441c1c614000c5103404081c8421917050104d024003e07801103030240000c0c1c44503074078581c6000c0c81520303882a10360b45036101401c0d00d1400c48100c038030604801e4088165078011440c00f990605195503075213200170b00c07000202921880c0c1d4000c4c00f4014544000360691141c1c9082107040c0200700722807030f201565072400300c07200d602c103120300c10000f00e506103031028080c10b440306082190001401845504805c0100781c00c05c6540010003130600204000c0014032890500c044011900c0c0c58681680315418005071281e0303005c4814101222034083c210143c0140c0c3c000c2c24940e0007803082e180440075410b030040138103264600d641000d8281c0c81420304000d26a180115003a1007840195010300249030f071000d02c2d00c04458203000c010091440b5a9031070044060710b40c810355010340542800b00341d401c000340c0155031200c42900d03001e40c07941244100381071440e00528070750010099071004510780100140c54050f5494180102d98488 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 187769784 1106 187768678 187768699
    0xb1f05061210141e0105090d030e090c0a080a1d070f0918030f0f0306030b0115090b09030327040c0908070609121103012703020705030a03050405 64
    0xc000948400342244d40703107600710200310310211418104403082c440c00c1c81c15030714410044c01082c020303110b245242c02c99805201c04658010005400c1e25401c2040f984800da10030300055200a4024001600c0740d00481074841c035103e06500039142e40310f60103001c10380c0c4242c10704c00c030100d0301c40e24800c00c400303401035927115010403503124044c01040c3c4441c605130420340648280002035010389000611245c580c1e6a6031140f00003a046034407140700000915480d1a0400c02c040007a103049041e250a104074100001e40e248241d4000e01b0102c1d103d13035014040c06021a07524440014000c2051000c88988400141203100c140f1900c5407501ca130f030000140ea54000c2844500b62008034401d035550182944030b200320906039104158154ad62800c0394a010510401d044100300b50a114101c2d070300b90340b814000c0c508102c54101c130740713381c0090950f100040d130000b0480c0e044403000d407001c00b0030 = true := by decide +kernel

theorem cover : BRFrame.Cov 187589928 187769784 := by
  have h0 := BRFrame.cov_init 187589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 187589928 ≤ n) (h2 : n < 187769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
