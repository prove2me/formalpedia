-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2668
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:23:18.510961+00:00
-- url     : https://prove2.me/submissions/7333dd0e-5f63-4905-ae67-19933f755067

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 479676258 ≤ n < 479856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 479677508 1250 479676258 479676277
    0x60b0f060c03040524070602033313020d0c09030506070f080411061614060105032d120f040801060b030112031d0a080d03050f1005121203010609060f1103 68
    0x81d04103030302c2041e0400108200e4040a001402d40d46c150034207041000e074005880d8002c1c10086400107410054122004001c00102d01c96074070b100007440010841c0c110840910502c2454081106400c1000f5a01c2099102e450f43e40724407200a0a40c24100c0c90048002d00b0041444641401c4d144420740080c4619440b0b903200d15540401074403070020a080307004106407020364114212000e420840d4006102c101091041e0403140140e903038904141e031f1050300089000c610543e0381e0800f00c03200c030404c0806440d45031640449040060001e003001c1d0320390100e4400c0003c180042028080743c0c0c0c0a01400d001020052029030955040012846100503400d00080c2407204079510380c0f0700d403400c010801e02c0c0b5000c010110300c00c269883c1c0d1466200c06805401a0000f46000700103409100741914003070281c020381040205041c02c0000780300d110f88221600c1031a9100c3c0d40f040320320008ac908000c6000e00b0490b44c0700d9080529008000d000d00841840d0541404030600c0c06911219000059803103130316 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 479678758 1250 479677508 479677519
    0x1e02010c0219020a15091508060310050f13111c020901090c020c060d0f0608010f0606210b0102100c0201060306050906240a0305120408061008030a030c0e0d060b0f060c030405 77
    0x245089000e0f80d081ba10307075204a00454203040038001040d00400200d00c2080150159501106041c0c004021100104c52844034003442e03202040c0c10304020714181c1c025500c00c0c9181d60f9030a041800185107030f5040e0300034070000d500b2464518110300304503450f180140f9030b0250a01000f03140c00406034842102d05901800707080080780c10510301c03c03681c0041c03140008402003004880c2d110011680a001d00e020700803049420070b00001241e074400c140c20485074110320204010a90190242c4000d40011101641188030700008144040c20a12401540c21015000003412074a185001da080d02c1c03004041c0d1500350460003c10801d5255100380c1c0c44400f0010b0341810700c00008500045a41c5040e810281080c400c11070b5075036540300840010b0003500c0c602412200302c0d542d6941c18103032041c03c2d40620811034005000c4041654080d4008002c1c03c0740a051100702c02c0602c2000c01c03200d1b400c0704020345003240c0364280d80300c1f1800d2000c8050401c01098900c03030f25240903074858903035034840c521400b805071 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 479680008 1250 479678758 479678789
    0x1b0c0609020a030f050d030515060d020a021513050d0e0f09070233060603040206040608090109060f02090103050108010b030721020d051c030207020a030605071e02010c0219020a 78
    0x19030300c000400010390b5000c5410f0104c4c84080c00c2540d07585104103210030119180001244010803014500c08010400401c001c0c60300c0c1072030807201c0107500503080d5001584a0098600c124807260380d0b1440c810940005015200441c0d0301f4030a01d00207012100209102d02c148101070b4a03102c2d031040039030b41001603404080503268080c00700e1810032400366004203001e004000c4041c010301251300e01c00d00b01c1081e40303405603a200d0104000041c0b00640b0002c6d400340c4100301c100030007030081d8040f07076100f0440e030000104449681c0356002950520340c00c40440c00e60004480b171a43da010701c0303554050700c074880c0200030208000740426501d0a690040e90724107400d0b035040da45448106070703130f804a861b80030b8120074600140b45040c0d540c0340b10030340701a19404c0200803961050742c40380c82603414440c0c00400795400545980c8400c401818064800000c201e10090000542907450045101200f166400080c60080b1500002c0c04c010390302882c903120000d4555002c025954a60600b0241c0d20040b1490110 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 479681258 1250 479680008 479680013
    0x2d080408070c0305030c0f010b0f090610050c01060f090c02011505040f200c06010803030601080c0c030c0a0503040f050402040e07053118020a02100b12100603061b0c0609 75
    0x200d01a541c00104680f04c00940b07a5070786400801d185c022412054000d000074180d040402074003880ac500d40b550402c85400005255103042c0700f02950f01540d9080c0280342410401d88a400d4a03040d40002d840404215000c200c002c20511071500441034038402000309000081030103104003424460144215121820218002045e902030043d03055951307510401450f802e101044207400079403010110b8001c1d00c000292400c408400c0300d01c2108141c0d01c02000d0358450b104500e03640c00031410041d01744400e00c804140301600b08402c00a09025000070b40e222840c140d041c03010030f151a0007840c06140180030400c2225245181c05812000c1400c10588403100c0c4900d0721a03181340c03281000740560101e0084204401c00c0628041602c48951240c0303103403140c240c50f85081c0d1055103080801a4448020340c80d60001a40c0038070760801c0c0003820800340d112800c801a280c480301c00d440100b010354801040040103a0391044d030f01c0f00c2c510110f0790b031001890340c070740030f002103405000260032251699880004c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 479682508 1250 479681258 479681273
    0xc040c1206030b060a05060406020c100306030b09070e010504090317150a0905070e010305070c0f030e030106090213080a150b01090b1206030d020303090703140106090c2d08040807 79
    0x120018488010000a50780303080043c4000026103201d80140220000460350303043c0042181c003514203a400038403845075160309110407002454101d20805903030f100b022000400c0000b900e4000d0154800a101c41420300383e110244500607448a40300301e1405001900080e0080409407140b6494660398849a86008512600d200c1c9040b40c1540b01e02d0002e804203040d102540315034060421561401d070f460846200650456400741ea82c0c0c404134440c12180c00000b1054600584130030312920782102c2c0f500501003c6402e48409030030110790302d6004120629400304281b007942c01008088021300d0080300c03580340c2050651a0355221a000c82c4c44c5d034203641d456400392424030000d0000c0055240c2d1b40c6902103c444824406880141c802e00903281042035091000055a02890500c405861080d01c2e503503030101d020a1090f4003c03081c1d501c0d2000000c54083c5841480b85186e1542c451102514105840341d00d010300f2845100e00f6141c0c0c400d4555003581c0d0182d9460f40c0943c0c03003046030381d0f07803007240c28242c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 479683758 1250 479682508 479682527
    0x120702010f20073f03060b0304020919020a0504060e0307060503070810030813032306131104020a0315090203040b070507050c1905180c071b1a030f0906090c040c 71
    0x31010300241040c04039250b203100d002120150342c4c04006048104800040301034030380500c510140c880d0305101040140c50140005a003003034014540704054035030011400166080880030a001c5400440c08100b075035081009080300300c20440192031600e0400c83cac058240e02003c0d04001c10081444000794021802801e1b01002e19040f00c40b4680303032006aa00d140b14192940001c48410300001075400501d0041c0d02c078009004141c0b40501500d83e02c4601c0040e2407100760405a40b001c52000880b2100e0b1624401864030790260307500420444002190b182010348a03a121045251041041001003910081542d420001a1511a03601e403e0740c107140340b8006644841c940d020101c0720602000e10352161034102242c80a03034010407203040b03403d500e40860b201141e440200700000c201d400c0025400e03000c11900444c28000c00c0301e146454504141100c1d1808110410040d0300100b407111122050508660090402008017101d141941c0483c2c2c50ba003880310b07954055601c40030040d640600071305405 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 479685008 1250 479683758 479683793
    0x3040e0f0402010212040b0d061502070905070201180606030302010b090c1602150a030507082a0a11100204030201080f060319080d0e06061c0201170603070902120702010f2007 77
    0xe500c0d50344500d007e0400758801802c48045514142e0300103090042e00c00010208400b075001317000c0341c40c42c200d44000580b0b0010a901e04556071384a8800e001c40c652901c691005024240004095056241c081e0842c6e950494582c401d0300c8040400c11121024000c031010b1050607a102d0285441030f1003c102110400b9412101100300400c07a00c01c915450b500c070b103200d10050360b43d42006440b40410b61000d103581459102c10a40803483e01006902e01c80018551200310340703400d2402e00640c0640030304080902c0309802c0c1050b00000d04000350340e4050051038004107000e045000314189100043d5461101c07502413100c001a281c103c0043c0f0000c50f0580c5d0342e20211031014460b0010116882ea121402101c129218000465400c1050080000702c40b001940c1a12920200344002480c10301c2202c3c0103040f2507041c8504072000c142182c0700c2c00a0300101107114244083da0901107070186c01e690f091100746035824606081c9800e181c2030302c80b03a48140c903e14000c1581d500a03134242140302c411544840c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 479686258 1250 479685008 479685043
    0x1030609050f0406050f190513020301090b160e100c14010e0708070b04031218180903030b19050618100f09140303071e1209090e03040e0f04020102 65
    0x10442c2c0030035100390341842688100070811541d92014240145000b06072480c1405d003950702c150f00080885640a641c20000020904c4440d11300c40c2c0c0040d080d02c41082c070403502c038112542805454504c2d61181c090303180450912071034a0b440500818a05250b14905200f08211202c0c400c05020780031000090f00e0440b030000380300c50300210482668406040c400c3c100b0310311075580d0000d59460301006982c10345e5402041002c090000d070340b0807648002c01c41e01040d441604c12034000f81000e03007241c1042c0c8004180e4000b007648802818090200c4108400e00f6000e4400315100c01c445ca030040d20322900303441080341d49640384c1e851003003a04414012107640b5a0403410800b0f12003070391504152200365030b458903a0303002c103025215968044000c00894503541c050f80140090f00000e01d5914411191507021060851004481c0d00e90124000d0070036690f0300442c1400409001c0a1400e0042045180020300150310b011315101c0070078030300000100b240950a000c8400b090841e80709000c1003450a02140307c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 479687508 1250 479686258 479686261
    0x12120815040e0c1302070b010501030e072705090c09040201140f0c0601030b1006140a03020f03070315050a032f060301090e0d030e060604111c150603020f0f07020103060905 76
    0x46196030f50011060b50340f14074840e4141031980d00d0f150084136481680007002c400d1692810380150058801d98060080c58000c02e03802080c2c0a03c8640310381c0d480364117451810b04480311b048410b000c40780c001d0f00307031406600024581c48040e01c90521064110b9420b103800c01001070000b030718070214000c802c0d60004030200012042c0030114000385581c10380f4042e80c1c46883c140c0321000400444101817040d0b8011900e0351240088400409020341000340d103a0138007620346607240710071141680c000c440740ea012990351036030003510324a03454071800503200980f080010b060654403080c0201c059a402141100e1040b900b0380c42c0c000b8002e56464a841019100725201e5031540006005404010303801d1800b0310074a82540c010606c64010120301e400c081340940065140c11091202800580d0800f810703415041001c90950350405c8482c0e80c102a400b240040c01c55030034500403000e002e49621005c1010300511030f29140201c450110f4841103010420180d50340d141d440141c010303002a6100f0351043d4540320 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 479688758 1250 479687508 479687531
    0xe0402070c09060611060a1e0c1709031c0b0301110705060a2009010807111204080f070501090b070501110f0306090709180906151e1212081504 63
    0x1004641a205050003d10400343c96103000c4070015001040302d01c4980c00f007008203c013100154002c1950f140d100c035401000489007104042940e01c00050b150004240032411120b41044000e810381000e254805103140c000c8240d80d203000500702d43d4402e0400790307880000040f60354003507100350744c40d05a924456480784500c3c141700e51140e40840d402c52280d03080c514805400746282c2455104821202c407000c2c200031140c0c004540d000d10003801c40c01446442011140d180404010306800d0080c0d00c605155030f1401d0911890911415511046060303212080501c01680c2101000d0160762941c26542c4d01d0f101681000ea02408482c1100c2c4081c1c0000102c42000c1c0d828503008620604050704c120600743c603108001c9500d14010300c1800c016000004034141c0351b001136045040810300403480030410f84034500c5c00080200c12036024095413460101080f00d151203008d12174000f8070007e92038910740b41c065220b880f881a0881140b00800c102c10001aa210b1254021000f8a00c00540100011132011 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 479690008 1250 479688758 479688773
    0x1d0a03030b03060a060e07350a0b0105030405060c09180705040609050105030712020d06240e0d03080c0f0c03070507050103051003200a0b0a120c0801060206160e040207 74
    0x3006228002d00400000584d01e0a040c020002100c42042d0025080d0342d8244084800040d02448159000c01c1969482502080810a03c55004203818488201c2c140300340745ca002c441115920034140075060003040045440232600a80c4445a01c01e07455680421900250000a1a01001211072005c0050200040c2d0100c054019506262601c80002e40c4810054885c0c1c001166118001002101401d0801407160091300540801c00c0021520039141c01280844030203c01c2d9071181162641c6889a0320f0303a000703400144440f01502c1c091250350251320000d1a0341c00051036080301c07a00000740c0308030307100c50941241c41503031482e030032341b41c070b80100c0c0c80c041e61103060303a01c10140041d041002280728a8681c0e02039804503035000f1064210302ca4006018900c011001d07032a02d5011400c1e100000350041e04500504098405a41d074240c0d44944940020481d110440c0000070841c03c0001400744540001e8500e4020b00000d5410328840303007840d4200c54881c41e402000340c0181c000701d030850402050 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 479691258 1250 479690008 479690021
    0xf0b0a020f13140904110103090303020f07050303040606050a080a0b040821070201050a0b0a0909260c1b0d060e0a170a08090d0207150504031a01080c0907050d1d0a0303 74
    0x80d071903001989003d40f0f08025031078000344c80c060a500c400c0480300507690b00039031061080078840d050140c1880d150030f20f4552660019601a901904004108810041c551180101070311080b00e010030520b0409034265914141e44c0744c02008201d03c680450188005542038035040210704103006524a001d0440c00701c46001540d03040c015600301004070b4117005150103101c28014000d0301c40b000341840c0917183c0d009003155543c166002c400901b009004403848030260f030040b0f2024092142e9800381118940d141142c810307204100c42000a140f08860b03a5107144114820780c00400104600c00402d803451704180d141c160040035090100d4442d1545c1a00c60090081c5c4101901e6031002e69842c2c01b0071300c0e00c0d52040603408005030001030040c441225000d00a9000545030b02e0075030306003070300da59480c003401005440780103004000034010401041c04105080700c8107002d43d074032410703400c00500c080c11501403400d02c04501e644501c01d032240307651070001e083c80d40400f40f0100d4200361807904000c0e0007441c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 479692508 1250 479691258 479691269
    0xe01112a160602012a0c03091503060303110c06030408030a1401140a06080603031917091b01052b020705060a0b03010b06031006080c0f0c0c030d09030f0b0a020f13 72
    0x70701c0d4001354000703005c004010140007040b01440035000401e40844040d800c1803070443c1480055003000c00c8d6908007031f941d80c400f1000394400084960a5080150802d450b00041441d151710840446101d030711020150380c1c029a01c04111070300c035250340700890040d00c6a810324080d50320341c5c2d0000062007800002d0b560760103002078079148002a201c10040b038140000b21010b0b50035610030400310684501c641070b007284e101802c1c5843c0d4030303503801d5041e800585003040d00c1c01c8009500ca81003805404811842c444942503007420100e10304200140141d0402d440545000f12020590321050751200264048602c3c09602c0815101d0328500b00c0d860302c000702400d54895001e50305e0030000c5c0e10182445001c807405007008090003c0d103586420812203240500074101c503401041440346031080110b071800b13802c240c3c1d4404080c016003603280f424145400b540401ea03008004407900c0820214540d40d8551071155000b8803590069500d19103a039010f4450100300d1245d83c1d40024030082d00c480500f980109454 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 479693758 1250 479692508 479692511
    0x60b10080a06120804030206030406091b1d070e012a06020304050613020d060207020d0f050615060f1c0207080408070609050f13051b040b0406030e01112a16060201 72
    0x1911402c41050b115020f280c014003500781040144003500d04140610340c460312410000c1051085c0d0f80d25944212120f0140c07078114070710388009001c0b8140705061070518030880420a451498080c20050400e110404202e0500c10b01c0d11400d01030f84020040d0548181d043d406403034418001c0d103001c500941c4202c40542d03250084c0408200c10642001000320002d800400c3d10602c51400c0d01c9650003544040c00403680000d1101d00d0301c00080550386010f101900034400f402d40c6103000501c01104c401d00803552440364108006080c03c0940c60340a451141c80c0d52078402209001035a44680244901038018100810120b800100e1050024a010035250560b84003101c01ea901d1303091202403000c4a1815502500340110001000c00681c0019072000c0c2045c1c00701c100746e100b401910741a51158104494003d0001014401c103609030150112650905008102c20a0058100941405040840e5018258a10500840440348034400600a0841041e58040c28404441c030f004c040d9684038000155 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 479695008 1250 479693758 479693771
    0x1020310031b03020d080c0c1003020a02011a060d020f13170f0106180b061903020a0f021203010618030c0801060320100819150501110f0316060b10080a 67
    0x100a902004400c0704c2d805060a140c1d00950b95a01d00c0e0341d0408080700040c0d12600300d01e925113a03a41e10b00c012a401c5907450040c1d5501c40342e207009007991181c0002c41c442c3c9100301007a404a440341e00442e48100a082401a25601407120844151041104020b84001c00c0388001c110a417400d26503280558842c4115006a04005805400e07509588544040c951031003801c2406241a600311500020f4000c6c0018600384070a0261610b0044d180d4454001039404121b8010440e0050611544010940000c180080201c5c4210b0b440d4841401100200042000404071030b0200004820203154041010400f498407000180e0081100344000d43d010b40c0600841d620089039124807c2c51a0009408051802c1e41d0720303c140c1d8141400f524203e900b01410300f004145c0c015034490406040c0388209644852071914000522007050f02c801e40b240b5403c200c9405080f144000201c42c0140d001d5413943c5000b0103142010802000d0000c5402e810940461111104640c0b00e06400e00c80ca80222081140 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 479696258 1250 479695008 479695043
    0xb0a0f0807050901050a0e0301150e130827030a12030c03020f0d1e0e01020d05010e0606160503040e180706110c06090604030c0b0a0f030515090403020f0102031003 72
    0x500e80607200c11020481c20000ca0b100c40d4801c03001040700e00458281144010005d10110b4210344d60b03e400c402a6181d0b8820a0104901e61200f0940091641500365000011511604050300c1303405861143c2c00b410030008401070962203191450844010b06603841003210f41860405100701c4550800064a4078444202c081d029100355408400c900700b6243c144140703006e075074001b0000801c0c031416050442c7d502480c400d01c64081c0301c210008901c009602d508203008400b050321010780102c0c1d0303122484c00c1003084c55160f240684040d84a03e6282035003108170b40c10460700b14441d5030003500c1c07c085080c08000441c02d4490030900302204c540115043e0b0303541c9071800c889052000d5044200c82e0001c1001c0d007590300e007071006070110a8005004610305a07581c1c2d20303c40202c0e01540310203942c03c0d01142207100250008042ca080200302d041c280018a05540101e800551041026205032403041c045824148200000420594170f000215036074204510f0300340320340c0744a1008031140171003a40c0d20002d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 479697508 1250 479696258 479696267
    0x40b1005150d0e010b031b0306060f060f070f0609140f0c0120070801020a080613021201050607030e04090b090d0306260f07150e040e062706010b0a0f 66
    0x1500c612484207030905050039803400250070b0440400d5015034a5540d071a00c40d42d0140307e83c11903d010007014280d0210751b01c052506240005000034424140c1e000c8040702d0380c48003c00c8401903441684010754038203c514003104c813840d212402030f040c00d140c4404030b020446442c80414090b03841108845241c540c00d04d00130b035641c0c48105134900103014002140c0b802c04841e900c100184188070709944007940c8034500b00782241c000800c070100084110061113030505000208078078400c0500c005600c2c003071300c402800c942d4403010b11440e40900b40005000781410b00c21010f54540103402001404006013038240f8105a420a8034070380d2450003414126407000d8020f1141e0300486e0850038183d0908a04050b400041641d0700f0380e58100c2d40542603066154002c20f02040c03000e403031180300c0700f0104142120028840718030084000e001e075140a090f60031541000030f0b21a802a11213403245141300102d80b0380c00003e0304c568903095040c850300002046200c6490041d241414865441e000b81005070745080301c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 479698758 1250 479697508 479697529
    0x1501092a051b01231008060a0912080403020a11010302070212010f05060607031d2101050f130305071b05120f010b01020706170a110c06090d09050102150a1103040b1005 74
    0xb02903180380d00c060551354a2070034a555022450402c6040e000e03689401c914100b00701140d41c0c400c0b00b9074440030441008504038a000041c06903161195030303458941d80181d80d80c0084100a007400021485d41c40b0140c0c42a011039242a602605540f40103048150b801c1c081d000c42c4070050500c0e42413800040c41c3e4180030f03069640c05274044d03a40c1d0206001c40c000c1405644044403445800c47c01d18407090703203040352101c10411082000c2e40002458609820300d4a4864000707080d080d1409072411642010039440020390356169001b4400701c211280003444014151102e901c03c03900040d0785030380c0102c1e400c3c02080401d20720542c54000d200c80d00301d5000487c0c03241400d000790408643c0c100c00e0240041503402c003c680c05018001e000803001110608250943c111707064103019030b400724080041e0f8607030501040090803202d080000c84c41e410030780041c1d12011600c003000c4410800d50000b039021901a00501c0301c0c03c0f2004ea0055481c2803e0415100d81541140d2072803100c488050300155500300f000710031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 479700008 1250 479698758 479698781
    0x1060b090f0607060e03130608162007150c0302191208090a05420c070204060b0307021e120304060906150f0f081501092a051b01 57
    0x300c04051001c0802039550040328040d1015981c3e20f1300c00749003080401c0205903140d0a40c00b10503d440c60716038028803a036002801c0030501404813102c00e0241c3d8101d5a0f0509040007812002c0001840031764441c0381840b02e80c4174402e1903070480c850742c50640d0040310b4000030314026400e03660540310006001c0c080020081c0024400d481140700b0318142071080902c0ca03000b801210546106810039244c280c98440c4040044a104030b8a1712012424030325000425000e1042c00d03111403005240e0b4a40c0365840344020030599104000282d12402c6540d1507100c0c8004c0d1045481e400d8032800c104000075900c058050080030640c001d4280f044c40341c100062811500186004107510711f40e0b441c5c1ea44005007050000896850742c542d01c10315905c40e070124102001d81200c1125044080c03070112262020200c03a07014000c00d030003452002402681003154241569030031200031850781c00892480451310b124101800111400707a4008581c0740e808402040241189100000744c040d05403499422a02401840c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 479701258 1250 479700008 479700019
    0xc1404060326040f080610090b1809031608030f010f030507050f01050903011d0d0e0315060a0b0a030c03110f03040f060609060303030b1e150304110604120501060b09 73
    0x1030220070460b032a0300c8040000048900c500307280d520340c1202071200e600e030840c512030b4100100300030040e4000c010a01c0108099030301032155884600100e42421040380d60300002103482000540780c0d000400c00c0700c03501c0c1400c50603254021020b0a0400c09a0030035100e19042c0d04d00c0300300002d00512440304072401c1d00e41000c003400584e880c00082000c0b59000c001c0301c03810b100042c0a4a203e0795802e02c0340c0302007102480d2800c1071115070760380319a04158505034540c0510201c3d0594825644000403120340000440e0062101034a5050002d48640303010381c0114602840000d0011406606400402d1440b015440510000c5c59050414055000c0c15901e48140101400010301081354405199251400b03030704001175081e200e4105001b6a100c603002540401c0d11400d002d112803d000701b420940b404a288170380d42001d5400d001030406041e0800b080706410000c404601440340c2c440144071440d600034852076a65940d40844041c00d044401d068540d9441e040000840c000044c04a8030019002440c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 479702508 1250 479701258 479701283
    0x6030f06090319090b07060e0c4c0207030b070801060f08060d080a0905130b0d030503040c050301090b0109200904110c0d0c021f021b0d0b040c14040603 67
    0x301400c0f6500d407452031410840b0308a0b0004011020f1740050101c1d41c0074400119051010b407103914908078500c80700758080c010307070345190000c08180b02440001c0d00b440000401c5c461501026810403c2d620b00c1c00301520785041c0303030070100c03507400040860803079120b2080700d07000b0f580700001030715550002d2168002040000000c00015031017140030350307404000185180e544840c40e0f01c503c40305811400c101c102003009020306200a107003079001d8285100c501c03581403003081c50400102c0c50310b5131701c698024184034021000c07500700300d4440c440b0006400c014000308070301d1025040c90400d43c41c003071040c0d01c0100c2c90a042080034000b02c1c1034003254910f2080e1540c1c50800d100c0d0074003008140c03111041002c800700740140207403201c040c0200c503006e90460350340c1c1c1350f00384860041006c408040c88058200680c0f074222010f2154021a41514001c111002c036a12600c0d01c8004c5031080c0e00681c2c004103011140d1003000300300000b080940b0183c0e9031300ca04158454811009001c2114158000a0002d68032100d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 479703758 1250 479702508 479702527
    0x140a02030606011b0f032109021507140604060204180903020d0e0402040b03090a0c15021b040b030105070201050406060518010314280201030c03060b03040b0a022106030f060903 78
    0x101c1004084c94556100e0203405100d844d62680c107100c41c04210000b6018441880c07010b102080b103101e1490181c030007000b000d0240d50010b082500d2840ba0301e001303a040400d09006110f444035a0407501d004540680304940f81628104009600c640606101448445e61281c1c80040ca403089903041c1754550010460101c000b5401c0c0e8225117100744040d40a40c00304008150311114070701540c05000780d98024089081a0f181c16040e88109130401c0e4030400a080c0221070280d0700189000007141c41500060079864104041405800d409038801c0d059030800060000007a41540481c4c4039a009450400c101c0f625082004010310307140e00305511000c010001031011506015420240581000448810700f0300c10904030f0605c0301c02202444040e001c000312406658049c02408610b5400d40b1f8100595420400052181e00014101401d074040500000d660070b0582d604440048140c0c007503803606030342b4581029000d064222200da0190140011881b035030f00c000101d450245481102443c240080d01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 479705008 1250 479703758 479703767
    0x11404050405010b0a080106080d020d0906030506030715050702190501090b0906400e0103110a0806190f180b10030b040b042a090f06050402040909140a0203060601 72
    0x140042e1201c0d540d600740c0d1843e965510048000030712081002041032031601410381d040c14080240c2e1019500400a415203280d17110700310b1010364035181000241925800007081c503140580e00315400160038600c040c104950440042c20303801d4401c48103140e0f41600014000043c844511400380410b40c0c07000f0078055040d1010241041c42006000c49041100903001032821070300203058001c25800c0d1581160808840340a20710311890b010410610b4076141103107415030000148005001c00a900c140c0034100d075120b42d002001800300340119680c5007060341410300d00d0001e05107071440d110301d084000d4210b18694010880c0000160700f5018241045868a44403900300504c020303270891075184003000140090700c0c0a0300981c003440d8520200c1c41c0034035164400340004542072040282e0850307215080ca040c0300054040c2c42c14050042440d08102ea9000040e001c5034000f1640540046004900c1001c1907024003481406030811050761019004941d844101204020703400d604501d00240855004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 479706258 1250 479705008 479705011
    0x8060901140c090402130311030f0f070302010f0314070305010501020d0e0a05011103130306020a080609040b16020f0102030a15052403070903050f070924031103030403122601140405 80
    0x50805454a03d02c6c2100e401c15002a400449a0140012803911141020440002d4030801600100f503c0300041c10015520a001d11000f4100001c8403003803412203119410000429555101807201070421200c040c0103440c00f40a41401072140b140b0301101e0900c903111044e011180503002030b10541c2014011244550034041003d250312007040300c0d40004200c02c02001c0218021440181c0325201006c1c014428030001e0580d07445816000d0902c00400d8a051405400420039101d400d010345000509078102a0703d0406611694804010001e014849400406560390300030081c00c01c0d1901d500802400040707844144e41941e80000c00340c000e03144400019900041c0034104060703c40e6403650755900d40329083c241d001e01d50300301040c108540c1078580512592900b07401001003c203102c42d0310041c5c54840074403003d40000042c0120541648041c001c46010b16008901d8410300f460302c01014129415082c1c0102d806542001d19240c41410001158180ca80801da407840c407846074401c00c00139040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 479707508 1250 479706258 479706277
    0x90d020d1d06090d24090b13060f090f0b0109181502070602071a060102010e0307061a030d050a020709110702040c091806030209090f0604020d0305040b07060608060901140c 76
    0x401c12403d40b4940e90782e6001210785102d0082c5030340307a6020220b4180450b20302d0114030029420300085c41c00259000098030f40c0488400c8031001d0000b141d051200c0980807114018400900c2e1400e140148003c2000c00d0b2030f694090b56021640f0b90340c807803206d8220758048500e03881c2820040341810025124030680d00b04551070017805810000c298072a50202d0f80489411500c00c08600d040c44040807183c3ca2041c0c1c048800d0008200d800b44003400a51070707100301c42009000d2503032030031580d560802c81c0880018400001d011035920307401000d009410b40e400f4203ca10094418110300044404641c06400ac1044411943d0f5003091810341c2400050310700c00040c5018015101004a5003880400b80004c01d24503100020030030030720b540103002302c00074050301904e41c941200302d210711380c1e0000040c2190041c0e81134400d10510f01140c00e040b501405070313030480101c892001480c141444071680102084c0d0780d049040d58881e4443c00c6100e401c82e240b0400d0f20340550800c000003101941440081e0400c200c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 479708758 1250 479707508 479707519
    0x606090209151e0c100c0903020111070f06050705030d050108011d0a020a152d0e04270305070503160215090a030605090c0301062409081b010c050a0b090d020d1d 71
    0xc10700003801081d00d5942191000140f0847c00410030b546e840f810200c2040304d03040282180c40d040c042c0340d003250b40041c0907a2092102c005902020010304204548160320091403c21503540c6503610305020f040c45000381144c480d80200300184040010500031091a4014a00480340d842c0102c644050804202d10506002030301c0380c0400390742482a02d403940c40c48901d5500240c1c1f01c07148000340000c01100030b2607000e0f0380740504080440d440c0c0380340380118040c00322400d079412500b49022109845184030003003441c040400c1d02503003840c00030101d0320824030840c1c4445010080c4030b18000207004e68910365030301441ca010200042110b680c000c3d40c0043c032800c1529150541103010a082d50450323030140d502800c507001070358020500e584075400c0346c960718504a00054681004a50f495180030081030440390140c0c0c06c0f00580e0b01a0180c0b00c0d2466206003510f69080d0b160601041c52142140e1025450050200c4440c003c0e201103402110b40150b62102c01e0703a0404c075010044c0b035010582525130411b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 479710008 1250 479708758 479708773
    0x11090c070b10030b040c051203040f030f051c08100506031e040302013c0c051215040e0d02010b10020703031115190e0106050105070209040f0606090209151e0c 70
    0x4d01303480300f183c841c078041d80904c0800ca02e07020038840f100c1c00c014502e00741908140010700060b0a5401402e0450340c10018140460449050203070800c05080a40340e02001e18051400c152500490401e22a140d0070003680b000f41d56940a0203550b2008440d5041c810740034000f01d10240c07074004400764002e8041e100005060541190f117910074800300b8911442c0403c03800c0811503500040c551a4059102c0c1d2005001c440840d40001c3c1c4a4000c140400740282d00c40340c0014100542c859040301c500303c0080040c08982c02801200da10703411103450910065003000d569401324106071501d045441e2a550041203078074a103071421900d41055800c20401c5005903000ca41c2c47e00503000d07205004030f58160b1a00b040c40b044214200456901c0b030038242c41641004010006070307800c5016a440503030180c0340b0403816500c2d89411070707441810480092865207060000b0420130742650140141a80a4507240408580400d002c2c001d8006d206080036103002039240050070f409000c014198800344501141c0b0003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 479711258 1250 479710008 479710013
    0x6080103080429040b0702040f06050a1a0d02030c041701110405040e07051005041e0305152805010f05090c0307030e1e0610091b0e0f060c0a11090c070b1003 69
    0x2135025500030b19000300081294002c0d0314082c0300314060000162000c114192400010490880d858440c003134003032902c961904e015200f101c0840340c5881ca05041150b407441c1041c00c2c041f80750130a0090700c044020900319420004014070a050400c0b03141c40445041600d002c0410024042c0c420190440c0c3c0500343c0c0c00900d0b600c2d140c801c500700c1e22180d121541c4442c01d1110081a040c2804070015841d01c0c018001c1001c0f078004228a507a0100300401382210340c0d281e9580756502601440c084002c1c823886c555680c141ca4940d80824180d03100e0085442c009a42e490402440400654001400d164200041680309000754001401c48450310151290304241d034054010380b010300c030311070409a00000c0c10800c8034003080421ba4080c3c0b94407a82006104001c092003510780160403809418402c8080b44091035948040715400c1d6000020240b079a1004130089140d00d89082401c21144e81e4603017410880c25103041003441d44213412002c1034504040c925258404074070b1014296a03054000000d000c0301 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 479712508 1250 479711258 479711339
    0xa1e02101a030c18070e01090509040b0115050705070e040c0519081e03070b0601051c0b03070503150f1009050103050a0b061e0f06040902031807060801030804 70
    0x40e100c06000c04401c01e001203809250038000340c542010310070440121008603c103c60803215402030740780d2405003020010940142d428429607003005500c860110200070030007280701140c60580b4200442064400e20310b440c19100d5004400d4010015003007174006000c0d141d0071000301a4058011402c100303949a90b000800d0425480070301c41c501d04d90641c02d062003060390070020041090122120140c54901c903111107600d030300500034001d0070b40f61400040340301e031381c8940c06480040030500e4506a5401d12403107940300070495040480e0007400b41600000f100d00d400b240807040220900000c06455850300601c03038000d40e0050450048003a2090041902c00da01d01c41c02d40078502c220010844c0f03110300c0c01c040307070110360050620307200d0b00e10080113802464031110b81240d50041503c0c40c55000e0700541c00038426024581091000303510100030030140e10b522245100041d1400c8003650640d54032000120799000c82408003603d0f4500801041202c802c6030030b44107111298641540c0200002601900c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 479713758 1250 479712508 479712521
    0x15060c050c060a090806070c021f20010e01111603080925060201050604091110022401170102040605090f010e0a03080301050a080c0f0603070513030f060f020a1e0210 73
    0x400135110700c0c4240b200c018100314094001409003412450800c2c998000341e030344d48124454280034010040034424450048080070380f50325100000540180400369000c0c02481a402da0401c50740c20301c1d03203618041e9400c00c21a00010103407000581403900f1900e050b0350f41075001d08004a10700c0340244500d0001000b807c002e89890040790b126200500d070020007405e54101620140c4100c1c5404d002e00300080d0040d49828180c80151071a603240c504135103041c0d0034409040341c0703002c0d440c1141d0380680840c8440c032441070503101403640c02da40140655036200e00300d0140c0d00408001c658101320b851402e1800c0540002c941005241400c044e8240744041102101140e10456600300d0100040c045454a113000d4005003003a0f1000304038089034240003551000d064404c02e0b014403c00004642c0482c45241142e2580c400400c084008645e42d18200b442c40c0c0d06100285c94242c500454448200c43c02d000f100d0400e10306e9641c541c881c1d05110000130314020b4100c1c101e0150321070f03540c02e002d07060424003a10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 479715008 1250 479713758 479713777
    0x402060a080417040b0310060e0a0e1003140604020411130302151b100c0f0e04051f03030801050f010804030206190608121b03040501090b091519030b0415060c050c06 73
    0x5c1c0c4ca0b4204040e8000c100e8590707810a800740b002464042d102c540310342001c0801c450748860401e500e504c910318a11070700401900702501c05031200c014800702d0b9030f0000d0000e00031391003036904000556640003111014013828a00c001e48144400c0c08001514100c4071a211214403d45900d26241716044ca40c00001480d02e2a03500542081410b8041e184940c0703d080c0c201112810590500c080c20030009080758800c40d8210320442d03841000c2036061170710545084a101a9031019aa03140c0c59003405080c002091041c18800d10000900d03105e1940300d421058081c4d540354009141c3d40d00c50f100b4007a1040607002c640a50250740d030000081d42001003111300081c280d88200705950341d044400d0605075501c001c000c200745030300402c010090799901c8400304003241c401d091000d845081210025080d10016003900c1440240880d10040b00c4810101080c01c50050343c40400680003a00300340001c1e40c002a20107145403140d0b0004120540c00b03405540b00b128496010340e21f451400c800015420b0f084030015 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 479716258 1250 479715008 479715029
    0x30212090c010905060306060a050f040803071a01241b15090b0c0c0601062703030f08090a030f0f0201060306090515011d0106050906090a091505090402060a08041704 73
    0x7210740c1d40c2111100c0040d00e000c0d0346192035442e002c400315100f1700c00c3c40400c0e800c200740003c8240f0810700d0542500c0c0a440104281c81e076072000760500c4551407201d08103003440200c00c3c000000d00182200300ca40d4904800358400d00e400d410341c840556486c080513214041d00064141700000090190010007208034495800040c1c0d05003505200020000040c480500c0742010084820840000590281102c2151030403980801c940320003181141c04800201042455012022041540202120010000c9a66203205598070160f81964804504401030042400400d02da5a0340d4070078400704941c0600d6000202d4820b40e01c0c1d841500303c58a10b0004c0d070742074203d0902d12030303d5102140710703500500320038403aaa1000c1141201010180c010302c58881840030016111305161030f28425183c4110000707100440c1c440e07480300441d0180c081c0952018031a100c1c600085010303d407214203680900d4024140c0741c01e020003980300781d032517000240094449602c0c80c402420076064840c0244060048230381b1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 479717508 1250 479716258 479716273
    0x312091b120703060510092a0e0d0602030a020f03010b0a080c040608150a1509050f0d0f060b041401060f080112150903090f03030e0a0e040b01031203021209 69
    0x85800124030064611032242100e0010001d00110000c1d40d074041e03d80001c40003805403103003100210100700c0b95001080c2c2d1414031101e00c01d041c83c034050b0100101707000d04070031000c021910300845003040360158980e44a07480c40b4581020400700d501031503000c030560710010b152444c2c55041a080381c20990003811410780c00240d00f01c0c115070000e10719801c20041c240c524105810b2130005401404002c0184003029540c104800e0140d6a810340000103104014040d10380c040e003100e00500000107070003110302407003808030102c2403030034903005550010b90007a4008006103800e65818015214040d4107903409603d488400030746541c800302642c02042c0a859000c40a500d646016000c40016800103020101070b03e40f032030214492040281f4104260000000c004015180039106288540c00c40061a42001c502008054200e05800d03480c007421110303d035000341ea400d00b9888810f400c0f50000c0036035100400400003d00c801c403550121031828100075007041c488030102c601851044030004c00320b81c00f494 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 479718758 1250 479717508 479717533
    0xa030b0405070509010302090f0c0702090703051614090913061b11010c08040f14121e0903120c01020d1a0f0103060302100e040b0a12140a0f0201030e031209 69
    0x2c5038000402050315004a11741c51500021001d880040029090b850390000040ca10042d0804951030340e40c1c014451019400d02001c004c0080c40304032010106241c003180c0040281d8091041d030703440d142d040102185407184070014000040d502502c4442903485009120b00024810302450645003030803512291302c501869070080604e16102c0f00340103542d142c00300891109600c901d019a129401c0210141c8111182c0340c0100540300060006100d8050b8503440000d4151580050986200b806c0102c1e0391503068444034103061040d0080168181d02103800c1191003407400020f00810341101000605041c201031201054034012400e00801c00540302c1d04400384d203080803001c0420007082c07800700401411030b40803505900c005101e410610207040c0e14003809965640140401d00b502415508501c0d03034600790310100d559550021140c0310031080d2011100c550004030400340700c5c0c108002001d01401d6800541c000c1090980c03006050004009c22010003500c000100c0c01292540000c00c041001d40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 479720008 1250 479718758 479718763
    0x2070b060114040e0606160b090c0411180d050a0501060e0613051b09121506100c0b04060915020a0c0507081b040f021b06100e07021c030b0a030b0405 66
    0xc0c203030b850084042c0b00521481810100e859440380003500d19580d10700280c0c100740d5400c1000c1b0030040903088000e0402c4801c00c2d012407021000341080c1d8060220301c0030010400e0b914003a0341c558400c01844550054110b24100b079450007014003540981e80128000d85030142500c1e090303000710b008002c40e5002e00c2418180000c4401c048428031200300300a0504181c06820807603d5800c4201c4109c1c082142e00103a03441080c807118103410741040b12074181000507a04410301c421140184074424000b20104c03694024100030789803580c08054903000da5916580c00f0000c00c410030050b40c2d02c24009078206540d034030500c02000090b4458407031135021241450503a10303200080e000380142e5004136138041a24104485800c4403075400700e80100d540385090780008028001c2c600d0f00070049010400c81100018041000c41c003480c2e22803074500440d81c40b00329440c131a840a0b541940103038090740d040040400e45403c0c542c010132941c035002c02c40350004c80c0015044412030b00259004240e010a200400008 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 479721258 1250 479720008 479720027
    0x50601030c0902030c03131502040609090e06070512090a14150106090807050105160209010626071409030705060301090c030506040e0d0c0602130f090e0a081e040902070b0601 77
    0x10761000354074500d00172504207018000507049103001440b04001e081005202103c500c0040c2d0a02c204640751581c610b1700401c6244540300f500d540510300f8250b00303000c3ea0003180480c482c0000b07488561401140c82c3c00e0b03185503c001042020240206044200041d08503403201c00d0b05034500c40101841c80d0075154026120206030300c800240b2114900030444241c0c04101241110740034200fa0341c40d2a19222480c0c40c6055594009601441d40740011900580104201c00a031485103200d110301810301c80222000a803c2c1c0740d22000c0340d00d001080100800302c100400d0501710280075550321035900e8010641c140c100383c0000801c00e4030780c2040301207d0b61500c00c07280c1c004c1c0212001e00a02d00890b00940c1c4130312002c80c0200800105100c00024030207640c04a0300c2c10070100b4071429440c5e990300d45454100b00180910141c4074200240b030456036200081d034501d180e81007100240380c400ca001340c41c84485070305a10606908402e000003c0d1051a0344085c055090095a4200952401c103000602800a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 479722508 1250 479721258 479721269
    0x30a02040b130602060a2705102d0510050607050f0718270311120403030f0305070305040b0c0a0309021c03030b06030c19030603230c0103021206040216020d050601030c 74
    0xe00720740d103100880d00402c0071f08404210b0444140c082e000d401c02500381500c80c05445505420030201e14080d281d00c030380043e0503e80070300c1c0071003600d8890003c003400d40e001640c152000301070940f001d01c11483e0140040c00103611400031130308005101600d0f54244001903100401d0310390440800c903130013000d40c051041c4103041d80c1e96451880c010324200000342804080d010703082280b031010200c4458000c0290040114091400741e40b190b0b07491030001c08090400c80b403000001e00b040042458a03010b405001d02491b0721912a144a5980c0044004542c00c9a0304281c100368941c103e000145c0c841c6040360500001c003191384066081c03d4180a0181e80c20703442c4040c0220f50030020030206850071015a220b20303074410150f400c4420034031001c0740a05005e400c09003102c025441507010f10100e00d4080d004100140c0207454000c900d90005408900941541c02a8510b20200044c120f1620b036004185480d00c003021480020107030f8010490302c915a407000c03a01c0d50722000041c0180304100144600500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 479723758 1250 479722508 479722511
    0x1b0a08030f0d020a03021b0c040606050414100e191e0608041e15020a08070302040803040509041505010b0a0e10050403020d0f08030a150b0403020312030a02040b130602060a 76
    0x651000d00c01c5698440c1042c401c8400b90f0104122520600c65011120601021030180f02403007460707514992100c0310040380901c99850214009000f13400783d0144c0d811110003080540382c2104810034000b08246602c55a010040a015140f000341e4480244a10341121032800103091410005912104500400b0003070401080001c10800c0c0b59100041c142e0055215030440c480201c42c028180700a500d4107802007200502c1010340001400c154003502c1040d04564500c070b070946600c4800c0e01244224080c0d0343d1150010802070043c0d0800b100c04581040c4208200d030500c582210b001c1c01211000e03044000050300000d4030f09803090b480118101c49050881d0700029010039218090814455480020f0184401e0a401c1051041041040c4011344c3c0003a14a0b40d28607000703042500401c400200504401e0744054081101c00542c01507900f500c8d8082c0040c400b50303840e8510b41c511900014401d0100d944c0030030002c61820180c201800810500303909940001e030070100c0c080d00f0030700014001003005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 479725008 1250 479723758 479723767
    0x5030c03030702150c12120a0b010905040c020f030d0219020303011206090302032205120c03100b0604080115031101080610050a0e0a15021c08010902030a0902031b0a0803 75
    0x6a0303012084032107141c1d044904810810b21680c02c5a550301959917103201c070317026220a00700e8030b809400007001c01e440c800030103220175a10440044120390b20031104034000b44160f0410301143c00c1c19881511266a5401120302194030254102c0c5144e2102d50040720181d00825102181d403144945450b00031100c0c0065410340d8102280d280101386030300b05c080d20140d00c4801400906009008070f600309640a80400d00140d544030015242007981c0c800c2c03a01650f600c40340c41d1807120f07012808907803440b8010003500002e951390306e240c4090303e070f80041980c0c030000811000404100900c11002c2010b6540c4c43c4501c581c1c5141020070442c40c01002c4141440400c104108107540c075a8a5005889018200340d034036401842e60480e5100c1b50010039a070440e00c020b0022031000b00c200040050515640d003152680184440c184001581440c044004245004014000070041340c0145a000700000e000050140312500000d191003c1840756220800e6421070102a82c00c160311002d019242d07940c02175151 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 479726258 1250 479725008 479725033
    0x2040f081e070e04031b0614010e07020706200c06030906011a07030c03030c0201110d0f180506160c121110020405030309040f060e070f030b09040c0501051b070b0901090503 76
    0x1180003003006040040200302000900d0b0105096040150401f1040100051500b0300c00c011900a0041d803250712413000000d1545840001c2c0701060300d145547d03810800d148100c0c0c000c040d0900b0040200340740194400d032041c50300c0d090082c61245806100500c5294500551001c4a0700300029000245004019010101c0c0c1c0025902d100c2c1ca606180014071078102810072401012542d20007103c201000404c17041418640d04104500c5d01c201808001e00c0121494503045100c140328000c01503017005c0001003001811140b19001403441e800c083c40f48600580d11310b1862184020303c440443c000c4e070861105610b040214000c1d180c41500c0844c9000d051100107562401041d43c16480741ea00e81c042c01c41420400e402c44030050a503580c00c12003e04020344040c01d58080d203404040080d00d0003d4982c2c0c24940b0b101018012508030380314130f842d10b0400c0011141540005000c44509004a005503440d080c10007a081c0103080381902140c80c0d10340200010413104440e40454860760040320107103103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 479727508 1250 479726258 479726279
    0xd0905031c080a0b04020d020403020901050a05010903081b030a090312080403080a0f0216080913020301052d13050601120203090c010e12070b03040201110d0c02060d02040f081e07 79
    0x280e144107410500342d41e5840403d40030142840380309294005001203107819000c04190042c01c2038a2080b52140e0b80ca80e251418000140640cac0b01702800208050701c10008154034000420820079242d400c00c01090441b961146140e003c0c036110380000700c44400420a1110301c17410030110b4003c61920321003904140d24000d040400103040110b042c0d0342e45044c103005410990494032030f02d400340541503c180c1103090196941d000400b0450046284544411101d80715108990503200010b00d4450400745028450303464201900000058100c42d16401442c3c1c4d0740c1174500d00f032144003a800070038240380030400140343c45400603242c140c0d2401441440b00300301002c14210700c83e032400c2c64000e41c0e020700d180019031110f2408a42d26268041c3d44000f06081004000a43c0710398004e0300c5082c5418801c1c8026940c03651003207141400504082141c1d401854242c0c020a0f400c24000b8000d07042c076440b40c104011646480c2d200360a554000142100024079681074503030340c006410003600c5601d250403500304 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 479728758 1250 479727508 479727553
    0x90f0906010f050a030b03070e0906010509090a0305030408040e0a060311030d020a0f0203070e0907210203060f040321060504050a0b0916090e0c0a021b1c08070f050d090503 76
    0x282400343c00f00e00030451910990000c1c0c4e004100500b103e4001d40c0e120768a01d8482403c0e0744801d001d000d181c0c000700785403e100c00100d0149101e0401450100c05c940c40883d42030b080600122040e010400c0f000a400c09100030f11801984c4269000881301d203186030844440c1e0100202c3c1d4040d402c044040c40c00303d40c02144030b10b13056810540141d1104450710001c2d042099540100000707090314824410300c1000020502d054a0b0b441c07203100c2d1462240c001450b0f0b015800f160003903240c4d10000c00200305801c0c800b201e82c0c010384070303040110480010000b89214410f040c0e64a0110341d80d40e1100b0001d40c900380c090660042501c640070808030303880c0000b01d40740202c0181a8070215040032010011b03039218500b0b010080250011031115810721103c12021395021015010041c812114034001b509055102c01c1c001c3c1c5002800001003140008401380302c003060709801d641d044001e01031314001c540b0400003111354070710800281004081140015050141130b400250103944a801d4100180c40c03e2484038 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 479730008 1250 479728758 479728787
    0x1103040906091406031f0b0f330702150c01110c0a0515090705121c11160b0406030e0f0a031701090204030302070b0c210c070b0c0601210503070305090f090601 70
    0x4501f802820340400d03400d00d04150215004000c80b00c900d60a040f0408149a1a212203a5024040d412203800003049000d4581c010f5881900b00b580040e07000c0b8540000c3c245080b02000100704001e080c1c1542031960801800355603107802c00309103a401c122050000362089a0703100c141180390305103ca12642e03614054058280215040d208c0c4124041c000c02c8482c9203114041c0456a4004079148001d0003a11202c15085a030701c10516a141002e039080b0328801991031211049084c949410801c6000d090b0f46403403140140a9a00c2c0741d140101d0510108c4140382c06501c032a50802d2110030413908501c016803000241038418041030001a0f03021600d601141e000610541d10b540c07a094085062041c0001c03940c940c0a0b0103004a400e03510000080c02c41850450242c4080c1a61503c0480c441d2241d40300402d40d5812400c01400040c0300b4100f4480300d99060782416284103620340c2c420b8074640c8881e50607002306201099030401c620308400c0c150075078801903c1c40340507401c001340042c25941c400c2030700 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 479731258 1250 479730008 479730011
    0x6020a14041d09070308070f060e01050708070311070203070f050a080703080d050c0909040311060c2107050f0c0a060609060e06010e19063c1103040906091406031f 72
    0x46030350400f0030401d210295401100c850b564080600d0203159100710380404039041824034509003c105010b00c1824820407180e00c1e803188070380c1c1d00d810403002031000c00b10188c0685400e102c0c1c8000342c0c0b0300b0049170740074000103450b00141c14100320400c04508490343c4403818135030107010f0920000b0b0340401074808014541c2c7c004100c41c1c0f100e2304101e400340600b02c10b141e00070520504100a05038046021044040402d0940c0c820740c5450048550b035104110074400c2240c5040548400920b10041c1d09603c4061071030060304151a243c1103022590210b00311005c0d1350300c510004070134010346110f01001482d003003000b00651460407882c0c968a85c00148050305104d10101015020740b140d0000e6240010b1480514003241e03126200907211844007003540c01c400000600030500128020076a1f0303c01c0303030450782d40c00000c101c49000311a04800440306049030700050000059501050040d400a01096180400e8540221032400c0884030018031080c07282d800500707121607104050b140c0d8000820440ca0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 479732508 1250 479731258 479731261
    0x403060b0f0d0503070204060e01053706090f0b071106030a060305120a080108030703021207140105010b040608100f05270408070c1406030a02030402180406020a14041d 74
    0x7888015440d401c1d2a00001c242129408000700030000386951807088500f00141501c41c10104409403007402495007000520110504548450030a100d03038540c100301c00b540400030790f00d80402c141c030309030710100108641160030701070008080141ca010b03294100e221410011a40c603409840d00211001c0d501800300040402d20040203500f1050185401408540c00040314040071003041c0e014103030b0000000c15030f00c00401d0b10f44000c82110103c0340c060b0300508040e210050300986a0f840702c4000c8071143c900b6074505954100a0003507a00805103580d03807a0700d59207424070180000d0303001881740c0d07040ca050a0301440312451459040f03037a5501a078002c0856601c81034050740c0044102c4201100c3c6009104100c2000030b03800c02413152611442880340c15540e210004c1c0c0d0700013200c0d207a2550210041c00050341000303041d400b0b9a4403034001013001c0d00c58038420040d042030000655090f10700c2c640000b0007078505034122007500000d04541c44c1452902d80380c910a03017200004505541d00d000344090 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 479733758 1250 479732508 479732531
    0x7030f0818060c0c0f03040b070b130c09051603020903060106050c0f10060518010602071404091a150a0e0f040303020f04060f02060f01030f020d06200309011401050303040306 77
    0x7501c00c214444004964480c180318082d1912a0002c0760754408500c00c8a9899418810200540f800c8400c0358102030300f488201e07074411114010080120040c404600c0c2c8a00104030510f80c010010140c0c00c0f000a1030b8242030019000342803041104000f810300403c0355000c2500c0c001912411600e607450800d8a072070b00070400314144801a0341e03000407407140c603d4040f114201540414101d036000c607241c1584c200c51418890551030700348200000f6070403d45080103405000c05890f00c0160700100000380d180e04907981c0361030040340601e00001000c05c00003040503d07204108040d181603011107403039180d40d02e440002600301d400140754a0100701480b01250070113020350140e40c414144000441e80b1641c46041c02400300380c0c0e01c60010018881d400200d8441503542444a043c0c03034012030610314020340e94013800907000c00a001160312950b10141000c8800d00010800c524056180b00581c1d07900701480c0302c600390350345a4520303414404400c004114913a0004200e604603a80074002103900d802c4807 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 479735008 1250 479733758 479733781
    0x1b08060f10090e0612031605070b0d0b3c0a1a07062f3405010605100206040b370e06010f0902160206070b040201020609010207030f08 59
    0x1940140e03004880c10450084a5410000c51000e035004030f2004030300c907920b00040290807074131002c205010390004c005017041e07800c0e40240c0c0c54825000d54100c0c0c42480c4d85440d001d59035402000790120f0b5030343d9a001c0c803844e80ba0400d40c68455144034007009030000d10300032850b018140443c88040540d0400b140c42519504c40395010001040146e00e035090708228084d59822070b03806880200c500c94904040003000e1112040490a2034a4000003075010f01e41c440d0081442d0342c0040d02d140a002035111407205858000034540c055404540c685c0b00640d0750528109095a030290020351240c8a00c1412000242c3d00146030f03a40a82c2100582041d030b16100d501100b4007013402402d000d03009265141c0395440000031460780c0da400c0503610401010460902e410380707070176082c000c1c0364184800080801c5100000d4025054013541c1c009040080445640010415400003400326104040c1001f00820340d0f80500c9800da2040c9550001c4d444c003125a50000d03d03070b02c2c3d40128242481004000310b00e241006 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 479736258 1250 479735008 479735029
    0x1401060c1704060f0807080907120f06050c040602011103010510200109050604140d0e150c0106090f1808030c070f060c0903051209090121170d0f1b0806 67
    0x104854265255103c60000f0302080d0030b0001000072400b80d0300400d410a114199903407162004c0c2002e8608141000c9c40b021452042c00d0068410070403a120180100d080303445014090f5004188066031180f80c01c0000c0d00303403148034072032030b44d0b054041c0700400c425180d10001d00c0e10084545041c0c65460146400402c5c0407840c10600350040d8607290060b4108540054401e0103107024620249404600c001c10b40e694109414400d0000381c429498112241410303aa02d0809400000c2524100041003001c1400c4540c0350340030000413516050070558104c4c4c1c0340304052810110120998036101d03107495540b00b0344000b900e504040640014003005000b084035080d41c1041e840b1205115980324101c2c01041391003940000d60340390084100c5080c94111381000c035540c000c0c1c0507149244680c0381001c1180c4000e6a05080083c10010448150000c0c0b1003094052802010b02c4c003180e10782c0460716100d011a030f080d0070180c802c60700d0002801c0965150020201103030000e40b90001c010307034400c0c0200742400f11 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 479737508 1250 479736258 479736293
    0x20306030f1005010f050a1212020c100903150b0603040f170f071101020d0c020f120a12020f01091106070303060902040b120a0b011710050618030f011401060c 70
    0x4440b800310021010790401412210380560040905032107804001d607080107442410604c01c0c041300e1220005144080c00d89681031580140c910810442011442000000c02504c0000c1d084910500c200114081340d8004c0c0700707185004001c0e5800b4940490044c1c80058006011083d006261008208150240106400460840c5030310b0f10703005605200640c003c194215a1200c0e07a0a03145415440011608200800e03640c9209a02d10142c090001c40010034090075084100211800c0c9040350400081c498035110704131640103100603810003410321070013122040e1141d040001e0400411590b504480031040c1c2102c800b581c1d60341c00e00d01a001440151701038040d20340085000500b540151015224070a261010015165140b80c00c0804032030611340d006000c981101c40c40c545680f14450030641c0181d803000c1c40786000d1303291070020f000c0707401410b501141074a000c0203030b811034142400100040107a41c8001d1201c0d0f07181d0303c80b003801e05005000d59420068000100030a00000307940c956480071 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 479738758 1250 479737508 479737513
    0x20d080405012a020c01020111180316080307030f02010e1e0316030f02071e0b0313150f0b06090d060f020405040e01050601020111190309140607081f030312020306030f 74
    0x401d80903ca403101d51001c550140c0282403100c005940180554240007002d090601e10f480c0420510801c03085208200079094032038202e00f01d0302501e40e680b00e10040c00e0100d00440c1c80b007406150040c68101c0c031102030701c21641428440c11000b103000680d05880e58502a810030600045200c19107903009140002d03001d07038220221442071641100e0070328203800c1039500b91110305403130780000781c4410303903d40c11200b580c030384d0003001c12200a204000d1500802e0702e41800b00d02a0381619414500d20240800d9800c2c40d1342c1d9140e00454802034414030303c00d450240d0b14141000c10380f60010f90315a0020380e01411040d00c0e121000440f951603811a005404010803c000030104030030524024502102c0003809586450340d00003447c11140c0c04c1d11550f0007140c001e20f10520344035604030094010108125104100c0c01d149107240d0704180701c3c192080d40241da400d0b1442c64079030215061820301c8000703580520080107080c40802d0380b000c82c0819185601d04050794980b2020302291400030301a82110050 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 479740008 1250 479738758 479738801
    0x9060b13150c0b07080105120f0c0f03010e0a0605060a1203050d090204150803220312031a0a0b0903061b0912070b1c05060f060901030902010c0c0609030b100303020d08040501 77
    0x5a8000d070f0642c6c1644c2c1d00340e4181d400907212560056a8100026404c2483c0e0b000a8103401c2d1407a04902845050b03d000d4004680702da20b0f1a10386141c08a034000c12180715444404005043c1000040d050082190602a00380c840d0b950303c02500b13030703c07401c0001d590803900d5940c04070944d15560010b80303000c88080150017a1070b079a0200396407240c002041c1001c2c00d060640401c400d8944840a15082d6a00241540e03c01c01c45002c043d801031201080c0c0d0403601214103461001a95401882c2d40148501818036075142c1e0302c40c00700f40c00c0050042a81d01048800280070030400e03503520a903828684103640c1d011542c07101b0f0146501d051400e0f48010960f00002480d0401440303000740901c21030490800901540d261710f800c00c150b04e0102c00b6400e4112000740322064680d071082c0c006a03822401810b21540400030360300d4140101066400040c042402240e0401c01c00c81c00807903881d0b0095444039441513980c1035650094840c81c1241100c400c00c07514002140a0002c20341c0420b000700721284542050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 479741258 1250 479740008 479740021
    0x6090a03020601050d020a06080711010c0e030f010603150b0111010e0d080f04050d03050c091518041811011106070804140a122307050709060b13150c0b 67
    0x2298652142200180036001c00050701d801c100d0b80c500c95880e0f00030181c2c41c03103d061000813a600100208490200680e03c0358064042c0070a11440c901c607006a5030340211484ca5905051070b0003020026070003a41e24280702000071462540d81003040540c1004046a0101041c004840510b050407181600c0d504c0c2c10060720210f000014403041c4490140c4403803100c0d582c0e4031240c142c1d542c8111800382c4250000003050503201c1c440d50140f13501c0030380c0e15480c90034850350303030003050304000030382110751820030009a07078908004000c001ca0071007602100c09121543c0c0d401140e9a00b1855168000c204a1800a2001c0282e0041590380d40d00502c2030125442c44c0b40c4518001c00c3d501041d541074410217001d0b5005000c41070080f411300c0c0c8550f0418103210000b18420740071600c2d600d0664070302c003c05550b0004a0400260344d801400114040c00c01050840e0030441804100c0d08250b00c104540542048403085040618425100311586580c0110408a00c841d0940d001081504001c05030007490702000b12 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 479742508 1250 479741258 479741263
    0x402060a0e281505191b050d0306080a17030901141f1a0a11070512010605091303081302010c060c0804060e0714060304080c1905010e031606050603010e0609 69
    0xc480c200c80c0b40341841c42c2d903181e441a040401c0303c080500010820000218038101c803c214000010440c42c102041c0c2c0c030b50f0200c1c001e0020388480c2c2102d03517030011414164095418010030001c4c2120348040c148880050741e980c0300380304581c1c90000c1c0f440300c040f0014042a10a5112000c071507140760150300300d4a401031030303210606000764225103084002003000c90000340024070510520310040c200c5150156104054030b02d40d60b00034610003d88507914000c983c80c0c23148040d82c0a48104078002280795800c1a0400004400080144045003128590180070070392004210390030115245040100e04410f000480d4a0031030700c40c020b000300303003000e80d0307503070b0850784040c05501c9507000311030070044201c0d840700a80e01d449151207400390302c41051000d03003500e06d40070380119001441034145600c3d281c0c8914000f42491181c1c54070a242d885c803115440107102c0207010300d040fa96a4400074614000e845000c030300c1c0000880c503025100c3d507038400000341c03103480c25444019003c19042c220b1b10146454040030b0b9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 479743758 1250 479742508 479742559
    0xc240e03070605070906140903070801110d0501080a020d080c0c0402070305071101080103051f0f090c030c060203031e070210110306010e0a1a21010b0a0914090402060a0e 75
    0x581c5289040005644e0b541310f407014506848007a6200300d5001c41c201e050100d2508403204140d4140a00d10f00000c503440b00b40304110040d8034583e041512400c1507606d100031100141d01c40c40d41034110344040f600581e05c81568400c101c2e840120580c84408640d07005107455540101d4079049480003c3c020305268000001d001c1d42441000c180c081500440c004440ca24001e00c402010f59214201c0302180c1251203104645151040d800060132540d0310110750240ca11600301a01c000d98030350028028404101c1081002c1c100b50300065156060280a200e21920484000c0e1161000d942c00300325541e00c00c3c04608480d1515100900c046003d40400780d0440e4010341d02140803a220341545292400c080030624100e4943d038250360744190702801251665844334800c03d14041c00707001403072500170f05185100e001c0d0480b0020980c4981c600000500401000d421403594500c2d1f4a82102d1542d4840700c9095000760306035051340d180e261640b8142c4c0c0320f038041001d0540c07107640d0a1256032820501251403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 479745008 1250 479743758 479743763
    0x21b0f060a05160e04050603010b0d0b0f010509100501200a0b010501030e0a030203030a0207080412061a06030603061302041d010506030c0f010203071e08040b070b07020d0c240e0307 80
    0x20400d507142e20f10381c0e0103000003410110000c00c6183c1e840228901d041e074032150b4044009000411000c140800203460100e50403411a02c81d82c29006020b000c0c0404810f10b80034000990700c0c10b0643c1001c0c00e0000e5240b050f803043d0741c10400307a20060314444941c007a030f842412170704408843c0c0140e201d1034840002402401440e0029240c4800076400b003400207140d00e0354540503000b46140d5210348192001a501a00095920b60703420000082c1d010b80a8650b9054075004242c001020030080c030802c00018140103800344552018414010b042ea0041070064001d11090720400125001e880460041c00131300c01120015444c2e8109400c0040040d0040d500c540707000c6003560500d40500c010440400c3c1c83d100001d0043c1c1c414058500081c0e03450800c600c101d407001c20b414040c0401b640d16000c0c19842a000050113010200b04801080a80486103800030040d0000c3e04200049020050411400c080080e040000788803280b9480943c2e16a40800702d000c1c0c0d4000d10071800300403100e035500d50140504 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 479746258 1250 479745008 479745011
    0x2012c09090a1a131403040b0c071e0f05010f020a050105070f08060a0b0a12090b04060903082a07080903070e04170309070b0703021c030f0b040b060d021b0f060a 71
    0x60860584a070545584a0003001030013200701041d640720f03252044443d440c0c0840c06e220411022603814400c0d405843d6010503034009000207820320885010050380c1e0fa110035181070b5011000c0c480300001070f0300030b0140c07102072074142d62040d60103400b00d10700034040c01c011307207503501c4c0001740064180d010042c5000560540c42c1d040041d00e03060280403010f082d9104d0402c40c048203108800000784200c9019105182c00c0d080452840c07810380394246a18026501212201e68a83c0e51104058111100981c401103c00e0302d00ca16134003901c036070040c05441c003504409003a03000500b0002c120380722054032034164000c1d0444140c640c54000c0c0080982080d1026204120030f010320b61080c000f074008a030311480d512030103440c00074030300130020203590010300c030440c198010a903000d49001c5131003150320503101d030641d00880c0c00f009404000084410101400b405036003003100502ca96102c00c2d0403a1440180000016501c441040d440d80b8810122518207026006101e0800d0701c80100040341401f40c580c0c03410 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 479747508 1250 479746258 479746283
    0xa15050a0212090c12060f060f010908011103010e060612370605043603140c0c0f030a0525080607030203040c0e0108060604153308010302012c09090a 66
    0x1240c0c6c4810442c0e01682503110b0b100000c13101d0504920400030080c0c18103012420320f4807405114251070407011011006640400104581c850065159410410540d8040c6c54014142006102c6c588010452800ca42c0f0f508405400030005510307903e0705a00c60750724201128454410b18001d0055071040c00d05c21810003103010000452000f40350740c0354202c140d03100d01c2000d11001c0309085090b0550154284a0840e005032400e804070070007000d59104480286c01c684600000308810084504075241c001e500c0304004e0341c00501d000580c2c2a1200700700071104507000d078000800036001125007200d4002d0240d4014001c450f60980c0180d40214410031907980c0c41500c660713100b40102e209110344000380d130107a40810700f04d0070144c0c00042c0c0c0e00c1058140030059a1220100c04d07491071501c4000c0865400d80220400c0d640c103000e07012320031000600e8074020035403454000906a9a5604003414000000c0d0740742c2654070f10311403898010702c034040c0410038540b604400c2140c9070364441030180c3d2511032120 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 479748758 1250 479747508 479747539
    0x801060b0c0d080402030c0604170708030408120f070204020c0303010905250e0a05120307021203030f07050a05120c070203010c080906070c06090b09010510080a15050a0212090c 78
    0x60607141c4145001c401407140700c00740e00044550040203401a40c06002e00c0c50300046544581000748050842c40801621440300810742c2031030f00800341d010b00303001d1300184020700150070b01180000254444007142600c542c0c0721030b6000302610808400030b50040c40002d0041100710007102640c101e82030b0290801c803031341e06d030080450401c900b0880180319594911500404500034248050f407004094260b502290b1107030003146119118146115041d07101052200461601402c20441b0710002005141141050f400c074110000000e001c3d0000d0140201c1e40c410110710075015290f100b20640704089203030810030148001c0d940101010b9009500f000b8440c04298050311000340520400001441329644600d0119000c400c812303c1241c40545801096020450200c0c0003070003210b0480000443e0304004081003103202e9944c0c84a0500e0f0480354000f804075071208811074002c1824040803e6550307520401c1002480754009544c9084002028805104000600f0400781da9098a00388528030591 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 479750008 1250 479748758 479748779
    0x4061d0112030c021005130e01090b0d0f02060903121909060509010207050f180a021b061506070312021801090504060b070609050a1202060609010e0705031f0803070c080106 76
    0x740180100d40452410300040c104151820340400091411504041e9042d6802c200c04013140d126001c4040301a005100c00b1119115020381090111100c004585031503644580300c942008002c0d02c15032001c94071311225202409a00c0b1446600760002d0f41d00c1588034032440d0f01d604540a801d000944e60000800d0003805401242d240d00c0f8160000c000c01d81c43e0408015111200140061f0080c1c6030381310034811110b600d10f20b540524400b03c80562102424441c070301760404413042403c500d0348a28107201400346103243d0031015000c182e039401d40d2604036040c10b840f2010402c1c07002080f10300c00588c00d00240c644660403040d00100740d03191401256944100400d0703858074040c1c200d0180b02006804002034031940b00c4220144214195840a00903032240700a0038040200d60016800c0380041006601d443d00510740501604424050320b4144840c1c020020300006002601b10307180c0c1c080e441d403014044440100181006800c0384e6030340c40c6c40e00e0071418a09007803190380d45660a00c10041184241e2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 479751258 1250 479750008 479750039
    0x3150204080303270106090914120a03050403020c0d03020c13060f050103020c070806040b220f02090901060509010b070c0509010317070c030c0b03041218121104061d01 74
    0xb54215150500740600721400311070300e1000d5480c001222002c01d0320030300a00c40102007107480007560160a04201004100f0721440c0360407500904094040c0c42001010f44110b2081031500003420782d201d180030b92030f00d1544000c0351b0b40150f42c40c401108256000581c1c01001000381e23409031401605174500d400b92400741c0507544804410010500895219501030304441d60741204440c0b0140c0e441100340c1c18598195001d40d007100440c810484850b4480c07603060034480c0760510002c07040b142501c030540c00300c0080600078130a81800b80030404900d4250082d401030f00c00140210070340e5940e070415040561000d48129072221380c9044c002078070310b01000b034103049941140064100440c1900950340b594031030b0b80c0850710040c1081010002c075082001c41c0c8003520418091581c0d030b080a060003c085240b440c100d00402903002c06840130280202c4c0340504581152101c40010005440c00c000d814500419082d001407a0860008a00b45590000d080c040090482c41c0941d0762500f0f181000d8424 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 479752508 1250 479751258 479751269
    0x7142703010b0907140f120a0608070f03050703060e0c041a01020706020a020a0b0304170309010b0a080d0e0402030a06050301090605010e06060a020d180321020c040b13090f0804080703150204 84
    0x40c40042403003201500001071001c0400802d50502d801000c0c0c03042a81840d0076034024400725a1480e0038060410200305800240150300d200cc80e41c0d518542d520b59850369140001840c590321040b03094410b6400300090004101c00505c240040c607510380100241141241c500743c014400e84400081041c0007081003e141c0d50042d103140a6181042c05165465002400490704801c0400c4070345440140e00f4003460141c449400089070018402d010412015110b0b08016865003028400041098000180c00c0785807909482c0985ca0b950b90101540082501e03500058165003880d07400020044c090740a04c2c10313079600e000030241c1500c880c01032104901030000900090f0b4002165800c55034000e1500103156594400340c440040c0c3c590340ca040d04129584a0800b0803080017881005031f03078042c03101da456110305490412421006000048003400401040c4c2113156a5000010038840c8038041e42a030a07030002540b80e51541d07a2424035585d072249200a80302a030b1220058200c40d031080c02150210b64 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 479753758 1250 479752508 479752517
    0x151902070503090418020306040f0b0709080c1e0d0c0f060201050c0a1b02060a020a03120c02071202040f1514030102070b0a2a02010605030c030f0607142703010b0907 73
    0x20b900000d1200400c0d40d0800f0405d00e48007805d003440140c2d02042200e02c81da20408040d207000d0a2840d20003c3e000e8041e00050501030b0700b0000744410302000901860012003210004105031f81407100114040359078a00a4008546940700014810214202e4080f03d40040105099559030441207003280d20554812070440c00c00c02010500c644a0030406c0030055488182c86003514840d8001450340d4028802c0300c0c09038105070905020716410000e0104803007581d0f44203102d176440c090b1000b92190064050103646502859514083d520b80d42e102c040e180140541c204003a41c0035600e82243c588603840b40e0900c8800d84242c07a422420103000b6512099808803e1080d9502c0300307210708004c1d0100b95002005480580b03068010501040240f0941400f00c1c1c000040c0c039410041031508140c1100300341c0d8002e034000c403548420b9950004055912801514103400d45984a242d1600b061268001e42094110b000304440c0780d004465103202d41c03048040b0002c00103a40c410b41440040c10040720b0120108 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 479755008 1250 479753758 479753767
    0xd030e0d05030d050a090b1e0711071205011401060327020102010e10060f0e13030807090314030909071d011b08070501050f09030423060408151902070503 68
    0x900304801001845407080080c1d81c1489049280b071012140121032072016146c0303d402010620010605107a08a41406540300c644c084a1175640141d0b0740103854642000224040d180c8021001d00503140903040044607030b500f5030740500b0403070f000e00418595030101c11003000002170014003e1180d000e1840321458104e1899032910700028003503681d10f00c141c0c10743d500c60820300c1d07010400340160310509400e40400034615061119201210909400c4541220220780501030700303181290342c3d607a543d503240c5010403155440300ba0031200e4650503800207240a070328505100c4000c0020015001100081c1d580e00f00c0c1d43d45050003103800c0c000d600701c1c9030104800180301041552082880247c44985404200c00303070101703036950380c2d1a030788550004d4030165541c00a101841d000d105582ea0001402c0d0000d50030a424441144560115510b174600d40d00c410121513610307902c0b00820f4400420079401075403002c468207256aa060a42200c100302d0b203c0c80e580400032417811500c00e94060300d03001001541030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 479756258 1250 479755008 479755037
    0x71a040512030a172202040209311a0906010306030b0f250e010f03020f0d05010f0611060a1806050a020a0201060801020a0c031808010c0207151d09100e13050c0d03 72
    0x7552014051fa000740c0c0801007101907807034001c00664518007001c060020483c0c4450316207040d0408119400c04075042c001c144040501241d0308904008003103c5030f109036290240180e004180c02d50000703001820301d0080200c8507544064035481aa42c440a1034400e0109000b0580c0c51190742a4030404a2910f8806c0d89a035442030001c05801c02003030800500d800c010a0340c40b0800e40200381000c0c00f640d2240014040f41900c084944020700007400c0caa80008206080c4a8603180002c00b00c0840e00d68a0b151064240c1c812040444010703040b51007008282006004800030794000035890000d5800c0140004020005200316103020809581d200307000903243ea000c030ba0000010a03045443c8180d4034010840c4102841f85103440c0d411030300242400d91030918810050380207a4004824000c40841800503030410514808031142c1c11200b81d10340e60b03a10307440018011407a40000c4240000c4274204002142000d521119880c00b07402220356100c10700d41042401b407d0403000400044400405021 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 479757508 1250 479756258 479756311
    0x30a0506030d080a150e0c0705010f050c030c03040f061d3f0f04240305010305071a0c0d1d0901030c090902060c060c0703110f071a040512030a17 64
    0x119001c41d07409946040d83d844024503100c10f0f069400c00300c0100c0020750780c410400c003403062f442020045003040c49145000c2c1030501060000500c088441c140000c0000d0821000c045031a07440355015200b00001c1805044d80c1e00e88241030548000640f01d04020049000320f10100600a41e403c2d00520344002c27010825544558500e04505441070310a1104014500708a0050301c040c007480c000890704240358805613032101d0040d1814006240c541401880070400101d0315000343c4000c5a802c40d0504240214aa11380c810034500f15124024034441490f219400a01060b50070000d10000610f221104100a00300b00280310040c00746850365030401840120742c2040060b00e00090a0780c0c00d242264507440e00b081c0341150040c00402d4006401000c00d504100e008500310f070400020300d210882d099034144d031004075010300e2080c004060f03603410020b5500700403600a48400341010150617090001507a89030003180c0058041029110804018402c080d42c6500c24503142c1810605003909000441 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 479758758 1250 479757508 479757521
    0xb06030417161505070201050c0301080c0105030c040e0a05040302100e0618070e09010b190e070c020a260111130b0c0109080301080607030c0305150f0d0b0705030a0506030d080a 78
    0x20740d038a08203080b040880c007000b0070f00c80302080d82a40401d152405003c000d00311140102a0140d001d018170050280c0407000540406145080c2082c40d41ea8980402006d02c40c000e5502c204811500f00c010009890341c260010342c041c1e4820b40882e44400380e507374152001d40750001c15905c4142d00200005805903080300d10080761040c80f030103a9883c25151003061102d110308640e00d044582d114003480c6507a042100f289035014400ba100d9194407030400c07041c416441000b6000d03600b0000c0929520042d5074a0014500c003c1c403140014a45201c1513001d140345592204503041c449518103aa403035100e003012000c40720880200c6d80003046550910907000309170381285204407046c1d035031181c880002621900095000e06181e4000308407915111100809499164803203070304041c02c1500340450000f4000612041c64012100810040401008102502200407001d0018004541400300d0381d80c10600840c0103c00c8214203021554400092694800b944095880003840900005000b0703401d50740f042 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 479760008 1250 479758758 479758777
    0x402071104020c0a030206010608190507032d0f020f030f15031005062e0e060906070605010303080f04020a0b0d09140304050111011401120201021f020405040b06030417 74
    0x100d9030030030304004034040f60094a40c981d0349a01a690081c180340e01081420300420151404111b28900030385c0059910401c1c2c1504841c450f12200403841c02406500301100c142e03940780e0320a01d800050194032032044c0141d4030b41020a880c00524204c00600d5008540078441ca000d120340c6141c9034511019030050300100045030401d5980031500c01c0340da00f0b00012034580d00c3d025010036241401e004200ba030803540606100c01c41c0e1000b80c05035404085080d03c443c000c1d10f90400790f580300d100c000864514810114180c0d4480b20020304e81040120940c4580c0c140c9009681d404070580c2c5c2c0c002456601d001c25100a54040c40c100010882c420002000780800c20101d08003107a201074694a07012075000b0900e0000c803d400c045414070545d6880881c0c07001d01c505c918000c0c06080c0807001c05110289042c050200820905c900e00415a4000c10141c440f01300c4564460454080385500390000350854000c0d0b80c400c03401d050a03901941f4080041e603001d55044009022100ea068900018982c40744044 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 479761258 1250 479760008 479760023
    0x9231308070b071412010302090c0c01020c0706110a0b0115030609020c0c031204140d0c0305030f030a0b010302040501022a10050705010b0a0e04030f021018020a091a040207 76
    0x2150015101101400c4040c1c0309185560490820b02c50240204511481c90007401c032040c44a00400054400c8041c11660140e5807000d894540044203030081c803a0940e0404150300004281d50f001c040001c590040f15042d60343c0c4024201c841210584444803c40090901140c2d0b400600801000362243c40c1c040f015030900003031203035448411500b0380e007080c800048207820004001070541000c0c8a204a44004828018901030410200343c420b0441c1b0195180107059102c001c00c10480703501282c03c061038000048130f07112100c104500a240d40111500d10141d400d0400222140d4064000e031026144160054460380030110040c19800d0050b0107030a00001600c860700d0701a80700c612140c0e14a01032562480c2d0795125600709a800e69031846c0c4218012149424104000341000030000d4006a2501c0c02c4000d144020600300d02d0b00011000d40002a0301e0300d41112144021020184940c1c2c0c0b0a41e115080640d5400340c5070200c481d41c944443c031800003100300e41c0c07162801d5130083c000305114070b08 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 479762508 1250 479761258 479761291
    0x90e031201090c0e0a0602010b090121030c0f1a0115180509130c141e0102030901050d020c010507080915070509060d020f0a230406020c0d02030f0a0602130923 70
    0x1840f088001c6e4891030260750740f941641010308050006c0350151049810403402124601b003400b4222440010103010002c1401a0604000091001740c0400740c205400781c00d015220550120201030038801c500072004291076010b0844c0c028560b85040441c2000040d04882c034080034800300c5040149020f41409950310b154001442111400024042d01081c080814802c2800c5c80980da5903458003021003ca600c0207141d483c2e074000b0031034540030020710380745440d00380083c60440a40560304450780d41e5402d2008001980d039002d60b07101d108829441c22240c01e9101d081581c402054160b508100043c07003004403035550b0604170b00401644062010041c40d00e040061407142607005007501500040c0f103842e113070842000036000003060408004409150a00c0c092000e0350b1202c6403040540501c0742d8007801c20179950705201d00c8400744e1400040d01d0300134400e46410f400075030140452991480481001080800552185200c3c0e0802c030148401d807402b10480020342254004c0c8410309055101c0c0e0f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 479763758 1250 479762508 479762537
    0xc0d030504050a02100e0d06050901180804140a03060609090209060105090109060f1103120412020313061b0b04110306010909050723030d0207060e270411100504090e031201090c 78
    0xd00c0b00e02d00311701230600002c1034244900c2160070765400c0074030f124040310024000c2c404102d40b0022501124495034030f81448004007408542000f2041d40007900711032030a903000030140f45039001030340340c43d108035200b2100d941c80b0744c01036815002e110341440c00545030682c00c1c0310741c40c018841022501c0c4a410112201d1101c4000a49103600410340098840d004138207000c10840a4038a43c00041c140340051410601520b00c075600e410010b10581e0108018002074141800f40304d6030091403103800170b10302200341c075007414070001c05444500418001d109074400000e55491034132600c47c101d1380c000054403d151070200740420300c0c60119100740d540041c200c805a40f582d801c10003848846655005400001e00d0610050914030449607130902402084a0810400f0407005000325088402c0b07259040545881c00e1410000060075420f82d00401756100742610032341c00c42d001c1c0044071021002070050080b01400580c0341d00400c103050395005040c40041c0010303401d68100000115041c54403009856010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 479765008 1250 479763758 479763769
    0x6050601020f0307110a060203042304181211010c020c1e09131208012607030803100315060e27030301240c0201021002070c030204110c0d030504050a02100e 69
    0x80c404580302401e6081791545400c28071609030040813680003640c107140c070780461202c03d10101c111040441101c0c0a2003403159499a1100e5443c0f404040035200034201d0745030068840c01c42e14042408070714010151000e0038814001c101d040c6450754080e00703107021603005105400e41031020a00d101d000900c40c600b4603032298041c40b485035140450698018160703080c800e5403040841c5810302000a6500140001000d00c051014200c508051080030b01c1c52200030541800700b150401801d0b0f401c0001400313507200d0005070390419207000341a01800200251700350803c4030800e101e140c0110f0114800542e09907100e184c0d10007910f00c18820070484500000400d41541d009030481c3c001c040c0030b041460003600d52858210481407860415a42c141507a40010359101d40d08041401103a8000540e401080744c0c00c1c0e20800155405002848483ca01e190b480740e042d0070003010b8541c98400d10603040782d285c0c0709000341303030040c1e8004000d03100da0b45e415003e01c00e4100000f0040002d00c00030301a03001868544 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 479766258 1250 479765008 479765017
    0x1116060e0f150706061d040b0f07031b0305060a060c050a2d061a010c030206010504110d110406030507050a05070204020904061707061e050d0f09021908060a0203010305030706050601020f03 83
    0x30781d00083c50600700442d00c0d806e003441c01c0c0001400071111041000040a00691941148040841416075900c8100840c0900b0b518849004812422a6440b00e40b5070160007260084108543c91402c00ea1921022070342a19446406050b5500004400010408811102640c18846426000300c0d241c91400300869105020080750402ea50700b8410304040e5440ca120740c0001c00910f0700c0746407600c5648009540b400e06000d144e2041e03950b9080100c21030750740021660100c502c00800d005800b0500342c110001d81041c41040c000c06c9c00c000004030054424411903410500c0c58984900f4045d00341c090000035086a8200c03500170390348103400300380e901d001e4659420034035031800280318607814400c004201d070341c440010b108540c0000c004850b04941103415076001c8600e221001900744101e9001c0340c0035202e07441001c0e412220365080c02e001121914448000d0380c8400c2d003211019200d541d102800c82c07101340300c0070740141c0040c054603000840c503801c13282c0c01840502c1100c16140541c8440d6007550711 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 479767508 1250 479766258 479766263
    0xa020c030f0d030b0603060603040303050c0d1a03070e0c0304030302070f0606090f270b0a0b061c050c03070903060504050c0a0f05040501120807030f120204061116060e0f1507 77
    0x1c1841c80d24a2158140912544c4070000d540e540c2c10360600781702054035408041c00050601d1744407000101c4400b4200c040d24411499804188400003d03180740d40c1e920700d154840c0340c0c0240510040071449080480600c2d000d140b0040c0c603585140d4903a00c0880003504816412126141d00f032540b1000305905009250180100950014110301700d100c4c030701c1c1162603400c1c22500001c40311822030004403c030741c14015042d0300410070b41102d5031006150350080411201c000e912001c00310301c0c1d1a0fa1513882c40b92009410341a42c0400c01c64445c00080200d40c0000c0728140005840514148002141604810b801ca03210300300301d480600321200043d92280d5260002c03410b040c114903003000545060300544c0d00410702081840105111600c030750401e80304044006d000d1004003111914110b215485400c80d01115841c115100d54546c1002801c4000100600606110f00742180c0001040b04a0460031905107031105550441e0b140c050004407420701141540c0184c00209003852800c0c64002041300341e1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 479768758 1250 479767508 479767513
    0x10060804141f051e0105091f12030e0a140907050c1903030c02010b06070b060f0109120302060402152d070602040b070506010f031a0a0b06070606030c050102031e0a020c030f 76
    0x14050102180d8103a04914401280150400400c0303140c95200b5810340284006841644841c400c0b2040c6235a1200da901401ca44e40c0c0f00720f001340034154040404500200120790890101e6542d01c00112040003c20f81c1d81d6009000b4404200514000c030300420100c0201c90130760340380c140d403101840840200718a0a5000c0382d150422058056428440e1100d070600c2111054104510b640390115400750040c2124004d0440c548a80b02aa0040507000c0c020003c1130420302c481d010301d180c0291565000c0e54100c0c01101003040e1280d4041d0301c141641d000d510420704030f000e0150001d0b40d560899440b801d08400407041000420003082d107900003000139186541301503560b4503107480c0061611005074402c80c082e0a03504400d0000a070303c40341c56044140c202140c0b461580f1a03110440040c4158421a54409000504c42082014603001f0340122400759118400e03c558500c01643c403445422001400d90400c3c80012841e003461201501c444440c9104441e00041c020b070200389804404c1801e0316107075 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 479770008 1250 479768758 479768761
    0x70306090e0a120f140c0c030303072c01120c200106030c06110304032012010c030b01030b030c04180204110d0605012c0d0507150810060804141f05 65
    0x10501e500b4004001c2c03494000140360544c1d00081400c0c00803108980480c00004e4000c034251820480303100304490050507207a581c10700d00d00c068190f50314407801590401d414400c001c20381e080d001c3d0720460b4010684034180f403031a0b0030203001d00411007600c0307007402d02050b400da44603010f4201d0910701510100f0b10000500c5030460034040707543c1110358000820040c025424131a0002c0101c2a07608999110703614410805482d025540306400345400f1a03041000c140d8104d1414005400819036884903072010040300e010345d00114140d4440d0800709405600546a000c1c841c20705500446100c0e4001c041400e440d00980e0004056802a082c01c0380006808105244184801e02c1000300500003424540007580340619202540d84841e40503941c801c0c0105110516915546600742c41c0030f41c40f45c10340e41110b46444240c06101c485148403030000b881c0c0c00001c1c8070007004d44404806c1c0c030301c0d42d190486556101d640b4a010b020030900119101d000e145030884e801c071a1b860f200e094a04041c200820319 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 479771258 1250 479770008 479770013
    0x1909050f031b0a050a0f080408030307050d14010608190906090b010f060e09010303050d0213150906050405030a0b070215131104090b0a0209061219061208040b03070306090e0a 77
    0xc0d40382e04100800d0304040340c001c00054000451a0030150701060031403052259081081050056030300150060200101300031409511100500c500e00b102d1900b0060340200c41580311060f01d003402800040b4500390080380c0f41c0c05004030310805080003030748041a1030580e50707078400988110071003c4801480c214014450a83c007110111302070300c3c41c0d140c00550040c80c4000070314408410b2001070140007000454a4509045404540b02d95900813a030000030380d0b842040c040c11700c0d081410200000c1103e40b0104009109404540495200400820110760261180c08240c000038207407000b90710800d010404481094403402d4414014809034240c0380c4001d0400d105c40220b0070306440d00c5245803040c408001a60f0b0829180c208084940050700d42d80d1340f82c003013002403180e0354840404008440802401280150401ca9080a200302c14413461f90303600005907410b440588000c10003d8240400d11450440c40081c43c0c0c0604989000700c1c066035540c03100d400301c03401180b04c001c00d030b00981c102406 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 479772508 1250 479771258 479771287
    0xc12070b10120f061d0a0f050105010504020a09150509132007030f08060f0604180606031e0908070212100b0a14060d020c06130303231909050f03 64
    0x800030041d1180300c10002d07545406680c0e648010040c841a0382d100c01c1c280c10039a841c50881c2c1c2c05034640c21101ca40666061003000710760700781c1c411507056007001d00120300c500b07090095035031014050310780620480c1410a03043c0503400d0321020100304203044c4280100e0742d035000b00440c0281c102c2e04d0006141c401360740030001e82c400303001074030700412604000c1c120000354042c5424602c20064508a042900c403a000101507014062940703030302184c041400b103281c1a807000d0800c80c040c4128020000c4940d01e071000c2d0141c4111800d810742c2e02c6400c075000b41100b0303e1034002041d0342d03110342d0080c0e01e4070005500240743c010704000551240d51060a4105100340d16101b100c1c0c55400881e500d00449240420b003031031102c00c0d03182c80c070b000b454042100d031208042c6030140c5003002d100c0c0d029a131061414107401000c07880c0c500015030010b130421000c2c41ca00c100c030228252801da900a86403203030303036503c00c40d4996458200d041c0000302c0780d07505581d0003c50014010203548002c46800396596480000000c0c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 479773758 1250 479772508 479772541
    0x71709060403140915300103020d150b0301020406050a022415010c05030d050712050c04090c1e051c050606180307090e0c010807020d0e060c12070b 65
    0x2845640300d001803002194109200e40c07003007031403418000d81d100603400105040c18110b49003400c8401c0c000c94407101c0c10380c6202540c8044200140465180b01c108030350090600001e20001c0d4000e800c1007240800f1480e441c0e0708068104c4d4844002c6030700001c940101e422640140c0c0900c0000704081111007446078184050b03101c0b880b25820f2000009068402d02c1d0b0014400b900080032404502d02c00e500d1640101982c5d0381150700a0140c03a15200805244809050200ca00da0005000c1c000e051204500b14425036000d60794481c08241080d0510b64200c000708203800d2010700b0301003a100210352a4400048be0020301e80c040e596151118460481c0d0b102444100c04125285420881002440c2c0c9455003a40d668651000c140b4207600c0182012034200170312034110880b0141880340c0d009080d100082d15540b100d4003079a5403901d41d50ba00320203d850f0f00c1c50702002000103003030703200d801000d15100c009450190041d1054409100d5208138519099110000031510041c00e40104030f4140c14560025 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 479775008 1250 479773758 479773771
    0x13050601061d010c03022a040f0f0b010503090c04202a12031909020913020108060109150c020325180c0801060503090102121e0603120703140c060717 66
    0x204a42c44545d40c001c2d48500110038820314550a8803004095022841d40c10468103c0160013085041c0030000d03400c0c0a414200c0289000ca0300741251907801e54030507001c503032207240070700c001c1c151420400080101070400d402c11503a0250b4100c441c081285000401401540500d5801c0071031032051240280e074540d001404e0044c281c000307040d440404200d107000c59030300c407540c0b032504d41c08a030300d01042d0f50090010940203908003e0311030400034101d0300308201c0d8841ca4000d03207507500c1d540da401e401114501054081e1003040170310048072002080c0a0f034081901e0902c0142a80d112030b0340302440c0c5941a00e98021040540002d001c00c0010b0005001c2c0070500031003088040c820b171034002c03030068252070f030620542041090000c0061070000080d81a911800f800d0611030000e420040442c1481d100400c404880c6000e1010200349107180001d01420480307102c41045051040c00d0b101601d0501d803071030800d64580001c000e840415030092000900c034614070740f2081c034030320003085801807004030080c040f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 479776258 1250 479775008 479775017
    0x9010903020f120d0e03040f03080319050412030203061302031003230c10090306090602120a0c08061909050403020a051203071202090d0b0a05060f01020a0b0f13050601061d01 77
    0xc051014603e0740481c2d80403c1e040901060700e0b2601c241c554030b188503d501c42d041c0707010504400720400007440c00a5014002c2e040002c024400104110003c0311420307140202080c29010289520b00e010390069940f140000388818200e40c0700b050000241c0c1d100b02e0f601c804d9480140300500c10040c481c4002c468071a800340940724954800c40741950707640c0c040803100307200e5840184072036262403180350700c000916401101403280e407501c2e01e4007901a4101c045103040ca81c070f00714000b4140380c00078400c00654070b90350b40e101502500c1c4c1105000c0f00c1103003550135500203040203074007042c01051409420b0042d41b2a41c0201282641410418100b00345164184036480040080c443d0655020b00a80c1e25113000c880700503038030042800007a1071082d0383e58004100d4104030080040320a034640c0315501c10310b01550007160760b0a001c0c2c01240c490107004401003c02c3d030301c0c00208445042d10907070341703a000d218013141c02200c0e401a00c519140c10401d0348440c0c005040041883e0700b810458500e1420204207080 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 479777508 1250 479776258 479776273
    0x402090106030504080d0c09090605010e1810050d0c03050c01090e04021c1b0f05060906070b0901021b010507030b1e01080c040504180b061801121a09010903020f 71
    0x42008406119040030182c80d03c1c013040c14003400d901102c0224400c24801c1100410406002c5d29044c0240305032009245044400a0154000d59803210303e564010131003205030340146599080180064503905070030200e15404a00d60301e03140c0c00e80c06202e000f0061010110b140d40380841c075041c1c503401e005040041c4000200902803143e040160850790403588901d40540485202440610000d006444030200a05509004500c00d59103410307900c0040e00d1503016520380040c07200031320820f45034541240d007c100942c0841ca2000750260081c02d8240054a004c1910b00d075030304480008030081c265651f45405000b0560341500c60105203100689003455103204d05c9070305003184080306203a141400503103800501040c141500300c0340540fa00910411a443d062040c5401e189a441812104c00c4118008a0428a4010f600c404500c214100d00c8801d43c0c05c05244030f5894054101c100c9103410001010210880c1c1d4000840c8507016907000010500001d0400070310b003248010b11020150094403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 479778758 1250 479777508 479777513
    0x13020405090109020d181214040b09010509030a05070b031005030a0f030c0303140115020f0105150d06020705060c12070306080c120a0c0305150705161104091b061704 73
    0x49141d41114070308100183c0362048916040041c003038a441000800b081c40000c2800c10010301c1c906692000b00e03a0b200c001c6a0085180000f09204030300a4140900302400441d0329503104000a103001407000d0b084d2090001079a03246454030103070350002080c1b40c002100b049122500440341e400100740480060400e02c43c07589030b84445420301d100c0a02044103017200001418080e42041200410361020701101d50381d00c00f016044580c2c820307092030040c094507280d4905c08a0500400c2e0040000c1c20360050f520040100300417004041420498101c1e40034003007c404501c00384291441002000103096448084501d00003034464000c002e041414500f0321700340180b05c400950500351220645d0014020031415062910701000c0860042000d0100e01002c0304002001c00c030890b02c903221504e51026a00d230300e4004d0300c2d58000c003070031140610000c5c02070f04045048100c140b8040c0d070010340001410b1449840b130809240d86103803103000101445404100440d03011000c0c410120840f110750009080c0ba5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 479780008 1250 479778758 479778769
    0x40b0f0c161118041112010e1e0721020a170d030b06091c0506070816030203100503060a150605040311120c09070e1806060706050712090c030213020405 67
    0x3100302510b0082d03040e455403200c2d1180c8a210b403094080554000d9540381614021074100103002807180100c03d250a541034501050140410205400703000d868020845040781a141e070441804000520414400140a400f1241d488803e21000b20700c2103003601c140c1c0103006440300c80d5072003e01495046031040040d108e011548200c1240c25240125080003464000b0740340d800f903841e8065009400d410030069054581d04500551442602511074554901205030b800000c2103c3d00170b203014074514042a0305110f03600440c3d101c404c41003040125511500482e10b0140105d403240b080b0f95481409102245030640010020422407401c0d9140c2800c503031b518940080403034041c1c1e0080018140e10356241d0801d2140d04885038003c2c12110161901c0b400c005d04102268060758020340c41040200505140781181c54403038400642824903000c41079990400400c002800c00b41005000e41d10f070100a540c0d4010035415600034501c02d025503055004114002c50f0403030003d07041034070400040104d900d80 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 479781258 1250 479780008 479780047
    0x4030201060524030f040311030d230f01090504050715050903062a090301020c01022106030604020108160e03060106170a090c03170906041d0a05150f030f0105040b0f0c 74
    0x1074145c3d03402d854035189030031b40700080740d0101d0480078040800c00e4042030585910001191400340c003406005004204c00d4040010262007507048818100c0040c417041803140c04c181c0d00940300c1c00884a07900d54550819543c0001106c03128001800051104510328003002400d40042071039107410700501b001000d40c9049041181071000041d808550b0040c16642981070700c0314108810020340d038a805c2803841100900050901c55403040288000c00c02c01d060004081c0d01c62503041e12007507030360f03211850041310700e4024600f40d800300216400f00d48510740b020b200540c002c124a84a443e40950078400c450480d42c402807a03490520b01d48040640031402010301401129003140103684002d90301d00c403a81c5a44154000d040e0419000240051681e10000040150f01c2c0c950081c0503168660b2040346080da6400c0e50107040314440315800310502d15000c40504080d400c0201151403a001000c102400d40701c0c11181515996408003c1014070014081c000d0f62007032803c03070300c285000d0b008001c0203401c3c2d00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 479782508 1250 479781258 479781271
    0xc021501140126061e030607030203040f12080a060801180215040801051e09011802040b010201091b080c0306131101030b13050403030c0504180c0302120403020106052403 75
    0x10220280c5080d41d000714000d68040c003500011542ca50300b0021500180b1800303440050196070f000ca007500c0031785e15400c2185642d83c4000d0207000c0320303124088101d0180d08003800c1941c117034210040c0d07800000c00c440c03102c50b203100090302d61000c40c0c03406d44802c0044030302c0f5900a500070390501c1c104003e41700180e000f0307851207541180c04402d01c24104d603c10120b0b000715000800340f0741c07820301070118880c04501d120079040b506c2e180407001503a58a168a00fa10702a83e81c04c102821590003841c010325094001420200062000244000f003c2c2c49030070192440d140a6640903a9140083c8008601031008018981c0b0981c01800c003801d00101600388640d0ba0039018115800003140e02c4810380c440d40104006c00401401c9274101036910710b0400082a0945088011074a49090200c04174001c10580741100c040f0700c400d101da202c0d014490b0001e0040b040240040540c200804028440320f0100d03680102d0281d400010350500b031800b84200c07205007a0101c441c00e0400254201c03008400780840b40d0040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 479783758 1250 479782508 479782529
    0x62004090507091a0706050c04081009060b04060905090708010207080304030302131a03090705120709050a060302091f0e060619180602010b091f0501080417030711010c021501 77
    0x6454540403a10f8101581000d24070601e030008107080c240c0100c02400005008000401c050344030000200c00c80d2241c0c0c0b041c005a0f41010381002c1c0d0a48050744003049285c015000410721003802d90002e42101e8190b0442240340d981d500c18007017400b0342000840c0c041d141d090021807800d96961503000c501e002c0140b00504241c2c000400008154032001b00c2801070071a0000c0001c0c00e0101e1603626a150011561002c592296030000903003851304401e40107403400d542b00900060781c1058080c9020702401040711100603200c400000050300c030121002d00c655100380c00ca0b603030108060603187d841111944060030165000040c010591b95170f8044070900303840c0e4404840ca5940d9207205982d014244d0300c80a40e54154000c0c0020415010b4000c1c90780c1400444146106680350001c40d0410720803e03810b41e9605103041c1091200d035000e0000d40d90020b004401c002c0340e0030092021110a0350040701c1000000e9200381c0e14015581003409100628960741c0084e201c4503192030b00541c5011014480e591801 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 479785008 1250 479783758 479783761
    0xc0322030528080f09090709050a150e031606080717130f17030a0606050301030515060a081006050114070f060f02090d0c14150f0a03020408100501030620040905 71
    0x1e0340601050b41c40c2541c0104810380380c003c2207101d8903850304481500f80c0074401400029130351314440c2e1580c1c01900c074020030004041c0d0400415480e1020003540c1102400345165a03c2c2c40d03039404100907110085814801c500540c2052030040c85440050488411b00c0360361001d858400c000020030590100c8103258148920070346017400300c01c4950480015184030001101002280903a6005510507411000e0a0252641d100300840d00c1d44824440a0038981055040040030f41c0d1081440d0703001f4070018150010923440d0b00c0803a0a0403110071580c0c4003d681e8880820555800c041c00200d801e80100170941400300640319240d02e4078050030700421403584c2e1841c900881e03a02c0e5040d10b03203440000d00314505c9210a4a403850000443d8055010000e41d10044c00420b40781c0b160b994207c801d100a010350410007441c032070074100d400042d0060181034003440040707120102040500c190700900b02c80420154954100030b0101c0340d0020342c800030307602c03882207904030480f0319400c032004c58404a0f80012603 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 479786258 1250 479785008 479785063
    0xb0a0f030b09040303270807020616050304170c060f0d2c0a020405131509031403042001050a05041404020903070f06031103070f11010609020c03220305 67
    0xa0019010255002e5000c6041c07000f030640c140e100201d080c25900c05002100d1500160611007854040004c140000412080006041070130242482c0003140740320000840d100c1d600c40303045410075044001c1d220010307040e80c1c4404808000d48414540299a92498030034a9043c1413402d110340801041107545410001030840c6d10100050321000000099a06060581d2109a04c1d01b00290044c1d101d44e0800c408251403030b0402d883d40c4025540000070001580e6440c0e0382c00f0203020380a03025024401c035407806141280303081005501c200c0c07003401d00109002115502c0e000441140810742e040060a01024120307a400c0800c4409507851850b074041030840344070014019204800a064050003802d030700040e02c850174012401640c1c1151000d0200e80400e0001c04200d00080b1007120001c0c036812900b50145000b1050840c1704084000040341817a00e50000e10300742d0b400303800350300f03000e50001800c600d0144140761001d12480c0b604500e07030402e519580381c5603510803a01700c3d80c400b00d031002c0345607400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 479787508 1250 479786258 479786261
    0x4050c1c110a3c091508220b10051c0201050406050d020405040c030b03060c090a090f0207050105011412010908030a11120108060406061415090406081e160b0a0f03 72
    0x78200041101e03d1804031070070301440b4103000000c2c400d0081164014045001a500d0f400c1c8514158182da644850f81d0f00c040c0d40c01c059000f41010030300c0d40c84044006a010a0200307241034411401e00b0780303404026240800b0710400c4c101680711050010b01c11800540140c1e4884c0466044030802d2504c99100c00c02024114020b01c101d5101c19445840d09600742c84072034160304018840303501142036585e581d0722035102580030b1041c0142c203a400300400c0300900c11204103074411003000d20080001400c00c4d0700c81d03681d1307801c448082e00012120310ba1005280c51518110f04481c02e42a491b50082c0f06854050743c600620b4040680440701442d101c2c0000b00380c203041038040d600844500030219045580d10750740c0c0750b1502d200ba582603902c142001400700f0034104d500004003a400010f8809043c00840a22003203d1750000d021030396100c9d80360640050009401c000c10030f90780c0d015105040f602c1d40c240340028901008580401d2042400c00410040541e490007079404c10502c078102100705003a412001c90 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 479788758 1250 479787508 479787557
    0x605091f1407050d0f08090c060a211406040b031b22060f0b0f090f0f0301020f0d050a0902030a121e02030a1403061011010b04050c1c110a 61
    0x35009072010503904144003000403801c50350707802030720b48421034152403100301e0303940c2011601c0c1907140e0b000c00301e090342c0c6040844c01848000b0161405099603041c0c103294890301d41130300382404d07620707502c2c0c030950b124941040c0c1c41b071358004500b00c0d020030040c00020040798803941030000300c2d11040000e2150b40c29544410401e12291000541c82403d5035040300c404100a0542d80242000c112030100045050056401211003c0091000d800e0508090a0410242d4407801031155082001c9854917841a2030034005881140d0400480c540c0325410414540101d80e4020201c600ca54200b914150158501080c20080745404c42d05102d04400c01141c1031741d1812050031903500b014072905d442102c036075020000d4822524244d9440441441d0810130030210300054920075448139066403080601c134001c0501910b5104004000300d400d07860f90300040c08498045802541c0240c0002e8180210340c200a406c50340c0c441e0300c4002300300001c45208100c4031401000d070103000f80000601921803180e1880d4004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 479790008 1250 479788758 479788787
    0x61d0a060c140f1501090606020604031403070e03010e21040f0308070f020603070f020c120304090c030b0301051f0801020406080f041104050405070513050c3001060503100605091f 79
    0xa98100c15032100c0d5100d030304d01c240700f101d901529003140420310502c003203000c0e40a40d4140d5a414640c00706040300c04016440078042600340003400031792400d685c5082c01340e40400040c5402802c3c200c002d90002104003d03103424819a6280100310501010307400c400d8100950303402c1068183c403031031186020200e40c00b0010003e58006c201104210000d0392144038460710070026401c0c0e07900e4205010a11241000000204049800620080c062074005600646200f200d51901203805011000030a085450503940301010000d40c05d031140e40314081c0b4220800a01c1008021840d2501d800340091299101606910845140314045024400440c44181c034658005004100d2410f143c60a103075548607a01c115030103003c80e00031100d8507071180d1058911400300c0c003c40c1840c100c0400c0005007800e424001e440c80c503001c00c581301d00c00200300740e440740d02034141c0c1c1d15003076a0790030040404092464241d100c038080000130403400c031041c1c031b40a440d000025500c10034a000002c13918026542600101c460 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 479791258 1250 479790008 479790013
    0x6040c030609170c0102090a080606010c02091f03120807110c01200f0c0108090304031707050102070c080c1c1a0c0f0a2106080a0822061d0a060c140f 66
    0x10080049065006206866042310491441070781e900c401a10f50300700700e8226010506a1a0f03400c09801c2100510780c2c8103540c1501545103100311062801240c016800c1603612043c1e0400441c2482e4126801d0794100002e41001c07204030000e030b0126580c4501c04100b440c10002c130001042c034101002c0d189904403910b4602a940c0042c1c80d112600c0e070f0380202020340b90020703407040e001c40c0764070402108640c1620f81180f0742d20741c9034003050b00005084d40300078400c460965081003a800801c411750760410152078540c2c094003501c0350140810080070100c410840421b00da2040043c00a06c06085c013071040c038085c0d80c6444541e0342d00551a012405000e0000d2404107001416404907940100b5079a9080b40d00c2007441450724908a4840890300c2e03501038155150700846011002c20515005801c1016002090310000d6000594243c1c2c100c0c840c0d40004081003030010b008050b5010324201046013901070f142c0380c1400c0c3c9000b03001000c0d469401c5c006803821303841f40c90790403100c0c20038030101105a0b0355208 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 479792508 1250 479791258 479791267
    0x903120a0f08010f0f03061a040504031106011a09040f0f020301060e01030615080f1f0e040201030e1614300d020109080a03420806040c03060917 64
    0x502800300c1d0320030307428a0300003040d69002288208000c3c0b0964140c58007100a03044150840e42c50034010104060725810410340d200607821159124040e01d8802d0380b20f503480380604001092900c2c60024180c106102c611545841001102083c4041d41c2840c0000c070b03000f15489810712100001490312004080c10180008008038050790003403011181c17418203070307001c00c11141e556034800f0035042645980341c006803900c40491140b40d14891115002541c40e060040038103040311081502004071360003104480c5d044070800083d580c06106141c65464014080e000790760780c031000c01e070010b80c4034000c0c0e542e403101d0f03886403411603103d400c8c4c01480880f4145c240010510800038000b518181300a2800c103034491703041c0103421184180a056111548600d003641000d2030260117401800b82c0143c0814485140ba040d044c1c001d0ba88081c20380d1030103901601480544030751070704d462002e045400808095121405010014040040c240122608042c001640e4034581c50304004407000c02840c82050302000c01c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 479793758 1250 479792508 479792527
    0x20f010c020d0b161d0f01110109051c0e03060f09160909060c110307240504140d0e0f090a020408070b0903070e040f14010204080f0102040e0f1b090312 67
    0x34090060600710390f000e5800c0c0307025400300c45c095000008010b2116039403603010b1280c10080030310320b55810141490240082440b03c158210344082c07006030350303913841760f1a807818480c4008102c1e0840300e490f291480302064600c0c0807079901d90014050300d0300f04041c2c40000300d1190702840440c55280c4082e40c0052803c1e9a003d000003d040841820741d885031a000c60038600c0e07030141c691400702e0f1140c200a0743c20080c01c2e40341c2ca45407a03030082d00484044019448a14000047d100d940c0c0304900c10b080c08040300400c0d00e00c491030181d80702404810701845241c4190181d0750210a02031500c4122641200340e0f8800000c84068050340d070040001d0b201d4000007280e0b0105610140078540d80a40442e01c059a5814008000e440700f0381c2c000e03000754035918021b4041104243c1d0700b00c2e0030801800261503e0358030440300b80381c840c429058070041c0e54040390a200a10140e01080c2d040b40042a4251060411100c3d52600503140a42c1000600e000120000282c40c14000f0406440144214a464170b5808 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 479795008 1250 479793758 479793773
    0x10c0203011d0c0307080a2402070f0615051e0d0c080a05060906070516060c270801050a050606090603040c0e070807030510080304050609040204180e0d1b020f010c020d 74
    0x101c20343d0f0b100b0b004807000441c81e0301c000122013240f01c1d041b412030504242c14076407000c02d00101c5000c001000390204150320109803039951401d5a54400c500000d260000d0140c1b03040c8210180d08000d12861610040340401c840d283e40c001b001c030034100d6482e070100c5a903150801d09002254011980741c01440300721001d01c000450018880c0080400361104c0f5034030780c0c00444030381c803030500030800d840d0b0b00184e0007011840c2c541c410b00d40c0d100780e401c140c3d8440000318511181c0c41035040a801c0180704891050003030000c01e008040e0000350500f42481581400d200185107030189001c01c80c02030001000080c10701081000c202d00511400500c045107040c030240044c0087c400300c3c0e04a021030308150206444800009040781200c21841c0518182801e0a04104080d400360b60350b03603442a02071001103802411900d911270b10041041c40040c01e20607410a241c14080f0003c0c002061140c41d4480c2c03003031040c1e4a858407500a0703040300d42141510302c01d401038903082800c0f0780c040e420036035960000c1c0401402 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 479796258 1250 479795008 479795023
    0xc140f070c080c15030105010804030c050f1e0d0212030403080c07080a0302030f011e060302031009052e0b040905041a040615050621090309030d0c120e0f010c0203011d 74
    0x140d801d4080c1c052100e01c0760b400ca105c2841004e001800c14400100403d211300280003400f44034009071941944411030151030805002c911a1426904113040c5950b03d50070000d4800d9240d160015045c452660318060245000041000c2c051014407000100151440e0080700c0341c0343d0703100d441640c803548140002030003500110b42c129502c20782080082110030040e0100c4801c00c00e0102c14803041410180c08074065000904105020803020101290903070b00703030048502c01d03a00044103650400780148800300f2000c551000007107590341c800083c403032012036004590682c5c10050000c2180c2d1034600d0714100403150f0911080390a1003010900c01041925040752440d040080f83c000d40e202e8640c0f003001050f20458200d000340c05481700c1020f0f61410b41c1075010f07134025900401e2301d082c5070095001ca030400c625034002d0800540742c0141031080143c90700c2140c98001946c500018420300001c04a90402100304013103040c48900b5800c40f0440d42d007500402800c0f080d02ca130707806000d0100b11000c1d584925 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 479797508 1250 479796258 479796283
    0x30b0109180f0b270c0d0c0801060b0705070902040e01060509130903031407050306030d0e03010608070303180b03010b0403020d0222020d140906010515090a06210c140f070c08 77
    0x41c50342c040c401c1a1040342a42031035813010300180040010440802a46401c2202c2c1160590584040040e04817028821003000344955412940c0c2c640c054642070b41000c14640001c10541c0c41800140145041080514155406400c2c05a83c85078a070700007403000c00c5009001024075050940110030581d154101608451800241001c607840c0c43c3c000352107030b000442c1d82e1605a840b409402170707128400d0110580ca010040c00008559031124901c0e0300740340841e0400d80110fa2602c5c40c0100c0c07040f4a001210003800c111f01d07541e04550505d52000e2151065120192240c21038803050001e6564440f24035444803003011341491145146a070600c00707508941c0040e0581071800c074445540403996003555101d401c0020240155030300f40310030000702e00d0f95940340e03000c0d01070300340480200381c1c840e080028003808082c1c43c1c00840d440f0300f5804011000540003a10484c6080000d60f0403c1500b0001d03e00c1411001c0c10155100c20403000d84900d270f40166038025202c550110b200207000320020400100250 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 479798758 1250 479797508 479797531
    0x1020706020d0b1207080c0607060b03070b190905030d050a1e091404051302040c090314070302090c07050a03111f0e121309050a0b06030a0605030c0a030b0109180f0b 73
    0x40001c0307244d4643e5002d200701b80181c1c010b82035405503071902900810030f02e4810000000c1c03181902c40800d1038070b6000e42140885190018201d240403c5040c01d01410016506d0404000c5080001080c3c8031000801141c0c03d200f40480d06425483c080c100385900c444540702070240046a480000700100d4107031003440c5440d841250581c900c0e08060140303600c0303a0505030f40c00c4004240c42d82444000e0152036503401c1040800c49003c40000c074090b0b00615000d00c5600101189401c41c010000441c001030015100035a041102c0c400103180890450300454242c2010042c1048801d559030401c0c681e00d001c815401394048940800880507846840c0303410103101100d009400c500e2a00900d44580c00b0b1402c4001b6240c4001c0201c07226540000303911000800c00071864204800125459410588140c03070b1031034980380c1c00e0000b800e040009004038841107440f01000c41c51500e030500904010b001e8555081d4651000154004800032030804031507000c1c1c40816002c469040181c54498152004156070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 479800008 1250 479798758 479798779
    0x1e2b030e090c1215060903120d0516120e0f030f040816051c020607240c0201111e0c03070c0e0601030c0f030b22060501080a15051201020706020d0b 65
    0x1100710070f0302c11888506040d03241c0780e110707050740d1403e0000c602000f560007502042844000d0f02c0138041e0340d0483d5441846913454516003020502540c030000c250020042c04007a09085980e030000142142c41070880740007a01c0106200324602301726015407807210074031002500c1c45001150800500464880e130058480b990344400c620b01c40d0120a102d441c0e030140010409100c906170b00b01a040200d8401000c5500e8000703140e90b1385200754022400f041340c40b040c0c03c034440e80c080010300070409010400d1000f00021544990b135802e4501070706141d0740e41c100080401183d012400000c5900c9a03160300b00300d03a00d540702d91500c404a180385001e0202070f00c1d400000f20794154041d0050700f034000603546581c60000b10358401100100318800b42c03e50700c2024038680d5160500f003060706400380175101c2000305010b400d1800142030680003601e120780b618502258802d110383d0b9145d107039040d00c00494907a070b2a040c17042800e0380640142000a08041c2c40041d47c1c02050103207620004e050441922a5141c5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 479801258 1250 479800008 479800021
    0x15130b1813060803031617070519140d09060e1b1f1e1206060f030c17070e0d0b01140a05040903081614030109020304020f1e2b030e09 59
    0x568041d4450310240740e0041c004510000e00440305446050390901e0b105807101010201f81d1400348081c2c07052008620002042c80c90f04408103035810005c03c1d0340c24a104c1c095040c004501151290b001c8005040c1e41e9188040100201c2d03400049000316808111188940340c12590562a40d4820246100b03214142d00071455140268012410341c00c40d40b10011100c8822003051a01032880b1000c03130410901000c45100301405100d058050042ca03650355918010312580a01242c0004c0412018040c61291080680f0080d07180c40c0e500c4121032401181e0720f4041000304141d0105800b004140c10703050000418503e1501544104c2c2540071560405034583e03540030301c011543d11107000780000c2c5e103d200141c12400c2c90300a45813401b10925081d80d8201040141c405503030000e030086a50b443d000400d00042d4903001303841b038600301011104116070a1410031080500b0b0920a55a80542080d0481a80107144807050445c01c84043c89010038020451400800c042d0046440c10320a03030703404010420 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 479802508 1250 479801258 479801261
    0x90b030d0809030703050a0311030a090c090b0607023303070206070804031704020f040608030405030c06190311040b071104110a0f050f0408011817030615130b1813 72
    0x2581c80b40041c0d0326201c419101100c4541c022100e040c149030b203c2e050340c1c042c4019107000310305c140301000e0002441d03002480e040c0b071449a07541c040036916003410420a9a07645040454514981c1210300c0c10101604500307081024288940c0c0345842c0c441003400e25840001c2d00001c511409003075080c3c80080d40c0f0030f0405e9904680a54015000078955024a1071200c0701400d00c40c2c029000420a8001160050004059514580101d0301c4ea80001ca010401d07820108000029078104807241c9048c050011605900c007801e4034000c0c810141c442d0b100d08423480d0904211005480b84205140e84c0e2011400c20001d098503080600740034a181c00c020380012406401515002d10665444021540c810401118a0303082a6410045990200300010341c4400900c2101060303c0f840c46111507440701400c124900c1c890b122100705d00b0100800030003509998175401010007007007541456440d030401059190803910650091500c20100042d900345080c030080f46808070820450700318610400d1100000b0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 479803758 1250 479802508 479802511
    0x3130810061d090a0512120c0705120307050c0709051f0b0316050904152409060305130210030b0f06070507031410051302041d07090222090b030d08 65
    0x12030302d08031a02100102c0c2d44007095800203006000c4507400070250f103501e82400050319a0102c80c80001803103420a1802d110301a610144130040c65041519035119142c8a031110303144070191000020000b6200b03030080e810b88210130b400307004071402e254540407010001c09050f210110f0540c15480d000c01c95081021500c010340351400400e608545860380c00841014907004008248001848801c1c000c1d280c40c400c1d001084103043c001c01c500f43c81e00720500c20181400000c10301301c0d06000e45000c000e5030000181001caa859190000e95940e4000401e240e800318014025400b090900349030701c40c10740c0758102d101c600d0011100d90190000c00300402c0500c1c41000710050058111200420110f200400d4015001544e00c007990b0444c0c2e1180024000c0710401c0300c0d042020300310010000d0650030140315440b955410301e00450a018141c98031580c0c1c580030303403007140c003451340000740740d0700c43c41c0c3c18000d03100c569030b01424480170b043d1270720b550380c01070000c040000b4041c3c82803140302d0007864031a00e50a07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 479805008 1250 479803758 479803769
    0x5191812031a041b030e01060b03040f0201090b0a0c020f01112b0912060b0406080703060608120307021c050c07090e0f0a350703121d07120c080313081006 68
    0x28110382c99a00c6040d006040b46c41c281c2d0086550b100b00c0094040855002540320764419092141d540c8900e20000d00010001c3d0411f1030b03039010a11100d0401904424844001901203c000f00320340340701c1c00100c80d100a001c00c800c01600884408643e200c040c2e82c02c00440f50b502064075a01952010001c031448001846000010645032880b203001c82c250768040407403014080c0000c112140c44000483c900212a801210180d40d100401c20035040107010030060a011b80311800e2031410030600080d901e02c01890b4040c50550154214242a0300030340484042e940c150055490644d43c4101a130700415646010248500500100010100c80403c0c80d600003584600407504403010070075402c40c810026a10f045201c0d0000040b040d8a20f000c80151078403034070079540c4100e45d1820007608019900d1210705050241d05600c560403032000041200020ba920102d503071810441542448424641c0b43c0c3c1c0703e1841400002613030742c04100d4580703880081d600c10804494032070041c0c2d043d000480300280b040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 479806258 1250 479805008 479805041
    0x2060603030d0b03031b070e07180509070c1e0212010c091a0412200f210114012909060403170d0c0306051305191812031a04 55
    0x4030301c02071216400450310501c05001c81b810045d1455904012403680103215500754030815080002e4581011030360350149041c0b41c0250300c1e00340d518250440180f02e018041c410054840050034503403040711914421030f048882c110002414080d00160b61030008016030181010102800c0010014000c5a82a8000740d031030f0003071149030000403600001c01400d03001a4510400002440301c1e240d407500d10300340b0701030116420303040c595031100111a2400c040e0755010b200d9101001d441d5540d440381c0180c00c219211704041100c00743c138004034010084501d41c1502501c1580010441e02a01070b2844481c107403088400e0134100b600d4003140503901070360504a910000030007081c00080d54100340d00c804107516030703002070900c10780307001280640d500c42c0403400000755205804c002c07030310740108044a2040311007000c019609241ca50302c0d03400088199550140b64483c02d903203078442c00c001c2800030290b800c100e9080400101d07450003000350100855000400c2c90000180205180c540b0401d201e10060012 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 479807508 1250 479806258 479806267
    0x12301090c05161101030f0b090118020405090f0403180312051c1b120902061b0f060a09110111030306010c050c030a050a02100c0f0602030636070206060303 69
    0x6050280c0002070116080000030b00800700d1074040c100200300300c14803410050313090600f12400101200c84143d01c681c0c1003800c00800c40c40c240c464444003030640d491490f045c406010b0001000d030180c8030380d40c00b507030300302d8450010400e1815940060601542c400e0360780300d95440340702c6140054850340c0c2c040a40310501d40031801484038060002450b0040b0885403501070140c100101e14111078101c120b80d410604400741c441c403400c2e80403003110001c00c40320b602000884015000b10300c0b00d005044801110301c4840f1400b5205190410441d080b050b401c408907002ca01c3e0101202000d0041d00c102201d800351460002e411a40c003031030b91212424030a400860a42d85e411004407045900b180c1c00b84c9045c043d5496010158500b0300980d103540c0c1c003440080003183c480d8418044503910340c048500400103407001040c0003464070080601c5580e084a005a140e8032030700b0020b038108500d01c4400903401d00006170715040d000019075801c40c00010300e001c08030aa071807040c103030b880b52012540554140c00421 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 479808758 1250 479807508 479807519
    0x8031509010e0f090a210e041a0402070f171b03090105072907170a05060a0510050405040c03091509120315050909031902030703020a110f21012301 65
    0x622141c4d2019a850885041d50f00544039881000171100088240a880c24821641d0a070001500800000203407030800040010410300710080305081c8880344501d400103070703d80c140400d03006964a681e811138940d0803031080c07002c51002541e1101c0e40030011003a4000511601c1003004c030a50701c0941d01a103589182008940e101c1e9204507440300004c20032240394800f50100e450351500c0074031488107900c41e9100050a460001500340b0300402d0040030904040c100002e540361444508201d440c2078400615403081802c2c2602d0301c2c082c90b00042c0d00185414405050190b154000c20411070040140ea00e404c404030b0140300541c0c101c40380107005c1801c2c2550740700c5a14800d0380034138113000740036190781040f03038640000640400060f10114996031003c46c502c88041c4500000d0307242e411041c00110b203822455a40079440300b4510780060200107003c000c80055840c0d103100c81510403130040c1791040d40b40b0422514038010401c0c42c5503800079880d01221203c8080a90b4038424040300101049810b80c1c40c02 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 479810008 1250 479808758 479808781
    0x307050303150d050105040c081b1e0102030c1501060f023409050f070e0913020d0305190f03060617040f0f0209070f031a060d0f060b040308031509010e 67
    0x1010389500580a41c682c0c1c00410f07006e00c1483d00662245114010262a10003520b01e01a50f01d0703c405050340000301c0240300d40e03550042c040d4452168000c1d00f000000a400141e0660042d481922042d010b411000100740320a006001c2c140c07425925103040300c00b00f02c40101c0e55041100001c00c0070031540c2d1262441d558901d104455200c55800f9021002c0d52205445010313100c06569100c1241d030301c0382c14001c2c01600100e103420700f6a019100030741c092038a025094015100381101900541c01d074440d2078141440b80c012105130500c544100d580c80d89481c4002010b01c5460346020700042d15000300410417030700c80e4034690000107625920007819115600c6412000500400440d00e0004401041d001a1154421203108a400b9190745a0b1840d5010340a019100e21020b461070f145584062440309556000598944401c2ca100000c3c2038050028181d00400c0144c001e003c070b0b1440440e00100f0024200021441400c0c0700003480500a4101d0502801140a001d1380da4928840400640d074190740 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 479811258 1250 479810008 479810041
    0xd08010e2403010b03072312030711130501032303130501030f0e070b040e0604090f03110c032e0e0c060d0207021305040b060f06030a110d05070801170307050303 71
    0x4000140c503061110029240c070007181d0048605507d1900c00c0f1410020544145001e500c090700c988800c0c0559003c82601c9109003a07008010301800d0400c003400351542d410801121606000420480d41c490070507017000c1c484c4402180e040c95031100080100c4e0004400d0744c10301c0c141e0112500040e400c2800540207004180d00100300c444e600c0703940c1c403112041002240010140b94541079901c50418803462206540200201d0241c0d003080481c07000900006c4200760416018130b070402da00340c032012a1908041c6446611079140c41035407a5180300705c016481805810314008440c01e800c9001ca80140d0545213150745501050300111208045030030008000c000c80c42295100601e80001a070006414522529144140603030f200100402c000400784100d410030350848014041c00300b0200000d1140c0310013043c0001c0c06407610f11200034480c008050b140981c10042041c02241751002d0000d002e00024441d411456004c1400c202101c0700100440b00034541100142d488d5036603521101d00203551 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 479812508 1250 479811258 479811331
    0x90c1806050906011b060c0c05071205071205030c0d02060a0e0106050609150f030907050439090317030618010e220206070501060e060f0906090c1303050d08010e 71
    0x141503909030006d02603216000074030025032100c1c6580300d01c600300315141240e10f401013498005403911010129800088c2d03107040301c0a040307250440c1c40582c50403c0c05c5014124001501e8426841c1c8105000e03000310b10a0b21a440c0f142c0208110380355a140307a8240d0b0210b2140a8002500f004410562704000d1141c0c89540c0c0c48240d481d10303103880300c181c038081e4ae4421144141140c001020500107031801340070302490205000c041c0548103080340d1400107100c07030030340750082002e00e00301d185007030280190020001150030288241c0403401c0008510590352044600c08d01c241807a8050041c034100c0700c2c945d54180c40100001710565076418603800040070200c41d080041100c140d0301a00141d464400800302c0070312030000410002d1410031011101c8001030b2500d8440c081c0d200c1c40c46c62586400ca8040d0340544119281101612040f003441c0300c41c8281280025240c2c011074011083c8940001c0301e4800f800fa650f684c6209a0307891262202c042000e0303031117580c01d84001030b42e08014100d0150f00d628008 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 479813758 1250 479812508 479812547
    0x1003020105040339152f16090609110c12030a06030c0909121b0204050a0f02220603020a0504060309050f031b1204140d0312090c180605090601 63
    0x1308005004608a41550808040e500241024842c040c60389150f43c802160f20300380901c182c404101c802c0c0d1101d5020b086014400c050b140352580c0303082c00300a0b400007102c1c9400381305540c03a12411101e010b0041e40c00790404040c100312810046d000315204903003000304040040d04080c40e45214040f0380382e1014200003080d5850f82c40100c00f082a0b01d2810005084041000644460703d2905203040c0ca91940d44805000180b203140044c04941c0f8003907504980e0480d400102a50381d400030100800c009041301c1e201a2010951409494210080325440000a030340b041c0703000e59824046080c0d2003000900320015030113200c00c01c40319002e900415907883c8201c040c0c40c200c070381c0035414518603042401c80131010070b010000b61079444400c0c858086810302e00940b06d4038103401c28040d80410f07007000034803900942600e45030b407052601c035450f0b0040380d6a07800411b100c012294103010000301e900d4080e280700d8000f00202c48511480d10300c40d9004070f420160040455545a01c0196601540b040c8100d80c60f0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 479815008 1250 479813758 479813813
    0xd02102003030a021b06010b191e0509090a02090a09110c0604060c0e090603030f0a18080a020109060309020d0206160803010305010c17010602030f070303060b030a1410030201050403 80
    0x580207001451244401c89001030b100c941030001094000405214048a6080480103001420320482214100701c1c841034010038200d02e55004691400300321034000c4000ca2900d50555034540c1c03120040c0404d580403280035215455075040b00b412031081b8401c680d0f1220148100700202440c0d40c000e0141c41403010350183c10a1155680c0600b015021a02100d910780d8801040340c989402c80c440c6100740d0000c2c1c80c2e001c0c55140810205e0307034903c1440030410f40701001182942c80944256440c0b40c55001601440458983d070b40c1c0210f80d04c00e10601d040340400d40501c40411014468890141000d0f0010f207003100e5800d594092002a9100004009007030150922010100d0300d288010b50003148103200000e89444440c03030091803a014082e465035058109001040041c3c2c3c00015900203034159108250f451003103280540c0184901d620441d50644013000b0000003644551080303036500c14054625110b03641d000c0c00c03840721110900000f800700c0d8091000b0300218040448104a44980c1100c02011 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 479816258 1250 479815008 479815067
    0xc0209070809061b03060d0219060c0b01050603131b0504060b07060507020c0102150603101103070906050408100b190b19030b0f090601120c020109020307050d0210 72
    0x44215560008a4140000d01030142d50821a40760301030550b0110254000300d00b100320b00310348406458184a0f40c040c080c41c03015940c4004402ca010444c80301814600741d540d560147c012544036509590505c0078000000715401e00f0002c43e07104401c0d0741c2291001500a0362502c0881000c00d4000302c2500102c5001314050b140c0d4030a800c080d009210f1065140e0344d2601e0001c050700c00041200c8115004454504623590300003070050440a4840101c00c425643d1401103480c3c81240500c1149942c00d001c0c1c12040408024011070080b0990b5440c100b8068440301e00751340d03030b1080344030b28103080e401000840426052580561280d480040080c01d2070b180400304490140031030f4000c0c9461000025042810b15000050015549210f00303050210080c868000707070b007a901041e0f06c41c1c06098200001009070b841501c03554408140030340200115401d14000034003c00050000324080d05c0360b0070b00403c5e0391410b16110641240d00400940c445440a41c0803241001000c10540780a4491103034000c5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 479817508 1250 479816258 479816269
    0x2130e070f0e150604050d03020c210c01141812100c02100e060705090103021303030216062a020a081c030b1f030e21031b280c02 57
    0x1d016505188041c41c0c1802d07480b500040b0083d19205115019410846594a80384250741c110b840c1160310380614070850600382d04100800101580c05030100002c3c007415400500390060418128044901d00340380c020040d9800c0e203000d0407a180c1d0f40070a01468001030300e000e59615484001500ea0100c1484034030440b071070301c203088812145164903203880b0107505604120804040f00400c0c3c050150080c60314007c2d442d0b510140c0811300700080040c0200c140c0c0d001c5d40450302e06c0c3e60b40d408407000e955980c0c01c0c009c4d2564016010035910b084508000110b0038400c000460a40550800c1c5900d04407038422101c6248910003412600596450303000644014240020923807000250f50b1101d043c603000d134000b412100d66004140c410514000300c031034050644044900c0480450400203903510162903058540310b8040325002c01894140340f040c0d002020384020318051040101c1001418001407600031941c0680020703a4200140542501c5060921960003d207007001818040000003854002c11b2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 479818758 1250 479817508 479817523
    0x80a180209010902070b0708040f031b1506060809121801090f0608060108070f08040f021504030305180405011d0c250203070e01050102030702040e030c07030b04060506041802130e 79
    0x200841c0c3c0400c4100c280160b9040740d40c0c2c403d2035440c18144e18906541e460303058802c4144082d0400c40e11003c0002c141d2031028cc07410903941c0285516411004980740b200c0070749054060440021000700104070407480004041071943c0c0c0b0051213604190810301135519520303903107501c241040202200024075081e80703001d00c405000d4030381c0d135824246006000984030f054042c00e41010010035079100c142e8554002c03851500554050001c1c40c11023114000941d00720700300c42d00c6840103000000c00108040e0010700600d0300883c0c08100d0042039480760108022104d00340304030107a5490100702c1c1e007942c6c80d84801c0030b80e0003019072411a042c00b04060344280160002c00040b19400400500070055240800421004105408013400e0380d60400b40003e46034056414000c1c022521048030f40714000040c001d41d06004503880c122014a5070700c0c100411055015074007034030100d2414010400500b40303400307050031041d403c80e04603007020240d50034040f0a400d0403102e003103440e80c6c880b6183c40405061001d00c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 479820008 1250 479818758 479818769
    0x609100206070201060e070c080901030e0f0d0219111003020c070f03150e030a0c020a0909050604021207030b0106110120090307080c0d03031d07120b0105010c03080a18020901 77
    0x1404640352007503003e030855606402450590404404106903180d100601640780341d0700419854641c41100010790242c44018500483d43c0150b184c616068000056624036240e400c1e0700300c5800343c00408400c000350498480c0600300044402003031499041c40301d0f03600d0038220710b4500107240c00320b40c5a10030b00f44010340d00401c1c481c0c1407400c01001404030503c0b09510b12007211601700440a4030001180c1d5070321036148082d0601c03051030343d880c09568501d03d03071100a141c030000a2090000900c0d040c0c2d12000700312000ca20940441c540820171a600081c1d48044d1b9500c410608102d07424030605403082840b20351010029922104c1e003408001442789000103031015262201d4888442800b01820315610350068085940700e0000190180c1d0303030300010b0814a4040c107001440003406003005070200100c00e2080c645103c1c00300300054078021400c3c1c41080c103010f0503244d20f1598840d001161410f041310401f400141d184800704103001d64551125100f8804044000e40c030070700c80d038045038070271009034400d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 479821258 1250 479820008 479820013
    0x519060b150c0706030b0a08060a05100f080a0f0213020c07030b07051809251211161407210c0608040b0406020703090e011403010608060c1806091002 66
    0x141998100706030107640103010004041c0c10146030341e8100d682d446551091104160b110302c0e1070005910b800000b0300291a0703030001d0340c0e4a0725040c2d5001d000780c00185c0c0c0d00110403e00460016001524890020503542144043c240a442c181c4070070400031500001a0b0b40402d0069012242e46100c2c40200122a00c00f00501561450341c1800c04102038018045006e01a08214611030040c280714120b501d150300b00c0305da01180e116582141400d003640b0400c0302580308191854002550800e865191030a100304080c032903d804035450040c2e42c0102900540103203105980200055070781e00440340d8042c4000c080b0340400781e035000303030b4040240340c01c2090b030305896a40611000e100212101d403001e0003c0f4240b4010a0a0170759805404810062003e002c8960104103001010302c1090517074010700044000050550f1100b000f101c060808003001440b940c642400021031080119299214540c40801c450400c000c2040008051250491566210390200300d001c030f00c0da81e11320011070001c1040d0300 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 479822508 1250 479821258 479821271
    0x40b180f150303030c0d1e0c08280f0b0a0e1f03081219020a090509090d080f0405010605270a06050f06090112060303091e14010507060b18070f0e03030d020304051906 73
    0x409407800d480030342b0804110b40f0f03100d40d41c800c5400c084850503040040c801c000890741d07095003030100208450700140740c1c050314100c00014040305041281d03000d03c4002a200c1c80514010961800e000c0052000070510142840100c8030485500b0003103601c5034440e640204040e602e03103103184c02ca03400f200b05900030510800b01804181403011009512683c00d0300100300c02c0c24000700241c503c003002802005840d03081e80006003040401e400c00030062001501d1545a00c040e03e1002e41c00707c04901038444078001410010790030030600d00502c001c4441c050490200380380800c0030320415600150303415040c050b60101803c030440d03e40c840d0b000118040d54a03110704038200742e4406002c408070385082c0b10707140f0702040a1202018000c81c031a0510424206140d80d6180d520b01600a404040d070f0700c0e68040072486940225580c0d02030031501c2a003496585120144004000380d51300c0e18442c1926415500a1080c3d42d8480c034503a00440c0c0003070203502195544040170698500008001c1d404852513500ca04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 479823758 1250 479822508 479822531
    0x30a0b07030c0905300601030b0115020a03091403160806060102120f030a0b120f0a1407062f060103080a02012711040b180f150303030c0d1e 62
    0x1141c2c050384609403820716900d43c9040001100c805080607280540c500c0c000000c500382c0d40030542003a0b508442c0381511100d40c2e40e03040c0444148002d02c2042c0c4508009800911450310100d281d0117035036415250f8005141c2810301b00c0b100c400c0010942c580521500c020081d0008070105680e00a124503401415240717407c5000a0420064004c20070074442c09018080100461905807035000c6d001c4400012450469000141c882005240c08151802a8503200e40b0111000c100001c07014043c0408070060020190f00b103581c0d00141c0319500028854013119038a0540c00c00c0034071007064a824065521424a100180c10b00350280e0040f200e8003400604950b04980a001d1104104000c0491a900200060000901801a00000b4101c0c00d80b481c1a07a840e51711640104c0c1c031182c020b8482c00c0c145e441d1070040240c1c0c84090368111010b03010b45001800c0e0960041c01c0c1110382c10090081c42c03c60315000000f10a81d00210000350109440b1031901d1800c9015000e20915440000000329004081a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 479825008 1250 479823758 479823761
    0x10315051336050d050415080c0706050103080a0314090a0f30170609041401110d230c0f03041103030a05071103010516050c011103090601051c0209070c0809030a0b0703 74
    0x10043d88141700090208100c1400c0051040440741a136041c030000c203a8803040462010300c40c100004003618031380b02c008000c2c001a0300141041400c0c0703440820405001c01c5000309102003c441e2001c0a038044015400028000508071000d00e00c2502ca1000040601c45e0301c840c01011900340300803101c080e000511702d40b03a01c068103054064200b08600c00d5130512001241c61914010409464003004075070502c0044000d50050304003140e546107441d100d0351040d000b400944000d81c0607a21002415a1440c0d022502984642c001c114032020360f1710306084018200040c0c0c000401c192103040f4144000c00381610144014081e15505584c0d944e031701c0c030591078003610035262160b5581c0a0b80c580420802d510181e10440d60704480d240c00c0613604c1e0f0f084000158054421041e03515105880481403200c2e5000000c0c01d80e05075202110301071081d034650005c080071002d45081c080d51085403c4041002180034403451030800e80940c2d002c038a0585400c005c40e14002c800d10b404c448051003401001007541d450b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 479826258 1250 479825008 479825023
    0x6031036020423180a0b0601020a060c020c030d0216050d15020c03070210030504260d090c08060702150f040609080c0a050712050604061d0706080601031505133605 72
    0x1812000b00160118081c0685da29102c00000300130070203080c00302e94103030b008102c0100c10a03400502480a07850001000352030745050507915010341320304ca4607800c4050010446080500c00c0381c1850509503d000f081103010f0710070038402d40300c1c24940c100300100007940b03000402c45140e5550042d950f94a00d40f051081004000d030030041014603081c02d00c070000303060241300c45e40e008410b20943e250310706140c43e0308a148607403400d456120b85480c500340200482e02c0035003403c1f568050140d0704184d4940b0301c2039031108610600d000300391418a0000741c000b141640388580107405120300080229107941c41d14140d07400204100c0156002090000802500b049800058011120a607000450030341c1c034217640d0600500010080d07074680a521031540081c010280c10700c4581000c4807103141ea5020301074010a415552140000c3c10410320b1f0f1026407008400c0b100b11000a0543c160b85540030b00c2c1140140b00584d401c1c0c0c1c58900c84400314400c80c11480304241a01c0ca5400e00391a001e904d45443d40c54400b0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 479827508 1250 479826258 479826271
    0x70305271329010201180b091204050d0303020a0e0a031a0105010912061802030d050a1404050d061e110406080112050a0f050a02030601090506031036020423 69
    0xb811451000802800040107015078030034400081c00e5108001070b8050094100007000207558250b00b2010700084003d01806441c100c01071b00d00b109004d400f0a51103104a000d00c0380c020600c000e070078001030f2003503000380040881440c2c0140e080e005d02c00041c200090a5105842c0c1c900110036982a072100c03e91054010f00e824200110315510744101c0b8601d2114407140544480d6403170410b8000914900c41c1455056401415111901c5e8001006032964001d10702020010300320701410840454282c0031102561401003403100f0000d00340d626000a4607500c4001c0c40789a48440e50000c0449080c041d03001e20403540c000c00343c0c4a17401c01800410005050b80154001c0040d5408400400ca011680c3d9074265040b90744101e00c0d45a60600520302040701c103000b5007610441d000011943d101da0701c03080c0034090480548191804c401900d000740e89040f9a0003510380b00100004440803951050300c41004000300c00d60800b60f110f50005421078810203508a00d075083e21200361511a00f03805002d901a0703 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 479828758 1250 479827508 479827511
    0xa0e0a03020102060105040e07051f0f020606010c080706020d060308180306040c030609020307030b0a0c090e07080a0b0a09020d0902011b050a1212050403030e06090f10020703052713 80
    0x1840c5400007540e0701d5040c480d05003d142e660202c4aa204404d0001a018160143ca011310000850b5102c1c0c0c4400e8503080d0700e000181036030341c402d545140b000c10421f002e030303105035640280c071812920341c00000e40c041e1104403950307542080340f6114900c46001d40310086004040171600c0d018541c0c2e9080440c0d4000554a11a80040c4104000551019802c80070781e504100c0010360b0711880d00c046468018944c10203041469201d007000034039003441d04884176450b226a24401b0090340c80a041c4541101038841030080b88403c400100c0c04100ea5100038482d250043c84102003070b5039820b0b41c3e0101d90014140030b12203034840c0381a005558205200082840032a0384854011000751075488e181e02c00c01a0080080c1c9440001e030201900ca50700a020700e00c0c85a1007042181068076002e80106980f241000c42401041e000401001010900040c03034580400900b0b44500c16445020003988102c50403400c9c06424050004111303038000c002c0000100a10b40d00030804141d02c100a001001c186a030300000d0b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 479830008 1250 479828758 479828779
    0xa050915030d18120503090d0803010f09060501050703080a110c0f1b03070b21090109230307030311070b0408040812090f0603070e040e031e07050c060d0f0507050a0e 73
    0x41102c1c00b4420484032800001380406a040c0b170407a080d0f1103040100c6502903c40c65084050140d9180254100e0f10510340640100e5614031111050f14282e120b51030100e0414805240424040c0d050380d988002902c5000850078020380c0010b005800080c00140103900c41d00da980750812040102c1c2c21071000c03c01c0c8100300c400c1180000303651040d042c040c1e805081008500b4900030100741d44802c04805201c00c041d4500c1c54540025130080000010a4960800c150003000d40e02100b507a129915040341c0d03004d54541800c80d1000c0d00588800083c41200c0c850410050000c03410b14072020340654400e0184030faa44c0e15140310300d441d0aa414915029a1208000d001007681c4c440c07000d0075400d081910f407140c503a03880400645400c09412000d0381c200b410020715280850010005203c0b030556107401290300150080480024000c543d401005940580d800315554901440900b41c1c82c1341540d4003003190003000c4042010b80708284d60000c041070010640a91264104d107c2d01107900c400da40ea884072 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 479831258 1250 479830008 479830037
    0x2070c0801060f12050c1041090f031e1204230118060302030a14040b180f0d0906080109150e070302071a180703030509010e0a050915030d 61
    0x446800340f281e5440d20fa04d0510f502c082080a0041a9500300e0040804060520130079010f440c200b1b0b0303194542c0300e4000c5a0004014019040c07034500341d10075086041c0421140d696560307852507112001a50344510003020034001613500308808054480348141080080d1100180c00e46440c800b600010801a4148020300140e038074030344417140c4140b08004000014000c640162401301c144103000480004844000c9001e40d05500211700402c13000c4403c004c240110000a1300549081e1801482440083c001c1a003e4030303d5405125030019400a03546280050118149085d085d0141080491101001080703034580040380580104000c903802d0000082c1050040312901c06400b41005101304040402d80042c826810382d603045a0102e4040c503486200b482505500c0130850b000800f480b03202c12040000d800c00714400c41160f525450b1582001c425038019542c0d0a098000c06410010602c80007032103545200c541c90040c10f010391540104003600741410f0400340c01d111900107000e660b1101500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 479832508 1250 479831258 479831279
    0x3151b1b0803060103060e16110102091507031403010305070e0c090d02190b0c06060f0312041a0d050f070305090313120501020d020c16050a05090606030a09060606020102070c080106 80
    0x1041e6001c60850368980d1448016802061035401c25074070305601c0410464090703801e0000c501c0c482070a442d04100c0c654034006803803d070706c035203010150812040405001c5441c20500038050300352090500f03141d0048408500e89054000f40c2c02540c05900c035400800002720010030320341d0003240c00303500c1d070b0318091603000400c101c3d0308003080080c090000c4000f6041040610490b001c068020f410302c60b5541d9450301c890613601c183c103039451480b49a4182c400c10203460000f410301c0c1c0002c2c59600480c1010300d00160030090040c6244606102c1008000c0c11321409410300c240c0348908a00a18101c0d9414071a000030100d800041001586500030032020030124100c0300304004541b044807070602d00d40c003585011406801240084419a800814880d180d0900420000300d100345042229104956690400585070391341c0c0709068106804d4004280340c4c0c00c282c4001d680c0007074100720204804660756641d40c1141c01d2075121100503540850114200f00a00075400001c0011b60002e1210781d060980640 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 479833758 1250 479832508 479832557
    0x30d020708190302281e020a020f0901030201020a140a150e0607110601050f0301110d05011814010504092105031b0301030503090909150c0409110307020c0f01020703151b 75
    0x200b2089040400b103c01e244101d0340710403024030300c45007032099005000001c8c0d0b460200c50b130200d200700ca05c412100355506241d0740301c1f0304a070f40582c0100500d135002c0c2c40d100c880200310945440280900c0c02007a02241c2032a503012204402940b002036440c2c04041e01c2401c0caa0050300c11030410070804a4540000d0340014003506480341201c0c0b81e070301140e40c0b400190041100c0308000301e00d1a00440d1900d41d60450768040c604032000140d01040281e4000741c00317011901ca8408000804108500501071410a5440940624420584030081d14880d440603000c10301090301010014000104000d00166111035488030800e4541205085504590713a46450340104480c0c540280c0c00000008c00750401085441008227040303200c1d10032030421083c41c074000ea00c1030207020421410441c204a0f5624140c0c12a80704900544c05061700000440c100703c0d07103005c011031141c1140b01e103a00100118014184452545c40c025500059410902c50000488114018001c007440020314000756120142e59040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 479835008 1250 479833758 479833807
    0xe0717031c0e0d1103070c030f0b010e1311010e063702100c0509060a03050108010b060304020d11120d0e1009061b020d0c150201150b04030f05030d020708190302 71
    0x280300504d41c00ca498910f00070701c0c3c0050001c800120001050041050543e0840ca019031003210f4160b8840842100003d41621856401d2034190040d002240382e03110150501d0f00e0514092b4130141e0000c000803c40d4020100000502486048001940400404100b101110054400703071207005180040e44032042400c00010381a1501c074500c3c1c0080c070600031106008002440b450300c4000d5924000c005207001d00406480b0f6207030041e001c0c0d9500c0d01a041da441a98000c1114020b00d40c107036501c1701030b448250540c90300481790203241008242d0a04c084920742d116942c480c0001100d40f0200044900d013001d40c9424000c0f401d1041c0003980e88041c400c9036030361140842038400d03030262000c00c0c0c0c040301c8500c000e80790741c844000100c1c21a08000030947c0c0c80c2c1c06503009000c40d17403070620f1002004100e40328920043d0402c000810010f165032102c61401d900580550341010801c1c40350205981c4121001c07500c003400015500041801d10500400340401c901e0304601f0700100b05508130b03d5442100d2034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 479836258 1250 479835008 479835017
    0x702070f06180306230112200f0319150203090c0618033301080c0f010c05060f101401020309010302070f0c170705030615040e0717031c0e0d 62
    0xa00311410614100700003594001341c2080041601e1845000b01c0c50320307000040d03e540d918400050400b6402008240d1150030501c600101408151600c2c0b0054221054540285001c0c0004000307580a00000301c4000c2070841511003a0300502d00200320040f0404c032018010300c184240140020000740740c1039545c40598050307540d840301d107100c40450514021650703418032401a01680310710080403291900c2e000d0b841d4140c0000741061660680c0402401081143d900c2550319242500e80164620851581810284401c400c0e64551a090180417507240c0d00c103d8a450500102d640b084103c200103241e00150305000310746d1000000e45030311038171400740e04058002c245241030201c001400d80e000c0f5030080b01140065a1160f80b841c01111508000346035014138000001c090501140715882030040c020038104c0c040d03517001008000c06003000030442d14441c0003030210790940604512107038808100000d40c0c070381e08035003240c0c85206071030b4102a131b13082c0c14103901c1c420114000408034031041e5103061 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 479837508 1250 479836258 479836277
    0x40b060f090d050a080406030c08012304110702040e06040219120305030a06180c030b010e06090402031008150613060503060406050702031c0b030c1009030f03030212040303050601080702070f06 85
    0x1080c1c1d1501180f000041c5c501500020002000d50b01075000220070714003a2940c004980c3d0b200b841c05030400c150308040d11402e14607120b05005242543c4808900024a51902d0400050f60042801c88444007a01c080d0755024409100030361900a0140800509070340c6000805802d1100c03e01e0444044140141030040210100b14048855080722015011000400500d0781650301c043c0090f1001c44807400c0405d282000015040d48142070500c0c1c0c055016144a26050a440522001b0340c0020480741903a2003102d0003140310744041c05005a2101030182203452030400c4c008000c484900170350040456031601400b000240c801040a662240e08444006040d50f121103050742141301c2c4003000381d620096403140b4580c0c50707070f40d501c40d443c02c020a50480e4011105001400a10308030307180da03540805c1f900c080410000700c200001403241840b81c5800340c20b03d01581660f44e5011b101740c80032800b09480d8000c01c4803559010075903da21892902c014100103182c24840440300d00a80a40000c1060800 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 479838758 1250 479837508 479837513
    0x2d0a0c020402070f060b100305100e15060309031305031f05071709150a27050c0d080304020f04062615010f1509030309150e040e0c040b060f090d 64
    0xb4165a07405410400b00200301c41c1a01c0d01d00018049100c11501c0f4420440200d00c1c183d2282c070400740b0429040e02d06241c0d45040200600885e04010820300715000c0510800d08035445030000745004480500c000c42e2280700c001d41100380300c400303a00128001da0048039001241c0c035042040300c000ca48641c10004983e140d00340115038440d02e0001e100c1455003030100b4050340600002304280c40b9070b60440c1880060700c511913544251091200c0c0704000c03040220030000c268030b40304a4040d0399441079003111359014019000c9001c14005100075510000c02004000a5007441845034031803000032241084560b0a180b02c0c00a03095194030320782164450745000450b007020410070503c02c1c05949100c61905d41c0c0da20460280c0880c1c86c00341c0310b81c0c00724003401d010101e401903400c1d00c00c3c1c80d85902c5180c003660400c400c100e507006144481c101009400000151561118411400341032a404080c000307100f114024031050f81c610b4002d040c02420100141c51001a80d00c0540d000090700700c030b11844105260 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 479840008 1250 479838758 479838761
    0x813170303040f1a0412110a0c030b060a08010c050307110d08012303030304060f201c020412030c0605010b0a1d0d0b09030702010837020d0e032d0a0c0204 68
    0x20398100e130502d074014140b109000c80105048503401460b0341d001ca110040d0503200d83c490038208401001c80c4619038042c40010360070340146a1128001c3c05e12102c003541c17124103600b503030006000c54010a0000081c06003190b031004c20300c0d21802c00f54000b4505407c0e0300b0001800704034141b0030744d03101c89603006014500c000344a0031304101d1a8000c040704d8482c246400d1040080000c014421816481c205220390310340032009504042100c04d02c1b20307031b040080c1400324100c4d00b030034044076480b040d508010100d50084000f01d103190580c021369030180d08807001d00d00760084450603080410300b058240040c8001e10b901c400c1c0310300521041c0c80300302e103580c00d42001300300721004102e0000c0091a10100704406104000301400646000f60386e6090f40d80c8440f591481180c0000310480303403c011403402422901943d0011290020007020018501902e6202101c00ca5410a4044d0b50075040041c0f50b164010342200215010300a40241950a002504040d01548140c2015406022030480c9520070366481c2d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 479841258 1250 479840008 479840033
    0x904020111010903020c0f04060501050a0f0306240f1e030209030307050105011805240d0f080d020d1109031e01091b080d142b02070813170303040f 65
    0x1d400a000d04003140c540a9180c40708903045a004101c01294195a40703068001d003c100d40c0181c607568a0134140c08400c0f1482221103500300d05040d04d4103400a946540d200c00000e045604c0d10030303440c1d030090070000201200e6400031028100440e440154490b00484c0000541e1010389050042e611130044011034114010700b80d0290940d4a0400002040c42d45510a1450110142020850f82d6a90340d020002848691412507040f0041d505a410311708156005200060180a84d9490413803981c2d0341e81920740c0000c1a40940c0b03074002c00d61144161040c080c3c0d80700c0194a4100c44c0c1810440c4000c00e542c0c40002128a150078888281600815001c0d40100322042c4c020000c5030604207200e14090100a46203d80ca04501c203658022403a1384c4a03c00340c042a291865186240031048440c1c140b41d03041001c01c090296544010b140c0f0348405520081600302c0c031864100d40c61b0300c8900326800803000a0380c00340140c13a20100b5041c0c0302d12404400c50354072a0340981c1d41014201a810301440411f107 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 479842508 1250 479841258 479841287
    0xf0b160c0803190216051c02030d03020a02010c0e1324030c0608063c120f0d05030c2a0d21020903031614030a0804050c0d0b0609040201 60
    0x120200d0200d04100c0100c020300d40400403414440c1628861101280e0341d4a002c0c2d0500060700b04820140a1450a003445910303e284013601a42c4200d0203400107400e040d100e400c1000866400606038841540a0090201010f0300341000b544d0000e076030022822000c00116440100750385c8080081d07450007072603401056903a500003d5080d0179180d03c0c1480c038614440c000ca101180103000024280d1038078046c0520b8042030f001038004500400c1d010703058403064a100e0a2409000c000c00c080107901d40b002080f07104007042004004180060324030b9070803c266460748104020301082004120b100c444202c0e901003280e44400f00f03480d0007001c008219244100d4041082d80103614000f0f80650703010523049003a0380050703a1029201d21102d004030072441444030650b010340040c8000c114041143e10040036080c001e50050b444108402d072284d04581c00313071220030042903004040c4000e00400304043c0c0003804003511162050f00c000d407211444400000c04d21486140030f000010b0840e44030301c80c0040f4022 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 479843758 1250 479842508 479842523
    0x51005070c030c0e0a0209061603020c0d0b19020a021c090512030a08070315180213030b04050f060402090a1a03011e0f060b090918030409020301030201180f0b16 71
    0x203849203891500303602c084c41240341c0c060383c41000c110780f030240303108031002503500402241ca0808008a03104101040d82000da040d4010208050b4164903031403280e200e0030b4801c10321000e491a24904004908090400400b021841030184014464000a40449484500143c0e44040024101c1210506200d400c440d800280404840b46491f070000054100042c45071100032466450040c01c6040710185c06030407a83c003644100411240495085030072513a91002d102520300b0790ba000d400f45041d034607640b08650f40707483d00040006010302400341a85107503009018100a0526070002034207014068508100b181e5201080b054915904c0790448031400054020f00c500300441c041e9440c22191094908407890600c00d01c0031702125140f14010039105446c0c1d0850920400200b400003443c00280701c00401c1e03070201640540e00c08104064401400c10210140c2e6030360441c4001841f41050740a1080d03241b076000300034450042200c001c00291030568203090340302e07815041140c00c5035194090151612 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 479845008 1250 479843758 479843783
    0xc0e030708120423060a0f200613030302120103030c0b100302010e0f1f02030307030b0913060c0507061104060f170f062806090b0c121c180b0a0e030405100507 70
    0x1b03030308004581529141a11105d4640502c85440e5000303250003a403481d200e42040e0001031400141081980d6001c1c007900d0018246050240c4401e2440821303041580030034404000030301007080003800d0742c0d4400055000c49506900c0c1d54000380036080080d0030207201d401c072251103a02c0d58950304e0303c0c0e0b5000d10809040e0f50505a081c14040d442c3e03401560b4040010307042035508140c9042031440765000702c04a000c2e031005d010b0b480d10b804008281201e40031040000030030108020444c0c901070794210b102c8540c0429929032806030003400c900320180e104824490000c40c402c84081180480da580583d440e8441001591203d0010303120403540e00070f100d40ca001022462a00c01d403201000310030344486840308e640c05a107c0c1d625491070b01503100c4140712a0300074641c162125203948083e0841148a000e03101481000034500000e07a000454039030101c00342c440c602d5040c81284a002034022150110401103203140394282c1d40c40303116600559000e8511203c02500140c405e0341200c2a0a80110084294 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 479846258 1250 479845008 479845027
    0x3120203130210090602030906090f09190506090403020c0f060d090605090606010201020f07030e1908010e1213090213080f0703050105091b0108040c03060c0e03070812042306 77
    0x124032420402d90141081102044020380254103103026100d05400840c00d0030594001c20400c2d0303101140958014034103100758a40c42d1615000d03140904441000005041980083d180481d00009e00f090702c20091a02440042900810118000303481650040100d1b00000042840b034441d403e19103125a10f048900c0061003032903808140540f15200544031142c5840004900b41e020391013500d041c0600400003031000a0280d00c001201c0c11000d41091706604103841034a524203480d521240080e5100c6051218564081c00110203140703820640300d00300f40c1c0c2d219000d05240340d5400368011283d800968149a0543c00020800400e8204125550800c01c19055501c03450356200c2101c96608007004100e6056021400000c614000c9c00d0011131101003200450700c10501a1081d9501c0800c101c0110100d42c00f4015500c4c0c01076252140340003501e80340181031920003140e00103040c5401c101070780b01581030b010040758101c0341352140b002c3c01e6401000502000519a40c4110b0340240005142c0c0030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 479847508 1250 479846258 479846281
    0x10c020a1110140d15081b0603040606030209070c0b0708070f140702040f02040614070f080d0f0f0c020d05120628030c0302040609020a0906030c0504120b01170712080703120203 78
    0x4845d5509982110810750b00c400352992500c44071001140c000741d9800c8810107007000809540e00038059800418416600c4c0c01041c0b0404003616a1000201000361240600001c0e8514a8000c401482d00340e240d49402c000c0203001c4414030003400b041040d48210100d01d001048181e40480386c0080040081003a0f041e007100c002c0d449440b411011441980c0040408850036080e03d820310741001032084c0c0750580f030b0f13103131007503075111040c100e00b155511494615140d1481c820541440c24403d00040c1c40c0c0060a070191030305524074040801c000b0b080200702040070307211400700d400c140c0c280d603020540b5280102c50307118107001e4904555401010007001043c0071100882c0002c0324000d036820400551500c410728181c0c0b08803244400400e601500c2007280c14401c1d405000201058a04142007903107884a0341c0d0300c51003111b02039403d040024010301c201d0f10811004035041c1000001412900d207448803c08032540b10340b0b80504200b002088800c2814050300070322041c1c0c010b0150466880c0750451401d507 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 479848758 1250 479847508 479847521
    0x51506030a1a041419080f2701080c0a021b0d02130c0306120206030f18030a08060f060304051908040e09030705010e0c0604120206041a0c010c020a1110140d 69
    0x3284c6049900b8040d9440c1c10200704400d0f4400202c10490405086886002265000300c59034800c902041140c28428020684001800c1049000f800855202d0100040069402500d1803034804000c205003000160001000680741503140600e0301c1c110943c00014101c800d03221070203904404901d1085540340059400041c40400c151400c01115442d81d02d822120840754500070741015081020881100e02440361a60210640c1c0907040034407020105981960880c80780c031004103a030141801102e1400300c20f80035103150180c54040c2107281980700d159076100d05000f207607040b10071002404244041002100c0c080c0c00300070002c2600e81040103401e81d40360302002e801c1d19203520300200c2e81c0e52140040703030042c881d0500500b054140b80c2041829100d610003003000b01c0e80b00d581000001454128980c200c0f682d0705103040e101c0e4460304138591090a40b0200c804200071900011101d400140c042030711032002c9501a69165103c0d40d540a00391b44061070000440b00a1902007441405000e0329001007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 479850008 1250 479848758 479848763
    0x9020c0f0f0d05270a0b0706050c090d031413060c030e0915010e03030405040e150903090a03060b121e1006080601121e0b1b07051506030a1a04 63
    0x190000301000918546540200140b040059420041000404501801e485180c4860102e01c8000614032001a00c2c6170b04581c06904134010201d0391070107100d002d1088652000c40700040f04c2c41c01d540000040c0c8070111155009080c40f4146025521780d0000c0000c0d204856903070810b07407400c1601c958001c1d020034458001280020f00994030843c9500b03040307007524001c508585181041009920041d0380091405000f80e8243c802030100048035505c90003080962446e110241071500400790320840d107030100900e05070340c43d4000c00541c483c58480184410440350000f5000452a000c000001c09050f8043c01c041c81c544111070703000e804400344281460b400d83c409402c03914029030f82d15217481a600c8a20400c10280c100c200100128074206548204030b5100e07804d070203004080341089003641e0b428a20107480070101d03a000c04c010208100b415400880c81c5540850030a45140d65041e41d884c032451b075805220902c1000b00d0380f00d443c200020306c001c9a01681c00a400110000c000100784000c503401e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 479851258 1250 479850008 479850013
    0xf04020a1401090e0612070f06081e010302091905040c0503060a0b0102072105120409111603180f08060f06010c0b0c0a1e0309030e0f0f09090709020c0f 67
    0x1007800d15075056801d1204180c540900305071a1140030700c54100d00402440e000104000030401c10681400010080c001c06900030b0740b05428880d0080462800800046040150100c8503420003040141c050443e81d0442c0c41c81107507540d101d86039000c0203000c10b031424035a040070309220410516507010420344900741c0440c0d5503944c0340000d00f03040d14042c0c203049001d41c0000005026a558100003005c1003103290f081c030500640c059070303031516241c5400001007a034040424140041d441c01d01a500039500c40d2002d95007000810104a0807107007450000a0511803001d000c0c03007030303440c90300504401002c480e1600c2030b00591718019282c946908643d140d005019010004240b0340c061118080110b800050000701d030340e58003c00d101b055001070004011f1088030444141d5844400804491001c4542d03404540001685005400408003040544c0308031103009900c0c441d80c94103078000400c040121034214043c0c84055a1505102c0c0c10b801c40980607000181c80d4814034030000780e40400442c48002c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 479852508 1250 479851258 479851279
    0x50a110a0815060324040b061201060912030504090509070b13030c0e0f040201050a030e0d0f02150c03061c0501020d05011e0303020a0b0621060a1508030d0509070e0f0402 75
    0x40080d28802250701c005c041030345030080b01100030418810128408041c000240b290002e00004981ea001004807140912120005010f44c0360b025607000001c1910809010200015a0f4054024040c42c0584000d2517500d41c00074041d004200804401460100e0000f9a5101d0707410342e8400c191030301c0c0029a441a151030001075581254525144644000a498002601c445d801102c0a80c0008510001c050320750007a04030300b03c0b05008003001942561590102e1000091010b414924410500a5611089020050380f040841d080f6640003404403200c030a049001d51408078405011400608158404207a81c603000585921941c181c886e40310724464806007920b0100100b41142c000207005812000d03191000640401002d07801050080103150400081e00d00c600c0072510066948450794040000c1c4181a6442d104451912134115032801c516810994a590b0320b21504641055140da034100103001d445041c0840b1015041e000400c00c090308100980c100c204005503000e1380300300403046 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 479853758 1250 479852508 479852551
    0x30f070c0b07020624100516080a0c020f090403020d0521091605060a050d0f09050f0d03150605091009050d03030204090c03050103021807021c020a050708030f0706050a110a08 77
    0xa2200200400500090740c0031b920b4032084030190070000d6050000c50388800664001240c0401404e9044001d640d1125404e0f62401000144400412213500900d08030f0140004a81d0110f111058001035041641ea14101c200c46418800c000302c0f60702a81212071420300402c0031002c11245000000301e4000d2a5568403141000782e144140c1700003c0c04940f0800801190030381c01d42140f56400c2e01040e00041c000d0b255290305007000002082d004094100824564055405200ba116244503640344054003a040900261052060046130f41c0b241c0e2014000c03038880d61042e0070160143c540644050078403070181c0380150107074200e402000f0810741040b449100051207441064100c030740042200e400c005c441480c1c0e90328410050034000441c084d94011550003071400044107840d503402d90040c507810b05181015824501290041c0d035598100700b00c0c01810801d01004c0c0c1c2e1101c1d0b0003810001d410748840ba0348100130144160351041d0140e01042d0442c5840c0c001001e14032941802070751601410369003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 479855008 1250 479853758 479853811
    0xb03060f01082e05010305100f0204080307170d0e15070f050a110f240a05010b0703050307090503070905011d091e10050108030703020d03020c03030f070c0b070206 72
    0xd00030100c480d4001d0001c1e010001d00d04400b400d8202800d143c0c405101428010942524405d8000395502e40c095510351900c119170340f0a00b0102c105100c0110300307290920154030707100d04c00c055001c0d200d09549849883d0003070961080b00c0b058240e6040400281d07065403000c030b0300c80312503091200b140b450040c00160742c140280003204074845946d4502d0f24204407000c0c1035501035019098101e4034405e080109002c0d100030842d8070000740c089600000f020704000c0d250b60400304005e191000c03050a001c01005107030003c00c1030380d02491303246c00c1a540301d80e92030808072008881703644015414800d9070b400084494280c0e120f035041c0c0e001100501d01c0b010203034045011100c41900d01310780940c000403002207641c084c07011003600300400d402036a10125207080e000c41564801c2e00161009d41001484200300351301000501e56582540c1010750409202524940d01c80c00b0080443c00b41040b2400060007940c810080c180703c0c2179120007001a03e04158000941d40c0c01c0484650f1490411590074241d4510f82c0d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 479856115 1107 479855008 479855011
    0x7120f0c0603060807050612010302011416080d0605011806030f0f09050c0301050f040b0a050a140f10050d021e0402071208150d08090409081306030b03060f 69
    0x20300614a080000c1580b000c1d2040c50100320048d0940364588110307044a409003000e05000d4507810fa1041103201d80c08000c1403001a856208040100b02c3d0084c00006501103010001661180010740c0c4407040208010b140a0401d0801c0003030f5840380d00f0107001d5540c11a00440c40d1400c058851081d45d49581046a49030841d070b10001c02070509200307040d400000d42c00102c090f400d00c0d860305c82c10b10401618104c141a00c41d400508803c1058000100d10154621102001e280c03900b600480c50301c0036108400d0119403090b0000e22403821a80c4a541c030340d0000d01e0090440b80f030110120b408454980f1890b01301d0b80038801c600124400003041044684162620b03800d034a4941511050804080103092042070309040f0350b401b1a02c11003e0742c1007400c00307440c0015000c1003030400140e0340c0100315021800049400011803429070640286007a004d01703070100c0e6141c1c3c0b00c20070603c412a00 = true := by decide +kernel

theorem cover : BRFrame.Cov 479676258 479856115 := by
  have h0 := BRFrame.cov_init 479676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 479676258 ≤ n) (h2 : n < 479856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
