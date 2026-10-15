-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3857
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:53:09.77443+00:00
-- url     : https://prove2.me/submissions/0ba1b2b3-66f7-40f1-8ed4-0587c51e673d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 693525179 ≤ n < 693705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 693526429 1250 693525179 693525221
    0x1c030c0e1e1207092d0c140d0b0301060306050405060c030c0a08280f0e070605040b0c0c0d06021c020f090904032c100903020604060507080f030c090301 67
    0x84803880c44610181c0365440b034145180600c081d81801c0100c1009081c55070710400009442a051140002040f1200014282040c2c90302407060102d00c50803107541c20319180c2d0101150a00e0303c04070964440900c040d8030954a90545409407024810400594841c07040010542003a081882c504032001b80380202d81d41703080003080303480300444050311382d44c84950416000a40b00c0036043c085100e40710711269111089461010039102d1a030b004013415190340c2c1c000700400046540c407941c840c10702e07009440104074100b108021480c0040000c040030703529182911414280c076800140603070651402078a000c1c1d000f013003116921504080035508169a00c0e001c510b03095400c00c442485024412003188100c40640000b8107050140075032007101c0e503070030311202d096850041e060381d415605080707114050b841d01c0903011900c81c05102e000f03094a400622450074140b82000c11500343e40282d80032280507000707200706426011400003440c0118102c4400325100c0404000303150840f10b4050401c0c030035000d115 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 693527679 1250 693526429 693526459
    0x5090601051204050a022e14040b0c030f0408070603050c030402011706030a02040507050d1a06071b08031c050604050f01050f01050c0d09170a05060f04051c030c0e 72
    0x5002c50b034216409080e03642c2e056542e41070550420340610400394001c0150300b0340c5800e610890f0035030061404d122034441011400e42d2001c03182014400c00c1034801100400050200c8025100502002d9502c04100c0b460560720340e01910464205900083c40c4c0d5200d44001d110150f054000c1c01d83c032213a1000c8041c11882d00381c00080072028900d51000c5548a510003251194800b4001c000c00b198000d0000e0200341015900201558000380d0044c08041ca0100e200e021110841c50b0120f102c04018601401d00307081e0f40701c0380c0580c40c001041c0500700100d0340d40081c05040600280c1044030300c4010043c01d001498040c081511001400140b1640c0791030104280c440c0d085c1c0c1d00c141175a8082d11885c80742801c002c01030704c1d0351291728105001480b920720401e0b5510f0f4000c21a00a50786c0c40d43d021500ea183c0001495070b115030038200100903402101c0040c4085c12103190041d4042c0c01a42210903e050070001503414010290003280003030348807000940c2080d001a01c0c01c5440b0401da502d041c8841000c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 693528929 1250 693527679 693527687
    0x307090b0c0705010f270f0503011e020a1b0602040315021e0c1e010903031d15070905060a0807081e01030b040c0302030f030415090501020d2708010e0705090601 71
    0x43e00500d810b00140c0a070401110713200c2c000045d042000418441e100d2000c03020140d00701405840780d8000a201403a0100d102d05040c002c0b8851449183c1c41400c1c0d880325040701c00042d410440c040000c20000740102c5521031840181c010005000f01c000599903419070a20280e243d000b0f1000d0242030340100311000545000d03499620740035900120050b1641c94502c0d015042030000200c40c01e0500138200465091107040d800442401d100351010000c0e1140d04407400d000300713440403158100d43c0150300c048454801c0c0c070b5401580712540f0318091410790780b200c0c00500039801c542c901c48001411a0300300000d09401c150001e411500d94601120740000e074040e0070b940d00710140002400d03585a1004502040821110700300a035a000701515032900300b1002c00d5680350030901c11060b00c4094041c221202500840525041c1c400c1079028190020110301c0c10703244000503120390b44907021200402030881d90101e0103040030744900e00002c50940e071051162441c04180d600705c1441285100d0503c403c607a00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 693530179 1250 693528929 693528943
    0x40603111201020f0a110d0306050d08091503070315050f210106050d0b10140a0902031e09010b03071706161b0803040303150e130c09060303050307090b0c 68
    0x411118440031680700484540640601c1410b8a92508041003a400d5180c10040041019004030200d0340c4a614451040b01958807510540c0c1e08071341c0b84607841c00416290303401420000c002808401629005040380101c6500868028000070b0b0381c9c01c501158854070304000320080100325540300701c843d00d120020319003200d011601e21800c2c440ca11504c0e00000203421200041200070013a50484186081040b4126403c841c024401343c0307581004980198541041801068040d0400081e03905000585000790b0010707020762510101d120b80502d81d1900400c9541c45200c20030004146100c12400f45440c209640d0000003070710b0b040940078940d030000015213591010b0440c040c1c0c2c1d1084002a01078820701d03051000d1481c003102510700003090005910085000b58840d070b50401c0401e905114103d40412203000354000009400080745a4031100d02a0041d0240581c2d42c1d003644542d100301c103a044401070752048000c144040b0802c450a0b800902110041c0300140e0342515018071001106c0d21403030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 693531429 1250 693530179 693530213
    0x8070302071a18101107060b040b131b02030906090d140d0f1d101409190608220b0705041d09120a020334031706040603 53
    0x25001c00c80400384002428100300392001844155103605040315203144100790400e0b60400ca104901042c80c3c1024940300e00c01120404004044c1440d04070394444010704502c60100740d0080c0c0783e89100c90680c1d150550005200d2601100107680001c00d220051048590000b84041d50024002a0100c1e2a0281110921396040701c00b419506110324000000940c0c80b1407100e09032007a58650001c80350804141c208076a0306840d898130984030343d240c0300c00c0180c241b5031440d08041505141030806008189061111410403c40c9040440c440049001d4115090641c040220400300030024103401c041031a8122600300351000504200280700080c1c00000900104403d105e417002401151052040d140070707111036152030442c2007000b0144040c04038155400341c864050540424208182c0f0323001c03200c02d62a241c0141d414040c400c03944106a40521084050601118402c901d00c5440711124128141c0300b034540c0030340003084403804042e001004010300d01607440c14400b400461a1210408030010b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 693532679 1250 693531429 693531431
    0x80d110705040612060c050705030d09170702101805040212060a14091311041406010f020102030114010c11090c12090c0a0e040c05041a040e0102031611010e060703091110080703 78
    0x16a2006e8102c0e0544030b0150f000c1c265000100d041509503120387c110b005028020f00d405561440b402940120303a1080c240020751220500c2d400d25080b5018a0000e403405840c2c1c0090300490ba541d82c0031606031381c0070400f80301e00c44440c6410441e95207002e0001c4800b030b22903240c0c0c4a034446000c6000c6000c0c81c0000c0d11241c4d00041d040000410440c02000032250100040c1062101020f80840e0007000c5c1001d9034003501144c0002c10541005205200762812128100049520300c19140700548210103000400d90740d003040c410803a1215291003500e0b9000d00b07c1d5025003580c8001940000c40c2c85140a8408141c5070041c20354032000e44d80b1021150300303462041403074400079240c13481c0c00ca1030a0085c4d4401342d0000c2c104030030541c0b581a4001852800e6200b07a030140003604600007003a080344030494480c084241e081d1040301c845446201001daa000021000080100c4d50f822914a42001211281d0001e40c13902e100008101c0030b904240700748082a0341d841480c100b4400c0140c41408002c080e44205 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 693533929 1250 693532679 693532691
    0x180f0d1e0e06030405190f0b090a050d03090c030602030411031e03390304050f0103050603120309071d1e040c050f06091809010501060903030e010f0306080d11070504061206 76
    0x40304c001c0c001170400312000c1d01040d580043d140f6011f03010311500e8105561980c030300c0d03000445407000491a0310403280c1c0140907042c039403a1440c00750700030f02140c082925121816400480010303890b200950059000d41c00d9040d00c00c03041000c151402141c0d090412413501058000758071448004240d4107031602c80030745403086035850046c0345006078a00b00010506a0003144050340030341e02000034000e85034282c2e80b242d11042030744c00560507684151411901503025901000e8014100e4000d0341c1c00c078021500b52002c06586002454000c000b8800480010408c1c07014088042403030000e003104145024001500303032405441d008030303035030b80c034801d0501031107a01d821030a881d40c8060407540d1440d401084101c15045980c80404020011a880b4680c0c0d03291400105465002d40d200c00e085940c5581d0b040144142540111204040310080034281a00c0e03c038041641c5074240032101607180b8599842048400480c02649030140c3c43d44020b01072450280c05201000f9010f440c0062150016000300306 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 693535179 1250 693533929 693533933
    0xc0c030605070c1506180209031005071404030c0e0601030e03180301110a080a050603010605100c051c02060405060f0907050f030f0a03050d05010e06060d05180f0d1e0e060304 77
    0x3c40004503c0003000e0300210381504c0003401c0ca50740090300360ba41c10002c079040950140c541104900c40d403030540303505510441c005030007505690841540300d03c4038a4441201c0000c001c0310405500310360001c0f034042e1442c18082c000c500302000c41c0307a0b0119091a0034403016040c2c07a50151217128404046280d074114041a07512a14250010810702c170703584908954030042c00e14001d100003016905505094280404910305180c14003402d410380304010308000ba842c41425081d10720384481c2c00100c1e1207011300c2c141541c64003621051f07414907400b103402030170183c900761418030709050000f4419461000d05405015000000160210a5a0080d240081e010038400d0021740f40c4a01500720044501c55442d0900405500c84041c1c000e00b000d0386801d02083e600c410a80c255400201c881c50381004040c0b06120f00403d041d084540c000c0482a50603607080705509042c0c1c00d201e8170512152095005004030781300c1c80d82c00302c03101c804000342d0490111040c04c9508018524008100d90324840c0d4004030101301 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 693536429 1250 693535179 693535187
    0xf01150e060a1706040b0616060e10020301150903350c0f070611030f0d1808180d020f01030c0225030311011a040e1009050f0d0c0c03060507 62
    0x18030200518082e1200c401200040c8480c50b8058085454041034010a585003440d00808444c05801003505081c1400c007040d400032620b0b96942610380c907850760220100c10303400f0701a0b80c10346680044050303501e6041803201076001e24602d5840b4100318a0701d03410004504a250344200700011100324484859040d029000244c0d43c044c44c203140094009800d0f43d880b200012000d061020744d0040c0c690301655a042a00c00a030079403c0b241a0350003c000049180820400904c443c1c071507450700044540181190f0500203907580e508540214000035007048004040403e011113140807203200304540030745e90109101c80742c52106941031584030311985440310b000340025134045d1480c048402c02c1402040c00c580800c5160703c000d0f0080381d519100070101c05818002d2912009440010b1030400305440c080c480180626400d0020f10700030040002007042603401000c3d141c0b03000e08000c00d0b0b90000c144000781441c125041e0341d001c1c040300100640c005400204900c0843e9008080003915594218080e5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 693537679 1250 693536429 693536447
    0x60b090a1419090911060a0203030105040504141506040506061303020609030715020a02040615021c020f0109110a0602070602060a0e3906040605070b1e090303010911030f0115 77
    0x1d907441d240c0b480c0030038288543d03800380407403501585014090801c0c000a0001901c1000c00344001a041000144001e0074941c2040b60007921881040c01c0b1208045200c0d401c0510011440b1039804981061040c2854103000301d54104000b00c41040c40c014440c1d844400160482c4002805514082405040b40c1d4040c030110b8001c100c140c0c20707041c035461007060094032020504000c0384900e2810401240b00a15007006420300382d4260010080440314146034251714602182a008612607580c2c1e9070601c00c001e0050f007021070310811080c4109040300c0208a94031403160440000c641c0084010001c5503800102150000841c00b4009049000d40800d0f07414491407031b10708000e0400c2c01090a080440c00d40c4d002c13036520658208600a46c000d141000810304c02d1b441404c0025205004c150007051400c813030240c001160b01443c8e0042240c00000701c01c0c01608550104140d000400100329641980c0122100d20b508034017601e2540c64070000c070080a5078103008984d4480c11750031204100e00d004035490 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 693538929 1250 693537679 693537709
    0x110d1104030503030705030a0c021504260d06080106080c0105031308070b180606010c080a12020915040312090303122d0f0b03150c03070c08070312060b090a14 70
    0x3030303030f5130b4641001c01500b150700a5410507082e920341029003040c5840401d401ca101c861450300145151640c0d2240389502a985803540d0b004010340005812407a00c09008020744080d808000c40c002c2d1500e8112806c4903603a501c1920b0383d80110098a031546c3c0d2000403a9481300c0c140c00c104160600c281080a940c0c0101c6800410b00260700c03080c4121000d1a402c0c814050002c1811208030740d44840c01150400f049410003401c05200b8030096208038002d182c134044c441c140c00c10040c11f0805000010f440528160380031000848000340c140240000400e840e000006203091a82c2d0300d501e5903800400ca903103904403c004840d03481d0a810b95000a4815400700d10300c0903d062072007000361514100042c0480400040c07400c4ca00f800344000c41c00c1c041049550041102110b0850790790b030300550780184d48014007072010010901c000c0e0002540080c040c1a060340603039076502c00340c400c1d5030452040311a04e401012030800709114158040d0383d0741c0181c82c190b90180080004c2022034202158080c1c00200c16 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 693540179 1250 693538929 693538933
    0x63b010305101a03013308090a02090408030906180c060904020910081005042d0b0307032906030c04090602040f03051501050405070503010303141309021201050301110d11040305 78
    0x5481c80c520309000514183c0340e2203120020218400d06c0340c10254801d00420b000245044200440745500400c091540091941c06407a00c20220f80c0c0041c156100484045030048000f00910001000400c522a03004980aa403102400e243c9201c403590344c0841045984181c10000d00c0b800c56807181d030140d444050021700650720040703503210058507412044030000c0340b100b8002c0c1d00041900d003e000b00c041002901d049215200483d40c2c1c41c8098103003101200d101651140030455080d14204110402035001d01503035403079400c0004400050003001c0c1d0015a8060700c020500500b030b0340104240b00c0c0010120360004e0f15490700d107031500284c0296402100c2d01240e2601c0002030103800b007a021201c56450310030054a0780c032982004100c1d0000d41d850702c0014801d200500000b4041c82007180501c541c507070703181e081100141e0b50348245692034004488998020546554a80e80c00b9000c07400f4240c124000d0210120b910b01c038000b94010194008511902d034081507018105803000c840c065034010007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 693541429 1250 693540179 693540209
    0x270307170a060507270f06050c190b040507081f05041b0902041706040f02120a060903050a0f111c090306020c01061d06060711040e0601063b01030510 66
    0x58001c0400959003850b449102c800c0351405a1710300002e4050f074203105040440300d410540119000c4e082481c003c442ca2203852060314841083c000c104107101d02c070714900742c070900e001c0ca0320508100040d0710111035036020968048401e58817101c0d040f04000c08080000f9030303903203d040207820050101c03c2e08102c00d03441c50001c100f07d0015001071090769129601d4056800078000ba01d960740b001100d000e041010030105000042c500748504440508001080310b44845c0da60710b650702218840740088000c2040080c401c1c42098024003111600440307810b01c082c0c0e0005c1c00c21100d40f1060341030b819000425904c080190003034095204d04002c0c6400c820300b15180c011850b483e9001f041103008a1803510280184485000c000040c014450700e0041c103c917007800015500c02012511900d24507512030786a00c042001e203001001441e00800d1243d40350b80e01c4040c50035610034100318415100c400005214001c41d886241c00d40c03803666111082c6070010307280e9680c6070b546480b80c505400441a900c42d41c8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 693542679 1250 693541429 693541441
    0x507020103020910200c10030b0102070b0a0e0f0103051e070c23010e030a17060a030f0605041e050c1512040b100605070203100c090503010207050102270307170a0605 73
    0x34001c070700c0c1032004d0a807064070b5002c8421aa50386c4011036005c079404000c1c1c030918014688a50000044c0d010103004840352103403541900a490b8008003041d10001d0510f0020b0426460008084550600300307003000c110508013040d40140351421100300c0c0079002a00c0e8041801e441c403c181c00c281c4550000041c0e0031925440052190409803003c240c203c1d9030801c26140d255410120403141111240d845408121030019102d031002e901c010300c10356110b15102c9000001c914912820355a440c0300d800c0c0014140382900d40b00441c00c01a0910340c101d9803010701c0e035800080300051041d03007500701144d01c040162003200101506200b020740711001503110006000170864681c9a041c0112181811048030701d0b220070048070540520341020354161b011030b0101074070b180700d60b02a40020285203041e541854131400844d0030381e40086012280c9a6000612552003040365001080e2884111301501c149010700d00003a40e1128940540d01d01032b542c44000c0c4248071803c21410082030303030160040c0902c0c5814 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 693543929 1250 693542679 693542687
    0x3030b030c310c080712060e2d060a0311030c040c1107050904081219320f062713020f0114190c14030715050c0304030507020103020910 60
    0x200303840c5034204070503a0b900b160032024014200c600c4200d548070713401c543c0da604044404600e448800c8400340d44d5082d001c81c80f8418001c10f41d1103070600c414030310b288401c114082c11b001c02d08020b01c2e03107540c0c82610a0110f00d54407e00d41c0001c690f004118100e14903c40c1000070300308a0004803882d07009140210a401c0c81d038110701c03200c02c12410b250035030f400340f9547c2c028020340305411a0700402a41040203050030041c06081115000b9010382d00e540c24464001ca1540221036081004041c0415240b9022034920781c6a85200c040111059401c00603041c0318081080b002c3c40904080e104010026a08a55120000c41620744568810300508507082c84540d0340349042040e901640543c82d840b2340d0441c0c650055030a0050824500186854081c010070b100009081d41c6d00f180007001085520040401d80c1c03440c2c0c1c06003410709407000d1540e40341c0d00e10b01440c2e14190303051100e100e03d007050704210441c241001079a0f880394150038460356039109403004070000c1c402d801c4040ea01c000e03c0d0401414240d48 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 693545179 1250 693543929 693543979
    0x3090f030b10080307020d06021b0f010f06080712020904051609021908040f03111006080714031b041a0616061107170f120708090706030c02060403030b030c 69
    0x103084034008283c1d260700d8065124030941320003942190701001d0420000c5c01c241d0092030704441f54440c240d1024245031842d0b0602800c07821441d8280c0d1900c0b07527141c1441c13040c45982c008014110017032001501e407508000500c1400b0030081d01c6022208001000c0c85000c0c0000400d420000c14042c0e103460315003c2c40e038001c0d00814404801a4038005c11046a1800790302c03654021034022501402c110382c1070341c040f1008040d1020100c514050000028680c044900a940103400352002400300141000030070150707000604a9144a5400600d1542c0d101d28103058a40c00d48605640c0800d0704d000c48001501d50440300410650442000228007000385410340000e1000d902c140320500080b01700d1648000d242c091034a018015003141464045095a03080007007040300b2400080c0c2d4100f24844040080a4000300c91000c003103100071041001c586400c0c01801e014007003d0034104040041004002d580f4200103000406043d910325290070240c2c0c00b0011a001848010150798051301403104004e04448 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 693546429 1250 693545179 693545191
    0x109020d0b0108070e0d030905120109060509071214070b0d05090607080c1b152410080c0a02070b0d0f110c060402100e150306240f0703090f030b 64
    0xc503040c01d284880d0320410005025010560312842c10101d031504000c1c1120000f1742c124248044940001780325126080801044041400002a10507481c280034041d6600101610754036080b04006010107100cc01a801089421000040e0002e01e802c03001c5281440076004400f030038201184a490041c02d0b0740001c0d11543e04c0409a4520340c6800d14140d4400209032140c200b050418012800149080e400e500b0100405008840c86100c0c2d494900945001c1030742c41380c0c40d040070704203100350440700408260324115059401801d40c10020000500c1c2001c003400c0c814035032000107030309041140308008a4014081c05c01301d00340d480709800c1c5172000070300100910f81e01e07040c100042400402241300a0351481c8078081c010700700c99603c1d94200030f0540240061041030004850304540140c98262030051160f07090449542d40382003040802070500043e0000c1c103c20709540905001c06c148400c00d4070054100c11019588510359442c09a0b640c03070302c80c0c100200c2d501845100100b032100720349a5078091a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 693547679 1250 693546429 693546431
    0x2180a2703020f0109080a030209012f1b010906032301080304081e060105100c05060f040204050c13032312071406010f1802040302100e1f020a06050406140109020d 72
    0x4400c4214103007aa1780034500540852018881d160440c0d00940007824420014900302c1301d030901303048452812400002d201c0407500c8420b01c240488400421881d03489500d481c08412000c13444200091044250f0b02580082640707417400010080010500c54182c8000c9030207100302076843e14542580e9030801d10949409105140005d0103042c5201c100d0f20a01d8011000b40c94540c0c2048140140b8100080d51481042485000603020503030a0001e00d02508418440d1005801c1c40d00400054940c0500401c9916030100051040030121800410440790302c4881805031804141018035203610220702c403607aa0050540b1801c507084c6900013064041d100d0b48890010b001e5110701103a85903424040c0f00d0011a02440c2070161544440c81b8400006020b036001d450241c6036800328203068024507080011840070280c0c00480e242a1243e42115070030303001070140310303588260020340d142c4000c84003408a60756980410148241d9030080401494501d0144541c1d503502c945d032000a600c442d01591082d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 693548929 1250 693547679 693547693
    0x1506050a0303090e0c04120323040524160501140f07090b0c100c020606040e3d0c090303030f050105010503010513091b03150902180a270302 62
    0x920346540034806481e0590b03154500c1074103080600800030009080c002c0d0244080c400003c242000c0c4800c01d80081c842d596400c81403065150100101003403003131441c58602d05100500003134840c48210040341341002c0305c41307911000c4080400701034403c07200655840c041002c04402804015005089410b4050302078081c50703038030310300b00203100300c02500c0c444000366001008210140d07880c800b608807030030720780143c400162001c2807140c12205101060340140c1c01290410400e45800d00c2003510800c4a82c000d0802e000702030340610586883d4210704035101241890040382410700c1190307034001541c400002c020340e010062020340540e5180c0b02c100d0010303052007241160103202e4040c0604880040e198181141d0920007001400701400c010702030125940d18036500400c04450401004007a101140c86400342541401d660540b50070303c22103042c0f402d2040000058845100e50f011041c615081d103403450b140e47d28003034042c1412101d00c071034800f49129101030401c2020000b4080034800d401322418 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 693550179 1250 693548929 693548939
    0x1091e0c050402131d0610110705041401050108070906020d0c15060806040b0705040501080f040609050d080105030111040b0403080c210931051b160b0912030103110103090501091506 80
    0x1c2d681301b1524141c114645003414404580100581c10380200c7c600c007540d0440c0c0e21000860700701c2d800c4245101c0c802c031418004205a503080750400c3d800200c05c0c600100c0c1c0da818414003a6840003800d2409080001040040c02400081a050800600954024000c40d999140c0859855500703650540741d810101c00403070821409002214200d9106846441c1656184a10803140c400014000e0345e41b03e07140d13108000010018005001044015102c2031102e504100605d401c55181307006004181c001000280300240750322042d42c0489a02119190343c60201c071210342d0078111003004c12a05400d84140760200900d15001030b00d2440020340301c0c4440c407102035003080840a0602c1c03a0391581d001c1e50941081034420b50304100c1e4000c00495140c07100e4503141003d0041035000c0b22000107980c51624140d42044908442107410003a65802014070004485101c01d0301d10061000a24804550303080d06200d901a0708020106900302d0b000304540c1405013090a03c05842e0081d11080d645000800302d6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 693551429 1250 693550179 693550229
    0x117090313030506062b0201031805061602070503070605091003020910020106030b0a0c0804030311040f0e1e010b220504021204110405070c260403050d1101091e0c05040213 76
    0x66001b43ea00117079090525940055004002440c600104028071145c02c80108200300021400349640c0c4484c0c0c01d4102100d50003d04000300707500254800d4110900400031560b01506995610070119200c0410712824101070b0000d100d00d00d00c45401030021064607d58a0b01940000c003164011000300000c2e9860b032140e20201e0300705800c4040400c00385408100400c2c0b00b50320000c0c0001300300786824075054860a416608503403d91200952269080c00c1291899029020f269040e542e160032020075410710707600031034a0090303446c0703134190300b855035110b038082c28040600d00d0040c4000b178800c540c0d0b000c000d51380c241e02d443e0071101651143c0d2002400c5071903040c14440d103807040d96603030340c3d010b06e0b50125501c29044280088641909030074064122103800c1071040240000c511540080aa20381000405801c3d038002004000069140c008403002141030000d4021402441d0304940041c0101841c020312480180d421080d00131788041103090600000052880030741c0c882002001c400b00c000c605083d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 693552679 1250 693551429 693551479
    0x70815060f04231c061b020d14130b030610020609100209040908040603090c0f06231b01021309021c2705010209041a011709031303050606 61
    0x25050740001c1004020403c00610000c8440310454403c50f400000c00001808140e0507180252400c0c00c4042d020003001540c0c410211602a100d0000409110307451000e5103036180c8803d03500500088550024200400004070b0b40701c0c0303034500c00f42c0c0b4149865000723114403904105c82d81d40c000c51a20741c40705000c03400000c0030703446440c021005080d110300c0048440e001e90400c110b229045030702e9030a041e00160421001c2c10191031641c2d030000d80f2426a0034400c00b18403860340b10392485000c021051065623031084410094600c0d072480120352107440348030032030b140c410442106a80c0c0c4020981c0414203806400070440e44040040c44d21035144c6411007802288544a81e6504610004460309c00e02e0840c0d41050f81070301c4d00310442c030800c107520280014a00c2000242280d042c0d40c0002ca994440c5003500c03510210440140f840a100720180c400030300030b2010300c1104000500c101d80054480d9604000721a0b0742016048038100c07240c2c4c3d07132030101d0340c07644161545403084110501d82641810140311075 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 693553929 1250 693552679 693552697
    0xa14180f0102150a110d112a0d03110702120a030311090102100b03010615051926061c03110106090b030a060203070c06060312030506030f0d081e07081506 68
    0xc03c810307140c40f101800241203006a150700103c0900070004440071030304c103081901054400141c0d480e00b0500c0c00c440074910708813101c580760240311455203e2074000140602c005401c0e090011b1081903591181d0154040c00c040203522114150107490503810119000003120310a442c1440300b2165103841006d80d0180717840c5c407401a0b0000071540d1b4029441d8000c404146005800050b0b510307181c081412504008000c442c0200320001070710b0101104070079180040c05079924050101180000184400c9401e0303c01d480c0c0d2041807840416038940d200074807800350308024402c0d24914249440d010745400956203043d116946480c20000d081d8940740111801000000c001d40a80d0003156258002500090441c5040100148841d0001511032040f2405103008030f040d50f1402200040080c16150000c0000d802500101411440030100280310801402c041c1410001540c6201d58203004e00e00340c2c4000003c903075800c01480078079508921540d003e03c04211003401454010b40c00e0108074441c0e4112 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 693555179 1250 693553929 693553963
    0x307050d0801120b0a090b0c13050312070204051b0a020f1509070b0a030219030b1306030b18030f0a030203011508011208090118030b100608060d02060a14180f0102 72
    0x4040c001a00344804c20b5010043c51000102c80150781c581e081600c404842c440c42003000016810520103284035441d00810085009016400c06022000400c0c0079071603000303000d1600c440100c2c0001510303144151021901135981d98440d00f410200a42e9001511a0314005000b5454030020b0106d20203202032103104c5003001000030341c3c41c004a044c400e41c005000c581c1055030a00c50850740748490710410307003889215540030844c44100401c01c1101c14440300c800c040d031850113504000060540340903903071021000444403090610124001c0c1140715050604440c5c590000d2004402500350b40918143d44448258004885124805032440c0743d0a014080212a102104100140351400240b5600341c040c58180b62804018150713a50744000c5810031130740c0740e510302c0402c0070500e848840600104100c0c540160a07040c4800820100e1981e40d44c00380c000c8800281420600d0b0151102c0428421009840d40d610400074409402c05450303034001d207104041c8420345500c55880000c0c16104145d40b010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 693556429 1250 693555179 693555209
    0x50309150a2421021206100504050705090a051309080d02040f080307030507060f0b120a05010b01260606091c0b0c07030503060d0213020a051201081609051909050307050d0801 77
    0x243d021031030805007000ca9101130041444040c0e003105011940c01107460980402c81c0d241403030104000d9520007090003040003018084201c00d903462102c11000c8403001e45200784214409000203000e06a5a4000781c1130140000301802c9602066005200719003001541a8600751034005640e280d206041004d030000300e0501444022803080d900209168501802c0000d40d20521004510290901d06104a4507000740106078207212080c011103c13a01803d2070445407020304201000407403504403007455042040e5200150781c98440008031112544020315604030751110035101006542c04490407541c100108010800c032050100564401d41e5054135404d00351360701c1c20b01b84149403105000c240da018503000740540352040c2c18402000120440d03076529a4a00171a8240500040103a04c580000e5000e40c1c8480d419094a40002d0b0965400c11408282501e502d02d60560f0071001d00240700c8128900848c410421000000a040d820b02c95010784d103044100160940e02d1361002d2041c9554440011 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 693557679 1250 693556429 693556469
    0x10614030a08130e0f0402040606030c1209061d0706030b040c0806060a090b0f09180f041e0c0e01060e01080114040b0103021207090305061015050309150a24 69
    0x30050000744010fa215185100e580e41c400040c611010b490140000724007400b40000d505050041b44064101030505000d00603d20000420161004020b0300c9800e80d01d00f00c1204111058028400d0784020f81040d841c0c8600000b1410788907aa603100c3e80c000700780f80210841160806000703084c13489915441d04803281e03880d00c05100d51644841040010003d4076180818170341c0c06030001d0007180c429076407240e454a050205025003000c4c0703560030030182d4110008109184040d88031040e4000c0c4d0150108010180d110310034104040c880c00c005100b80c500307000204000080c00021030486202d5641c6040c00c1d41d40c0c0c0010350700c410080c0100310513458503008400a600f0070350040b00d80c018042c5001450308098400340310321882d09448080001304032020410501c4010044560401040d4950202041c608a1010201144175600a0500002000040340101c0030301115407050101e0f895061540f03001e00102c0010900000c40b1148520000031030310098440d19045019500c0364113401450f94412 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 693558929 1250 693557679 693557693
    0x3081015020a080a050c0a06050114010801051c1a240d020f04020903031308030304031116140f21010f0623061605060105040f0e0a1b091805010614030a 67
    0x1130880303809010042281c00f25813201001000e206c14003500d80000d09505101999070401250001c40c2c1c108841c1c00300610882d0380380700303070220350410f0010312250150301e070305d82003915000800700111120a0031040115501810580740d0201e03211503082d1207050301510170008a0b512032400603400403103008961210742041e600030125a44018201d1f03052003064403c45143c400903401403075246e0004802c5c0310803d50804005455140100094010112864204d1107041d20500c80e00240c00901080305032252504104410200c9002e0281c441170031400c1d58650070b031a8010707030a4141e0340c609030301113400030043d204010585400c2d40003140b10341ca401840039102c000c8051425805001000804080f450444004c552070b40704601030500d0750300d86000c0100b150720580342d400e00301d800c1c400008600140854402d4020394402c2c100e80c550342280c054000048090f4000740441da207440e4110551522030890f4540c060311980c003c0c00004e03203c0000e681c1d01d025a10b0015015440745100c00002155 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 693560179 1250 693558929 693558937
    0x303050910050f070c0318080a05060901020f0720090f0403112e020405041d0607091809060b0402030901090b18070512030705030708040e1e060f03010e0a03081015020a08 75
    0x39242001f800300c1340c10f00c0d00d2000c80e400e40c0f242c60564040d440c1c400401c58117000155000b0340650085081403503c5080c0b074039612800000800d01c0c110f084c04480c00c03c1c095910b000038404041e266640310b00c0c0c4400340290a50056034140e0100d0050614014601e100041d0401c0c090318820152058009003940340b122821009401100310350244408100344d22107100d0300010110b0755820200c1c8161110000b030903c4000380001d02004003071b80c0705220607440320320192003804840a0000c0c0d5a0b40c1070610800600414507001d0b446800001030240514054100782c050900400409840d902c48000b0704564603a04e02050100341c0000408200900c0c1c210400c41c1c4400d8108296460500950f6646045900c500c100701d99030a4045001d1203503250030b40c0d8075644113101c88410300480d680d030803001204220050140380b1440300c0c0f0001c40240e0b20300790842c840310f544290444a01a00514000c1c1c4039000880310010088620040060040d0302940c0d01500035070302e81c0260407034000a4480c4182e640c8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 693561429 1250 693560179 693560183
    0x1063c0e0f060304031806030218090a02071a0601172a0c0102070503180f01080a020a030e1006090b060406082a1207030b031203060f0a080a0303050910050f070c 71
    0x12001c0580c0c541500d410004502c6030384291354803e940c012014019030b41e14005c0c1c0003003040510501403041034580c3c1616580030064111b42c4100385a940c2c6107010068414804010861100340400d440b00040721f407000c60050100340c85e10700f0540d010308280c08025804841c0085150114a00300c411400072000d00358002d10443c0006140581a140c1c2d5030036644001c00c11202c0303610001d00300200109100801500303d80498103807851003040400244800b0011744550b54280d800240390005c00c0c0698024812500031105079250050740ca000c84004011a108821956090244000c03803841c02c8000c035400e48407103440302c036096101c840c485910040019240c1c00c4a0541c05501310098490102030b02c414050300100725000d2400d620700400762060103502a00030380c4240b440f2052000b11405503948207a050380e040c0410000345000034036682141e446900d050203003003d00c9082c568141c0002d403240869008079a110162a1040c0c0105c80040f81c5a40c50f43d405600170460b613a00c103250701d251141c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 693562679 1250 693561429 693561439
    0x61b12040503042409120302030a0806030718020705010f1b0e04020d2a050f090105090a0f0e150f1f0c02090106260108061b0403080301063c0e 63
    0xf98440c66042d852513081c00074034804101412a01149a42c03042040d00903007a030303000c1c1c140c0429099402079901d02409155a040c0900742c40050002c0e1000c0048000411070b090000f0403501d65640700b00001d5002c100191055400d2003200c503902e2810b40542c0300d80111a4121a50580201c1c404440540d50f4682c81580035801700109007a0f2011030145080309040404046000d900002e01d040000c1c0351291100d0034040301384601d01070881d6134400d42e05816000c1c2020b40c0e461111500240e00303814650000400606c80e524007140f40480481038a02c1010700101e4070030340c0c0c181042084001540000c500360711008403c048810b414205400e115100032a0a0214150586034009030580c1e101b44c1001c000507100d2004505045506129407010b090031020b1342c0c10b02e5051120007074075080020180c4034504004022552402c5120381110300850b0030103002a241d5845c0d40c0d00901008510038122115001c0d44445980c0220340000000d1800f1011361040204451080940d109084c44400c580e002c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 693563929 1250 693562679 693562687
    0x60a05070921061104080618060112050c0904050c010207060504050a060c1b241d060f0c16050a05030c030a020108190204090912021f110c1e061b12040503 68
    0x2601030700913011150800d94446444500b488182460010300408108050400c00c407044d41d541c1b00031980e141503d103030000c0c01c100704040e41020f07403078211400141074004044004000038440c012170071705a01c0109900b621891750340c1d08004c40707090240b405030540c800d401080130008a40142240313290144520040181558407540003030703002c1c4d803990106c4880241c0382c10310301c41c040c7c4040030b007034045016080c030326012000c0c82240548107011078030603800703450f0006940074001268000d03a00070100480c1203c2250840c490400c6a000461190500418070140302094034500821030b07071024000039005011002e078a03001103415100180c24440130126445001e503c0090781d0008001030031311014080b540d092546410303141d4600c07943c00002150805080c006030440711060020084d0410100418800c0d0402801840c0d0b1242c480d6400380e610070400382400509821120018101814055940e2940c0c1ca212211001050b50200e80c00d01c10200701441c0d0000181401c5504640140100d0f410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 693565179 1250 693563929 693563933
    0x617070309051c0f26181e0616170402040e01020f040315060e0f0c161b170309060c0c042d0b10030b150a050c060a05070921 55
    0x415a030b403000290f004000fa07080340300300d80d0000410b01000c240c91401c629030429030b04d80402d504589241c007020703041c4000c001c15000300d040e0701005140344166050702c0455a010000f03030005044032100d21031354012400040c841035036a54400b100340c0390715141c00041c03500f4100703444c0c3c2103000104101e0744a59103180c80480c00b031092000d80402c1d40c0714202c05a45604605001c038413510001d00019a0508207a000c1c000380140e0000305400c44c0b03003112030305040e49910990078414010005003c8a490201610606020303848400344454007185040303003034441d162b04140181d45800c04219420398010032002c072580c10702c0b50007031210f0031101d400c0c2d50280060b140050706403607540d0742c01c00e5026141e9501e004000d9405c0c4114811151047d4100300c0348032418003041c2c115145007a00c00505699524844141d25031089072401c2c003096400f00e5544008030140504650001c6484202622a00e400550380300c10300d12400b400760426444001051345007a20071120403000c50f0501c2503800e000f0b030340e03140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 693566429 1250 693565179 693565183
    0xc01081e1b0c1e0a0c06050d02090d1109061f0f05071e140d12050402041d010507091d0a020c0f010f023103060b010905180402040501050901061707030905 68
    0xc407145030b006804110b8a01082c3e512030a00a203240c41280c001400f8a030001e820b40d03400c1004c403045420156100c0c1ca00c40c0d244c00007030091311130464000034114014800c1050030989851580380480d14682c0d15110b9030180080c00c40c01c800d03a8460b582c00010001010780c015561588200014030b030040c0340c020b0603543c01282d0480002041107403101d40007007500704045030103544d0600001c000200224500080c004002c1660001c40d55500755803040494150348440d0040c803808040450701d0301628030302c844040d009040880d11800018460782d00401d8044019407005400340108404000031b440319030612001354803006141010f0311809200c464101428084c400689004078001615101e0740036150340b44001030000100a03a0020030580740c004110b90120041d02d4001400161448221006a4601d011500802e900910b120882800365a03241203180c450b80c402c0c0d400b8003442e41d940e02440100035080c00b41e0740c04a002052503c1500343d45924642e132041c0c0c07500d0081115099a15414 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 693567679 1250 693566429 693566437
    0x103020406091521211403071e050c1c09050307030804030204330504060905010e0a0903050c0723040b030a030c05070b040e07020606090105030a02040e010204050910080c01081e1b 79
    0x150480895017842d144940111602c20840c004210b02d81c503610f04158010500300c040d800d90316070301803240130b0a0719151040782942c01c0400030b2402c1f60303044569691010280f02015200000090080201103802d041c01302c0ca1104aa901845250600342140e0070000a0100e000b201c0c1d001c001030116160343c000100102c05074000d550400e44400b03500345002c0c401502c030185c0140003424200070040185002f0704c40c00941c01a44172900251001c014a0100c2da1846120f002035410300c2000e202181710140e40c4000102903d40d1166404980032000030f002c2550008400c1a9154011400c1c0c100428002e01c1d140240601ca241a111616180ca00030b030304a0304140c01c03580c1d40210786010803030a10f4040098540004044400d04401e40c58140000ea485030200802402984c44040f0103c16120940580b0081c00d401026040341c0c0c1750500240900345801e2103901c669100718014650f540d4060090310b0300801c20403850310320050740d00030f02d2110490090801c1400e9900194001c0034082200050 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 693568929 1250 693567679 693567713
    0x30405041a04020f0c0606040b0108040212012a030f140106111c030b030f150c07062007020112091a151504090c09050d0b070203160602030103020406091521 69
    0x1545038502e040b005e82c680303100200483e014502d044081021a82c200700582da00a604940031900070305004c95450140120034901d50381c0c40265900c41d2015600014941c0c21480e059508101328403907071100006442d20032840d00c038441038000040c4581c5109180303c80780314102c0c40c01c6461000141642500b603010004141002998031018a4010300d010320404810400001c01464603003140140b01401030b5024184500030350300012400304018558014040303141c03402c21950911201c1071601c400b00d600c0004100c4c00280035a280100c1d509951041404041d0050044100030040901c850a001d07000b60000700000a143c10b12207081e5200c0101200c04d0f0f400c9046c0fa134680b85007040440035515a2540e150611402c00814407803901c682088498503508020712038407644a0820603800c0d807058146034640310340120781d50000c0c014150029070480384290350400c03134541e59001144c21a21a40840c0420300f00841041000030096890803000f01c0e2440c0707440c02000c0c210343d2040c0e0102202406 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 693570179 1250 693568929 693568957
    0x903160303081509060a06030b030c031509160608010302010c031202070f050d1d091005030d02010204140909031206040b040207050105040c050103020910081009021b070504060602030405041a0402 86
    0x1c000340f00361109a80032801c0000d4079842072a040c500005000501507024171410550344201492580ea0b042002c9200f800026094a000080d000e1594421803421a4001107501c5001d00881d10a0100008001100d8165858100030790955004441001c4035820030703020000446402040e010040c0b0042141520071284101d82c1212445c05078103100c008188541401800c901c10064041c1c40b290600c8190400c80e0003280030760f1405907403158000f0301d800050300b51103102003449980d60154010410307200010041d81d00114030004015030000d084607100c14641081c02602d980f0701402c1010341c0c010000a0000c1005041c2c00003060403a0811070080e10281c2d140c0c003d000501402c01c50300f10203070000b0300e4194513194243d0041042c0303400300b801c94420841c0b1040026041d80010240201402c2c8541003990384401c17101c1031001003640800c0c2e4103094090b10308000781c00d180a00c5840205c40d00d80e0040c42c1020301e801c0c1084010500900c0c1d441d2844400043c8207610382d100c0c070050114000880d8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 693571429 1250 693570179 693570181
    0x30606040b0f03160e0a090f060308041502070503010510030f141b011106010b2a0307060b0f090f07030b0f0307060207030c0e15040e100527031905090316030308 71
    0x39811001341140101c3d02400400503450486480d0411900e05554503058089144001d4000e00d00082c404c070392010b0300c0d448011401143c00890811948040e810350350869403495202d43c1003500300c1e1010366484244000b07961040000440258105041d1030044281e40080452030000340c3c109141c003645071000c0324852441c0c20b003568002080d61264030051004200c59070504007050101c0c400c110102d040c83c540180190400c480c1d400d80d82910140d0f03030b07056079110102c51a09034003510041d03030002d1017032244800441c20340c00e007081414803c4a10080701c1d030b165200d0010580040c1404904a600300c0807101e008286900c0c2002903030002c001326401800e18514500f090541c0300c1c41e42d004075080c40f1040c401d009013180c030520040340786501101d00040c91038051004518210760510f04414032824a0200300203034070313812801d48827888070407034800034a0f4a010342c040e101e00c1907544202c0c01203c0c0b10581f0300050300c10310103040442d0003e0b086a07445d61080780c2c0d11503d68000d61080380042d140034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 693572679 1250 693571429 693571441
    0x180213090f03080907060e0d230124050906090601050d0605090408031e100506341707020a030f1e110102210a030f020d0e060414030702090c030606040b0f03 69
    0xc4880002c0c85245401c0350103d0942002450510b0300420140000c1da606200504880d4070b066405404046e5400070003182440bc103644407044480750040c42a40054440000e45040440ca00392055000400c2100aa55248010b50b07807a0002e40c04030041030f0f0b41d82000325458450441c114010742c0542c2126444c2d140c4015401151100700c2024491101c1c450305100c19a0f1b800e41c07441050360300845455454a4021551940013482e2a122469103241c4402e1170f0340041c0320303e00ca803155501800c40d0419001400c499000c552240f0b0600075044099a02d0070804907104100e4240428820018441c94408004610b4550702829109503011910b41109207407560301004540e000e840340e541150300c0c06084c2030408202d80104110b441c1030507102d01c440c50800d01c1e00d6044602c06040400308100c0d0b03043c038013822a42c418040f5000c4990008000c030041400c0c6000003680d042030380c000c0071600c1541c3d555040030001d820141c650303a000b06082c04003050880d0f004014214004050590585031700d041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 693573929 1250 693572679 693572683
    0xb0409031d0406060c0308070302090a151e17040206070501090309061e050a0503060301091b0e0f092d19021819020708040308040b1c180213090f030809 67
    0xd9070124480d62400908104c0c16801400d80715046030182044082580c03241c6007640a4480d0080d860346c0900518004075030240b00c40080039010405a40318416000c0000c400340940003044007020229980540003a80c3c0300d407400046900c03a2000e40b0341d07820300e205a61400c0c25103101040840c04102600000c3c03110685c8400401c0c800b8007800410030640c20070903030250592141212074030420900000207801c64909401c00c2c05802c1d07011580782c2d40d2030310b14020303035801c01d0147c044c42c03000e5082c3c000400c202c410310182640c050558030015180e21400c4407040c0341545c0b076103080c8081122a45404900302903060016aa0102c42c2e41c3c54205a0300b15031040100b84600d81c1903031160b581456040c4221a203e44400350300c40c0c40544001030b9100518108101c0c3e900850340000c0000d82d00180100741007043c400036210180e030064100044910004400c815511241e40b401c03980144031403c4405460f166407100c00e12021307031200050f842425151074a96109007039064000c42d1803a07050080303101c41 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 693575179 1250 693573929 693573977
    0x130f060213030203060f2503140408270a050d0309030b0112030801060302180405090f0303090d08060307030f030f0c0f0302070509060102072301021c020129130f0b040903 75
    0x4182681100b03840c1520056400300640f01651551030510451018114009c1c0d01111003c0c508040b8507600b8a064600309085074003124140300f1846108031030310070801c1080e446558000c001083d1010a6081c6400d00c080924030040a40030054140e000001140410a545000e402d044010601d000c000d824068440401030740902c04040c4100300311000300c03042004e0b8844c1658122404030700c0d43ca56910707a03032425003514641280341c0000428400e0125002030b1043e2036001540b90078450b039541004160700e40405201c09410000705c0942d074030000f486080c0701c040d070380c1d1320f400c101041611545955880802c030400450240c2d004420038811841c1c011581680a00244010f0081c0c0b824201e03200103199171000e0b124002e8610b03034284100d680c000c2c07040310400b068540400700140034450340240a0203c2c090811070380390303903803d5654210701b812000d0031160034003404444054080b40c140c90010b1100a03441c2041560b110b4106d00c06030b0340d80c0102d2102030f0090b69815407281d2009100c0b00301041d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 693576429 1250 693575179 693575191
    0x60310080c0d021f02010f0f021201051c1b0f120501050c1e07020d140d08160e01110c030601060201090c050a061e05090d140d0e030303130f06021303020306 69
    0x40d12810b2070016942e41d03800c0d85500c074151040b0101d8808806050703026084a101070070b202400c04c2210b0012024950181080031440311450302203903030740d8060180001042160a40d18000307038920301c010034120b11206601900c008540b0b0809682c0b14070001001d207503604000a2294004104014403000740a5581c0210400d400304e45480d00905c042c800700010040c400b983d0032808500c034010765a40c0411019020f030080c1c000c01038900c1002c8100d854409002014000c5140075001c1a40201d5440c00b5451540c0652142c2e201241840015250031808000c0c40019100d0000440030b140c500f84501b0b40208019000810a04842d20300012000d01c150400c80c00b8070161041040042d134030400c0810344000a46d0a05003000c01450111014030440c4c0e022504581c402c025502004a0304601454400c14181688c0c01842e03001d40c111100c02103100803590650082c404103017405980e504002030544a54080010f90341c03140d035050180d03000950000d014035500c501c2003055080510403694406 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 693577679 1250 693576429 693576439
    0xa09120303050f070806012312010b0408210d0e0f0a03020106091d060403030b011e050d050f060f0913050708030d150e0f061815010f020c0102070e090c060310080c 72
    0x4580000020030091819400d0000c20001c0c1c088103242c40e4021089400d90f00c6044000500c66850ba03510a1040d4403030f201c0e02205105100004825058002c110b240d00c841002c4520324007245004fe01e0301809030800c00b0000c5008160342100502410403642d80c0d103d1190300041400c0f0300e80740c105000c13540c05001314200d120340303032071107424201000c030700075500c5a8107040005109400745c0040b10507045501c803a0380c7c0c01d0f0303001d6000101103400c14081c0c00300c0c820f901014460756440c122000e034004810340d010794001444040c68031030362a08100c4160700607a800302e6040007402c252101c0740b40ca501548510602c1d08000303583c60200b0614082c039a0600700c002c881c0a003040c6804079201d0610300c01001101a850070201054450359001500e10807130b01c411800314070781c0c00d1113422030410000c0c65207111302007845030031400486800824482c46100058010f048404c3c81d0080c2e052174010001c100700340902a40024144036620600a0741c021440291440840c2c1c0c182428585060f520480c094410307 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 693578929 1250 693577679 693577681
    0x1b030f06060c0201020303011a0412200103020c1b0118140f0907050a050906120c030a270b100e13060f15060e010e030d0c02090a1b050a09120303050f0708 68
    0x2d130340c00008403411a40300a0040004038140013411805000302e800101c041c215580c869800d0000640318110725118280e0b02040c240c41c200c0040d001c07482543e4504042e9007151160394103003044061302411800040c14888021000c0701c00c11107607129150005000110704132420245401c0c00300c816007104a083d02c04403000d0400c4400034040f4021600c00000f005030005c0c5181d0a61221401d440e9440c803880c0c00018142803552075441c594004031050f01003d440c1c140c00300103500700c894204036800f07900c201000408d4180c2e111380140c01c1e8001c0882802d8090031000140d4040c4600d0030078071543c44015054100c5c0e01501e000310568203944140d40842c1d0274883c2c080020b0305403c464004844690a0092901c0e49403001602d81002d88407007550b050241c020754031355998000c0c440312000e9208590010301c5139a41c6204000712020010803c3c00a50a40c0a04290078044c00c010300341d020340d80c144941c40659804c256a0444507840c1c0c1100040c2e246c0e42401205d440314440b468010b00740741810310300c03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 693580179 1250 693578929 693578933
    0x302011d03030f0c0403060213050301050703060608060f060f0d02040e070309030906050d091515060c0c031b18151403060f1005040513260403060f1b030f06060c 71
    0xd41e00024002801c141e00c02ca000c144c030400208122002540e111105545800da00c107040704c0400300c14845e0601075401d01c400181c0080c40ba00c01c110a68045444808440e255602404400c5a0441409030410402c0002c154035101c41405061049107903040569107a0030a480d00c613031803030b018101c801810308184130400000e0700700c01004262480c030f2134015103d890f00010480505180d1001801c005040c802c8210100720b9034100780c0070610511a28521640d94001c1112803210141001e000e0740c414110600c005130a0018014215403a40b4001c11429200c400c030400303c0b001009001c1c134240d40c1d110104003240300901350740020840038031500002e90004000c02d80310303100200720070740c00c000207000211000b66420785440034040c0684100300034a0030325018181c09060000c00d40c0c400c913103911480740400106c000c0c03442450007140c0080c28945141d0383c404c042e103034a400d140901c944031521010720348510001c05141018a6402180180b0b01c401110100d0f0b5458100200b000071140311500 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 693581429 1250 693580179 693580183
    0x510060515120f0a0902061803060c0a080a0e07030c1401091202010e12011d03030f010f2301030216030804140d27030507180e071a0705070e0907030302011d 69
    0x152064a482120401e5564001000e0080174600c40003580561301084012003500707484280d40c40c480c007d904403121611912a440d1281c010303090001c00150f141000503031400d4154105000d400c01100403501020340f25590640704404503006940b0040082c00c1c83c000943c0d1106c01440105400c19810203002d6007600001c08015044a07440c0c01840a440c203d500700000350f0049240500341c1c5011003408180c110010303100c1c1c0c07056560039001050000041340048100c00303500100c41c201141c22a09103440c4428264910503c0704031418160f0901c82444250180b4102d51144c1d44241e0386d1104610301071038100c482d040358100c03c1201d68031000c43d99245036000690200c03a0f0607480400d038000c80d004001c2045500294000030300030300a0090000b00e05405001460020340e501405015403400040400e03a0f42e00e441c17050601010f9800c0100d8400e07549400146001742c0030700261004162a0350424038000030695012655034000a0100241039080c031a002c180c17a444019406008040c004040e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 693582679 1250 693581429 693581431
    0x5071d193308060a060602010b03071518030605070509041b020c0111070b0c0a0c09090f1502120115030b06120a0b1c060207170c0a030509060403051006051512 70
    0x721012001031001114911028104004185410454140e46099603685020b0820f0f4400ca001641c248400444545400b0030107400f41c0b5600c0410a48245485008a0710581c00c0900400c0740e107003114010010030120b010302da1184007943c840541e0740f00e02c5000d02c03040720850b185564284028051102c01e45a0105001440071004d280c1000407100c511451401e01c440c0350302088181500003481e14816070042402200310380150140380649640d40114401d5444c0c100e40100014820107074803001030119000900b041600080c0107007040b12600c2903404140081e001121014040600d205205515000d031f03408003401130780d00c141004882c0441d0a80c3c0080a0f00300c888a5860314481d0038140c850062a40381d40d00ea00740c140c4241082403c11000030f620151007618000100501240618a64012100000c2c0305000529080e4039a441c1103070315412442c0c22540c0508100400804554104110100c09503007582c0005d15920b000e04000e03001c4614040224040c1c01841003c6013003454086503 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 693583929 1250 693582679 693582731
    0xf120c021e070905091b031f05131a0f070509011d010203160807020a0f05060d0b1c0503040e060d0807030309060f050c0a030507140702010c05071d19 66
    0x861001203070055481c2003615075000b018a081c50142000700456000070400a0046400e51803100b0050000170f040c2c983d448035120801700c1400c00801500c07a01c0075801140d001001d8800d0364203203e01c5942fa090039442c0010307029080e030948420f000c2c1c8028001b81a6400030f8490402c640792000580018011911020320a000c03100b5011045110364000d008542c000001d4401141065100785003502c000d401c4844240d00400394443c000c251890000c40c482c1c162030f030003003241d4117200e02c0710306000c05001e140440c01e40044442c10800107000c01103442e4900c0500c681e0107035440e0b50902c00c802e03c00360402002e0b40d11510340c2c00414004070300c1d0032040710402d42e0035250201c0c5486a0381410000340541c40d0070203104518140030400038540a9000c5c01210445690a01c041e44964004492058105404004018040189100642c00342085c00d4641e4480da0984130b14aa85020008686450701c41803190070311070b0400c1100002452034004c24403504040c0402095080c200c03220040c03340c217416 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 693585179 1250 693583929 693583963
    0x10060503062806030e0c06070605060d02130e0c09060a0e22060c0f020606011e0207050402030c040e010b0403210201020d09060b1804020d080306060c0307030f120c02 73
    0x801e0703141d100c0c00d03242c40d001c0e0700c0302031003803800308500c40d0020800d03402d4411040020b00d001c1e202215135030b01040b00d40c8100d000600b064205886501e5000003044090405603101d400315503040d0050705c69185110120003626800240d841c524001e550505103030203800340c86880706000700511650b030720700c0310826901e0020038922556210724103992403624403c0d003458051801c0041808004064002c4203a03885180d0b1031150b1252161010783e56080c1c2560381502280d500c0d08560003d09146141c8011a401803044600065444010504aa00644200d0151200010140407007007004003018014050400e01500d450720350f84400b50300c07018032041321b130381d0039540d07002882000d00c01d40549140e00c003104009c00901c005481c0c804001c1c890f0050311809814060829031279001d0181b1010302c202c4e009419003041612075034494016030310041450794010014004060001810400340001510a0700c0e003020103174600d00060894640b810103501c04030305040b00181501e501240a151104116031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 693586429 1250 693585179 693585181
    0xc0905041d0607320d0c112104050603040602030a0e070803090439020f1f0c051c02070b1501050901030b0609040f0204090c020d05040e0411090408030906060910060503 74
    0x524482011080c1c1c200ca52803540b0390303001c8400099134002441050700c00d00d410003211070400c4040c0d80a0f51005d910403c135070802000ba0000c90402404c802c20402c50204241c07501c4d403504001a45600b0a44060710042d901200704103071041a8411107001a02c103d004014043c079000b00ea6a0b20703c03078140414041c03503d443c0584074140750b02d485a048042c502580c1460210410050006001009003880040c42410042900690007054020305440c0010350a5030804d00c034401c11024184080202e0308000c0104000c2031404400e81c0444402da042440c05641c9900c01d08260030007103c00b90003042411b405001c002c81c43e80e049000c40342006003c2c240070903040c1090000135610700076030042c1c940182c01d110b000d8030345081c241e0041007a5140c0400420014070b08150407650b60a00400309004520304000034000000d204052552152048200e04046580d40300131890f6014261011580c45201005011908405014403540710700241c0c0c0c0e82e10640340c054406801c0e160244280014400000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 693587679 1250 693586429 693586457
    0x31801060b041a0409060305030702090a1a0d05030c060103120e0301020306010509091b31030b19020d0204030c0e0f060913030302130e0105031905031b010f0c0905041d0607 76
    0xc01504c1c0145403080042105581c1c2e0f041c0281c9a90156100f00d100c0c5407040d000032040b001c3c9108500900031407842c171036903001c4c120050140380d403081401602c01d44030500c644a00e0040801c00e450185d4030404000e445030440c400003800c480c4240e0f03044d911903401030017005005c1c1d0303101054aa0762203044602c41c2c10307516001d5108803a15940d0800380ca040e103000402e118600f4403052007100c1080600d03160124040c4600d100514000a070000400301da02420218150381c048400134014400e070044010324007070f00000d03100c0c101da000c0da1080351080386078035081015141c400310f260b6001c0c0d4454822103262400500080303045c0030003880005009500c6502c0340a06209078155841803100080d40c0c0c1d0000e40f107602041004400740307e002d1103486503540220881d143c0780c0040480c2e650000040d4280450b42d080d502c0c1445410301c040c403007990303204074070018003819001e0082c0e0036400e074403844007107803c29040c4401d07642d188441c4103c00c0c444140880a00b0700001c1c206070b00071281c1ca490032009a0712 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 693588929 1250 693587679 693587729
    0x109060602060621121c0207120c1e060f050a0209100518060d0608071a1801050c100b0108070309020d020409031701030c080607080105180703020c0f03031801060b04 73
    0x1c09a00d030024071941402100310305000000740300c900360011b06000922131148076a0309034810290300a01445588006040b4540a401865521885140030ba1007813050b5812140700281200c1065a04039110700311100c13440e01d18800d09401854100c3d096143c1130000003c603640b040c0921400c0100100005d80c9080030913014019118801d00401003a950b1a1804120340540803500680c40c0c18010031100040c10342301d0034890052160102a20703410000340c0d8009003d00e5850503607403810300404100e0703000c00c0c10050100368040d00c101d00f00020750004480004051020003048403092600d890403140240c0d44040f4030300146981140c0c0881c00380c03024641150b80e04521158041c61440000021080258100720001030f1000c9504640f0b5035501c0b03480854907a4803e2141d140c0140d40c501240e0400480000b285900c5604e606015281000c01280289000c100c48072031880340c0c00200c00c0c00030403019118133800b0070781081d00038003109051890000c6548074078850303d408800c9524072104000c02c5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 693590179 1250 693588929 693588979
    0xd0302010e030d150b210901061d04050606030d021209060405041d0d050702090c1b0d180902040e060d05070b072406080316060f060f0e01090606020606 67
    0xc0c00942c0e48401e410074102c07015000d4075001801d00000701d44085070382101401038581c1114007540b241c11a020880e9510100c09000c5d1821050b95294100881c644032121100e102940c2d0244401c10a407600307051040c1002806010300e4400d400076039000c0801c584c0000e6104050000e03060f00341d40c40011000040f114401d13940002c0d085401d010460308504101280904020310103000e40c0c060080704441141c5520406600a40c84a50503002c1409440600043d0035a602080f8114515440c4040f94071310b07254000090000048441b07024004181801c00d1100003443c3d8039000358101403d00740500703010007000700104e0185818048031024400100b00820003000b0700440269078000604001c43e0310022460004000169855046981b030800e100f1601111740001c00345061201117001c10070320f2100c920060760240e88034103003001160340b00d10480340140491004542c801e8a007030141000001c050b4401c420a07481c00004100f45a004030b040790b4480402c40301c440c43c207002c1c50030217020500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 693591429 1250 693590179 693590201
    0x3070e0610230a020714010f111608010221041e030c1407090b0f03060a02030c120a060303030c02070f0302060a0c0b130c1a0d0504061d03030610030501030807020d030201 75
    0x4510500c00601440780c003c2c9015040781c0d00307540c0d01a07200d0159840b607081707500f40c0703034001040034050039130052103041c00c4410003101406507909101c901c42407010018094000460300c1e540000c1901e01240300c001108810104203000c04014581900c5042c00c11041c0c1c00060940d01c40b08c0701c01c2041521400da0a0801ca27800500d010b030040140940039a60380c510b0042500d139a00d04804500c40b840d10061110721610000c2c014221035481c049020007070740004d003e2280d0784500380030102505860b0b14446210b100d440500244043c5581801001c0e100740002400c19504440f0040c403010b0030b000c4130102901c0d0103607001ca0740d4000c0030f9002c9425030300300b45029008030416428091075111078030300c000340b080c05a450241d06549405c041c00008865400141009900b0031032581001019080264090300445000a02903803181da13144200380342c00703c0e07401e060304000b042100a1800038581d50031054149402c11566055689000183c850200041e1003204249092800c0610075004141911 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 693592679 1250 693591429 693591467
    0xc02030705030f030108060106080108100c110a0506040519051009031403071d03030c03040e0406020c061e130c05040f200423030d11010209090f0402030c03070e0610 73
    0xb20b038040f440d08090700300303000b00d891502803c800050414401c1e00d505050701e03410409442201e18401115004000304502c2c4021b1100c0081d5000032040107020704180a8020070292140d860203240190404070001c0400c801d11000280340c00c041b54000410f4602000c01c54000a9203c10f04d040c15144600c401820940d142e40010800c004154003051172901880908094200c0946000426449001c0c1c0d981008050380144003c1145821400540d90440c0c007800380140b4150b80c01c0304240c2000ca0403503900e1050101c2c003a01c0e0100481142040380d0180103140c030b055104801d5990055030a03000e2040314891a11801240d039403280b25484804030742980511106100390f00c014002441d002881082100c650b80c0c0d03613079240704200348405140c0701001005851441882002aa5585112405100c0d250340c02e000702507076925540101c500815114048070142e02d05403040500e03059441c041039000740c000100c00c02140003060300c0c1940041c01115507200c00c004600003281c007a19801d00417000d207 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 693593929 1250 693592679 693592687
    0x6030f022803140129010f05040305060c04061404030f150f0507080601030b03010b030a0b071e02010516051e030a0f06030b06090f0408070b07090504020d0f0e19060c0203070503 78
    0x1d00385181460f840c841c40284403203e1620080c405c0e844a10406100524140b1007a6546611403c004034040e00582001401e00380c8a480d05440c01104845d0790905900004041c000702ea000205c078001d5441d5034580c1e82c501804c1d039480103410700d1107a40081c90304603000305085040300c55803c0b1a0468080700780404c801d15060400604014041e00c0182c042485d14a0400180c101809520b0482030042c00901485440b9a1070300b05402005229000308025104903500d09410018808100e4400e0f074004600f5040210100f0000040c61084009005040140d021744880943c0d440d00303010002c11f01152251741e00e01d2103001138140354503040101e41c0b80c8034000c82040701400d9500d00850050b15002070541d16504100d1001d08250380142121000f0321840c00007403980c00b1115031006880c90031074441e65481020a0170f0342c001d4076510400711b40701c0983d14818403d0740311f50500000a280109260782201c1c0561401c0c8148001c040c000d01d4072080f40341d100a00810072140c1d0a0307840b10450360b407 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 693595179 1250 693593929 693593933
    0x305030a0e19060501050a240e0a030c0e063313060305040605060402040305070e07230909090d0e0f150f03090c010203040e0708070908060717060406030f022803 71
    0x14070100b8401140c201e841d0800101c4c0600f0051142d1050311b40c44030030010342006480c9600c4ca03206080385010100515202e2100c4203843e00e2089200a42c401d80c120840b40d030401817505203105006003110300400603100d070390000c1600c0d0104021520581e0801c1d0040390800e950058040c888c00f51110f00058641c40c0c000352940e4144d020b140300d41e000344010041510f46d038040209038421488050704640c85060244040070808818a40140190404e020342040210519100c0040d60900308003004001c070740e0b00142e00f0030401d9140c1c40074103000507140c080785600d0058946840010303024050203890000580743e071a0a0840030200c2078045d542915800b400d40c00d001d0765441120784651178096060851199400003081e039050714040c1e0000384042d6115031080303d074030b40020701503020000f000c0400544548144030260050100b41d4896111851200e411748506d24003403c42c5020340e15003141000814005a050071020384d046030900400c0b00c116040c4a207241c00c45c0e403000107a4103501c0380042 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 693596429 1250 693595179 693595213
    0xd0b10090509070608090f030702102d020c01020114130c0905090601050a140d02010302070f230106050a0806010911040f06200102030f0105060915340305070305030a0e 74
    0x840d0240d5071094000e980309251b403510341c03031440104d44055005000500044c6860800064030902920b00041640500c000c2c5a01e85512040c40b511035488049100d08800c3c1c1c1072200c1c9190a01c2800244550001c0e00380d6180406401005949001e142e52981c3d0100084aa0705d4401404860b03428070050504c5c110081d142e240030f00c103a40c460524400e00042410551102181040c8002c150804020640e0010b5020354002041207641d540c840318040d0004002d00d41d081005440c0303041d584045501000304600310360054200c00e01c00c43c58a40c040005190000d0414191a83e82e0f02c04219001c4181c15607000d070040350080d50000c8405100032850a070f008070300da0500f808941d0308100c00d000070b03a1581d00f00d11055030b0311076000151100502c0f050418200034845500090520201000304070280c041c2504044141102400c0080c410704010031700154254481e40c50029400b85280c450303901604a104611008051103c0440000c0010306113074000040100c10700d0036540c5540904007211 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 693597679 1250 693596429 693596443
    0x612060f070e150904020a12020a080103060f11030a0c0201090515071425020a091a0307050a050616031b031206060f020c0d06060302041112010e060d0b10090509 71
    0xa00002d001c80c5011010b0328100b100c4207602c80c1e0b01100c2625058908040c80301035030028000905002c092440740c000070a8510040040000390707900d0f071001d9411481d0950030b40d60340240c0c4000039410078150650810300c0c2000c580c1c200b01d101d080002c4032400d585090303000d0030034500040d183d4020b00d030040c1d041400c0300e062148200180d03550107803104951701c0340030740a008180d201d8141d0640d81070390b000c08100c80c0d086039509900040070042d4180d40c825206065546c80326040c414488003505891050400300f0503000940350884006c510a41804003144480c0140070340c001c5410100074070a4145170040c003070584015404260960400c4090401401c024590350b0780000b1107107815400500c10b845840e407a0f00c400255400b17041000d04c45020400e0407085000c0944409603660f10003c0142e076584559914041c0c40380c0b42d16102ca4401880000d0848140e00c580e54000c0e0450070406280e40e98080041d8260b80118003141c40d4407120405e07441140c0540203c0302c110300e40418031040d240006408 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 693598929 1250 693597679 693597691
    0x2c090408040e090714010503090106170703060614030c01081302040515120705060d410c040f1203020f1b040b010c0818190f06080601170109050612060f 67
    0x50907161184000c0e40d41c1c245200b00c5d107410300040d002c486250320800c01580c0003490039001041003a201c204050030485180c4026000d981700002c200104000780c02140010728000300302241741181200800e440e120001240c0d4108803030440015841e841e0245010002c68010308100080c2c582a040902180b0904a8007442400c0c00c0f038601e100c8000004640040d603801800071030400c0d540840711030240030b501c42201101c080411000d6505e43c0417142141205001c0c040848120006048030740c0c0300d40c030280207148003513401c00040c0402072201221404640702d41c2c101022021003400d0881c188040c00708000c0c4d040c0a040c86140c14442700351241c8580c20700c12941001360704141c20064490404002d0000c081640c240100c503000c0c0c1c0c0ca01351000000030050400d60244180001240707913a07040e6001007410010000c0240075142c0d0001d2060b178030803400e090071807070300700c02c00c11f0001c18103014428015503603101d00001740070ba03d40d22003410b6038990340f1084902c2030400f40d5141000c0d0310101d482c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 693600179 1250 693598929 693598949
    0xe06040209010e071d0f09100e01081902010e01030906020d060812040e060405040302011d03030a0f0216020904020402040f241b0b0915011502120a2c09040804 70
    0x80740b480c40f510042c0c0d0140c0c24035124801c070000c645009503115082c0e050099800130008014982c1e507140c042d1064800d6600881c500412410600000600c20043e00601059841031a0a00c6410511a168244290242000310780d480d04103004030050050b02c240184018000304540c44030f81d589800c601d0980b1003600985424201c0702c080a1414040d5110ba040140b108a010500b28140f96001070b42041c004d10022030155403c10b082c40e540d00201a400c0c2a55100008200a0454510174a603009881603401c0d4601600c5120340b00e03030710046283c0684108001c0740450304650b60740e41190018900c407084280300c01e568844000814203010f4000012031030300c40c248903c0c1441444440303401c44c40b555008001180f561202c0807810030040a0b0030440c810a030a40d400c0c2c110707104075135000f443c02c00d000c544c180025010090424840340384107c000001030100b2400369400041200c00d0800c2108030142000b0507a108010031014a60510381260591003400140300c0341c00001d00c1654601a4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 693601429 1250 693600179 693600181
    0x611180402090a060e042703120606050409020d140106020c19050607081804140702010c080403081807050d06090b0c070519020d0212070f0b07171b010e06040209 71
    0xe10090707100e18100c265010140d681d00703000090107500041d0700c40c6409040010340b040c0e008859040141e280190b05109444204440c00305940410b800644a0344904107014242c58401c025105020b1401032094481d0085452100e011031648910500c8500c90000921540d44441c084c0d2035621047d1140e005588081040305180304070101541103c2d13014003801c1ca42070654641350201d030050100750300700c40c1d0300e180042c00f250f41e94002e0071104610721041460724100300078007908491104c80c588050011130f00821010a8011104030b6001e4149480d1040c000503000c0301508117211504a1544442c5560011007072025680c82550807500c00c0d58014659200c0107284515401f924500920541c0014109080c110003040c0d0609207902c094503242456080d0750000341c1c20703070700c000511002e540808010030500d2812807540300106500f1394400d180c120680c60743e0200e510b000e140200071840c0003501000c0c4595801c0c0505491081c6402001414810603400c1d03280d110545040e4410100c0e48 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 693602679 1250 693601429 693601477
    0x80106020f033901050705031008010c020a030e01031d0105040b09030c070b30251d0604050a0612050c12060d020112090308010e071e0e0406030611 65
    0x1110824040c82c50540a071400b4080d81c124660f40144040500c100360803010401810240500e500954180d02c5c3c094480c45c2807600ca203000103207540074030200e030b041680350101707250082a0382c00e82c250176141400c441880000168050021381084910b034141c511441401208198800c40c0680e11034490644a9201c64900541c3c03030240c1c20350f5144a4000000800005040d40c000303140c1003103054482a407040781000070381070107600e6039000000c0705240030400101403129000c1881c0c3c507642c4001801b812590b800300a090301e6401362144901c040d080d804103590341c1c03490156402404000c0c1900740103501c0c2c007001000c4200d40016038612a0421000c200c0c03001499041d1480809504181c1c5060b0b92803104100d904282c1780300590500039079441c01c0f11005024004e03541c180e4083e84860001d545003d064800702100100303054100802e00c2c00350301d222540032030180f082410f1071400315070101001780080d0042c0040d03400201107501d0034200055081d101c00240c0500346600c030200364020050303 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 693603929 1250 693602679 693602683
    0xe07060c02010527120307030221180a051c0c050d200d0204021b0709020306030307170906030a0b19140d05010b04020301060c0c1e03030f031b080106020f 68
    0x110030080c0420740030300541106480d100110300c0c1c80c040c1c0c00d400c028a81e2068000c10703c00c807400d034003002d040e800025002c014076404100020f44024070b4940c0c170032040c0000240d074805014184c41c0c0d804071030001c2030804e82503980c10006c0025040c001c2542e10000d103803419190101910340012070794048022800030b81032070040c0508489681200341c000400b112054005401d210000d10f0a900900c81c0c0000343c09602d5910141a100c02140c1c8a09031a10700004030f103103070850b84d511042d5118010000c0207150345001c41519145131f448098400020110403d1104500071815020741140c8007004200001e0310a401069a101d81a1703501c024101c1e0050102c581c01c0c21a014221000742181c1d800c0025042032100f8120b8180a40c0000890215080020701a6402a48128005800310513040c0070320950410b0000100504140c03c0290130803c0040308181c0f100d440054107000b144029000300354000d8000003082c14a0700c04d0484201c000000103003c08900703024041c0148a0700c80001c07902040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 693605179 1250 693603929 693603947
    0x1a0403120306080303181c020d0207080f101806020d0606080708160806010e09040b010801110a1b0c0509040506010e09010c0804150e030a050a030b0103090209042a0602010e0706 78
    0xa148051481c581e51100300c501c08883c0d40e41450643d101d070038060b8080c01fa48500052108255501900014145a00082c54501075401010940d04060600b1001d8074000492150340c4d1480000072404003406500080c0921007080003810507400082c2504002034036501c91010b4410685401c6050345070041c02f02e501000450303405156001314428080f1180c0036062650f884481450002e24a40d04500850300303000003910211007143c00c0300018062440c0a001e201c20421070342045906103488400010120382c900071846070361002020030750302848030710078100c00a00f00107070110044c0e040c00e1801c150307603071002d11524044038150030200c0d10002d418003418103030707426a40d5410056103803a1108a00f1a80404a104200381d03200644000070340706201400c0e80d03070040c0d00c07415290f9010703000c0501504c407140d158a040520b40440c08005076240c000c00c41d0030940001000c5440c8500090801e050001d0b100c448030301d00044400043c1071541500032582668641c401c1e102e125590703600565401407 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 693606429 1250 693605179 693605189
    0x120703060501170112110301060b2106010807140a090b070f050c01030b1503420315270709061403030910141e040312080f06060a091a0403120306 64
    0x111400d81480450315991b400c020102008000007882507480640d80c070651300c4204040044d1941c0b441003405e404410402551047d421f0070425224a0440c40084c002400381c0340c084148070000c45c00d00d1728a403040200c0400380451501c41541e400c1b031820b00501040310510229a00c0c4121400c08410f0751090040701d84002d00a4006441c0c4c0e080d440840b521074000404100c03010700c0843c002444910003480d000040030004030258005140c80240c00011040c000300039000350700c06078590403c0074010487c542d100c09820500000c54003010300c0404100070100040782c5e244100d1030042142142944aa03040340c1d1100d02950140d03c51800f4103449000344014664401082c0c0d04800100740203854811018440d40341e480c0c0741411040801c2d040d0324444111146034030022400b1300c208002000c00381000502c0e800d001080303140c40b04c031030b048042008004501611307011412103503050040c2080806480c00c0c03880700c80d4603030071310b003c10b20203170494401035420018886100d1f107401e00911817a01620 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 693607679 1250 693606429 693606449
    0x60f050a0b011d1309060504022e0c08130b0903160305030d1104120602040509060303070c1809050102030109020706110406020c0103200a02060a050702010e071701021207030605011701 81
    0x740180184000030b004407030104c2d0049400301422107220001d200348516144952000a13040c140360052124080c00300b400820030f4007064400c500c1425411285250b4141c00c1c0c41d1400d0b0341030091501d42058098000300c0140710b6030103007000c05c86c444c8401c00340000340800d5044402c0e000b009070360300e0039400c50b0b840003501da900200034804070134481e500914018207400c80110325241da00c41114041c60212101500c0c92075000c5828022441d14541440d0802d8080740110709000145d00d80d1150310b4070a20682c80100000c0510180042d425040b804e841d41e0820001c54582d030f55121803501079840740340110360301031508402c9800d841c1d21100355025103069500500340c00000300b0054000305001803890514030480100c282c941c11104009080400c2c1503400703000141032290580d404ea44004d00954150790508540c43c90428000074840e0880755400151550b58071030802e040e009110b1b000710750407070401a80030807000303d401d40c2010007140c80030b80e034120041c50b50140d0b20400316400c0c05500a01c0c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 693608929 1250 693607679 693607697
    0x140607080c0a05030c091f0e010315033302040f0503071a180303041703070219140f0604080109081c02030601080610090e191b05090904061404060f050a0b01 69
    0x620004406850f43c1170001c0c0070403807007951402c0c00401c11208143e2040000e02c0c0c8c54140103007540e0600600c040c1444880001d00301e182156a020140c41484281206501e1240080e41800700000440202191a0743c4119038441d101c003190010401d850040c50b000b441030742070008221207070741c071890468030710f21200b079050088812006074928100c0c2105a850b100c1400040344030100e85000114010720702008668585480c810b024903290340d075485018200f984c02040002c8003003050144040c180c03c41d001c8980d06140302c00038080d4011750300305442c55841c12000c41d01700302034030008088045010455040c2a4504d04620090744411980c190004000a021403201c2c18a51420598001e01e41000e09465840301c042c41c4c5014822604115030414810306810030210714800c0395054205045000c00401503150090b0017449510503c038000c0c3d00d040000303814803002da417000c2f0a5010602ca9181182442e0500001400c4c0c030400c850000c030310b808046822031b20b0718402c1400d540c0043c1c4488040c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 693610179 1250 693608929 693608941
    0xb040201081302040204060509040c02010b0a06030b04020c06090c01021005040201020a0305070204020c011b1404120b0402032109041a0102060412032a0905100905040b0d140607080c0a0503 83
    0x10403207000d0300d0050100455030035000169100c2c005400030b440203648107a1140040010441075441580144003075914200b03041d41c40d5180c6202210959a8608002c10b40070041000b040c000d1140381c0b0b150180d805207a0a0103045200402c400c220718000340d00b10b50102140902d40801c0b6101030301c000b40503030711030a040d4001900440c09031540ca400144010304000c000701c010742c03d440f1403c1540f52843c0303d1445104495821081d81427940c64480015810b2134180400c0005032128140050001d043d0403000a0442d0340c00c02c409804026140384c42854441410001003241d0807200306140320310f0500300081d0348060001d035011020441640107201740d48803500e0b11010170352080942ca0405880c1c1401c800741c8040c54100107180c101703071980c496080c05000d45c010111030301600003a02c58040000324030502644400c0203002d5407803c0f100054450a000001151451425001012468074803200042480d000c10840d01c13074915138951502c40d40c0c4d2030310040e0f40383c49004000340210f02d091005c100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 693611429 1250 693610179 693610187
    0x6320708040312020d050702100603240216030e040614180405030c0d080f07030b0d12022404020f0306090a0f260c010608070315050603120d020918040b040201 70
    0x2401501a0411640c650107004440d800d0b41e200710078400c1c4840e03c6c0c20a000c55160304100c038100350703141e25504104460640c0e50362416030102d49040d2420038522010080d840482d039040702c00410041d00c102060840910700070300481d10380300505108900d03021000800420020b40c03035a048400608050581c0c41c51381c0c0c41e03400044043c006940c288004e20528180e0001000852008002500d031207105140c290400024244014910b00403d4203141e5036900b551607042080c04100c0e4403101c3c08412440544080b4035041c44411000c414440809041c4c0c41e00011070101d41c0128001d44840e40f604450409056803150103644401082d031040301c00e180803a280611031643c29114181c0100e4540882c69410000307407010300007460200002415110400d07003441558003c01c1d074031000d003038a6840c544407914030308a075105194a40b6103410002e11796940c00d020100c141c42d480003c094070382034101040c0001b900319880041c0155401281003001c03c0300c01a42911556205a140c2a196038580c0115 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 693612679 1250 693611429 693611431
    0x11190e1f03080a180b04080606030d14070515070e0102150f01090908040909140d0e0609012006072c0904020420030c0702100c0309090c0c0203010906320708 69
    0x3d003c0250201a9004030380b18079860000411825a0064440782003c1d807080c18410090a103074807960001461205164002080881014004c01d103a0740303a6006081081c20142c7c50103856641c880c80d0380402c81c4682d0005200c00c0c90990aa007120030711500b8400c00f02c01c4610907070382140800c6154004020aa14540110400038401c400306400d0550b81e04a030810b0b584203240403541e42d00850001c00740110b0400440034003002600e0040500e4000d1408248140310b0170301c20604002e01e0007414039012610080e015440d07000041100e11510f0300071001801c0521802c0c01e0280140215082c601d1070788002c2d00031407800402812003107552038690801004002401d5400d22044041e8081200d00d500318024603c11a40001d02a9071031100d807040203203450380b8a2144041c0002032000101003540308050030291034170004001813106000a09592480c40040000d50560807c4039080800050b0340000d40042440f030a240e05402d20041d55800c4100c040b20000c40581003280041ca007184502c1c406 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 693613929 1250 693612679 693612697
    0x206090c27041112060c03190b1c05010518030f0915040303110705010f020606040e01060b0a0302120106030e12030402060d0207050a0b06060a09090911190e1f0308 72
    0x402200700008140c005039040846003516500e0600011450a04107502c003050141c882070044d00b41c916000c80c0c001c3c03803404041e203094468840c201c500d80c2a80703410b0f40044003002000f050000302408401c070341c80b0201c070441e070300302c81039400c0074003088410702051650000e90751914017031400c05400e880441d880790000300c44d01d0742c0300c0d0090040801c1c0300f00940081010394041d40d0707184003140c1441e06892404502e0382c0300604120004094606141c2d020034150340000381154045031003103d402080340540030700e800a101440740000c00d550502c1c0c1590043c010b40e034007055001040d030b0381c92006400b1208a8800d201d00798010782400324a00106c44011948184010050b82c101218505020221381140c0d80854659100280d40e0040c0301d00040541d9000d50101c17256403420840f000014002640e030312401d00682d883e1407410040042404804025200140511083d10b1011402291040c030324826224010740e188041100001d5007505e90100381040c0361182051441c5076515480c0f6400010701e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 693615179 1250 693613929 693613969
    0x3050309071e0f060203040b0412150606030f0510030b0112140304030f0201030e1b120f030f090a170a1101020a021513050103090c17120324010206090c 67
    0x1145107110400d0b114a050904074500d050182401a141901c08580c1c00c441d0555000340300c1041145100400ca900351180d86000d0148540b1900d0100e070381d132041d0140a24618140351020400076419401b2046203291a5824025a1151300c402c000d04c0f21140005450895030314010305c01182c051070002412407003002d44408071040c40004508642150b0022242c002c0392900c400e0941d03a01d4000e24501550500c05401800e4610f8918829803031b90340740031402105402094201d05005200e102c00400c440d40503640d40d103d40d084c3d12800340e403084468501c036880c10503010552160a1039180b01d8002c3e450f0090180031095100e10650101c10220b543c114441c0124603030060b25844122142e580b42031240ea42c64840600c1c29160b290242d400080c10585803900e0780c5d003c950300c40c0c00401100c4103500f030100c07241d1000303a42c182040c1240b0300120200600000b8040b08800c9050316030b1590040c00d5480c0c0e0195488001241c4038401580d66102d103521006075003482c1d14000c10605040040864 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 693616429 1250 693615179 693615193
    0x60b0a05120618160609050a080303130201120213030f0c081f2c0f100e1f0207020a030c0f0b0f030a0c0917031201120305030103080a0c0b0405012003070c03050309 72
    0x44c1407420035865000b03000041c440000810090a1031010140504003000180d8103514258003a5a900d050307102c406030411010703910101105e102941240d02000c03400244000350754590400c001540510442110002c400040000756010086482c4c401c58581c20060392521003e06d2031b0131302820a06c018644042000008159010007884d03c0c00c20a860500160907030240010006080130100c0c00681080c03420180c0508482101040184050b49040082075419494082c1400280141000290840041d810100030b1001c0300030b10104440403c142e82d0049a100c50b2185200d018a005e400c407010310a10200d11011880d40001030500315074a007100303010341c0d2040b40d100403c000d04680c20042c2c00000c0c0514541c100c1c1c00b0041c0c0500341500c0007100c0040389030381c028054881440003520900000c82d65145440c03080c10541003c40d08003140ca40340b0705090801034020586401d0402e13158000070301d000f0074104950183c3c3d101d03040e03d841d49200785d5402c0d00c1c2070350507501c0100340311a0742c06008 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 693617679 1250 693616429 693616453
    0x30501081e070b0301150e010219020d060b220f1515020c030102030c0c060105091003140a05150109051305100b01030e07240903110114120103060b0a05120618 70
    0x1202135402810783d074202c138103171944020019040282da070240d181150004c20011519107041400010500d60517a8105525511801c01c500200742d03890345140e002e580701036004042d410f400c1d83d8041c03050b18500c04211201c140c4007404200ca07a15070382c8102c0201004001c00003c5c4050360300d40c640c8842401900d40003042c03a000a403c81c3c0c41105e0b2610407080115410980305130402c8060b014000c01e807140d441a0910403201003003000c0c54400108502d1089030360360402103050141c080256070002c100c1d841005042144114104240651144107240000041050f403c11881c8188075800001901003180e40d5030650003c2c04082424030305054869940140c400400c0011034000c0c81813002000416850302e0f070b1054504007006030f04080102009003800401c00c1c15020403807601e024204444440511506c0b0020790150100704034441d0704210000080c041d09811542205104407841110035885004102c02e102a015000078250b10a000080c8114110030308044c48495240c21190590740720 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 693618929 1250 693617679 693617699
    0x1141201060e011a090603220503030103081e0316051806030906060f010c051921020618070305120a090f0602070e070905010e090c0408030d061401030501081e07 71
    0x703544800780e07808409004101244909803400414003102d0f24051400044000103141400050b0110b86860503c51541c208030480002e103200441d8840300380d94403582c0d070341070424854002c00200c0e000c103d4003001d8694000c550400701c81c401c0d035070159844081190080704aa2542000041c011280340b010324031100d41e503c0030059449600b03084010600c41c9001c00070301154207a1818920305211103c00c8100001c1c0011440ea424808910030381100d243c12410402142891041c80d0465040c2d10803042c1130700741e80420140d12850703c00c603658034080c0f40300c01900d6a5035020720002e005900400c8012514903a840000c001f0b40019180c1800303110707114568070b1006016544100c001d0703400000b003040303030090a040407513000c08541040c400c03080c41c140c00641404e56401816216140719400284206584425035028150250489403074104103080400108041c1c01400200d10b40b14048080341e600c85d00486050340c0706600a0401d41240885044440300078019010150254010226407004a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 693620179 1250 693618929 693618941
    0x10b07030c051006030f020424090506011205090a052b030f02090301022b11180d05010606021b0a0f0b03040501061203090e09010e0c0f06040807060c120e0901141201 73
    0x710380006c02e000c850310400c401c80d0a41c0e95808800e404003494070480061a241d0001150b44440700800c071640c42100403500c01818414041d002e920b441c06201924070001440701000b03218800300c81d100009400103140001d18031106000c99002c80140100043c4a6003003e851501525400341c01e04c0c0398031001900f603030800b69400525500f00001030a140c0c02d011850076060366154400c001400030b0051840c8030388a0226504031003050b40b441e15803030340c035a48160141765400c034008111703c3e521114025190b002d19024001000c027280c4441d40c0b0703440c3c10044503040703a104030860881d035441c1c66100c90032500000c0041c0d54075540c800c00055603115054140701c13458800d6440d07034401801e140d40000e0520000d030840c20960301d41000b0720104500040d4241c0390710006c540f60f1100c186a1000218544156040402140512000001c8694221010400d0544510400c10441d944402c00303e4101204070340031580300c0ca40100400c0203204c00d140700402c201026210401403c5811080c43c01c1d40e070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 693621429 1250 693620179 693620183
    0x220305100e0703020d2a0b16050a150c030c030b0f09040c0e04111203090f04020d0209060c010e0f060708070813081b0705040c09140d0f030f02010f05010b07030c05100603 75
    0x100d85184c41c41110345410b0300d0010b0601d4032030110407582c2442010359090260440c104088032a40b85148c06001c01000440c0c15503610200020040840c61041c0c000b422902c044040464106020102d1480c02030050200364240030b0421401007010b070007000bc0018000d4030a441906065030003060f00300c114501c0c00d2040e40241404d0403a41800000d00540240d44072109181c0c2e041071001c80000e9642c0e81200d000c84108550141c3c60f4008184540000d100e11800070380d104000092160344402c064220240b00064481510041c1040030044e0340c5900f401c41c1c01000240015000500c1a03001c0d1101039001064003548030340c0603649075543c110356448424040001d0402c050f0620781c1c140b0401582004e000103071800e0011601d1400d0142c07403413905000303003035000c051100f12068079220302c03184c1450035070040b680724400541420003401108000d280c035001542040840c082c0244180525130490b040d50107043d04e04030440e1811501200100e0b8119164000d0803800100324066001c0e0328041c40c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 693622679 1250 693621429 693621443
    0x303110d122013050f15030a0b01030209040c020f0c09040512360307090c09050105160c061205060303030601051909051207081608120f1e220305100e0703020d 70
    0xe13050000700140c040b01c00442d507115210b401441c04401d05940d041d41e8001d01d198102142d0103100342c006801900980007000d80003840d00e1000011702e940001c0f031140b419480d000342c8202080c510f041c0304038032004550240c9154004083d41131007150240003080360342c0242c0d00c090401c0c2c0342d6032820f01c1a01200701030b8203110313507071034403081560301d000d0041000412090004000c2d0401d10070002d0400c1000e80700340c0c1e05005d404101141043e000740030041a980e8030003a9885070725102c078000f1740f40d00c41c501c400184091070301d8002034042c200027044074042e14058480c0b90400d2800c9030005011000c03c02d2440400c10200800a1b140d00d0301e040d000e12607170b80394000e030400301e0401c01594503040c02c9900114944070701003001c1101d03250108000c0d40c0350b40040596590f4201000c0040020310071441d51084800201040d00700718103400020300000060000b00c0c80581d03500803402d01500d00140070240441e00402802103594802d5444003002000700c3c0d0640781440c0c1c0d640c002502c18145500c007501d0310 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 693623929 1250 693622679 693622717
    0x1050a0f0c022709010b10030b0102030f0c030a110a0b06060d02090a080d020114040210080403180f0311040510260106090207020102061e0402130f0e070303110d1220 73
    0x91003000c94682d0344040707010000c004102600d40001c00c070244a40c090810308d0b940380000c807156407080c0300700c503440110903112603618282540020303500da00c501214000180025030319481050081003c15240ba0820040491920b0301d104200155000380020400c0c1c88c2e00700000c00c510340300c0345481c2008107040009420441c0807004042d003500c0b241d40d0117400c0c00c0526170401c4016030703071204400c04500051802051695443c034082c0c600da1280c28400c0344481e84d4050008110f11020741c3c40003070302d1084204030406d0072000305120640e03c040e580c9801d0a60f00c2e500500074211080348003604c01d040e940303021180320007002c481d9007103c405401c03110115030002048800d41d601000445e070801d11406680d0401100c94505085404003d0002841404c002150440c1d8001580005e003480c10390310400c00544d070b50007010b0355981089100440220314068a000e402c07400105202d1001422526440029500225481d0040c800c100c43e400070314420402ca0081540c0c9074010704114004d6841000782 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 693625179 1250 693623929 693623989
    0x201020706090b0f030604110414100f0e040e1606031a1903030c06141306050c04050618060c0a080d27031101060e160e06070201050a0f0c02 62
    0xc10150340c01c680140501c01c401001004480000c8942c0700d1140c1c50083d450b0340750003000401500944070120756803c4003040208089110500c028515a01102c68621000d003c01041c0c03004007000e40700070045018070b94034100301e0401d03400c40070b00240c0c10000d46080308040307a1090003020300e6400210000341d0307407103031103001c091140c0c4840622101201e02e0b2000e08007180060551180381e000090804c0b100910100400010303400850a0b038900b403003409650b01d003900d40c50a04084081003034400c24240004950307144e9000c0110340a881d005004a407402da40d01175104084031003400200d810140c10000b00c0d250030400d10003a80c40b54450440203a440201007030240c2598443e869500b030103054080043d1a800741c0900800140d0390504141d0180000c104d100307401044280e0202c0c400106001c104400027400000b980a1603509441d0482c21074000028003646024a48001340407580800c40085907901408009000c0c9020b0f1400e01044000c41e8045000c0b41e2283c5c5000950324101c09889036 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 693626429 1250 693625179 693625183
    0x20c0c04061202060a050a18090c080f010305210d0e0c40020904141f0302060909102c06030a02090f060d0503030405070515030115080a0608010e0a020102 68
    0x200341c1008040b0400401c1d07000508036100e0501020140000042c0b2010311034022185801c0154444000c1c41400fa95010354070040d19000a010f4005a80040044c480d1444a01c1040c140d94100340245550b00d446802e203e9019410000d94040d24014800c5031618802e1b409114100d12004010345400c00103030040c0641140f40498a550301ca12080320f0710b80074005414100b04504c0800340e0201c965040c82c2000c4001c0c030401030003d070042e04110114840200c101c041d80e0040c0000e40340e001002c10300340a10350345000640002548000c0c10014038400380b402c61803a9410100b245c0e007120b0600d9841c0e54038090b00410402080b841d002c441d010440145003448039030780c40b040a50142002540030b034001540840000c1c150042c09045201094081e2034940d5044001a84002100d9480c203007418040d41d00c880c0e03841228460b8030384948042c5254040c206482c12212806400380100303400340415119200014185250560390340310010380110240500c00940d141d00000d0714210b030032800028 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 693627679 1250 693626429 693626441
    0xc0c190614091f0504110d030f091401051b010615020c01020d050322051204090b130b09040609170415030c08090a02040e07030c030506091009020a05011b06020c0c04 73
    0x12882e4014201d80d54549500402071243c4801600c80058182d541e403401c100d4140700c030100c1d01e400081ca00756401c20150042c0b1240504034440d1240c41840d5519070301901c10195441b034160000d0028000e088400e07003c52803000129001d0000811081c1e200c0080381050f65001024100582c0005110506560144170109043c0007614207103245151891281d07a907254810308615140d66148080c20503c10244074600d2003410f60fa42d42540e860b03603010801c0c003411000c100c961242c1c8a0003084080050103208072032000d200500480c0d400e0b6215113a02c801403907100c2003651101030020f40c118081108800400c09010f140849001d41015503c0042c01c403510901c989080c4010307003080c4000d480000440c40c5001e9811217003c1200c40c16606101c2c1400081d9000424003000c044001c0100403002c10318902c20018641100e4000b501e243c08403054a4580380081e41043c40303000f040c40554400c445a0b100c020b5044ac03502d0252080d66070340b2049a0144042e9070240d0025420030340c031460b260083c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 693628929 1250 693627679 693627691
    0xa180506240a120302011104060203280c150902040203010e0a0c02060402060417210406120507051b01021909090605030a05030d1e020c0d170f0c0c190614 68
    0x5040580e85500410b015070720502500c00c02c08040000780c1d0406100b50010001d020300b5041c000d07192595400302070358a80120cc40c9001700d8088404d07030442e0b5281001141d90b2081d55030b48104120b03400380c44404811152500440440d600e0b04034040150315a40015030080040010015481c54004200b00881c1c120f40da1110842d00418144005640c0e0b000130744003691500c81600756986211110340303141420069110368503010b00030b044041d9080c007070041d00444508d5258400640b140a00000456004480220102e030044c40800e860362617035903034001c035035621a000520342100401d03482060140040c00000254400f4403e0003410228001c003401030500b03500500300081a41d4640351039000d41020380015640d02c00c0340407040c4608c1c0036245124840450119070780c0701c4910b80780f500d039a2a90040c00104002c00c150100b1031024081d070510448020109003da80c4691210780390603880000060780030b00c500354041c4002004090182c880038810240014040342003900d40015050080034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 693630179 1250 693628929 693628981
    0x70f030c0209160c0213230f0c0a0207030312090b1003050f0a020603040f030905091801050f070509010e0f04020c030903010c030507201c0305100f1208030a180506 72
    0x1030441282d0300145a0401e0705c0e8111004906400c407016990010f02140d0120303243d6545801c41c82d503003107803d032200501030200c0a00c42d40b156034400f2a4a02984510305201e00103034095030040010038860030700c0068080003c0341c0800e8040d415101c01c0d200c464242c1d000071380a141c000e410000c001d03081161030101d08000e0094801c001c03c4d07400084840c00b005001800001c92038403c241054440e01728600904001080e060740c50801d190701035076007514144085007a61030400411100590045401e1095490f0b030b80c2d50785011104401103e12581a100c101c0c0c000d01092150b800f60b40e42c1e40090700303a203071400e0019038446001004041c00d6825045c1800289880d10043c002d1495010481d45240c018115501d5803c40d2512413041c03800380c04856038071104180b1040c0314412030785074104901903400786120144190300c4185005070040c15210350800c42529401100002d600d0401659200700e40d40310010fa64105400101500c0c140e9040440b00c5070031100c1048001030104c1d400002600c4c05040d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 693631429 1250 693630179 693630211
    0x203151f0806160302070f0b071806030b2d041803020714062710050d0b09010f061b02060712020601120803040b040501020705070609140306040b07050f070f030c0209 73
    0x500850000f540d01c0c407990415400243c482e041c8442d103007402e006075500004140440c50721040040140400c002400381c95402c040000404070f05c42d002d03441d03900000400e10304441d04a0340c5881803201c21200c10103c04884441209103655943c4940d000000615141440c1c031100c03454002c0c1812201d401c1007001035140a0550710320b84885084e42c0c94102458a2114041442d9018400343c845842c2541d1748548030085440c5010b03071103c06440000100f06007848100d4a80c010030003104404d010300b2000c141c0c101c078104000382c400c1140d00c3d16600490101003240c919a00441c0803533210740c1043d2170a0903142040055160b0401c5160700409442011f038001746c82d1541c0c0c001c61844003406c05000b952000010030240082035040722685544a4110f8022a613074180c0603298a01c907129007408050010218641800d0100341240724507444415002140c0d00e00c80152610f801845003079000703001c01d101e120002183c1c001320640090080c1c6640c408050f0754410890202c500030100003160400b10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 693632679 1250 693631429 693631441
    0xb12030310080f1018050a11040609050601080f070c0c0e040c0f03080d020702011202070b0114030309060702040c090e07050c010c03020901050904052206020705010e0a1703040203151f0806 83
    0x11803c0682c1101020b00803520707040d0700e0145c00341520014005030003030044070416000c0090b044502020140203542c01d00015584840450441c0d008461560200e650240010200d03440c112007a6408a254104403012090584907604ca195458000b000380e0703205642070200713020502d00340400401c00801c40d680c12030704507a140c40850080c06221003031141c01084003001c682c000d90340707038903541310b000021500c91400d8100040c01210a00c00c0e503008143d07910385072502d818044200c520000001c1d00240ca00149542880b0003454094500410840b8094000c601003042544290080c0c0d010750f507094485840e103402a0071580c00b0101802418810001109581d07040020f80c1c007901000c440008003a03458030114805c840d501c5160210188510f1580f1040107140c0e030284c458140510004c0103080c84040350241ea40241d81c0000d4200e6000c541d54a0204841ca801168424409020b07140c104042e600803031607081d03003900c03030301d500e4616401d046039810680d219410041204e00000d00c1281420 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 693633929 1250 693632679 693632683
    0x180209091f0c021e010f0c0516081309020a110d020307030c03080a0e1606020c1e0904051c0806191a160b04030e0a0803070201021b0102010b12030310080f 68
    0x100c00c811945a86032220942d0850080c89900e07a408400549402c190300c0454010340204035a5100d01c007098900038a4800d50352184099601d0380708880951440f815181c1c98100c01e9800c001140000302513000e0012402c0710b4a40082c2121070303ca602d4596205290540341800e09421098203801c540c001e10404002c81d900c8141031181d203406040c191202c5d00c0d44007100d80075000e145071103400c1e8400c8400308401d801d0f024940108982165094a00c1400500f0400076007400504071a80710400e030194044507031402c03a42080d001031245003281c107824100300815580c60014029400030900c480100680c50034024000c0030f804580700a8114101d0a00401541c0b201e001c80c4480070051010800c00c90111460038010340050b0030101c3e443ca2407501c0d00d001402c01448018444c00340300385450000368001b001043c1c515903641600900280c1c0001070304020401e0241d03030890b04643d01d40c0c0340e841c1c3c55165407600c031144880c107401440e560b14250150b4410b806051303020301169071180181103028000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 693635179 1250 693633929 693633973
    0x12080702010503090c09090f0106141f021f0f0609052725050a061809050a0f0e0d0305070e0d020d02011713060b06030c1c0f18020909 59
    0xc2402c149460782c0311024081e00e401025151990048078a205104000a000501103020b180c0d010082c00303119116404044d081c0403044405030000724101500f000401038030a9051020340768812501e0b50b5110003400c20380d804007584000c8089030b49030010000c00200c1d004400142501110a001c18200150019829107a14425440c900945c3c045500c0c0d070f0030140310b00c0d90500003400c41200c42e400c81c500b10000003101c51280b10301c101d0a071400041d00034091400082c0d5240204007407074000385012801005004014035100409645180c030104041003440ac0c80450300901004142800c0320003c06400c8640203050340c0d0500c503111010520650f24149204401a0306543c100c24425440c40140c0c2c4400002000310320490b50322081200400701c1c044000300680c0a11340500840042506000007880309440e0190088410045043d00720790705140040403109003000019840c9003440301100f03c94264081d4040544084615030030751418041a980003c1c540002d05544401000c01e6454240 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 693636429 1250 693635179 693635183
    0x160605071b051305090c0a0315020a0e04140603010b0f030705220212040510090b0606130305030c0c01080c04050a12261c0506130902040207150213120807 68
    0x1800c0652000305040307092407039000300005400c00d00c02c0c607000519600030f80400c0b80c003201c0a00c61541b081c0c04c04d15021640404503900004d1181105520a0058011394400c0d0001800e003c900c010851240c0c0f1740b40b10341500500d40c00c040c1c00440c00c04008044c2520380700c030060341c030400c01001c0000e0300717035004990070007140c01c01c0301d84102c9280c00300d00c6400b040c020030b208424542d10104604200302d0141400714811442503050329181c688244401045813042200503083e4101500020020704129000340305503c8041c109421482d07907642c0e414507552023301e0107200c0d508041c0751076489503001807106411002101001d8185420500401d150000781c1c45118000d004110700d00082c050300c42080c3c7d600c030004808a1040301624840313140c259001c0340d600b0035005400d400519050025201d000c2c090340c0001e0207040c1c0d0403110025040680f078036800036a4000d900700404000a105038a6034680e0f110740304400340e2a5051400510003145155004852100301302c8419400a000d01c411900c00315 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 693637679 1250 693636429 693636443
    0x7060f031808040b0406090b0309030307030923030406032307181211150a020d0f090e0f010602070509071202030a0b031506040b0d03140c2d16060507 66
    0x108021516a04858400700042c200c044001000716440350307400002d000341c501c0c940700d080320785030f0303a0704116070600c400c483c10714580d003092000c694194400c0d00315480c0d680c001d5501981962001d020052001007121030303921a0760001508002c59601030040b02c040d42c01c03080700004668070101e0546c409005c01081201008440c2c011851002070143c90348001e801001964944409103180020698002a5286229510030352503000701402007400c8800f4400540d01500441001501c21b40307110452210303010500062450101d514110182660710540c1d0010011070154074007440a810504280c112a005989078002c002d41a0f41140c10340c981074628000050b80c0781d40783c8030020300807d1180c1c0c001c0c0d41400b981c41c460548210100302c07280112000c46040103600000c0003002440e0340c8103100100070840500342c40c02c41030882c002030548000001d0565135003401c08150030b1080228644076030001c045200d1500c503200c1c0b0800c1018220038121442404c00c0f81000b1007e403560090440c010450 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 693638929 1250 693637679 693637691
    0x1020d060306230a0c030e030a0819110702090a0e0a06061814071d0a0e0601030629070f0f0c061e140a140a03060806160e0111150103150e07060f03 65
    0x2c903106e035111500e000c400005481d1982c9000750002c0881604ac0d448010b0441108400c2c03e2602040c416001300c141c0342c0c029a45803414584c207200c0d026500130602040c15030b654840010941c0107006241e003041c07090350009030031824003031034407c0081c40c1060200c6141c90320400c900f06001c6140c0480e0031015600b0400c40056408420400019000c004a47c11050440f00010640d149010090082074242c0f4248205034031050a2481d441c150080c00344c1d04032404081d621003d8040b4001c0003214040d1901b0781d601c01940e224840180304070306049540c80311800741000b09503800b945110321a00c0041000c08480d040d000d00030000c0c2d00c01c14000d54840000070b903a141890140010b6501d4044036010103448010800024000380801d01c84c00c07886000d8100001c1189581e05032541c1d8806080d210110b61000410044502c14195803891000c2c0c441d0160111440c07986d411002c0c001d6214008a13801804080e0001003540c2d0810035075020b50388000018080f09411038881480428149000140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 693640179 1250 693638929 693638951
    0x1e0112151d070206011e1a03190917090409080f0c0f0d020a02090a090b0f160201022a0325020a06020114160e06040f031b030b06060d0204050301020d060306230a 71
    0x1c0b0680d44141111f40c90340510412161146028500c82c92988160002d100901803c0c0c070b0a46600250081907101c03050460b544251018018200130034000e0000503a150181d0744440e86039121203000100c110340800c0000516030108a00440ca6020a0140c030003809000ca0296603102d0400d0300034810082c0100040c0d040031968040c8200399040360401d1250b01b410344809a400c142620342140c5403c8120b00c131040c5030b00500896500302c3d601c0076484000246c5030008138008811a22001c1a4002000794155241c2910071020041c8031050f034082c0d2000451041090340c002503401a0256410300140c0b45600c1643c030001d5500100da903031090944000d00e4000c60700c15901802e060362120010401003403a100c5c802404054078401d840c5c581c0d00e00840301344d61004510b5032200030724035818140050024200b50007d0484000440ca01504281c1c448000900ba60060410000320950340c0070100f00388103160040b9624024142002440308048800c82013502a000b1302c0a1071860f294408504 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 693641429 1250 693640179 693640229
    0x30507030305250609030e060f0301051009080f03030105091b0a181a120703021219060504060e060406090e100b0319140d0206061e0112151d07020601 66
    0x455048a00c10062141d4058503020004041d564415000501407510a0781c40d420120704452561030304040e27450842c1c2c030b800c0800560010b011101010010258030000e00d0040030031200300b103407803070002079501ca6040009105c0070200042075440d00039648402d8814007000001140e001a000c0d1400591010040c581c6061103086540140300c40f89802541a01818254018000b0021810581e0300d258491210490903802404440418a20cd0f140820001654100d804650b08103c0801144030380e510800201107850907803226405c2c5c0110070400c5042d281c244144000360241c460200031031104462502d80ea240442583c41c20140d4408444034503903010404540000121191108027100900d401a0030804100340e0145030310039840401c030000d00102e80c0501c24513029090841e0b662480b0740c041d041010305071182e814410540342c0c40c42825040d01840404a003046202c5d0b81c42d03407421a2350405906c02c0281d8280c445900d009001001e81d020030700c0d034115400f001d0340617405210031881da1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 693642679 1250 693641429 693641467
    0x60329100e0a0602030406080a05040b180f030a050d1409032215030912080c12070e0904050115050301020906040b0a02121201030209070e03120a1107080304080105060109030507030305 81
    0x1640b00342104800260b042d400002030096130102d580f02c1d50b8039151480d001050780d03001d48004040c000c0759000160300f014800042c0d58582e01901c101c8041210f440c0100d0b040d1b40c09840020005100024202a5003403180030702c5140240942944903603140000d076140c0c0f80d006200050310001140000100c500303400d0002980505242c0640241d0b061406030080c0080080400031282c21a0002694140502a651952050880307030911407810361100a020388248005010005010600804079180d448180040f8840d0b480740300001100d0301d102900a0641080d50f020501c00e80c010081c120070350301c9000035641140c0300d4610b6035450ba4040c0b0002d03428101c10059110701c0d603201041c1d000c10400c0410034030781203a0090351021403580710220100c0b13500d191101c1c0076405502441d240b001d8181104001d060b100d100346400f200c034884000768a802c00840c2e91041899500109041c88200c2c400e1058540080c024284500300c945903580b4162680780030310000c0d0a00c40c02003006405000030491007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 693643929 1250 693642679 693642707
    0x2130506040806011e140f0402280801080705060f07050118060f06092901030617010e0f1c2609031b010221090309030a0b0106032910 59
    0x454559071501080c2d642c07a9401d10680603062244c0e0740305170170030790b241d49160195654084845004941c10003400070a412540e40b02e40c019a0800c242e040c41003881d030150b040120681442406000c04420091507800103030440c1e001504900c40c1005283d0b2a030040303400746d1394100442c5468407100d00700300d40145054a4800782d404800a204c108101031607210502d25100148200315054441d00310408484078161344030f41c0d103c51507c42510258280b51081e844050514022501a40b68450403e00c904102c2488115a4492584681651003071240100c2e450240e401041842200c050b0614050140e91001d424020141000e00001600032540c0e0384a071003c1111801d03900b03100101540c1d0340d0142441e100c005411100c05d11038208103000b20390504c0342c80c12441c2c801a800b10b020a0a1140c0a44455403500c02000310401e50b0718240441d4542c0b078099014400650314024010301601c0b5100006040304003506d444076038280a003c2c410a01c0d0200350740d40d1501003021102910482200b8200c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 693645179 1250 693643929 693643939
    0xa051c0c091b14040f031e05011b020c0411030c0d0f02181f0801050f0109031a0906090a020a030b0621030c0c04020405090103140313150f02061009021305 68
    0x100b00c020700040341d5150845580d94a8010411440d006070307065026038042e00800351044007041010481d0300c1204154560685c1a916405105607600f5003101d105c0348c150b2440c22000000001d105405004000440d03000751414408241014001e03d00c40c07000500c00f8000300400b145074407021045901c01c000a05074070b4400c43d554404150b24213412940060300c40e21800e40903e140d03a1070582c803042c107a0300182c01d44564461380d003000c007001020141c40310414104200810008082000c246003800d410000e80d03084665814860803690400d10010480c004a074042441303c1c006031200118101100c1c0c010060640c00e031200000650401138662961000b10000c02889440b603c000c0b00504805072008122003030320300303610140016030280d80304031644084900010000b2540085041c03c003851401c00f52490038150300c04008413807150340c00141c1c520b400355101000a90f00581491100300700c074002850540f80c2800e4111210320523003d4900102c1d004510380080840c110f241344094100181 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 693646429 1250 693645179 693645191
    0x70c080f03030105090114030a0210031103010f0e010b1926040c0806070309080f090301110304060915020319090c080a062a02070608041e0b150a051c0c09 68
    0x200c660707a0350000e014092048480034000a800042ca4400512002010703015100c2c9a907250208261100d064071040141502e03503d03000068100280114081e14110a0005007036080503105569135005030080c0945400400c020300320a015421240d079000020b1a04046104888298001d460004801144040b05070030600c8200b050b100c003c0300a407032000c4200c0f421a0b589650032029103c02c864090b0002c41c041180003808440e080040c21b0540000c2c00202e2413034442d00b20519568000c031800d8902c2a13980f911201082016104204150079103d025400d5041800c007509107015080c0989220950b5100c2d081d0810546501c418010480390056402c00d0724503051140203070551b00e4915914800301c180382016200d80703c00d00d040d5410701ea80200110f504140c001d60741c4007030252041c2e4402021900c06035603003076100039a09041e131007000701c3d007940c0c01e10b000701d120a044088101c074801d8441803030500c041d031900d001e414610401c5070000d5400010360304103034480c4051a0804205282002 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 693647679 1250 693646429 693646453
    0xe0102120a021914090607080c1207050c06120c0a11120a090e0c03040b1005130f0b040e03030a0b01030935130504052203120e010501030503030c070c08 67
    0x107409003803150903840490303002c0c0c0d00080c1c048900750041348410400340300600a0f209035082203005000d80c40c0c404c90a0781e00e1310752071280c1c941c5451401c00880008031400900b6400700002408018803160051301c543c1d04110021902d030b1007981d00105610745026011441c0010f2620840c030020704480641e00365645c400304210290344d00d6208401503000324011030000580b4250f0946450b21400c400c00100c5d003140c45650300c0e01c450750005440c1e0311a4080c031450114050b9100159424402c0210b0000504500500c602d202610700e1820202c0c4200d10780710203100313032020100450f68800d601c3c3d1700000306030316a10f0050f0000e0a61840241c01554021302e402d2044c01c140e0b0741e003841a14103a9424042c5079100d11a0081841100b401e0100c000441000b0011818140c00540c0c22908000c41d8107404480141542c80c80c0c0b0003220150300040142e640d82141c0c03501841a203a59144940003030117198195124159030303100140c0001d2540c40c3c0090020240005000c08602070300e6414240c4e69038405207 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 693648929 1250 693647679 693647681
    0x70c0f151103011508010810091403040602150f07120f090803041101080105030a12030b060906070605010e0109060303051801110615150a0e0f041d010608010f0606020307060e0102120a 81
    0x9015a150ba4011310b13000a8400380941d85843c12074002e00010405210012800f201501000008540f500b841d048a891908014009040500641e500070400911a8901a540280c0140042c05c01480303850a0050301544550610610310380e590002c5003501200e01c41800130310076504050019007020040c401000090403071541203a800360385010050341c80e0400c05480c1c03810380c1c4008040e40c0d90382c0082c10007140280c011004035540203001c1401c1260710f1012694950024030210350640c1d43e00018072900820b200424054443d46504000844c1540c0d80903203944641490620811141100c4072500c7c2c2c46030324210440d02d0b111042d5609802d0051401d20f401d0590384040788078424803661807420200003001d8800400640d51900c01a40c1110181300843c1c0503001100c0d0096214502c1c00110300c444544000740c11030f100c000203043da2a14281c5800c507039408100c3d0718014100401007107441d0740001070b9242d0540000300098044011400d1900a100d010443c2c0e00781413142042000306140303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 693650179 1250 693648929 693648931
    0x1b070c0510020625090e0c121513361106031302010806040b040513110a0b0a050a02100501030c090e1203070507020a051c02010f0305070c0f151103 65
    0xc1900c1c0324501c016100016600c440044070140110884244410341c880d01602018031615041c0c1070100040ea00c030841c0701044201150301403008040041c16196500c2c0c0c02d030700c030369010341c0b01c0c041400c250794950000b54401c074101c007101c0e1081c1d440340348060a00c03441e034818100c40c480040d11a00080032820860495190340756091b19813204015221140d81060030860f8454102e068050340c0a919035401560785440c058000d64202e5542d503890030341038035a44906030041000102084410f0914603000e0400c403d10010f05005a400304010000b00d840314062740e24000040c100741d074607540070400c220300d0140e0744401018510705110000042c031407400466000e40303465100c18812000392103545961030300d1070800503500f010300708009006144614054a881403009190780340c2155107030001441101c50a102601c01400c420b440c0c011581c2040f40506058004c0c14140010f2030b0051000e483d4a841c0040a041007101c10220303400c000000300c0d02118003108010030011066421006034050708 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 693651429 1250 693650179 693650189
    0x1e0503120c0c0a03032304151407060603050c121911180103150605120d0e010c02060301091d0a050a0308041425090e06191103010e09100e060f1b070c 66
    0x3c001070070700070b007022854122008d986203280d0307803208900c012104503490b0407192050860b110060221200181d0720b4010305c00258002c00040905154000410000301c40160b50314440b82d000c20f4450100c036a00d007201c2d021241c2c0100c03c00120188010204000903c223080c04551166507100210400102c120301e074079184030121003002116111014050520b508000d0449550311454440c03240500c16a21000042c0040c035092901020700d80c0450720780d4001303802082070b41e5141c1c803000200368468aa082800748034100140602289500d44545500341c03804082c0c100a81ca43c00034041c40743da61902d0140d032041c1411a009120304c4014200d1081c4402140c04903540d04c0c0f100020340780075600500007040e81800160035981c0b1244d04804d0301035400040704103250346402c0510204e400e9100554002c002480281e100ea01e0070100391414020f00003d140c04680c40c1c00312014039180700007200c075440115030311000032680380c1d8100503a840da04006000d04000c40040d003241040404120001110 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 693652679 1250 693651429 693651467
    0xc0b4f1203050c090310110903100b03010506010503042f060c0123280e010903080f090105070903020d230c030f010509030304170408070e011e0503120c0c0a0303 71
    0x34440030841c0f40c080c403c8494041d03240d4003521302d03d4007201c075640c801003494407640d6640345054064000700e424102c82d8021050010b40c0c070300d400642420203002e00e031751204003403801d14514601540c03048200c02e0822000c62a840d038501d50308148140c90031b800b01c48200d0090420740c13605071042070940a072201c028041340303103018000200041d00d10601c2c41c1e40202080709800d24203400c015401a40c1c2a891520f4112a548070301904075408000e02c00c820320300d8003a44d6490442e180a4480101010000d4541c103166071510003045855a8020101c8056071307811200b410100940c4e042401e10703100c036a45030722054080941d00182540c00019108503240050b401d80d2030007608000c1e500e00b00d078000c80b02c0b140c541e042000041c00041c00c00c40b19011100105529605250304c4441052a1070126001a4001c0c0413800040c007490007000c1c92040301400a030900c080541c14440842d4491a03210660000442d0100310980d2020007071060300340540c0090b00e0442040d5882c2402481030700e02c5481e0110714 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 693653929 1250 693652679 693652681
    0x10c0e01021e030f120610020d050d05040311010e072d0501180f0e042f092d041a01030b040305030c0c0d0c0b4f120305 53
    0x5280160010004504140c0142a50714000b4544920041c5074204080c01400108004810b000316403001d852540341003105c0000e00d00d401400c0c0075400c10105100020f56000c202180701e403590000c21a1401c40524074041008c2d292850142ca0100384c0c80026181542042c445c00804c8100090000446281070141410b24521401003401c0914501403001ea234241154140a1540a481d60541402c0481c1107560b844c1d6607440c80401c0b0940342c0d000010001e0340d0006200034003007260043c60f0600c008a01d10740103240168180c512855003aa1143e01075064a80081c800104221034100c4041f04150300b6140407900d00c0180c070030408115401c5407180b501a01c400c003403507200c441ca01e050704c2e03008205188a40721928255120b4000401004909004100000a488040c0022121340708030361940201c88003949440c144046000304104020328201c0020f00b4221481d035010a08040e082c80351440080c80b55180070b201000c43c04421a480340c0c0341c0c00207000c10102c80b070001160000c0303030380070041 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 693655179 1250 693653929 693653951
    0xc0f030c0b0627060f060406020d02072705061f05040f0905060102030318010605332b0b0316170601060c120915030207261e040509010f0801 62
    0x10294001942c000c2e601001c03d9400c1c0782e4000c4541c568010000074220b00d08079110b503000401c140c0c041d030031520058200180102c00c8980400c82100605285008041c841e005031807130780c1d6200b4012100c1c16080d6240e101150340c2c2e40322211040d0141d4450b4184500c440e204d0100640642d11903c1804c1c5980014074000480005a10840b80a014164095890b40c2c40b940c10014205920160400d007556844100081d0750742d0f507900403040c01d072444038054915001008182088840303524038000d808010821001c403040c000203e10700c174420380100181104510a0420020142d030013070705806100d4103038040004030201002c1d4023150000d001c00480c2c864501c07a0140c0ba00c0c000e03c40c0e500460031001603813000405803c051f2114001e2407614802c4940d4480040700d4066107441408e022980c009481c0040c000c4c0070680c8041202c42c0a1004260170503d10041001d114102c0380100711034031548a03c00014a24088a0082c407005040d10013075611000149044003092013001c0b200c0d80303840c200074a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 693656429 1250 693655179 693655189
    0xd0e0306060a0f060804030905060301120212420c130611101d1209041404020f0909101a010305011409150121050412020303040b15010c0f030c0b06 65
    0x2041d00c1400308800201071504c24103130b4910300d02500407010311603400c0000c01c01c0d49800d4061802080c8840c0344400083d154014440421980032446505404c0304041c00403c840d80388400381d403244a001100c202d460f01ca18407080c900100060032845482603418000710000b0200501402d4413a18071102c0b11954501d01950094880c00400345560007440800c6148039041e801075914483e04640303903155010940c0c1c0c40341400504959503001240118010301c2904003403081e0900800c2103c540001800c1940005041c1c10390700c0e4000d40300d018250300245200400303201d2401c0b003001c0f01405014078013000d88280704010f010445140017a1501c000095418804810860b0f05d45015183c0c00031500d038810080001e10492000c1e5041c42100b132024001c43c40d12040301006207000100c00903c03410705182408208410358020000c551091042c04046542c2c0e103d02038220034103c41d044402c5d000c030310060303c1e48820354101804085a0340160814141c0100d02240355030710481254100f0364070001008 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 693657679 1250 693656429 693656449
    0x50c120c010504050c1228081201030615260f0d020703021f0c030c0303060b1c05060d0b0712150b030406050702032a072c01140f040c110d0e030606 65
    0x10b601e5a02c4a1f007024150ba111080080c50341514100d485484a1580c07141c0032141d225845150069001200410070702000b07205140408551181e0192020314010140007810304070000700340442030300410441103140802411209032601010b480341c00008140c0030b5200c00e52403005134024048140c2c00700501c030055070f01074001000740d02d4041c0540d14640341100c0324645180218145550b44001003a00200803000e03111003140e01101c03a590790b60240200c0c007640c00c080c010707078000c2103580c0d0880e001038614101a9400400c7d4903241080750044110030029119a2142c0b203040c00700d546012565144a8000b58803460050360140140e0701c40c4401269030b4030502c02101c490020352101e4400800c1ca5070381040e100c040c04002c030b4407040d40b501130201c40650540880c16080000300144444d03080c03100100c6e40140f0003805020f80b009884008140850b0703407414002c0c42140c2c0c032038980a109004582c111003c2e8088400c40c2c0c1640190000505002203101406210b8407c00d00000d000340b901030780300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 693658929 1250 693657679 693657709
    0x3060e010219112104181a060c03070c090515180a150b030703091b03020d0b060102031b06060301140108120901211b0e030a03050c120c010504050c 65
    0x304840c1c0191050440d40444001c92a02c00e600a071001c24064058018002a13000c4010704d200d60750b10b141500000801c0b050217912540b150408102008044152807040c9103491305880315959841803041c901d0445c4202c00d4014502c1007840700201da00145135001910408030141d8241040a516040000d1400701e0f80006004144210019500f080503401011040c4010300c12000a143c5840004000e80c10403549280041d59400b104000d100140843e43c009480030390089442c18159004920560b01141014200114000214140ba44208101c030b00c00a4602030401250344900b01007501c544003a00c007544030b90308150303401030040c2d41c200710b01d4101e078240d07401000004450100300c0c0641c0c01096082d410f02843d641c10140303e4503038070341c980c60003a84040005207801d00b0189030141160000100b10400c41300451128440d2400101e81071220b8050420a445445c0303c07030351a152038806100404c10190100f0701c1c1031035010542026024522540984140f00222801d02c003180000d5518 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 693660179 1250 693658929 693658957
    0x20f0405090c16061e09140618070303030c090e0a090506150607020f15040308030a0513032c0d1506120308070806010203090603010602030306030c0303040f2102100903060e0102 78
    0x84000002d616034000b0614070a07410010f00e10100000c02c0204440d42091b094604103000315a80a03814818041280d00c0000b941c042400512041006652007200f400700805260f580e100188a203400340300c100004000400110081c0e15280c020361014103403003841264940f02d03030804900b040a284206088007203005d4072450515a554007040f80319242d10302000e0700030003003036000800e00b1608001040030354010070599590382000c0030f01c03c084950043c44103005000007040c1000099100b1a8045040b422261841c80c1301d80b400100e00ca2030b05c1d21410346501918034a921002c10440c800390341420000510200141c40d9110007922a42c815504001c2c0010421400604d6850142c8005904000c061040f02e003080c01080201388154006e800420159201104001c2e180c50308001c5001c1c546020f4029508007840e0a00090450b083d5000b0818481d000000d024642410640b44032032498004000352601e0840c444054070742001130000341c4019040c014925014141402200c01181c00114 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 693661429 1250 693660179 693660217
    0xe0f0303070c110d020a030b15030c0a090c0306080f0a060b040c050f0d022209180b0c090609041a150c0a11040b0306101404050c040e19020f0405090c 66
    0x664041d03010088001254002130005030400076840d0f1384100000f4500c1803122413071a041a84818000f80d2820811610a0344050894500c98032024201e404564011802096580294030b080c0d0240500e0b8100070741510507000b0442941c0c900280384c142403801418104043c04016050005a541210b001742c0030490411481d40603259030001400260714210006007020394030050312242c03109580341804190b0400e601449225000c0c8180015502c4e46400c0f4503080c400ca958002000b0340060024148408c003160050142c4c0b134050881e51085002402000721103005426506c5020700c04540c06d02904021075500e070520520320407280b16a500701f00504024100e0741c0c803003030350701c054440031b641050304d400c444c0c034194800700b00f0140581000380f00c0e4500d090030500841c1c451280c4001031482982007d040c04110407440c4110b40680b4603955601c00203a0f80c1000110348280110700e0085910700c0080c10040d03e0b00c031480a4025107504560801060b11001030b071075034600030a400311142c0d9040340 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 693662679 1250 693661429 693661433
    0x30f0105061315090306060b030f04110109050a080105090c0d26070209040f03030c0c0b010302120a1703150d050c1e0301090f021f08130204020d02040602010e0f0303070c 75
    0x1c1c0c098000d800c001060203042586070141c01d055244588404408651a0032043c4200f03d514055030001e00580020282589454640380400d6000a03002800c03d040741c40189415903c0f4051090250002510303d402c03044d80c900f0036500030a4103c8022609015485610041d032420120544030300790000c000805038a118049004007400d8044810b280350010880b403030040e20380b00c182318440c60040030100c5220b40c1a0030040c00b507408066441d01042a01001c0c40001103d180340709055a0b015120604020b030030881c0303645070003403295000e0929070104603407800407034000e4011440740303103490a00300c2d02140740320500103002c0030090018443c2d00f001c013a109650a00030f082a950020070702c550b42d07582c1d00030400b00f42141c2c404075051380c00c9103609809a06500780800c10705000416095a42184000c010008005449c09409400e403c01504008019903881e60141c0e0f0f47c0e02c0b44842d0466580d80c0e94500a4001c042c2c1c100c44c0d0400380034240888802c20004810b03607219582030380300e00a0440b455 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 693663929 1250 693662679 693662689
    0xd0809072304180204050c1e0c120c100605150307050307021606020d141206060c0c0a06030c020606030d0f050c0102160804061e09051e090426030f0105 67
    0x1090070080900c46050103440aa4503400348001c03841e401c00e591a1225040d006000035900300420040441c0010000850403550070122070b882c2d060a401403503203c00111f00980c0c2010360807600c401011201007807a041520000c92140d401904110003004855035413010b00040a020b0a403d010640c0c05000207540c2c54014401550311100b1032050300c5004200c0b85940010201340d410036401030340150118000c142c0c2040c3d81041000b071022002d07003424501000700303e5400c0020f040600800c0d01103003444034182c0421047c081d481c00101002c0e016034458100400a20513034070054018807450b07001c00c901e814040303180d40027005d039a52081d02081c603031502a10303144d100c60014001036500704908102d4856880b001021248610203540d692854980000d010300b000710002c60445140155600c601500401c62800311001540c008110000d032006004505001c1d81c0020341041110b800c00040041b0b0085071100f4036400d0f901d110800030342d84103000c03d9000c204d0b4052035850710f0a00600462502c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 693665179 1250 693663929 693663959
    0x112080a0c02030d050d0f020702060406051c020c0d0306090e061f080109050304091b020601050405040303020403050102030f06011101020703082205030408101802010206360a050d080907 82
    0x80d40c100300700d1030121a0302080c9442d10407082c090008070041184e00c54081c090280b2980403280c484254140034203900062018411072142005000001406404554100c1c15030b50700108025011521034103490300c91a101c451002c4e80200080c6003810225081c1c1d160f1103546040b4110400405140d40c8504050f032558038804010602c15080000021301c403032003400b94028440c414400b0f151030710f00d800e03400c03001e036103100e24002e03181c00c0091000e120703541d8000340842c1112021607001ca07454440d420141c000340710f55080070300194000010050740b04000503a042c0a40e03000e0340d03440c1d0f503241c050070418204e01404500500150b00917010515003a104407030703011751444404103032518541c50354801e86107034403036807140e14250446440080f502e10743e0301c99402c52105541c00c189150b2120750000f0f407910401011302c2e819090110064200305a480c0150b141c00c1c461200e0825403c00a6003500e40d90242020222610b00c20190b02410540c8104401030080850400a09200741044014002625 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 693666429 1250 693665179 693665197
    0x303020903010c2006071202220b031b13030206030411030d09031a070504060809010b04020408100b03010b010e01050a0c050114071d032e0507030501051305011208 72
    0x18003440108032640e030038480d0b1079440020341c82e800642411a09801c42d071601004402036240c1040b400c000c0b030140c00c0000c40310041c00407080166144545da61803d540c60414451189440f00408082811010000218020400b0072411101c400d00340940000e00c2c801d604020f00902941042000142450380145070814421110b02d41000f0443c00880d140075406100c080024401600c20414054400d5810b18408402d00c5150040e1506020140940c801c910400c1d0070080d102c0001020000c0a5010581c11103000740207542c1e840d40c03904c0740d550740ca8040300d144915910380991043c96143c14030401c140c3c04010b841e65004036202000558084d044000c86c03505010458401d040002e4080c441e60106001d4641c110001d41020140140b02c10901d504690060304810003904076030350001091820b07000a001d4103500102061001da115031200a03541c0c024030304000603c425190150443c0707060302c1f016103a6044030104d020010702035800a22a2440c01042c000d46a000b1604840c02000104 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 693667679 1250 693666429 693666431
    0x40209030a150203041202010207080a0c03020c0405190c02072904090608030a201f02040803040f140d080403031b080307031406010e060d090302070806041209210204090303 76
    0x1280648402e034540e42e50100c1004110f9000041004002c1e81545414203211117200850414000d541c50700f9641c4202e001c18001d10040035809410103100300310060880c0340180c410301441c00c01c4003501c0ca24080b04103012541504240025084503c000b030f01030122010030b030a81c81c0484440006c622036015100101c40010420080856000d0140c01054001c02880b00259582c0f01c0e8498001d042d21a46100450156503c0454020a20b400102141d080c21405680711a000103c030305000244500e88c0314030440d000120300054041d8509841c0740445181030943d041c107015250410411060080c2c00070318003401400207001103842182609081c40301c2144c079211200d50390701c3e02c010503001254142c0010351204030302941024011030f0160822300a0030030b010229410400152a0300620031040d2060369034410303460505108002071001003901409840c410306040c00c144a42104011080c80411044180018880102d820554403500c001d1154509107200c1d900f00302c040c0503110000c1d0109 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 693668929 1250 693667679 693667693
    0x90c1917070803070809030d08041a06061308010501053a0303090b0a1d1207060908040905010807091b1b03090b16020a0b09010509060d091502270f04020903 69
    0x2101040108113550044410b540c85180b0300c001c061401c9110f103801c00410510b5818040054001d41440e0041e9000d0740c00340c4040d5440801060150190b03030b01108205021a0f80010503400640c861811703200c043d40e0903da0b82880046801420712643c0c41040d0100e8a040707005000d46102e122100594443d10340070800c100d6a40b24007080c42020b540d42d1010741d640304058580000039640e5106c01580f000c000e0303c9000c104d541c1200c4980181d00d0090401a02e5128a4081002d8141100e016150203001041556120010644c5e2032006009011156140800c1660356810100c001c0001030303007a07580d040044070044500341041002c100c085061041c10300011500981100c00b40148002125519500072030724010090350040079030025440d49401c00c450142643c0c00800c4030940002980d040c1d654202003081d0100900e0703c01005040c1c031800d40c00199004046400410f6003002410110f40598420b4003900c000904100000307501c032114010307240240c02d145d0003400138448000c040c2d4000d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 693670179 1250 693668929 693668939
    0x504020a030203090c0109150e060c03040306050405060a06030f020609010c1a06011b080901110f06010b12060f130510050409081902160308030a060b0c0105090c191707 74
    0x180d800030650400841c1e000300c10004803000402200f40d60341000d2034608010751910807001d410f00c0d044514a0100329025041d114140c07505021100c802042c1c03402c4a58955076410000d000b0712003588c049130b040c000e517800b042803070409000760010340750000003c1d800c00016078200840707035018481e03290500400f95203210100d200e00070441e140d00705e060b06040d60352524000041030940c0000d01c1074002e030a003103480804604454140c4840c0c01c000c0c01d06d00d0b207201d000b040c1d0502d030280300d64030b41656200344400850000b049001514064030841400801c03511004d0801c010785040c0c0710056042a00c0d100703010418000c1d41c1005401400905132000000c0d00c500c0810261401c6443c1681c0c10000028148410182014840b040c1400c41c4040c0c00c028901c24170014442480b8440501142000700100d1125040d90340320034020030810030045d690340703191181580a0801202c24568030300904e2152111810100c0c200ea90ba2021100090f141c1c07406d040c03518041d40b0110220300d00724810f0500c0030075 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 693671429 1250 693670179 693670181
    0x140121050a140115120207030513080a0b060d0308040b04081b0f070803030105030601120519150e0118030c211701090b0a0b07020301090602030c0d0e010b030a020114040504 76
    0x100407500c03140c0209503011210410004120b040e030000707595940e40c143d44d22455030700c49040c00450242e150f0141c0e403008903041c221030301e0042103102149804900400141500700241c0400158170a180c40a500da070f07203100308a06803480303440c0500070075001d03c0011b0005540740f55442d8060701c10702c52141000701410180d400c44c07100800c1c81040780e02c101c1904a198a00f0000c00e402881c0c104000d6155606100110380c0f40c2c1410700c500078102c105511b8040800006018000147c0e00c065030665910101c5d003020380120301d0803140088450f00e41203460075a400d0601500224112070800818043c01a940444000b40003801c1680c8918030800005888031000c1400b040c4410156511102403400d0650143c003040d0691007010950300e00b8448403001e0306d44124460031607020a03806915505075001107809070942920050904e0706c00020031031240c0d080342c0508007101d600e24082006030b1210000a0886402c09c1001c3d51590100c0c00000c01903103d411191140d4440300d450340d0510b540d41001c28 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 693672679 1250 693671429 693671431
    0x1b0801020a090503060907062703051203040227070c0503090406080309091005010207170c030f031c11030a0b0a0801090f060c0f09090e07030203070f03170414012105 73
    0x1c40040c085410400ca14602042030030780141c03000d4003421800d03180240280c4135014450801c1707211401c40c0442c004038901061410001c2d50054240d8181c0140382c501070001da4803c8400701d02c10400c01c4001070240c4000c4081c802c544003080b001c00c0c40c64803259070541e0407280080080b00c443c40100310803d89a1142c1c0110001403014100550302c4602800030008003a4000345011180700683e441006070382c0e0b0004a204c115449120110ae099520890b00c03420a6008440d080e054480c4621203a40000000300800801f0b00c01d01c01c998010251010346000c2d25030401290111400c24404100305071040e03800764186600003001d840000f0390790303403009003550003104080c2d404100d48a88441030041038080c0442403d198580f8501c0600d2109014000c40c4680c0140c0041c1e680d260a003114601c000c000c00f9003d16002422252010396804103002480311703e0204039182c060081e80550b00c0c01c142c00c00d0710f09076050b000340c80102881d0030004444100300d40c40b41401102c030000440f2440741d0148605 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 693673929 1250 693672679 693672697
    0xc1e0d060204030c1703180402041e08120c1002160b010905010e330a050a08030d110a0c030c020a050d12030c050a050703082a03010e060102010908071b080102 70
    0x580c5891540c1480d51a42c8456441458580c2c00e10265105c01440481103507010100900701103441d0003502c01080090280f078000411002d00b503010b4039030707503886041030303808035040101114a8001e0326680d2860324003e040c4c0f40c80041e1f2000d000082400c030690060451400c0756603e041d12904551524051004207038003c03405c641c1d41c0d4005008081c2d0140005501c640e0f5089250f85002c0b051185400190088001003100e0141c10000e951555440350500e00505e0010700c02c104940d01d5400c40c0d500d9030b0040c901c0002403407030301082015103803ca4054440c6035013103031a4403516440589080d921506210412603010041170320104107a07841080503010280104d5950b0458882d601016046a40340031401d8140042480100009584802224503050b410f00d0301d4402c5469008040070540b51000c0c51010034000000d400b44250300d8200954129000c42c40809040e4403500c0041e8201d803a080300c05021034a082003420040381001c4d11900069010020a81c500d5507552070003400c81e0024194 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 693675179 1250 693673929 693673931
    0x9150708090c0409020d0813230406050a270e061e0603060c1c0605060c0c1e0d110f1203040519240c0f06050115020d020c1e0d06 57
    0x14440c5030300742003081141c0541c2c250f03002c0001d03558940004101481c0c1803001410300200041c1090052a042c03035400040c620300b486901c0c43c806030003000d110b4400c18241d1038020341c03421000182a1414140c210300712142c0c0d224103185802030041c1c02c09442c01d0751003500d8003e80c80b20f880c0c03c0180780410a0900c00c208106e565600d8091702c00107171250101c09419070f0b100764000828040f000702c0100c111015189441101c840407040b05030820090026035001561104012401e02803100000c1110481100200d441007010303544030282c030071900d0080c060030360015068500140044e1075130100c40421000241401441d034030f0b00000400d40d44011898200b04d0304007103001c11050401b21a15001072011281c1d000c0010b09010040d2202e1000c02c4820803d078000458007904c6c07a01807803569660980100082407840f40c0b03810090007800e82849000034035120f2046208180d80b020403014050740b0964083e00002c02c6006c10090410743d03003030761003800c00303822078841a5642d5110b40a007800b6209003c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 693676429 1250 693675179 693675181
    0x31207050a031d1c090801021204020a0518040303020d140907210305091005070f0501050f01120206030f040c050301020d0f0c02070302060f0d0912030504140c011709150708 76
    0x142a601c040b90b4610b440c501240c100800c54001007001260007808084010720a444444101e485c803d595001045652002820a03080744103111101d00c100d009480c0310b600c040c2d480c003d00a4100084100c3d0b40080401d1011034002803181e002005c110400340c8000c0b910031003d03545400104025501da001a0340110320402480c642003e01c043c561040301c0c0d42d0503000e441514047c0c4140305070300d5140d02c0b03480d923103000354031440c018010383c2c403101e400c582c0704102c503105031802900030002a0741c208442c075091400010095081c41851407510307030203071100d400c6407900302e1020701078040034004484442001c2008113007904c00f4805804454090070001c40d00940d10001102212810b0104404542041070244003503150582120411200030380c3e0300f0b60f030381c0c28110304c1c1c0c00810070b04030000e054100b2506004ca1f11a07154000c54000c81c0070303503001d142c072200b1100004c0d0b0700c2121280740340c0803030302c001700d5101c0d9030f004d09603070030351140da400d0a031401540038003251080c258040716030388045182e540c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 693677679 1250 693676429 693676447
    0x70b0c06060108070e010507080f0409050117060105060708040902070501140c0403031409220b061c0f060f05010e04021b0607020f070e0f060f1503192003060303120705 74
    0xf18282d6040903450030a5850703803006400003000343c420786802a0500000240504039145000112401400d4140042103a075854100c0c0c0030290541403c00322992040d00c001181c83c2c0f4003942124001503000c5a00c074541880d080b4048069040a04295955503840700141c0340d0381d0114295501c00e041c6c54010594031402c2d0300c0c0152004a41c3d42045a80250134010204507441d42d81b0082205400b0200340419032112016000190643c060919040f410100301d182050f031044201c038800c0315111805204030210049103008071075451242108000c082841080503501582c08101c090074082d1002d468410300d49030000110400500740c440c542c1c860010000c00990602010104039004006850402e00e0b0008021402001a1244404600c00000f01c1c0d82545c404900145508000e400010306011007202e03455260400c5480021450039401450401090b0780314140f225540c802c80c401c1c0290b02e0b683c075210340303400c000d00d403540510042101604520f0020b488a1080c445903030351aa40719000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 693678929 1250 693677679 693677687
    0x1a0c0105041118011401030e1c0c060c080402101115132d02211006061b1a04030504051305150607050c10141804060806061809070b0c060601 62
    0x181c1c07000f20045002e81c018403001c0c0d03c040c9540b03e218800d2a01150380e22013801c1d11030038031a070075420222102e0140b410f010825006404148003034001e500030000740034501c02c10f031006081100c0007584607803481d844d000b445002d141030502d08a0648115515070909021440c20141d0541d03000805902c170110020410860410202400c0e0005030750034210350720b900c12480c1a9007040002842841c04500d012484004005043c0624035883e01b10b600c01d42c45061340500504407402103800040307800b04806038142c000140821800c2d403045010004810811b9501100c55003c1c00440c1048000c2000041d16560724549031441a0300c0980000e20342050501d40c1500154030b04894029142070089001045001c0b840810a1900b502c4000c071410341c1290481c6c1d0501e0100b4008010703e004101000004503020b82c0154070346058804200f1507480c3c01d0071176079a0f5400c4030807580c04040aa25141d10100d0010465000300240c01101e0116850780b500c0b134010b4200c040f010445600000c1085200e40e84 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 693680179 1250 693678929 693678949
    0x30e19060f0b0303120a09170f131401050406050306060409060b0c071d0c09010c0b0901141e060d0f060908120f0403050a0522080a0b0a0b03071a0c01050411 69
    0x100b01d001354178200070202c0301c2104400c000c00c520b0b0784907901d10703c2d401409420310954203440c00c100b400560350342945403401115002424000c51035903100901048600d4424144007091720144c4405040500c1d094003280c090744001c0500f50009000d00000a602c0114041d4a000c0c10450210b00d880e01406022989032103401d5002464198519120240d00d5001d6256160000d40da0f00340c0750340e203c511034016110207144d284001c4c06140084100603180b8070651122586507800c10505c055a214103500707858018004488180d807801e1200801c8503840e006440c1000035102d146080340006603030710742008aa2a20b1815220484001803050030719042d00620365000084524290807030810340c4000308103000307442c1c0f25401d0050010348034402e400041503030220b0300350804403000350035101c50744a0b456144c80d0504680b031400394404210300003510b014803402e250b00500108041e515001c1150020b400035841107040c80401c1246003460b88080c0921481140900e0000d0078180c0c5103000c1c06000c0300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 693681429 1250 693680179 693680201
    0x130e04030c2112050403170108010606020c030606090601030e0f030d1a120709020f0d021b0d0203161112100b011209020a051203040b0706050609160f030e19060f 71
    0x1c42e0b0307254003102c2e03402c4803086001180c1d000b070000c0c196a5525050704c1d110b480c0c0f1042407440c8814800081d018105420500c280d400b10b0742a80e403101415410b065881c18280c2c1d803a9030003581500000c415520a9200300400700108003140d00510703401035040d085034844214a0040d1761581452030115012901c1a039840a064403558026903929001c0d5840361140d0280044035034000540d00c25107010381d0305584800301074a008642d50f03a195890315550944c0b940240c54240100040315002c0750010080c1c40301c00446842c03810741d40440e56125042c4044180d40b8540c40b0311007824610f08004200801ca0a5030f00f2a44001001050203002420103c41c1c3c0c90100d801c1c901384210340c00181c85541c60b0800b220004e4400d0f40032100199120390441c0070701e41007104402e00c040b074640207202d09500b103d8000c410580b801352250300c8440c032016600703403003111110200c0c00c2003415500384c911a500c00a2203c0005042d51002000000107030318582c5168002d640b501e48484140c402012148150b5070102 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 693682679 1250 693681429 693681473
    0x303050c0702030319091a091005040807090c02030f19110d020c0f151204030305060405071d0301271703011427070903140a080d02130e04030c 63
    0x1403aa070b40000d42d40e02c80c40302030b6107075552034652000203180a12840d4010b00110303803654458031000120900a034212501c0b05100b1400c9051690600303000e502124152070541000d0440307541040c0700c1d640a0900c280d03a4100310b1004029071f4a09480f044041c05213548114510300c80d4913425140141040082d081c017000540100b0701d41000c1c81e8001580c02076410040d01c0548042d170300c8400207004160348042c07546000e81c00241c1d80c03007072a2800092502c600c0c8645c80400c100e4441c00305101c1107450032910000450200420786040e075010104001e07202c0401000418800503d02914902c1210301e0055000c0035407443c000710030040b05094400e105150205120701f1507140c004074001e02407007203100d03078081c40040c03024030308180000e00203105a042500b613503c500c0c24030f48402481058148030540c0e00040c0000a0700c40424007042a01d04690422007143c10305d00000f0000e8000e50103805401c201040920000601c000d6071100345101724021b880383c0700a40102e081940716800a516507103c18 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 693683929 1250 693682679 693682687
    0xf020c130506090609101512050406050106020d0504030201020601092c0708121216020a0b0c13150806120c030a1a010e01060503010902211006020f030405180a23040303050c 76
    0x101013500c4000c411501300295400c0d040b000f400341562042304078a5000c42c80d6041004000a008540d0021030485d459076084540851601e001128903000d180002070040e00075200421007d1401c1c2c21141e00c5052822190610300202010600c0140200c8400d01c11a00461400c01081d1418001400403240621076603141c218160070f84001510000c03e442458100510b2203c1d10a208028601c006507021569041c5c6040062401e01c032508000b4461130340c0c0c260041d003c00c2a0a0039000c0c6000c051072511410103075200d010400c160791780308a0b6080d406114440d19090140d0741003101e040c401e07001300220003484030103111004100c24140c0202c40c4101c0c0410041001d00d610004036811100701100068031004000e0b106907001f80d009500c04ca46024000074009803980c9200420700b1030b41285c08851030381010701e10316a04e074021032151642c45146102e490514885103500540e00405610300090342c20a500796000410560b419207080a000700400c100c00c1507007500c80e4541000c5507030303419410 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 693685179 1250 693683929 693683941
    0x21207030f15030b1810091110020d0809010e0718050901090b041209091418010623030c040203100812070f06021813020d0f06060c030f020c130506090609 68
    0x988070301d072000920381301d610000030380d0384219450800c088001c100c0645030f402e03400c212400302909a428050720a83c040804914240c6840700c000003031860180c020304503070802c0d404141c9000c0300044c800c6031a03548845100006410501840002d0b00038981ea810404094004000840b8002440310781c542e850011403d02103014440030030752050f44092400c41178150000c00319100203596000c01c160134240f0402c0c4040d23030181940c492107508100c1d66410300c8407101b06c105080c3c0788144140390b5030240f444800f00b071100380c04c3d0402c1c03c0d07004060201d0700d40244040c0030034201c0c2c0c02200c0c41d04a003a5059828803607250140965040e454000c00311504040c0c0750348071030313403100c040400003000e00d54002100001c2d00c0c09a4001040e001b00201075110300c00007501440041c1d4841c9084140c044c4c42c02e4a0b694110b021846000f0a0300c03059507402501c21080c3d90107848104e0640b0540e0298401e0b51074400f01a40e40da0300d85910b9041400000c241410080180081e0608c0603202c188101304041c10800 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 693686429 1250 693685179 693685211
    0x106020706260115230714010b1e220204060f0320030919150b03190311030c01060f0306050c09150d020c0102030f22030c030e0f04021207030f 63
    0x419215411000141c0f0000f01c081501c00190f100540808105e81e03211051022211034007415080d4000d0005554024501d10510b0880f2420602e0300e0707004c0200174a15042104802c005c0c6146603001c0c1800c0415200d051503804c203c03a0304041c0880342ca40004050120a13401500c06400c41082d04042c84428604010b5001c0001c0032140e0074155240400000c1101e8000c205a01818002d2480c0030540c0070141001030a882e500707041985001d0500c0081d040c0c5050000360030a0b04500749800da5001200c6a60866040e618046a078407075100500280072265000c3c455030300189a01d0a8218a2500d545080400e884000300319a00b00706060225030440e4842c2c9101d40001c3c650249002e0b5281810a1448000e01480095552661000c801c005d000b07076040300074178052a20340c19046c0201e00f21050b400e040010b101001000110b41942000002e07008000001e19407600400000304a14080080343c100d030880344401c007039140d084080c08403a58144c480c04161400703618040c004000701200c161 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 693687679 1250 693686429 693686431
    0x1806050d020d020f120403090b0a0e060a0519110d080606090d0c0f0b0403050708030702060f2512080601030e030405010c110d0506040b070f0905090405070509010602070626 76
    0x5010315400140e4125100e5055040303e5810a041c0b9859803500d86811040c031007008101c0342100481e42c0000081410320045094a03402640303941c0c4c1d030045185080510065411405085041c0309080c031810358040c0d0100000702000c030255842c440b2001d000c0003a2441d0445c0c100400b424885104144804c035140c20040312442d0800380c40903014035085180c140d2280c0c9142d44260340c40d45004031701055440f100700003801280e010380c0458030305c203441e00344058030ba204942009610150801c00191000301e548050100b03030b40c0c0104040603003d42c0000f035107218050003108445400d01034185500e0207400040254000c5000c1c40d04020b0030840c20b03082696880303030b4000c06052151000454040001c5000c0c030004083c0094883c50070301800d45001655280e00340d0303040b05c803980c00740c0005a0991146a03152007205640d5140c503c5207140406001d130040004e00282c841e806100f01c00f042a40f102000301e402840607500801c0e000b40b0b07020004003030003060900c208100c10b03500c04031f00760405c40d80b01403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 693688929 1250 693687679 693687697
    0xe0f010f09110f13181b120b04110301060611010e060621011e06050a150c1e060504030806030c0312071202031b010501060306050612070f050f0c070501180605 70
    0x10101c1d41030070b00003c0c1001c0003068090050b40d04000380d04032401e5030245c00c0703005144035619040040c0c2c04c0b41d0071956514260300541c920b8850040e0104049181d03008481c2e0483d0150300030403d178200b00310200f0f00b0340f075854100c2c10104e200110b90f0079004070248038154290a40c0809003419041a0002030b074a10304242a0400c0340d0361050008602030404c0d4009850080c065810041444061036480e024000910034584100c41140002030000f90041d9085000c01e81980c8500c00840507039120300d40800080f0384801a60116899080000c1c07581c403c0c0340c05035001e0740760090a8136182c000c0615100b48080118002d4010300880b084100440050700c4150b5440072680c680b000e2108070032441c600810040c28039040100401480214040d4002d6040c3e900e690340500101c0e13111002c0c082c5070710070060b400303000282c2980082d0455104007003e00d10795076249019490304c072181d001005182c200d010b2406003500300c0c00d8200050b6802c048200c0d5000000c0500c4440c103880d0a0028106000c1e40c124 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 693690179 1250 693688929 693688939
    0x140405070f0302030a0216050c010306080d1e1b11030606030307080d0506010309080a0c060b010c050c01080a150b130e130f0201020a0c032114070618060e0f010f0911 73
    0x2080c062169601a640007c005401c41d19118280f401c05036501d1100c1180b031342c0424030308540403801c54000303d002064400c89840e098003040301c0d02403e850700510607104100f00040e1301e2a0100b042c01f00f1480280c481d00510f5020906414502007500704a000b601c2a07210740c1c0b00304002c00010b8444400e407041c1d14000500000d09a44900058014040c4440e0041411500150f981e059a401003118006a40a000108000e1780f6000040d2103c13080701401504c0c9a1001e51000060340c801c03280c41e648a1100b04010907000742c04c01c8000d06450315a00580d1205401081c2c20031400c100b16041d00080580c0c03c070100700d5081401713074001107a43e2510090301504000a031001964000c2003001d4070700f030f40715150100c859a02d0500704a1502e51329000340c0b500c1c00703007004140000d20803d80d844400d0210081c1340e1a00c08150743d400001d0603500b4000741d140d400c0500032004140c140c03042d01c07145020f8078060528800e41103d070324210b444200b035050165160299220101d000c05601c2a00c1400a5030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 693691429 1250 693690179 693690181
    0x130f060e0918010504050312010806130b0a060f0b120a18140a0209070906020d140a1101090204020f030402012a03080703181410050f062710140405070f030203 70
    0xb100c00b0640d4042070041c050b600301028401040000030052802c4181e151461764582d803076003040c9850b90001d807801c0a880c080c1030713030000100c2c290181003a0001c035001000610740b0b65812078107a030504180d000d200d14410220ba0200340b21403040b50950b0242c1d8040f4100000c90146003c40d07204910190301034a008000c000c20300a0280400c6000b00c4143c000301610210300d48680000c24600c120f02502c0018020301090b03500042c0a00d0b455400019038410503414a25080c1c3e00b00c41280c41400c0000c440c1d0b40300c810420160300c0c0d86c401030480420312008143c0e04d00d0b0900015028030028011560b0440d0601c50034036540060340f40a219076541440d1054a03a1a42c110440207428140008848100820104402c0024401d03100310a07441c3e038829240604408100d401c2200c1741141d403e0018014100020010324045807118154501030455804113080c41d03e0140010f50100d59440750006007420612280c0c6c0c11b140014014101243c040c01289003200000342182c1d000320408040c190080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 693692679 1250 693691429 693691441
    0x50d05011401121503141f0f060504290117130c32371508011401050f190813020d0f061b090509070206010609120303110f130f060e09 59
    0x44082c0d020247e9031100403a0645401001800510070403070708000301441c0820015160900380034011034403503040e40ca030a04070017006240c0c03414400c3c2d2810754100001d0a503404010b4080c203140394022082012805020881c620785644805200d821490383c0500c0c1031102c5200c010f0401514621114940861030400011004500310495200c0c60720200c5103802155042411011098400c690812a110b4201641c460003814403440c85112000042d000d800180056003a0fa0341c981d5080d2010b150003460710a00408100c0140c010b59601031300350600a107181c00213640300700c1558004402c400c20710407040c6c255000403040100100000c280456204607402070202d03a9005001d900034018280b9015200408014640e0200e40141f6203d0002100480c5481c4c1c070004205040c1c806680395000c0031400e003038041c03503500388140c021402c0541354028540d041801c8405001c0405200e030500e92500d0110b00740c07407007071915034001d0440030040c00c104108040d8048500001002c00f03840c80c901d1900c3d14 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 693693929 1250 693692679 693692683
    0xa03050d060909080c060601091802031302042307140403110111030d020c070b070203030f0f1c050105030f1b060c0a0f050a020a1502060610050d0501140112150314 72
    0x2540500b555624041c1244180700c1c050008050502d50202524615541d5000640740c40c0e40351b019111181e50b4034801c0e4120082940d0046404c40b1920010000d0300d0356507070005003601c054070700d26844a0890f00c580002c0b00c409082d01900070b030860810b0b441a00c01450b21441c00d0142c2e20000e400089800c03001c8100d640140c140c003d94010210540e9580c0ca00f03c505203000e0b6000d449034820600c27800b94002800c81c1601c0c2600c3d40e0590050246141c05042c440c0380070396805c0340ca42d00c0c8444004016100102011422008007401440c801081d103615101c10103080c00d8046a08440e5600410040c06003da41600c5450048074101c4501d030f00d0f0040112098545031841e40000c002d4291712800c081800350020320810814821aa1148465210101c3d05070800a60038500d0140e406000420342a140030781206604044a1030514241a07001114000b514030070ba10803c4409054500994a56446aa0100740b0a2004424031029002d035a0150001b0801d00c405010702c0101c4041c00c00c0340070b003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 693695179 1250 693693929 693693941
    0x5010e0d1a16090b09030a030c02130207050a060509060708010911130305060117190605071b0c1806080a140a0c090b040c0906050a18090204060302070507170a03050d 73
    0x560305894056240c0900c4482c415140002a800890f82491002910302107203030032544032040160241c60003007515642070b920500c074070404030b034841a0f80440282d1790406102400005024400501094201d410810708403200600072881c550000000c02401c02d402c501742e0303411240513980000301d90a11841d5004180905410020203140b811000801d10500061890680c0e0203d21804081c901290078644d0754128003500d18804924a0141c00100e4200d9100e00d0703000d0781500b05001a08440c4025101005035040100d17642500f22100b031211780000030b404024106a018100810341c1040075150f9200d1070204003c060030080c135034261419005000c1e484046d0341c044004001c15440b102e004015101a140c140d0080d49024100c24449108100820440b1000c2d10340c00d20f044000345040355007003c4540301401c0f06c4c00e200b000080100031480148010071080c4c1d001600c070100392034200e0070030003130368040d101403059513414600c1007001185c1214010b5040c1001680c0e803060060301805002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 693696429 1250 693695179 693695213
    0x100908010f020d050709030c03030e01051b0f010b09010807091d0d1d0303030c030106030f1b0504031712131b150206070201110a0f02010b0a060c1b05010e0d 69
    0x401d00c119004048555000b91400002e42201403100707559440040316101c2d01403101500d04419544200b0109001c0d4a1802c01160107141051904c01d0301c00552807401c1100200c1042075200c0c130804040c0100a1083c1807080301c0803159100154506080c19584158a00808a04680d0b60b10215004110a820554802821401e03258001c0144002602d00c15565041004bc24011084d82c00c25181c0801128270a40204020a040d0303402c0c040120002c10400b0744855420b9a1601c950b1b0042e02c064445219400041c0d40302d503540d41c11031500c3d9030800245c8006008541007405481d580421450406a00c0791050380c0c14030700b901560901c03402656060006401800407888042005425841c40c4980607030b132902150303055192a40124221481d41414a244005c10310100071010300c81c8039050180b1100e4800440d0150302940000c601c804282d010f240401c2032110070408211a224189085004802e800e10715146000006406e20450a1440d80305609e400115407c02082d0448944104 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 693697679 1250 693696429 693696431
    0x2011a060901170124030506010807030e0a0f0506010918020609040b1306030302030a1416080901020a23011104060504260a050a051b1f0203040b0c1c09031110090801 73
    0x15030f403607140114031284110300501790800708100300081c5009006590164806949811207036070356400440041020510303461050091000d02c02c081400c01f02610f43c1e99004001802c01540352003080e004460305540a2120382e01c0b681c800d00013694034501a02c04940069401098461500c00001c0103040c19411000c10140b0707185011051560000182c03000c0c021a0310390508801f142280360507140100e140c24a000280301007280001071a100142c40d030140c0600444e0b00180c0d1950b10102ca41c03884103000b904030702e02c841b509181e02000340a800c0000030054486440e20342000c0d001041031180b400b0300d1145c10801480c40000f50480c140e00f20300c080045003a01c4506071245091929004401002d4841d07204071060290038101c4078000740407880b401081c060440c41007003261503620084c5120309055000c2413100150540081005003405441c40b005031000f070f240440581c00003960001101c5c01c010411009200040d03100c0c111204051080395201284441310808960036000b90704605459 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 693698929 1250 693697679 693697681
    0x30708040e07030203010302100c03020f0102070501090c060809060a020a1b0b07110601050609040504020a1a0705070f060e12102903031813090b0f09010c02011a06090117 75
    0x20015000250040e218050a003104685403004200c069000c00c0c00042c1d48183c00f6080d103003049000b0078040000e14030a00560b620b503c4d8a002113800c81c1c204c2401641c42c0d0f51211551010031000070640d001510301418281c500703041080c0d0541d51514014405007805a000800c4204180500950010001c001b05803e0500c40c01d4948400d4600702550a6000308040c0740d00da40c694440400d078981a904003400076030828510000700000307010b000e00107981001e1040d401044940c50320f1641c216440074191510703518030991501030316011280e48503521790043c00205002e0f00e0760100540c0b50700c2000701d4501c69a1010703500c0f000e0601104021061310b0500c1c0c0114400361124240b01f112542c4003d0381c0c5c03101400841014103840384500c88900c035040344186070400180c98441e50b5281d0340220f000f40001c80f103489030f49001c1030b80070541d07005081c0c100320010022080024020494005903601c02800203032240b0901c3e079041040b59007051701c0b40101048408031640b20300070070311408400c04180c1d42c00e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 693700179 1250 693698929 693698933
    0x210303070f0c0f08120a33080a0b01150804050c010c0201050c0d020105100f03052e0f0911041a01051c09080a02010507050f070b0a24170d020601031b03050307 70
    0x13241e11080220452050040c001811082036120350f11a000300540c640c4c4613100154140180d6124130362034030b400703154012000700340d242c001c12882003a98862003021000794141000e030513480b10610345c00400c100c010f43c10000020404100d40c25218803e08100300c0e40c07100d91006850a00945e41c0c022618484c510b803a45403258150800b0303004001da44851503000d6101c00c414005011507002c00b40207075102c005402080440821044040c100c200403200399841c842c40e190065559071040d07034980a03141c00117142403222000380d45c109003034111001c0200002c0201074441c0d10300070896590600c2408105c4d62103903e5000c4054a0f03120b50207000f00f00800280c50004920b800c83c8048900542c84e090015608600440440f10303240e05a00341e61b410800e0544c2c5070213080e00300a080242e1283c035510510700d103080d00207a0182e41000412100c5a0a04144404106100b040c020100542c4030704903008030590046000b5041d02d8101100c1c1d0820f0b11010b0700c08440a5603940018500e110000345401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 693701429 1250 693700179 693700193
    0x1e1503050c07021c0b0c04031115070c1202130b01080f07031805160b030108061803040914091216080304050106030503070b150f1309060603150902210303070f0c0f 72
    0x1030114820700010340071b619a95042e9100e40141d000c000c1034540301c0c05058140b89450150521183d4548035110300e0f0850a9403000306200b400d9101c0540242d41070b004004502d8404a0200c1e444046101000024a260002460104082e10b2095403005910100e118244650041282200300b14610703200c4210070702c1c05641d02d0f880303585050404290744d840411411040000c9a0488a6800c001d0031261544407200012140225107604940300421000070144c80030302483c40015126408100f0ba07103058008642807244481002c8450075041003181c0035055103050101b036454204205130346940c2c85140940c0100312580015165101c085a50780c00c1042c01e07050503118191851112100490400a00c41d10501140403503a110440b5a0b07185221021a0302c0301d10101c2c02640701141d02c65903600c070180c0c0784200030790298107562900c02c0e40d019070034602481c685c00840e400781248440b10504a240e12804042d04483c108441c10750f111100e140b080024036501500464841c82070380309454000e0f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 693702679 1250 693701429 693701479
    0xf1f120204051302030718021207030507030b01020604200301020c1c0f0c0b070305091501060315050d0b0408030c040801290607030903060509030d151e1503050c0702 73
    0x34462800c0100241042c5a0160102c4142c2d0340600203005447c2400740c0b0000c00380012804032005642840b1040780d000440782d1060040160341c400081a0a08071001401c0e03d9001042905540c090018000020303112000000014040e031515042800c0c0800064064480d089145900d03102d1300742420340030a5522100128a03100d80c5941c40c8011248409580d072450104028000124880002d881140a03801840d4025400340c151000c03e107000700d400c484943e0a811410000c0e90364960441100030030940036010304000c40d901c0703c619200d40d44400014200074401441c10300c0200c0403605a800b9007043d1005400500003d000341e801010020402c250006007000540d581d04840359901c0c00e09900700c40c488ad0b05a6a00c044440c29600d860024050240200352580f000308500290090360b44501070307012100043c0d411800c2d1400680c8007140d0098103607001f003c4880641080b112030b2511280242d01500d00b804500b1340d0b00c500c01c4490b18040c100313000c0e4112680c0801c51400c514501c0e80d00d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 693703929 1250 693702679 693702683
    0x6080d032409020307030b040c020a03030518030720090a1407030c0509040c18091a010504150e03071a0a02070803031005040911040c020d090501020d05030f1f12 71
    0x108152404002210000001051105129021203100707102e48503281d00150780c811464103011581005400124080b21030886030000141c20441695080580c1400340d150020501a03501c59510807003100f041d180d20811000400e409514030051218021203050194402e400812218541c074200100a000c1c0c0325504046030110301c0d01c800501e0351406032103034210304a01540d4490031f004800003444002c1241e0340c0c03948140b0410300f00b0000c1c0c0703021001003030001d01b07900000410b80c0c060100c10b2140c0c0d0103410003c2410b008003030205004030107081290900002e0381c2d25040440101c0d0b44007080c2000c4040d0131070071030700314080904000c103440140200400400340d400c45140580d10580e00740c4a01050368803120350801034104000d1494203401240c440ca001d101c038280002c86000029044600c41c008000160f0000e2920003181508200e0a4000300400c3c0042c0264001c2c110b1b008265100003000c041030000e83c4401f040411103032000c5003c0340c0e0000e4100800a50b101c0108d80417a580250003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 693705035 1106 693703929 693703931
    0x212040308100504021b100b01171008061302031911061b10060f15020a080d020d33051c0f060204030609020a08010903080105100e0406080d03 63
    0x906020390340b801b41c1c1207080c80160107141817082d89501099004e203002d01441960b42c01801000d5401200c04003401c1c2b03560741d10048188503501c2d0300031609070b115600800100804207005100004e000b05c048880c680e411030310300440145103900080c940c141c42643c1924900b0b100014107031118806240c5c80e064009a819545803400c03065100c0042c07034560000f00003482070140050050201100415040e015280c0e001c0d55903440303100010114140003a8600003c1a030340c0c140c45100c20307010b50500c04000c0c1c4003881102211030800d0113813200c510400740c04411003001000c0d0101d54016081402204601c412900b80824580003901c2c00e00314000c0c270a0015000b4030091000d184241d50002f002031250051141008054010707103a40da01d8100300e200072a07082000f250444d030080f0740034100d02c140d49204694060141e5102a0002d05041000c5802c46e40850000c00c80c1800f0740e0 = true := by decide +kernel

theorem cover : BRFrame.Cov 693525179 693705035 := by
  have h0 := BRFrame.cov_init 693525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 693525179 ≤ n) (h2 : n < 693705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
