-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2516
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:56:11.30276+00:00
-- url     : https://prove2.me/submissions/bd573f2a-d843-4aef-8060-5e6c5bcd8abd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 452338129 ≤ n < 452517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 452339379 1250 452338129 452338151
    0x3040830060a060305041e0305130f0f090b3a08041a0421020111010207030e040609020405031507020703051006030b060906010e131e050108060106020d0c1709060706 73
    0xb41e44094220f030040c0751428090201160080b0b8000741460052000034810b0800ea107011036203400b420340b840030284407400300400da4082e85414803003910480034082c01c000d551806413000b5120007546042e000303890400c103041c48044031000a00901480c6911001591740c0c4d846030000b11800b2101512b0484c030109050185076003075aa041202e0085030540c0d8141402d11440c0303070b08214005c00c81e100ca01c115060380fa003164001e0416070038501040008544903600c5040103080c1c1e040c1032501c0e0788034500d45140401e100d1554826503041d200050014222a18011660381d115034010f0924001d61054500c00000918104900c645194401c0700c045005440c61400980881000e811030388106d90010400a141e40c0c8020015000c12003244c200c0901014040c404005103080f1810952410500742e0b803800c1c0040e2900310504950161048030501d0380d84880498848642c0b049110015070034040c0703c0c011802003020511480c100040c0030780352041c103000003882c5610583c070440b44540c0b60341500305 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 452340629 1250 452339379 452339389
    0x1624031b180f06021c0216060804170d05040c0b040602120f070c150909050c120a06081207050c030304030c03081806031008010e0a050319030b03070b070215040503030304083006 78
    0x15604490004103810010807d06038000540c50245400b00201400000c0502088071000c201714210b03129501d9540e1030201c0e5600c05031004840a4078685c8140070001241400403003210111500c56001e00b010300240f1101c94000c3d801261200f0803408140b055201040414010703070f005010b51a4050100e00480b10301401d40c0d00c2070f48c02416503514020802c02446540e00888030b2801404400507810350b00d8418003801812a5085a038852180c0319040c041c188401c0010030340b60b030191040301c401c22140000c0603075910480c000240326002c881d0301040022210310140410341c8400d0014143d41da12040881c000d500100c1e0061031900010000b001910360030300c50755951021030030203000040c680d42c035065501d1080d1500340b0a0100e11085446d46030f8407a41c811011208000c0585900582d901d00c00005500080400d038412030f0700300c51800c489182c400c12201141c0010380910b066543d00e49410101d6004513030801612140f184080344d0743c2e04d00e4400d41441ca1300141050704c06007020820b0007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 452341879 1250 452340629 452340673
    0x5070503011a0307020c0d1a18070e090c040c0203190306090e0303040b060613050d150506010504030f0f03090e09010504030219030e0f031624031b180f0602 69
    0x3110082c08209010905601240c401513610094070031002090462504042d16001c00c0c0202c0d5030391204d60184486a40001908a2001031103401c66070031940799210902090b0041c0d440ca003003039020050b02c0b19241801c0d04420074081c628016a41000c03100015503d00110f01c00c11400002e5552105009088040c821840c12011a03c0110304500e4281d88903009113902511140c4610008a035440d0340c001100c0b900c0024004c080c00d4410490194903008089030000c009581c1c0e0703541482c00040595200e90240c50403640c100407068106a4107855040c2009102e40003076003003182001021841c840900710403802110f44400004071458181802820900200e980c0303901117946c0111000840e0b030280a4901e1400700302c0300d92105505403000640780040030441c82625003514480002d0305d0302004040c00f000901090072004807914800e040b0112050b10a581c640c10b07819031000e5075010710541c110090720310204ca00404440e00d0b0030007101603980715370282d00144d014581500742840c01020030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 452343129 1250 452341879 452341919
    0x7050301061a03040f15020c010504060e0109030203040b0d0209040c1e0504121401090f0302100b0118030b071809061a09060301180908030103112404060e0a0302040507050301 77
    0x114030041c0c180050382d0781610010300050040301d041c080010500075111008009034444210441d07441e281c0000050107400201d8081c2e500615086069144400600500c02c0495140c0c2c082c40c500340c10804441e42d2a04000f13001d29509a0170b1220724407603182e82c46080140121511006100c0c140000612003412840450904218041c00104885200080b12042081c0d22100b01a01c0e9a44050611b004280c1408040e10750105003112034241a0007141114003034180e41028410b4010103401914160014040000781c0d0184480c10401300342c03280c2c1d0141c0c000100b860400c00e0380100704d039200100c20658101429941d07692000700191510080d810806004201c21141050140b00c0041c80c940414030584c1c2242c090b4141450b0fa420095000c5544903602040d4103450396102c1c140803143d80e030310fa03070703840e008056041020703240c045000072209042016001440c941402d1103000c650040c01217904c65000b81c2c2c8442d0106c0140d136075020701340c4540303078560704c50383c5945c500f09030522802030030601c0c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 452344379 1250 452343129 452343149
    0x7050105280c0302120103081c110315031504030306080d14180a0e090c100203090f012604051506060406080103060504141b0103390207030b01080705030106 69
    0x4101c6503518000d9000e125420008800125002d0611082c0c019100f048020050302030b8a000120070480703524050501038120307000200d150f030300001c0503104855190642ca0a025000d00000c3d203540d0301304c0b000302d110860107016a4211290309046042c1440151030440210740c07203540c103106000e0204480301c1807c41c545000c0f00d12429080400140f482442264900c1c040c100110951603105c0c80300e11300040c40320020101c0140ba01c11006c980b82d11046a80354410941c460350019900d1001040e01c0c0c01c0c40b0000e00c629400d000c1c403130056910541c41d8901e4041c08403411058044402d00540c858071660040d4060114001c550801e82c2111350002d006c2d41c40348106200c280030499015180c00c0c103407a401900041e260300c440c20240404040315100008074407c41c040c06083c00700b0311503007080c1e80c0720a880c18095450000d08020350000509881c5403008215682c07410b001c810a5650050f8290070300580e50b80c22b46035203071481090000d0700318032050b510070b000400841c1424420b8000038504004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 452345629 1250 452344379 452344411
    0x601020a0305090405090313180c08011d15040f0608010c020604120516020604080d02060105040b0d080f2206021203041a060f041803030e030403080306091e0c07050105 74
    0x81c014002d07000302001540541c1c0c1d41e1001480e498020400c680c2e00d03807080e05d1100700c01e80d40d4030300c15156242809000a0b440b424140303580009130045120a05903402c0080c070394444255200158440600100b030503840e10751060390b15605440e03d106400359940000c3d404501941042c0c0e03400c0c01c1d520800440c20855100d02c2c200f0010074500c0c02281c00f02011858403c0e85c2d40385540c80ea100340d5001c0070020f036200100140020b88408005401c52a04012340c003a12020b84e6608100800c89980d001200d40100145081c140051b180354000c1c245a182500c1d0641844200a8040c802054041d0a1080702d000301ca002d00920360104a010b5414001c0c1060914501c4e2507a240c3e80e21200004810400aa001c2d0100f01542e41d0524a41d24034440075108204105c9500e8094190401000c0c0580100346450400091b0782008011031302a2604540d026246071904010b020101d48010001c1d00d00003050800358014140e0700803030038022541941c60076155811400e246084a10181c00301c600f801c0524 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 452346879 1250 452345629 452345633
    0xb07110c030f03091014040f090b03070b0a030b03030d020d090215072d1202010f060512030301210506090c28031202010906020c01020a030b010f14031012050a0b0601020a 75
    0x41201d000090917200c01041c00292941950b121008001c0303008983c00100c1c001c038021509104280c2154500d03038050107404290f01c241600c03211240617403140c0c20300422000f19014041e0304022038030f14010f421640f07000e40c000744083c200e0704658a440c0d0103544541c0787e80305518050000e880300003224003519140404030740d111074480380a043c010f0440300c015400205a4261520062070041e0010500c00440a102c0710003402440402c5100310400c3c0340020205440c1001c000c030701a070441d0b5000a51640e403c1111551000100252105c400303c064202080041e0080c000c1c14001c40700c101c0204486003451040080c40700c01700700c1089840404c1e800c0f10704071a05283c2001c040382d401221502c10300c020200c08034090842c004020700750500000c3c9051a21005600410050300c00d5a004c000c20303070300b09004603000040c0744009070009000d015590100c0c16034030010341d08150598448443c0729070f42c3d9180309100c2c0410405440c00e420004201040c02100051180c6c08a024800341840b1900743d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 452348129 1250 452346879 452346883
    0x10140603060f0a20070309051906120f060305030d022511010c0204180f1106070305030c030a06030f050d14030c1b010f06150201060905010b090d0f0b07110c030f 71
    0xb4404050f4a0710b890301800ca1303142d0109504502c1d010320400594985032428003506024481c0b003a9402034105403140da001c07842140c01c5000fa00c229999034000300502d6003a020141c80b40328440c1d80a195200000170000700d080000700300c080c191510250302d4001078090544a0821340c0410340c2982c000414200016010b0031141c0b03040d660900f0004982c90207800440c005013b958020480b00040e14401024400101d0740f8440017481140d02ea22501961414880039000b8810014080740040c00072486100c4082c019540c080d924480c002482d039501c2c0c444e100c2100c8600c00c181c8a642001c1301d5a06215031000c44c0c8901312244241d000d166003001d55480000703100c0c070b41081c540304180b240e804041010031f4000000104215009100c21030720303a408501c6254804154202661905000040300c072a40d004a030304a42d810030b45141002c4c40368050001c07140c2012000c0743c0422a80b1140b00000d007003030050a005080a607181402e4500140c200791402740c6e0302e1b0300d50f48694401c0024403448440 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 452349379 1250 452348129 452348131
    0x507031506300b1e1f0507060908030609100609060507080405030706030c1b050a02010e22020c070f150c0f060f02030a0501061d060f0c10140603060f 66
    0x201c0c54030035180354481500d96980500d0308408504540511401c1d01c40340c041c0d0f00059612141150404070354110000b924903000c59582803135402500038144211900b0003001d503400000328505080c2e10f03082d020360707665040b5110103070112500d01e40403092080c5420081c02e201da21580313580791403482c80d09054000e40040f845116481c2080400540f080402401d042550010f14010b8210340344a9160b81f0098040c20001400d4000a14180c2c504107040622501e240700454014014045003100c1e90011241896076400c8250031030244ca907080000130003d107105030600184000161190881e410351424815598065100b1583d010004d00404184401c03410800415007084074200c0410301c0c005116001a039030142c4040d14103111501680540c2c0c004500c14021480c0c10441c503070b203c1c1d41c2038840400d468800b0b80040030000000f1900d04041000301803507031a044480342816007811042d03140200426005046a03200d5040001c1c01c0c0309181c8168000390308a000d013109261008810170301d118 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 452350629 1250 452349379 452349389
    0x105040b280b0604050d0605060117161409090906090601050102120d050a181118070e040c0917102a0c0305040e040305030f01050405061503040203070b0c1005070315 73
    0x55070300d02c2d180d01c9a0311482118000d110161070a403c00207681000710081000311805400700340c2d4200d8004440d010040e81074820120800324607109101e8400c111400303444030301c075680c0400c0d04000c061306641c9d4003245980f14910b000001c142c5031414400d140c1c20301da01a070080f41907500c100301c446840320403402500c01a071142d100006440e520300c2e150001a2030089940c0c49108040b4108009004140301210700e946426190003d402c4903c0201d41625881100c0007c0081c0912102002501d4140c101d51801592403500c169400e40340d0445500d40011441007156942c40782d00090f982c0302d01d80c0a00003940c0c41c0b41482c00103400d00c18181016021500120204000340d20054508042c002d6003940c01801e07a0000007440341c5014900900160f1096130703000341481c00c11000042500d0503004140c41620040c0052447c2004001940d0070380c1c001074822a0305004032080400c00554440207045d9003160440144600741509052100700c40d800703840e00c02014242041650b6010380880c020f0100d031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 452351879 1250 452350629 452350631
    0x2010f030513030e060405090c0d0b01050f0703120f0216060e01020702030c2e0507050f0f07050f060405040212061f020606060703030b0a300b010b07020d060c020105040b28 76
    0x135044100203072080c80769420455104204200380422003140a0180641c90705294080141da00318800560b01c41c0590f200741140c0034010060107001078403a10410003025400100440d0213002c02078218241d802458201c007100701c84000880512a842c080c80031480307181c0c40214586411a0042501e40b00c00d50300e083c2c080c40314444078541000c0c0d40790029451110a640800b101c0e000e00e0700040895200c0d440030f5405108841d54032480d000d021401e80100882c0e100288106850082400640202c004603030b60301040c00d0000280580316800104607000541040c415070f45011020403065010400030442013403000d148421245800003030458008204844c030603210a082d01e8220054081a02d01c02d4000e0160301002031051781550805004418005101d000ea17030556034449041c0d4103225000d0003c9141c40e00401075010a500240f000f140064050400020716464600503264400c00202c0140e5481080000b4070550034403413a00135007162990041c040e050140840d107883c0c81e020943c41a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 452353129 1250 452351879 452351897
    0x90902130b06070b0103060c0801240e01050919030b010e13080f2203140c030a060903111f050709060807200d080f0a02070f0809030a170702010f03051303 68
    0x2030b654542981e40490784150003003140d684030b25250000d095007041842c00700d001c07040082000b48900842d0520b00800b514203d40961441c60205c83c044020340d0340303505114040040f100b0702c0d1100c2c3c00004c250b140071509811201e25624010411200590120b041f03d030b060018042405010142e00642c0350f084444503407a00151018180b45100c1c2c40c9403400030500da90811440c0000007012002241e019910321150003c0b8005065105ca00030000254150080401034001501c0d50f80854841800f914000201c04050289286880120701000c1e61404140400d4602c2d50064010f1310342c0010701d484c1c0620b92600e4840050030340c11000d03102d4814445c14142c007407061003002210290f0091184110f0350441e1100501501c80c040c16503122103050060340010320200543d000703d82034164040c400b0500240c0a803103080203a0001d907000c981c5070041d40011404903000034040301088040c03035400d95071003c603440050640303121010884203140c00c2c60104011051420703112450b40307070581031503040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 452354379 1250 452353129 452353151
    0xa0c02070b07150216030e0616080304060912020f0d0513060507171801090e090a0210050c010207110906010201050709140d120203041a0301290903010c110709090213 73
    0x41c4910707203449902c40b203102040d80c2d021505ea00e42d8800c8024007076111101c24121100500c102e0384a0402100e8a0300d5085081c400060b0715a8029036000c0e002c0c0c503000800d0032003a07848071401e0301801410300059020640c0c032230b40c603032080c06810f400d000319042452408007110040b0007090f03075512a80b014000041002420b001c0c070460070007003031070140700e4195443c603002282c0e80c40000045003e0f40020106680420300c00300d40f50149004000440040c6414145982001840e109202c005010400280030825280800740080e10304207110300044844504c50200340080300c20001e1203241103a0500e02800300c0746802010075030998071400f07000300348640c400b004545440310110303004100300c035400e44001c6480c2d4040042c200380c0301200341220f44040c801c010400c003404280034040c000030101980201b0201d004812048407901401d00300d042200300c80029003150120b41c40c440118002e441112111101484014080c00a90104004110068011502e81d0005400c03d84441d0307692100140 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 452355629 1250 452354379 452354393
    0x1030902061603050d0f0e030403060e0f070803042d05060d09081305030606030703050d1206030b0a1a03010908040506070201020109020607060905060112050a06051f0602010605090a0c02070b07 85
    0x4400e4181c0100090b03003014030b103001821648901d201c00d0703810b4500415035040380c00341d00401111800c09030007541464110f03240d000c01810030700c88059491140180c0300498200a2002c000106030f003401841c1c0340e074504041c3c0040c1c03c44102c5188482c0d10100c82c00c0441e03001c0d0031221400d64001361500342e12000509100c1c402410f44401c082c0101e00301144502d58600d800b0000404e5640030b5040e600c640c0c50b04005d00da650101c7d400018400d410038060307452090b00c1000781e034121030000c40e00880c0c43d0b40e80c3c0d11000315000090f00d20115190311503c1d525a8101041d0b5407a0750311405800810000c03815403500213250045009072446414001245415680300350081c0c0401d0760010040c1e907407500c1628214004007011502203646004010000850802080040d043c16401001800c0c0808051b690320000301401000020310ac08076401001451813105501c01c00390100e03400002d101c1e4200410001070140003801a40c0c02403d05864442c05980411001c081302c0c81c00c0b140c00c0d10b03083e0900d0040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 452356879 1250 452355629 452355637
    0x1f0f1d0c03012106021b01051605070f1e02040c0215070912061d03031008070504020a1b02040f11070515100e0705090303120402100903020a120204020c1e070e04110103090206 77
    0x90303c4202400c2006280c2c40123600c0b03e8080c14103a0741d0443c0074502c2d070100f524a4010900f000c0c1c420b8800d0742140700411031684c00c1200f007103c0c50728031080d030541d2940014100c40426034142c0060784000020101d09103c143e40303a80001d10760070312a0200e440c11103c40c081d0700b90000001e1640d6154041e188000c541d07403103025014081d801c1581d40340d00c0c04800034520901c0c14481c000d6188644100002c0508151007160080200c5030b072003110052140b08030f0111010b080408a0b0007566400f12654984110310482400c001e074540b01d66502d007610b0a00070701d40200c4500c0b510900d950a018448080e11070f40a0500320755014140441c0b95558034019070759402518103640d014000010ba00d100205808180c5128034421240b00a00003010310080302d008803540002074010700091402d204080001220030b01c1c03140300401c0075142c07040c42411641010500e8103d40810765020008105089081c024903000e064001d5407150b252400703880d00035800c40170803402c03810305903101500015034850400711 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 452358129 1250 452356879 452356897
    0x1150914090c15091e0a0e0609070e182503140a09170403030519030b2101060902070819020a05060a0c05040b1207030b0609091f0f1d0c0301210602 65
    0x40c241e1390721811045817060100040a2140105200214114020248090103158040d011030300503901c10000b034880a450302034496020706103161001c420400030001500c01d03103104000200040f100d00d240003442c0e58119003802403506040780c802c88400c1014445a0081d00c0d1000071520b11201c0c04c2c520090444006ca1a282da000080c01105043d00400140740b10100045607400005a081d01101190690529664000582c401c3c440845a000031115500014a00005511380d52450208100d070304c001e0044841081c04144039450b003040c1100101d0070b01c582d0010704102c0e031139540c92680b2043e008240c1d50086990301d200405d46c0d4840c009441c06050000d02d070320350301d60044005031804203044540100107070a280300e2a0031030030050700351422000060000740381901e0300c05800901ea124800302e04a0200000800180340d260942c1d003000414003600001036001081600c0d00c404c200003400d41c1c038210340801c0104070401403140c000e203582400180707043c7c0e01446c1d8648076010784a05411 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 452359379 1250 452358129 452358139
    0x606060e0f13110d0209130908090411040b1803010509120d05071b080304060b0312121906030b01090f0603080403140f0f01061e0b030c0c0304030501150914090c1509 73
    0x21310a10990280c2c020040f850f411210768210180c0390080c3c4c820f503000e1500013420020705001c56186400c15810105102850300c00e0b05040903258803031402150412013450703d4600c404907003100b9505082c03003655004084900901b40301d0b0300650800b03026219039201503090320b0f0f0700c00c00118500e00c00e85200c5184c82c20f40d01d540010100e10304120b65150010f84050301c1c00391804002200900c0e00041e01460a00c011002c1030401c407940344104c7e14090014540340803015041c0c00078000d03001a06c42c94000e54419101c40400d541020100300446101c1d0b107076100c0d41841c10310b0a101083c10b58090318101c1c2c2d80a0712049408032040320701070174040340041110b900d10801b458a07136024810b400c030344c0c01d40c1d0324005000041e0344d48400c09411806c651080c41c00316031007040442c0c14403160b80c00900091139280c04480c5425a80c1d030300c0f1400c41d01c40003003042c000107034014140040221805070040c01ca030100088500c170300700804880e44402040e0003d034071035900c090154030b103d5460400d4480c5440010030b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 452360629 1250 452359379 452359387
    0xc0606032306090105010509070e0409050633060d020304020117010b0c0c151b0f0a200609010e0f131d010531022b0606060e0f1311 58
    0x801c0c8190320907080c203110001c1c02100d002414500051146038100d031030050005030f007921600400d480402c0850610f6402584601000011a0701040490301810081c2c0020003592070380905141c4429a0b6058660002c064036100b940b43c1d61418282c070340b64030151100580d26100c61006880d00115424007640b5120f13800c000046032214900503094020402007511000785808042003245c0140100c85c070b620790f030140030040040880a0101d030080740083c0485410a02d4084840d1505846c0a0101e403003d41c402011450040c032550880381d000001d0320f1250805c031040001034500700f01c09685a00034480d1400310041503550b07030003943c489203580f141001180c8203003060090010300804000155030800c80412545114805c440060103003031b51003100d1543c980d41500d000b0500000d03061b0307400410420716100303404103550401c2d0400c0d00c0d201218400b2241d8a030801c1918143d6000105200722480c90b000c582e110494000b0304408211076070340710080e0281c444402007a0705400c2c6015000081 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 452361879 1250 452360629 452360663
    0xa030f14090c040b19030f0c1e1e080307110316230105030105090103080a03111614011b03051008061617010303200c150d1d0d0c060603 60
    0x1c140c6801080081d5001d0105552440c2880000d28602d0340116805840590803c080303061010f003001528401c4150010f900ea607040d04109e440c2c0c2030852503007402c0f03200c20b01700a003402616100c0702850030780e156a241c0c2480c000e07019841e4003403140081c04810b000321014150355818002210382c41c1001c0e00ca18404d9071101ca01003e103811502c9140303070383d6014011002480d030249094074100d40c40106401c40980c00e50b5500c105c0c9810200644090503180c2e0b545e03a60205100010300903151280c031000c0010f40c1a4100724005070b07032684120040b039140c0014138000005c210008254002e4a040101b03681e00c454609291120503036022003040d001c0c85041c07200294403a1114903100d034040e9100580f1460f110a188a6680700780310003404691591800d1040c5010882640130440006003a1401c04c110300b0040b80c01c0090710140c044501400052200d24448e25105840d02d54035100300d9260b1800c0907001c0344c0d40e0740640203161003e20901c1c068450070001260002005180c0c80f02510103406044 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 452363129 1250 452361879 452361883
    0x31e06140c0705152503022b050604050f070f12020a1107091b1d04062408060306060f03071d16050a0f080604020f0403110120030a030f1409 62
    0x102c90403909030082e40040d59005248007106800b5000c1d005106040c024921a100c926096080624003456004d001b605072034085002a080408100c24010300249683c440c010708442000740820b03c20351601e4140310102c4c00096515510880a007007100068404e0b94040e00c020020501d54400640006900750110741d00061000803900200d040700e840c540c883c2441002e9034000d00308040d00b15003c6550b40c14080c850b035504904a0701d0303001d402c4505203030000450103035001038129811119090520020750030203460329810724103403480c041c1c00c01c0c10442c1c0000d07161200a0107651098030000c1c0c030611a59400e11400303008244004103100507a980b18081da101080c2100c04000307940340080411800c034080c604a40b002c4d840c568512641070503680090fa0707100c0000e401290003641c00d000b41c1c2288018540104003460192034110011900c800004000d140c202072481d0b4024030894104001140c004156054110b550138041801d004a15004000f0901c00708880c03103412080c82448401800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 452364379 1250 452363129 452363137
    0x6090307060c0c120e0d051e10090807060c0201020909040b1501030203010e0601120608010e1605041b080726040606140f010309050109020907050c0f07031e06140c 72
    0x407422007030040d540030034820342e00da1080b2940900840810540d070f0640900c204485060380000a00b2003e0410f02e0380c440034a002c01143d0048088002001e2040640208100d103141000c0000c0050080c69410355900c00035006001c0d0080c082603d507081c1b00d01246c000e4050703a801130740140c201d2540346414280604100d07010f503001082254000b001c02440e510034000c40c2d0583e5100ca410000030713110803004444580142c488400c0083c0d907602d02203061042030280c544440000f1000f040110354082e894078640034190700c0a44140d281120491905250740600e1707006c03080d5810311051550700c140c001d48104e502a804078608400c00c4280300d4600101400307590180780500410044a07854451201c241001d52040c2980801c280b401d01c2003561280c0c1004001c580f2410011540c03030309030340c0840c14060702540c03030030f0210780701142c00d42101070200400d1400e840c04030014103800b03156842d4080c0c6122480103142c114a01e02c0d10340400d004481d04000b0310442440190300141c601074480ba03005404c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 452365629 1250 452364379 452364383
    0x210429070b0f10060206040209060910030503130e010f08060105061602060a03050f09010606022509060602030319020906161a071d03010e0705190e01140109330504030506090307 78
    0x1403038010903013620000b4800d02c01c2c1d0703020b490009991940c400700180380c50001c00c19840a148020f0110002e2014400b400507400300392490800309040040d00021000c0580105030008000301c0100040c050014070b860450f601904c01d00d030340d03da54001a1400b00c0781110f01030341090740000c0030480b00b0780c1540128440c8011000f610881d485803204942a10454480e03100160b1010040b1000301e40c1700e410058240d00460250b01c8030035a0303050b201c41603e600368840c40250300b002c0100200d01800c0210181d02c580b40000441ca0084000001400d42c0a1454201d044c2c00c0711418420400c4801c10800da50030759503001110091401010041c1104103401b05544d10803942da0ac0c1d1103c905050043c84085258035016040c41410103051000d02c005c400d01d24014514103040000e541c036100c1d1940d901904281c034400c1140d03401c0d28005090982168498100c080c4184418420808071074001d2011030010191140307050048032048603603000e607801c0a806400303a54240843c3d244008001c041181c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 452366879 1250 452365629 452365651
    0x50d02040621092402090405010e0f0601093006020c0a140312151945110408150108011d030d0207170c210429070b0f 52
    0x26048004640644125000051080a211804c0b1a500010f010300c0380c411043c14000506011040000074141c900231380c00078a07032246500c20302010450003900640d00460a01708800c4180c90300c03912080901442c805420084003400314520b03983c02d8180c0340311120b5000b1209540301c1e9105505d1a48420b01c14908a8405089140682c59000048243c814007000e2419610456a8620010703200f4810000801c4d4441400000810b01c00e11034007800001d080c4e94041d8200102e52942242940300c1829500c02d4403800401554511960b002c1e01d8182840d864078011501c003c00642e400e4281c041c44e000017540d40901c000c490003a5007000c180038101e514900091241c000d03030701505140030301d2100d1f1082c0d1580042020114080c02e540082c22060f00c541c000c0e1986a41c030400009032500099820b110f40c1d04901015403850024030781c40308000000704800ba1501c0e244c00008150012500c080c0d81e42132400d450398030f2040c005003040c2e0b900c180d0415207112462078550620310461300115003902c030174 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 452368129 1250 452366879 452366927
    0xc020a0806060a080c130b0a17060103030807020106030210050702121f18030207030b0414010c08041109010b0a0c061103102c01030b0a02220f0e0405030a0e01050d020406 75
    0x43c80d0000760b4800081d00039191910b89001140c6c0b04025166103100384d600003120460000301c601c0b00d070031944c1c0c40030407241c0030b4a025411403500070070f40c48000d01000210380c10010b00748003517543c100e151090640b050401c8c6680710180e1011503e04004402c080125000b400c0429200c845800a00c03001e408810408020f40190120701254000c101107028006a0000c00140001180039040f203030414084e80c074030854207802e00165420755840e1013101c80040d2440342484100300c0c852a40005007070003115084119030406030f001c51203002e01e110100400081040180a10a09500c03113940c605c1d012480940d20b182010781441c030b00149104021894403a080f03411541c4242905084101c60342540160107a40707183c0364281c01c68009020034402543c200f15014000c0080c560014a98503c0c4051001c500d14000d00706c07050fa01264003c000c801400c41c00c1100050740401140c0800c5030038281060001e06900048605028541c4c1d003c800c0e62000601040f5a03400c90603800c00d03184480d80040340 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 452369379 1250 452368129 452368139
    0x161406010810020c10020310150c020f0d0f03140c06010e010e0f0f04030e0a0b0304140106060c0503090925020109150b031908090d0b10090b060a0f0c020a0806060a 72
    0x8a20910030844042c2d00140b2034021071701c1c00c0d0f40007180c00c424407054126805444401111040203044000404251031070344240c11070501440c948a032507421140912084425145d511084440c0d64004013044403400056000248a00a6230103d41d21801115003540e1079411194400d80203000e10501c0d42c047c800003070021600d403100244204e46551005445480d160303400d403050301b1415203082d444112300c000421101d1441c0091031089004451280007000e00d5a4494211040b6400036820007681c00751060224800208807400c41c0e109943d5404030b543d55070f82550055204d0124449500007202104044590540090503540c0c01070185c800042204503212044074210031a198164212070880300001017100d5440101600400c840c6180c818204009450b1707114200c0c0c100e40b42030303808060201194114a0000103003da5900400c20120707450000b036014002d4602c80420000604004481070388500002c42540d58064502058141c40700c0c0318544401302250320394015004034000140e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 452370629 1250 452369379 452369381
    0x2a080c0312090c1903030f030615030c0f030506060406120e010e16210303020a180f091109180a0b10050c060f1911040f150f051e161406010810 63
    0x1186119071155200c0e881d1442c0e9058424800070746e011408d06642c1e4034001a4100c2c1c01898060901941d5400100d072202c0010180c52034104081d014101482e000402140761110411502558214142030062021031145030303000c1c011348201e01d6419401c00800c16200d04001540c240c0c101003140c00805500c1d11081c030707460341c0c420303020b08035403005040c2140303d006c07034000c3e401004c252100d480c3c00141c0540200c403a41c40c611031a072001402d0b5090010400c080161407140082c110041c500d03561030300c490030340081c4021903130f50413401090000700082228038502d0740c010b4203015405820114210110500940035030020244415103020b03110010300351021645609105591904c2e0f006035540105030034800429280d280c80507400010440414904040c510032401011503940c107c0009074140e00080003102d03550354003410b000082c002c21001c0c80908e01901e02c1c03081c4c21a00310f0b488070110032000300c400300312010107803210328005841c2101d4032010030828141c400160880d841c000c0c003481014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 452371879 1250 452370629 452370649
    0x2070f0806070807050706021308101401120210180308030103020f01050a0206180106030b0f070905060403050d030c05040b030f0106020d0e0607021002031201140301050105012a080c0312090c 84
    0x100010f040c2c0d400041c0140c1c001c20141400700c1c040c400c01824100c11b0005074007034443d80d0b04a0000f0ba0703c4050349c2c100c03c108502910f6032680041101908651625001c00700c19905c842009100301c4011044407100b600c00c1c840d04007107241812420402036600d0030540c14540c0280000d17809001a508504810350040c1c0c125031101015074028502c59403035040c0e6907c41000e940d8200d00715501c0d2040003001c00c0c0480b8217203018900090b4004079a00303001ea00a44000ca080c0d00c0280250700070301003000400d00c0800c1c1c016698449040103c0e0106500c5000c449910494214004055021003402814091042c1c40b6040c0da03010703021180351444070310b03082e1100c0e80703940f074020346c0100300304008001030410640e03401c050342070340c0100d030700341b809055491100c036009030010301d1004c818100840b26460b0900131a4014403081c280b240300000c401c041e94104061044000100c40c00848140041000c1c2504440021384072905803a1500b90440900c0105c54003940d9107485e9101d0119000703a103142c9101c0d45 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 452373129 1250 452371879 452371891
    0x911040506090406111905180a050306010324090809010e09060a0504090f05010c0c1a010f0b0c0a0203070803090103150e0726070c02030d020d090504020f0903070602070f0806 77
    0x2c019665540e60782402904450f13091604a400500005601406030f600e02604090307144c40329610b0b403140390a600344c441c40b4060414030410f000c0004010381d4a011403104d0541b9041a03040c50075509196107080442100e4102490292412000c003080c054440c0280c0b420842c240e9503003022010000400100080540d00958007000d594000c1010b4a0a6130141080c5131044014112542141e03c680d070031200300d840300c0e9021070b50b000c040d04d04000c40b01c0115500c000c4d401007100b00c03c1d4100150014007860a001d4500380d0a00003a6001c00b1303900410040c4402c0e07600400310303980c0e076071585801a03c80e00900c8015010a091205e2050b4030103061217054103a44070000750b02c09a544e10741003100c8443c400f0224402011900075050524000c0140c1d8600c0340c0140e032656000300d40075205051034030002401d0282150011100b0b151440d52055802d0111b9604560158486c1503010310341c1054800c41606c3c82d4503124a07800015400e401081c02c504403484904039070b0040d9980d20446454800860741c1c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 452374379 1250 452373129 452373139
    0x7060c0318050604060e010201110d05180d08060f03010e0a0813080f1203190e0304030b01050907320c0d020105011a04030b040c0b3907170f0d030911040506 69
    0xa1117690312442544119170014400400c0342d003416140c05000394005401150819140d1007082444881d200346210304c0c680110062110000002e0b0040128074060005842680b4034040c44c550350383d09400072008905000140c40114480f880c00d00155800030403d80300f5040e00b20400100580045005502405114046c113009542c0c008140f415510091001d540c940c40d00b8a07620301d00c9494460b0201c0901c1440c0150741e941d046080c06040240140d004034403405182c402c000c000c0c2d50240c07800401c200401d18040442c9610060300442450550071a0000840841c1d110300244001420b8000f010030303034008100c0380c0d807a0400c1d1510b82c0e4240e40d614000340c40810003000003400c0140b10590007409010001490703a100d4900320000c1c1d0080d090104080c138640c80c007000c1c3d80300300791800341501d481004003900301c8007094480e80c40d690a88142c100c2c2c0300520120030180541405010f0301c1800407000da868004503550050000c10380c0900507190303400b0b0100001d0150030070303200c0d040c0140c600a00c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 452375629 1250 452374379 452374387
    0x306120d0f030e19171e130f05010e0904060204080d09031b0506030f0934060e2b060e0a0b06060426070b0c0c122b03060807060c03180506 61
    0x183d00c034840b00070b81c0f10101307140c50420020380c241b14400e17468024a070032a501e4555450303c0c21300c005000d80458000b118000d1640c2c0040203141e07003001c2030b0161400141c40c4410742c2c1d5a58108400240600c0e80088920300412546100041d409050722040e01c2c03040071544404184126420304081e000c0c090345800c51010000f0400c4141d0100c2010743c88070004045501800c032300012555204040710242d801d81a04503124114503201d600448040c0c0400c0c030304108050902c4001400c4015503000381f900500d15042049640003443c5007200c038882c0c000798180a00d42c1e1580a041c2c1d02c00c1480d0094078244103040c0804c169260410480b030231101c500c24040d03410032614544035030400184401800501c521000081d4545540c00030b0001c0050b0780010f001e022032034000340f041c4c40010300000074031608080e0f82c4200101806908200c006541501400001080c030300036001800203400c00b8140f40b2403a134001402a5001d0520160341d48665685d40081280154250522503503000703280d80408240 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 452376879 1250 452375629 452375633
    0x30a0309051c08181f020a121a15070206030103140d05130e061801090507020f0c090f040f140303161805060c150c090102070b0c06010b0306120d0f030e19 68
    0x1400044050408815100702810350702c85c9130340c00e640c01c8200340c0c045500441d007410007030f80064007001c1168680c0020b0042038201e200c0c8900d4000450b09003441021120110074044242e5004e4500b46940a48115680c1d40c683c14505001c903000b07840c1c840c0d01c0c801c498100c8011403007682602c03007111652200c0d41d0142e04015121540b0040182455000705004500310202c07018044594002e000c540c000103224100040c00a003090940d1245880c207a01c002618040341e10365084090b03210514405405683c2c90703615100c081508000805000c4c1c00303503803514071035402010000790b0080c484442d0b06001c64404034002d84d040b140350600000a00e003a805c0402442c14202d0042280c61128025a001814241d0086810000c280d03050060300c3c50110300c410f0b0a50301000410040c0c01001089428001640001503403402d05008030180c941001c00495a2510742e01d501070b03990852042982c0c90050680301c01485100da500400d40064100076001300c0343c00700440c01101010384418503010f900c00035 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 452378129 1250 452376879 452376901
    0x90f1b05071e020d050102130311060408060f06010c020d03091401030e0a03080702010e031809010803030405071509182004230303070606030308040308090d050703030e0a05030a0309051c08 83
    0x941043e40c1002d040b00d90840011400e10003800e400300182000204c184c250b0402b01d80d10100b8000d2140102003c100a0245550000300180d10104903a440c248a0f81d030100104d515030b00560000303400c400078889440405801450040686141c008007218981038100114191400e1724030506258005181980200340720b0310b100c0d9804016800042070350040740111134074550005581101401da0009104004d02e4000758450050200300c000f1030031410140c442540b2403015108142103100112a0020080d01544031000100308910044070361741031140e03e00003d8900c50144501155418000c0c400d112007080c19582500c0c0380b1303d05071000495a1344565103000d00307110207550510050004030002683c0e400384201440c400c1d5228402810245805450004058a01034540d0448000c039040d16038800e040c0d0f45815010b260201c0c10a1790b113078001d8101100d00300c02070158000014107080554141c0c001141c118030070412180c9000040d580b100c48080b81400c01e070006211000070030207030100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 452379379 1250 452378129 452378183
    0x1110c21180603270a020906040b0901210b0c0c011803050f0a03021905040302030d0203030411130f1410090506031002130f18140906070f020106090f1b0507 69
    0x18001928004d841201c00301c2100100b48800f1940c0d070b80c041c402d1142141040c001c0150000d4040d14148160b10401d000210407045c14095070410403103048484000b01c81c00806410001e03001801036005040281d4004407541c4200c1d4042c62942c203100541000c2d20312508014049501603450506012414440c1d10702c5511011a11042640030300640e9600d125044054408070394644886550b54554414103003401102107a01003507410038020440032a180010110b525041160340800d9411500f140e0802000010f0040c2d811900d0000b400003051040070180740a040c5030100703000202d07942e51011050301c01c112117054064200c182c100c180b41145402030007070580070030601036666803200c986801c000d00b13561001c2611190001225100d8000d841009250b1442c4440c0c4011860068412903a801010300954208103a00141a81d4036100f0340c480d6010305200e0a0500503010a06140400340204190703924445030340c0e0b1191402da90080702101c181d07540c041c442c401103403034800440c1c002c002 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 452380629 1250 452379379 452379391
    0x3030506010e0a1725060c08070501050405060712020c0c0906030c090405010507090504061508060102010608010c0e10020f0d0e1912050c15090d0501110c21180603 72
    0x2a40c2c4103008a41e40d9400490040c4c10f0b813140340300e032015820a8492070030510103151203d20044c8034145c2c0a0b41900044002030b070300d050801c1c4c0c1402481e03203008004c030311482c140503225502c0c0c0740030b020070000c0100c0c0c0f06004502c1031b0b607041c0c0c0840c2c214007240120f10030302000500c40c2d44401c030ba03400e4900303101ea1600d510043c0101030300c044000f004049059082c0c21901111240d544404003c000c40e00645807801030502681d003002800e00f000001030300054584e84010a00041e4000911168401d4100c100940601c00003030014101ca848090007001c05480d156110b00000c41846408610018542122504450003420300490041c0155880c040d4881d4041e0045000d8044014402442903210000c2c4481000360610383c40a00f0603c0c14686801162441050761b040101c0c0090802415513444c00d904842e1614140b03114a440c03801002400804102031401140c580710125000c640859a00000300240300c64810054920f502171107901c1d40c983c10b002031030104014500b410b8002d154444 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 452381879 1250 452380629 452380637
    0x506031509070902070309380d0906150303020f030901200307080a0e0f0f0a060e0d060507030c02100c0f08090c090108010e072108091807021b03190303050601 70
    0x3030344a0f480d0000f40e9214034015004503001440130860f4580c000381c4480c0b25805c241d080c0c0481c290350300140030a40406820310b070041101058a01152400364050441c280d4088420040351608001c12120003049100550142c0164440b100c4200e40200446500c100140d50f8004014100313144168080d8541e2160700030fa00c000e000b200300180e070100080003070b800310361a400c401248020802c0b0701525215143c03409402003010401440e11021481d201703071040c0b814180700e62141d650124041441500d0041d000b0307801e203010300000c2134040d881003c0f020010760075505085441d2840b001641c1e9946501c0300010400c541c00c0038a544114040b0b0b40100354078050b22103241d00100007484600c000c0e0001c051995503481140d0403688204410307070081c112408405c0803070001b4400c1ea0200c001d155006000718000180c4a42199208d20814005500c154080141400c16010007982d4020200320442e100e203100180480d03034540003c0e00e8060350408425905919880d070f030110007174a40a4442ca040c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 452383129 1250 452381879 452381893
    0x30f0c0501051e130534180506091302220e1f0c0909020f090603070e091003200f0d05210412081c0509010e0c040506031509 55
    0x30340c00303004007400f0380d1072101c0040c00003a80031042c400004010b40081c05114100c50000e00296010404611a241d010040c0c005104400c0505d60401442c1408081d1a050a0404a1388808045003a920031002010400139540c50700c05100c3c0034102501e01c41c0b070320410490346070014a4010700358218404250498100310054040c2001540d000c030f106803105400100c20b820140446002c402648800e89900780b084580000c8054000010341c0100d05803543c0000320b240c11524003100719103400e98080c0c5026502d14141b20f00034811240b0594192056040d140401c034550a60b103803c9003640d822440e841601500141c8030512102c0c0400a56004000c3c080c82d5002540c441003041d0900e0f0141001e131041800194a08000e4103100e090075000c0c8100780803c0c004200c0c4110b034608040e501919855480300b40d034600540d842c1956800129075802d08003085130b070b0481904080c0c001074450080700e03107180d0100c00300820385500311810394150b440301c04500e09030151028a540c04c8480c200584402c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 452384379 1250 452383129 452383133
    0x816080d020d0e010b0a12080c152a090108061f0507030810030c05090c1c0b0111010603030e10110114040209070c15110c1006081b030a030f0c 63
    0x82038002000c0003540c580c0c00b150812200a00d03004019920340440000c10081c0d28440005010b9982409100015000b00d02010200f21807039044400310000601180d29043d24004016880d89084440003c880780d40101200700d102c400c1d04035410408030840144c02e00305c282c00110f414420043c00c10341d10921290b441c81e10308050170354107034240b134007945d94a65802e02d9040241000700040e1650306480e406043c10030119000e9170b66481510700c01c45d409103c80c0c40700c8174110098020f0903603516601008075004110026240d000c5a0000340c01e88071801e01c046407460302803c031002440090080344505195825a242101240105d56444c1c100040d6804c2540c082c50708540084c100c0c501d04d03510110600003136180160f54aa8050300f9468070180c40c080a036101911825a441d4440e0490f0b2507040940c1d1f15030401e0161481e11480714112001d004101c0c0145e809400a4414180140118403000801403101b05035a030180d007000d00182811161350b03030704a03a03400c841d040d6842000f81d03250074500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 452385629 1250 452384379 452384393
    0xe01030809150d06081b0d0f060c110f0309010801090203060901050103020904020c0111040302120d120203040c05090f1503010e03160c120c0503122106151c0e0a0308040816 76
    0x3030400400106590090303c0044600c00500f0101240310300310b180e5068000880142c03884c50441d40c427040128a07070300d1100c004d41c0c0c2014000b130003624a000e034098040003444000050321643c80700f680c803401c2c180d81e01d9007182e040740300c261b0360f903500600188010300965002340c0080a0098014000500d0032000320301a030300711201203180079050f540015042056140c0b8134450f981010382000940703100f16400174013514840311007120182c01e54001c4001030910100c035410314010b00003d4181101450616031b40003221304c0c229005155114103500703001c428181489495410807102c8002c1d4074020302080e850b01240b800f000111009d075030307050021414016440010724540d11480192402c81d04010402d030905240d032440c82400c0b01c00340160a0b1286020760320141d000d100c5480e50107992116004200c5402890042d8108020001280300595030307262445511480840002c105604424007616240d04da88040a80055060b4010070f0200d503584004120a8422034a40c0c240c001890307407949 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 452386879 1250 452385629 452385641
    0x312040b0301090f0c08041403090915030709060b04260a21050f041203030b060313051c0503070f0c05120408010b090115030911040912090e01030809150d 68
    0x1103001001c0010070040c8910700889203806901e100c10302c40703c1e6890b440100f032101c00078005048044200804150441d003401142c1e03c5144c0644800214506020210b06526030031140501038820709900040ca17049034400d0300e00b07480d14069511324003858621102782490b10603c0c03118611400541140240740108a64401e075441103282c02104c0714250400041c040705418020309001007000819514918101102c0c156a100c03600c015014a80d030030300f04d00400940942640046000050228080c00d58904028003881203045907100140b0807100c4401c0b504c0b00d008080480c6003400801d43c01c0780108034800901c405854003e920780d02544481d4540200d40e20f019009a50008080c0010340007030191100c1e0010030b4459036103d51401c005448a00d2010007042c2c00c0560750030305070301082034444042030103540042051101c404a414002d28403521003004c40c000c40c07450300d00000c03011040c01b1024104d0382c10a0b52181401c8240c07040c03000c40c440d00d1a000381c13448020440c5003000d0149104030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 452388129 1250 452386879 452386889
    0x1504050306041a0c030f01180f1104051e0640060e030d0c0b060d0204050f06040507080f2d0414010608010b03120d1116050d0903050a030e031204 64
    0x1d2070302080e02c0c3e49034009900b000e080c50710603460400c20440e5070346000f800c90381100c40490015091031808022480200420209008101d00f40314080031640340d6400136109844007122243c41c0f0348082c0401c41858107c0e004ca080d04100103100101c8001d0700102c0030304003035400c130038405464a800c03108441006620031140d078803625110070602c0002d9018882c90040b6105400918004030031070f0380601401d04403080105100c11500c001002c5480c0c840003519450f03400303002800b107428079116090302c404080700c040c0d004a1402c00020181da00c24401d280c02402001101902501c442661407014071550070498501c41460290116000c00043c0c1144105c0c00740b001d040001043c03100640c01c0d078940d0b03800703820140e06040c0b121400e66008a91070804541c01040e09a0302c0c3d002d010f0701d41c041d0142ca11001604c0c00c2c0459103a0290704c4009001c400c1520070303401c0d00c451048001c000d4a81c4d036100d001c054590384c449400d18002038014014091094402000c4a405144600d039400c0c0c20b40c059000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 452389379 1250 452388129 452388143
    0x30304030510051603050105031914010606050d050601021212070207031a040501060e160302090a050607050d2d1d0a082b080f0a150e060f0a14150405030604 69
    0x20803003405406072201004c1c0e101c614050209502d4540060307502c90300800c1182d9030940110300035041043e4202d180c5c10130903811000303001855403603402815582018040300940b90030040043c900350b00c04640e240c3d8190340b16040c0340c1840c408a0b00c5411185008058009522601d480440032a06d1441380000611903081c0000c141d2400c3e28020342500c0740c035880782c80784202c52024002c42c03007040c450f40d0302c03100e0b9103250050710707034100e00000369010009904c61900b1000008888081c0080032905008550341034a5501c0501c90810185c0401c8103007035406803c8403000f181d40b1005c94400c12680041c2c01010100d41031488100002031403502c2c1c154401c82c0700d6030012521200010718000754840404101055403125000300601400443e002040c040e01003010b9400141102072a621060710013411580c0c1c00c032429201c2c540c0e41c401e030330161040ca200e0034604e039440b2407038604141200c040d100c007094801d00c500b5454080c02540c1d44925050601b54109120102d000c1d20200205031045000b164 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 452390629 1250 452389379 452389381
    0x80715030207050115080c0306060f040c030902092a090307090b010512090706030c0e060304030c0c030b07030506040f1a0913020301090b041a01031a13061a030106050102030c0c0f03030403051005 86
    0x44081c580103056080c2230080c0c00100c10005907035030744240d100c112003041c1e802064188003528110300600002200035840300b009014050762440300b0b5201401c0e91030500403251721484075803e45142e4020444100d0b0706500412081c84030130080e42010301e484506041c218245040d010018684c1401201d07041c505a00c8100d0800409906010f490401402c5052503280c04c04000d01280c0588001003000e0180028110300804009050641c44000e40d08006980703981d05003100018017810f41514440d2045080261005408910388248184803d00d0b84441324200422400d002422400400b40c1d9030324190690280c026032028043c030300c2c01501c42c500b842018a000d03d01204407400c2070304a0203c071800c0b100144001800c010000c00c02915161425009503699040705041d9010210000c0219040802c00020345191003202c68a002084009101e2507840d94012a03803401004003d281d26401103000d142d642c02d2012243c1e60800c0c024050324a000d0b125250546403001c126000d61400e0f80e104 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 452391879 1250 452390629 452390639
    0x3031b030903021213030809180c040504060609060c24110702040609061503090516080a0309051f03050606071e03030e0705060909151906021006080715030207050115 73
    0x1124100401d1165070f1388506090840003405140349031404000c00d14034000405040554608501182056003001d9884031440c12005101942c0c2191190b240036174140800422000d0040307030b144061314070540d2000d00d800403580b50f1810648108440c003040b030303038080c0e80c44a810000e0f0098101c03468548086903a11480da106000072614542c0c482042c0c68905003084c00011400c113241d5840145d18179020401100c581004d83c1029030924145581c1051001e00140b4914080b951300d485c5406500c1320303400d0300c1d0b80c1d10a110700c0d65900e114020b0304443c1e03422806840e9020341d2010fa007040e00901001e040035502c1d074400c8433440301c062801c0c03407801e9500242020160715010710003501c003819000d0706001e4588401300b0814010b541031a40704450080003d8411003101c09082c201c1440105144003002040e04403c1081c41c01d03000da540140034510240b010403541d07024103400c442018006015461401010310b55440c0035180c3d03c820590200850b0012900901503504010300d0b0804045249141c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 452393129 1250 452391879 452391883
    0x70908031b070f08121305040f06061b0302030307031d01230109020f1c20040504230c07020112022a010e10050a180f0201110615040903031b03090302 66
    0x41da02c80501400d2004013031000c0324004c11140003104690103800e4441200c07969000031040550422500700d8174003161900031181580040c0100c410340d484020310b1081e4000400d81881506201501592003040402c600600c00d5005c01031004e820500c1c00355440e12521030718291211880c0ca00e02803000f20b241a2907029429440600404e0201b008500d0810f841c803c01c201401640d05c40140c2c541038100c0c0542d122202d40101c008520303030101c0707a40100d00000b44c80417650014056640074030b00c1c119005110081000c0d0300d070144140e60440c3c0829580c4c04011241c19881048100d040140e180e460b82c0003a04940060070600d4006074041c0d107103044402e00c8900b07502480610041c582e050421103a0160400700310750803210010310012072160727900051140a80516050041c4000c0d04040c0402400003800c00b600c0c409100341da400f5600d018541d0756070340e01c4400307070b445054140c7c1e001040710030707450a940820a5035202e41401b01c0e2100e100c2e40b20b0354003550116413040101e0307140c02d103040403d941 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 452394379 1250 452393129 452393143
    0x60e2a030c06191b0506150406120f26040902030a1503060504021005120a0c02010e0a08030a05130b13031e0507020102060705040f1206020931140f070908031b 70
    0x224255442d02c402d8a0b11707160764034500500034108250b000001000c040e10356400c10300180030801100e200352102171a040a1746420070000355040c180030144403000b90307000805601d48400d001101820581401c034207000079400600022800c0d1382d41c0c094103501141800000004500030900041e0904c2c00f8010310604203c0d5464050801c8401c2200d80c100c10003610225402001c54080018103810070309099005060310746803c1e03401c0c85210115810040d0f000c004521456158105125948401d1a13064140c02c80d500020720340c241b82800541411103540c80e16080b140245001c000e40051410b59000c440c801e8041c210014030006284000d5580400000c1d40100b0540b030040e2401e40380c0015684400c6c000c1c010002d80c0014090302c5402e014041d01a1000000018114102c81d00300500c5a13061080720074410900200807944901d0000b11071180d05a18544a4543c040e5613480301c0034208104401411002484502007000c1200413081000d040207000f41c0107080b00740b00b1118003407454400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 452395629 1250 452394379 452394407
    0xb211807090b0604090914060a02041e030f080f12010b04050906240a020a080301080102030108070807060c0b0619080102030613090809191e03060e2a030c0619 70
    0x820165940903646903c4212070460302d00800005000071a4649a1524031122001d0100c034842c600a00052000d6580280f08407580135080c540da8990b10254a1030201c02444040c1104100351405004280000c0051640d00348150b03100b890491540c0110003c0071003030308001c80e4810081000c0c88070b030030901c0d65140c2000003162982171682c0e001515211410007010750658000010920302c8509000b003002d15002580010090748a603112802070f4002e4000b40f2074885035115842001540d400c000c5441001e40d001c5507140030000d55035441c0d0b6080808064052030b017081c07190041c1c01a00c0c10010f06607000d04404c40001d0b80e203041040821601c0b82050380070b00541c80c9170000d07a00014242d1021101e4440c416a106a4221450348800382c18050701d0303000161544107100c9000c01c05002e071301080c1c1a644200410450b00030b4040d0b00943d120745014100310019181100085e50b4140c94400b2440804010200c81038404510b010600541000c16017907890807004180600058102c405401407030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 452396879 1250 452395629 452395631
    0x406030b090417180307030b07020c0111060604020703050d1518151401050c06010806040b011706060d020f101106310302011404050f0f010e070b21180709 68
    0x400d00c2d454501821502d68041c0000c8000000c0000740f1100c1c920141300350800c020181c42140d9901c0c1080080e5400c03c682010042c003855014080c59070040c160702070100c600310010500c0f562341b032084c8002580031a001b80c0a01c0001c3c0502600801c0328082d503401400c0740ca9601c0082c0c0e203009200e40d41c032400300c0c1001801c0c0741450208200c6c607a605400204540000304521551201c44006a0340c40c8504101d0800b00d020307a00004c9080080011094045c91140720452196a42d9109000c0090b80108020b95241c22490120301580703080320300443c9590005160074035100c40c0d01c0c00502d00000b642900d41c0403502c44106014655418045141d1240b83c469404003181c3c0d14039180c90f04140d00762000762090707002190b4801814406d40c00405610a80d0004032894101400c0c003c2d540c0e000c0c64084c40c040d10418180c0c1b40d40c2e80c418003c01400102d224000c15886003000041d000301d400c003d01e0b000e021029002c2c801031482640141c54010469151541901c51211200506160f59034100030012 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 452398129 1250 452396879 452396881
    0x100c111209030a200a0b1b030909150a09020c0109110901030c05060f070606120615050a05040f110427060e01030212010905150604061a070b0705041a0406030b09 71
    0x280c60220380d007141c8980c0303d000340304100c02200b51841300c110030031030050700255100c03808200603502400400011308000c514038003810b0740c4403800e81d0301d1042121180c0c00010610102d03c1441c44c42ca2900f140300310007080d07070a0568031aa40d0b0012030b088036003001c030f07107130345900b5038509111044101a40c1c0c1c0358181c0340041d856042d41c031000e0441385680700c0d641c0140c0d0001480080f050001060354005944004144246a40c64035842c3c0d8803c054601030b207140b8030341807a00c0101c0e50300da620002101c0c806405014a60b24010410000380b10001d02503032000d8503406c80800c0056820020700140c0304a451603481a80801000302460140d2805d41e01031600c1c0402c10f01c9040c0f0b00d246d0307030360441ea03040310302604209070003964501400105c000208144266408035040c0c04000c2d2000d1302c43c020a8504000701d50b40c0f0501e000e42c0c01d1841c1a0000680c0d800c001c5d84e000b0910340b910a9034003400c00d042451034955241003043ca180b08040700d0510b032000105041c85110743c14014103501500481c0c1030200703 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 452399379 1250 452398129 452398147
    0x7060e1309061b0810060818030301080a060509010b09221b03060501080d05090423040f1209060c11011107030803041a0618071b060509120c061503100c1112 69
    0x21460540118811f02061030000340100480016041c000d4180e5000d5076120751795400030942da00c116113400c4071014209000aa20010144078490745603e000302100c0d03550b225041001404030856036200c600040f202c2001000ca00000b48041ea84110481c1c1d002c141e0f071070350500c2011110181c0040a041c0c10266041590780c2d4043c0a44410040031500060329115500142e5000608903481c45001d5401e001004244440600a003050310301a05d244401d4641c8184100e84160b100d01070b9101003020801c001c0c6c0030030755120030741c8412070060411850a4110003102c0d4506407007980101d9803060004104020070030361680514080b000021059510f082c0314000988255102c2034640d441d032210030004483d1441402c80244070b542d83d2807105003d01040c1450006410304440071030035440fa60081c6e08404130904100c03101003403220058215611168000400c01015091040e4544138950701009100b009100e40580a90700c0d4483c0a503850705140d8141c1805007a52100c1c034080030900203110 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 452400629 1250 452399379 452399401
    0xb0a021507180308090d140a170c0d030216021f020d030903142b020904110f09060711030d0c120801060207140310110903060a0e07060e1309061b08 65
    0x3500d5010307440c0d0751114040004950032500c001c034050403000183c0d003200400320303002c08d100c40c025000b90100941045030f120f40884070301c129000030a043c2c0c0200c0030b48401501c2035000d440310001a030036500c80d80045800052807801c020130b03c980751b00c0115910000e441d0b01003105613900c0c0c00905050050342c1c0c098401401480b038144000041181c0083d03020307416988805428a40320a09c0118030000030803aa541e8001d4100031716480c043c0c0c7c684400d040c500d00300081507994900500072002d103440000d200344912500455011507900200701c014a0039035030300384010b08414580c1c3d40c45802e40e509034204100b0f881300d0600c028050060213401444607035800f00315203050fa524881400060741c41a40400c1c60240c02c4801418001c0c0b5200402c075040c100400103142e240341c128100e4019031103815141c0c0407590480f80c40b4015500c0400200101d41c080e0811220f4000000d1606000c048205c0207081034840052088555035642c00311080a81e0700801240344803840f80c685503030207103000a1030752 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 452401879 1250 452400629 452400677
    0x6090303070302031314030d200f07020d06050c0d060501030e0a23030f03070908240403050f030f01150e0109090b270a1107020d1104060b0a021507 65
    0x40c00705a00080017800316200c1045444940e640104001c202e107403124646030b241d0300a411501c02c07090411001e881c1c029050320001000710f80300603003d45440440500e00280d54850102203800c40d500e00d0040000ca0300070300c1858070621544a0351640e40c0356100d00c48085078101d402080c1454600300044035581c0f80010b065070b2217907200c0e000c03590840303c98200040491225036900e0084c0b0001486502c00c40124000d0350040d8055207800211548500906071900d240e0a6a1002181400980c0703000326035040ca0f01d07410900909000f4a007c0d030001c4c2c824415801142c00050914144004000005461801207403005032407510322021109407000901c40301080c411102042d4603004c0c030026aa07030720442400c044044510525003840030703600c51541e81c1000c440d035103031507850701030340900401c020403c48075910b90041c2148980103142d0344142e0f100344400d50071608282c1c0c0e1940030501d2800c5100078030300500b07550001c2203003003004441c401750010000d0019040040ea400d01c1c60500c072401c8030035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 452403129 1250 452401879 452401891
    0x10b0a150c060b03031b1e0d03050a0212010303030c092903060a050315220c03140705030d030f051e0c0c030913141e06010c0303060315020307090806090303 69
    0xe00c291101e141440006070800a6440d50b06000000785011280000c02c038502104020100f541d40c144544440315040c58800b041c0304420703802030340380c1c0084d90380309600195200004170001410000031100b04641c8034000d800c103c010036034502e540800d6541060681c0000c1c4511002e6400707000c03001e26802110785250780e0320b4080c0c18010010074416510412060701400000e070441c3c49030b82c1c5070031401000b108207a072944541103800010700c015666031301e160000541c0080c100c0180901d160382e28965040441a0118240030780b00011402d80c1c0c0a201100c2c00005036900803400d81c0340c12925030200c0c1d03409404803110310044204110b10680c080000c550240c2d502d6039182c0c40341c0d840820b007422f500c030b401151035004078140c3c1d1410354000c40794403804103001c02a901c444ca5a45110550900d88080b00c9008810328040d0000340f507961044050402d09403082c540418615030300e503034031400b19580c59440c519a41e0040200401107900c060000c000340301c20030041541d410301e66105601ca0bc409010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 452404379 1250 452403129 452403137
    0xa051005060c19110a090605030c090a0905120d15050f0402030405100203040515070f021011040302150405011103070b19110c07030b0a0b01020c0d0501230108010b0a15 74
    0x2e00d80c150051010074004200440c09034180d074010f00e00020784505110540d44074202040001c01e10030520b00c11802030300c00107002840101020401c200d24041c00425002e212602c03401603600140d024080204d03030340102c0d60640c0c2c881030600603843c10307588040c40040c46981309003c01c119542c0d8844c0a10358041040d600140d481e1101d081160030310700c00c0c0c116032203d1400002440100100090b01055a46601509403220f80381d003107003101c40c80388000840d030040e0301c02c110401d080d0300c4542c4101e07524020404000d00d020795039030114455140030100c2d809201070206041005580140c0d00002840c51003000e1450407a0659a1080714000a4016240702460b1036482881210780da10510144001c41a02ca407500e8086940aa030703150140400c9584d81c084102007a103044190058041201050700034100544c952018070165054006040e1119034989a27030602d074903202101070320030000528420026605180b00030b801c0d0780c44101c0e40c9004a0b190303a010070000d0100c500300500c01c0480c0c60 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 452405629 1250 452404379 452404387
    0xa060506040b0a0909140a1401060905010308030f06010e030f030c0f0c010c03030b06040308120411040608030414190e040b100e0604020904110d0609051305060c070303020408010606090e0a05100506 87
    0x4c203102d03003a4025030500e00502c202c011100602c45250208941823080301c0c002e120f46030303c800e036410a4a40a1000620f40c9105002017105503036031140c2164068010b02d4410035403428180020f04d8008668554034441d080013a07107101c0c5400c00c3c4854241082980001c200111003803000a01405c4005409400c26681d54400e00955031f07100c04460003507421280d800c1c2c803004081859985034070155412901280c501000c1003e07810640100422511010091428145410420000c1c0d40c0c505034500d900c12180250214203041c1c804540000d401004500c0d0420700e014980450713072070380142000200c02c03800e41041060050340d0001c10b03403100068801584812800b00450054203003110b803a048900b003c6141203003401c06900400850301c2480d01841540c13180c0f984180c540803103850282c0b454000200041c3ca0700d2088004289551003441c0c010301d401d50f200ca0b094212419a04500002215105d00704820402e401c9034a40269003442c007080700d401c3c074a110604144242c807e080c01010045 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 452406879 1250 452405629 452405633
    0x30c0d0212070315050a0c18050f01031d07151407170c0d020f190206030f041506030305030f07020309100e0105040b0301090b0315070c0b040f02120a060506040b0a0909 74
    0x40a410029503002c4c9030b10119404004495019000032100b03604494545807121184910980c0d100700c200103240309020506040034284004603e00a070f09030f050640b10402689642c03e4081300d1242000e100303010b00328950409000008100030340c42c0c420100003400d08140200302014003240d00c501c0d030003950f96081d800c2d0a65115441c0c080c640703000040d0f0185c0790310704031803580100f0449100b0300d1a50036a01452158076429090342030782007005e500084148001080912001641a002801740d0f50848000c10701419080c16210203070030440c005038002c010701c614004400c4180307800048c5400910304203800c1030013042c0c014455102c44000c1041d03248462500d40d000380122800b070f00c41d0445461740ea40c2c40d030420901405506a00c1402807150005610030340d0075113800c1030b000b80e12560b02c50565030303196110b5060040010744103803141c041c01d000c0c00006a90b24600c210403d180032010303017803401e2182041e4040350002400c25015504001c2409a0703035990940034029503950f24000030700ca56040c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 452408129 1250 452406879 452406883
    0x5010f0e0f19050a050709060c0f0b090109080403120e0607020d06110d090309051f050d050c0d14040b0a0204081f150b03040b091f0f0e030a03020d0506030c0d0212 72
    0x10208451180c03501c2d0a020358044d0715003003144560650740721001a2aa03419003112414040e02c00548503c9280b080344002801401104d900030f00307103600104104826840c0c03031000b075015920840301c00e0103c00c0c10203a503a41000919101500803034559040c0100c9402042c00107c10141c024041681c80588070140c2101d4016a0480b1070042d90801807500301e440c0140080803103004461241a8403203241404150031345401030031031842c2d07032414105181c1303800d1240a070070003500c00740c110001131044c600d1b03560452040d1a908070640c004250141032601b40340d06524005451401032600400c001d100e0400001000100d030454007402c03602c2d0511040e4414020100c4004500420345008000103083d540c40002c0c5001b0303409810200d640e900c40a418660780c2c43e500320001440700c100c41c40594811440c0e440f441601c5007012000c586c030b80358158804d081d03074130002c01c500109901241d42c8d1812410b5119090740b0071803d0b002410801c054000061501e10002c2c0001d114407a0050219105101 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 452409379 1250 452408129 452408161
    0xa0e060d061b0206010503011503020d240204060809070e01120f060906020301060809060403020c151b010218060903070306020f072010180314070506071505010f0e0f 73
    0x401000c0101007502d002c21400301c400310842c2d8005110b44d000216640c6010300c10054000100f4042c070940030310b113074223100c3d40101d44a415102504d00d0304005011100820040c8a20b1003d4000182d90301d090400191101402801500155210401c2403115950340300e503140c10344003084078841c1780900130315120028003501c8034020a00d9040000003c200096900035505a480ca0385480d07010340d80d5a046650785842c111070183c0103a02040161129003800c2001800002450303400500d04118100010986401d0510002c43c0f0ba50000340c0d10040c107400c0c0c6425070180c404684c194a4000601c001940d6201c03a40405060140d0024040c01c0600201007100c8003203500503075031600ca003040383c69010380041c2110b41130700807840d0740007010003a4420090b0181800c006824240018255200e03003500c642a550000228850600045032569400000e4009188903c1e0820911108080e00d981504d00681c48a141002400000c1c40b0204070036140c40d43c0b2030303945400c5044030b6403200c01040388980 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 452410629 1250 452409379 452409383
    0x507022a030c03010e010509060601050313120302090303070c150c0b160c0209090d091a07170c1e0d020102030906010303110138120a0602031b04060c0606050109050a0e060d 76
    0x210f0142c2c2d01710030201c10742140c3c0c8503500f220140c0c1c2c000d0350360200650f401c0c8030403521a868281444a1000050102c0d036284901d101140740040c244481e1402003451680085c005681001c911007080022120703d1071549003105039032a0000c140001e680d0ba0036192078001e0581c038101d03c560907038940c110b0301c0350460303030000c1d90020803031242c07400d0010701c0740c0c0c450b21300d0049100040c2e10b044001c14155106144410040206201e681c909100c648a080e01016118410455030604101c9080321040422075040b6008040e038050400000c008286440c100c2c510902d81c0079640184100301d4052004110300307044035010300340101200d42040320180101060030700d92041d106454240c0044491000c80d80007141c030688520342c00030f40e0600400c585171525541c3c50703406a20488182c1c0c00110740e5009140c000c0a01e401c926134080b101000c46d4019000f64200b04002601c001800302482903500841008000c28200340c03009906100c0403070f25a00031402008172142c0c000001c50501d0301c4440714000656 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 452411879 1250 452410629 452410631
    0x50102030c040e1b0406080406090503130608090703030e1c081204060e010605061c02160b1e040839070f080c0603280f0b040507022a030c0301 63
    0x1203000070a040103600680950710254000307000180c1e071500c1d200d0181d0500013200c601142040d20b010b04c21200310070001d1040301ca80391181d091000182040003c0d1510b40018640d4003031442c20508014032408000b00408841e40c0102010000f090700447ca544200c4003e070b90042c140c589405282010340700c019401026000c0024031650082a4880124065403080005015940222045500f6210a4041c0d960b21410030441c1014100d100100c2d0350001103407810150400300d03155100104911407143c16034050320300342c080105005000d12122500081c03106c08103507909003900c0b21040340c0912403401c0f107074440646500c60404481140ea0000c2520415605051410244000d481d550a4071810786c00500000b00410400808154080302c1070307000d010305055949100180c080845c502c8200c1a81081203401e249509170f090003030301c050300d031609408514032070008240411503200030310b44411900a285c1110715100d0210454000018024190f8a01c9074000300090601400180b595415 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 452413129 1250 452411879 452411881
    0x506150301050f01080606160f020906010503091b03100509010b01090e0103260412050a14030a080406110c070f0e07050a0509010809070b0d0e060a0902031e1501140f03190f0f05010203 81
    0x420302c10281403004ac4240c48444c00d03511008010f4885010039611035595822600d814801c0010f00c0c294561001c000504a401028070a15840f040b9141503d403d0a43d0351901995540f039604594000010243e019416440d585144c4a5a081070302141c940c641c200010450340c1007080e1410250b801408800c43d221620980c5864008d648902d110300480c0c070100c1b2a4001e2003203c0300441501d07943c510383d03203d416065469540e000d00500f8469008200082c0600c1016550b090070010500a03101c1401c3e085d1046003840d044103000240181039804100301004203101c641d0b03110095801d038050a00b00350704581c0798480c4613420000c05411840c400c0303901054000d06000c49410200c01000303008150f40b160389403186124113444c4c0d4950040c4d0941d0001c0c41e10420410150301c0f44001110890554102d04018204803144507c282d019424402004c3c100e00010720b0107845000562030110b008042100d40305d00320060007284504080c1840340300c290903209011010020a1006031300c00021592 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 452414379 1250 452413129 452413133
    0x2109061b010c0f05160311011b11211209010b04050c0702040b03010e0604030807020127030e0103061a1b03120403090b0307020709020a03020d0c030506150301050f0108060616 77
    0xc0c207884070008001009a2007903040d040c001c400301c50417200c144816041c900410784040d6840161149030320341d2596160414000311080b12034408565005030755040f5030108003010646011402d02215010b029541d0ba142c0e14080c2c18811258011101a501032840c1c1e07540c0c0e00c0782c0c01010151003854216061208020904020f60b005040140c0700b15400c000e4000d9040a241c221220360803800802d5011101180110380180306440c0d10452510000c03c000145041d02940d60072443d8000107280c00c104540307001c254001d030b41d03003200003030070704c5c003003101c03514098503800c1150343c8408000c0c4a83d40011000c014020303c800e04400c01384560101d07a5142109520f094441004803030641c0081c4207010003042048010044a000340b50a0740105401820103a1100c02940040840820305508004440214103039001d03d400240264800107100e26298040c014448220604005422420001801607544800b0003002a42007864054005d984220104040307110f03089106050341640001401 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 452415629 1250 452414379 452414381
    0x5060109020405011106090a0f140f060103020a1e0302061605070308030603070e090a120306080f060702010c0f21060b030a05061309120804080f040311030606032109061b01 76
    0xc0394001e0b0f0f20260340340e488174603680e1900c80564500b440750708016203850210304c4480b000401140107501d41541410a00795080c40d04016442c400c0c01500484010415460082156002442c0c0c6080c04800c424104445900c2d000032408020301c0307600c0c040b030320318010b180101010944941c44801c448903a900c2e0f00b4031030800d81044407000c0c0720b0b106560022401010252001c0c0c00b8101c0000144009103090341c9a04840f002d050003003040681c3d503540090041410400d152840c001900504850308000d0b20003401d6504038078812050212400c2ca506401d039010908240c8005028010a800d4000300007046c041c0c061603000306408130001c001e000d002000340e4491030050300b04450440c0c60b10417a407020f105031845940c000e0040c881c052001d844c1c4600803603106074486e01c03034100140b80c0140c141308000366030421740040e980074503400f0010900b410200300164010780110000c00001c814619800c08101d00c040c83c1a03650b1802090210241c0c03070b0002070701c0301401203c801c014503107614401c481c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 452416879 1250 452415629 452415637
    0x2011e210b0a090608101e0516021b0d0b04060b030715020f060103020f0f0f041d01110f040611100f090515190902030a060501090501060906050f0a03050604090506010902 75
    0xd110320b00220340001c0c402803a00c1090100c0b0300c1840a0881ca4001002100051160411207080f100340e840d080d8906108900c0749500c5000d1600981e440f031181108002d1900c2074030240603041d000b41c404e001000395100d188100c1096400a19082903a80d40d2400e80050a0f8010485030103104d4500c005c5110100036041c1840d01e42d8981c00c44074809400c802d6903984880078031010350003030418541412071b07003040041d103003e803940507103094102c9004038017040403500c191202d07103051040b1003500030303a100007806100f0360f0b160183c13a003908051821040d80d01601c01c601c07421050103008120825020018841c1d0b10085204003c00c103c045107154400024180c030080440c0c60b03000351000c030008110843c8045000d48180304c40001d60913040c0b4038001c014070510006980c9449000c0c01e03540014802e004043c00b030008800007041e40d5141c8200500804243d40110040c89004d0194210010b10700066845450300d0707250104651f141c4001160017400403a20107401c5d400f03079000204448030075800038 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 452418129 1250 452416879 452416901
    0x905070f020d0504050d02010c021216050a050103020306060a030c020a080c012c0a06150e090a12020a050616050702040926041d070e03030d0615030902011e21 70
    0x148912400c9200b084419104601417a80c0c030184601041015501c10f5850200b601d04c081c2a203441c01d130200c5195803070304100691180b1451210503092000d420700c0b174181001084207090135411410040c00148050080d588018201640d807403e60102c90700c01c004014109800100c550369500810002d14041e0074010014a102d00e10400c400f00020205021040024440800f521080c40315965142c080c003218407a6031616100060b020480d0300d072042d0280d016207d003100800d0039071900c1c640000680c1c05103ca00f015900590b500f880416400f144056104d0500c03103010200d10360f0311000340c1d03090013002000307034010303240c000c1c40380400285140e4045409004513200c41b030904510855035047c411400380401c03ca00000384121809003c13070115410a10394145101c00000020200c0e25540008620078207490b25000e080140034101c1d00c0350708150005150500060702190006000b04148041c02a070007980c1c105040c1d92288190009481200440707280c48240f00301c161100003030b040041e10 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 452419379 1250 452418129 452418133
    0x140604030e012610082a0924013605090601121a0d26040e010524041706060406060e150903030307090612050f061201060905070f02 58
    0xd01c1e209601408107000c0e281c4490001e14000d0280c091052024400078042207469891418082050141400700004450440c420802e0342d440b10f44a110800801e500c140c1d005e1080f400600140c0c81005002d13480129600074080400d4003a400120340b824649254844608003840c2d542c2031500c880306424440e0f10485401021840d00c5000b0403086010a41c1c1081c0403c0d1681d22080c10481f40d608000d1800246001495800078a5404070b90101c0c1580000c072080d480c030803561301c003151045072204001182c0441c4581414104810741c80c1b0a40d040c082c01c0d115118035080a00142e044400c002d00411103210300c40c1d1a10303a02e084030760070303042603040080c00b5005031800643c2a0500e4424001220015540c0c04044410038082c040139003900c030001c09800c88100400703421034804000960042e0074950390411158540b403001040040c00040800c000e034203102c18008a15442041c030b60f0494000c850410ba0300c080c0340841401800c07107901c03640c2020300380307402c100905400460100c034071105902 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 452420629 1250 452419379 452419397
    0x3080604050603060f1501091d040c0b0f0406082205030307020c010c12081317030711150403050a090503240705040e0c131806090e03070c03170714060403 68
    0x100f680300c1104440413417468000a0008502c184030a003e80000c240606020303000a403242c80401c26030301c03c8c0210000900514091000b001800d20281c4002e0880c0c0302e034075017081100c4420720060700c02e91080d0005c0188a50100320703c5030061180320f143e00418140055226001e10b40541c0b0783c0c20459440000d03000c1da03021900700e5405400089400c65004000122800e0005002c7e6a0b400028025002e01c400240a200c0018419002100d24448803803a042d201e20709464000e26004100280807529001212940b1100200c5207129802c41d03458103046443e54a440e108480b004040e51140c0d07414070a03207400075401c11140c001481c030b4190705004070441e82d41d08141990f1500c1240f0940365080d0442000800c0c150000300540042c0c119210b507408840e03901c4058007010901c0201825685582d0701c410002d1007968411000c140c006440690700b40030454503400000c01d614031019042043c441180c00345006a5012034000b194410b030246650705a808c0c40a65861045604030081200d1034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 452421879 1250 452420629 452420641
    0x60503010c0516050a0b24060901050304060b03010e1f0501060302030c0403060207020607080c0d02060105030607091208040515130503011b0302070f0501050c0d0f020901051b0312040308060405 85
    0x3004209803801d403a01c44501e0b12a6181440c80c034040301e0581941d181c001c4148500008010070180b60003400c02c00c0891a44004050f020125612018140c51151038100480034440c0d800c84181c0313a10640015000071140d4080002ca400f4001c1901d02a185004004440c5482030b0701c030b0814441207404031420840c80c1e1702d9070016400ca00c001c1e216820080c0061004000003030081d001070008a00c050f0803a0308040880c0ea0b00f2181d90000110118242c01c403038141d482c611390401009006000881c0185107604106030080d086007002c1c09200c02c1201c81c40c28045c180013802d400c031070003408050103c20000c0d0318031429070010380110b4190000040480f0380000c89203014016054458038030010303a043c1c00c88000090f0001d600a91040740c5104003804504082002071043e54418042c2481c00ca580e800c95800041c103d464101c190340d9001c0c03060100034540e91f80081510005000b518441407500d00c0c80c000e00340355000e0b500d10030589280c11800c020405a2044050340034034020390b400d0010345c80c0e030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 452423129 1250 452421879 452421881
    0xf060105060702060d110d050a0e01090308060132030718060e010509040e0709060518011a0a090e010f23090408091201111b060103080702040507050912010b010306050301 75
    0x284a80c9a00c030340700340a600003510340303500106011140314900041c164400303a00240da54110f08070040040313035100101301c5440700070301030350032240c2c564402000035044594002d004040301411003810010203c04030311100400700d8209402c0c1101a1000b0198100060294042d510494000c000030b040070180000d80f0705008020000c3d035255840c0c01508104600044411341c0181d902540e0117600e40403059a03002043c81403c2c040c044440300490792604000505c12503040c55500c1008104801c0010000e0341d07001c0200c642d82c04528000b81d641d40c019408220b4150707050b80c001104100480000040d1900d10440b40c00032980240e04000e03c1c4030400010180e0300b04030380100e41c0c01c04c1101000078006030340c0400901d2103030001072415005411001c9441c1c2103942d883c1000751005400170320b0600200710403c200f028460090700234405c03581183e0358101c40740589036000b80640e0301d070030100d410705000c0c1065030052000034240d0f0404840a91610380a0010403503c070340800d16100b40400d0a042c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 452424379 1250 452423129 452423131
    0x3141305010e12040303030209010c080c06040303110702090a0203060303070b150f220b061c06030b060603070c06050c071217090304060c15090203070612060803030f13110901080304080f06 83
    0x80b014070358201391844d1001c1c0c0181d408000e8907810070a6082200000940303080143c14154500c00040c0100c3c541841c0140440390141c0e4034002c1c1d400c043c402100148e40d01e03004075921645052026032607482d5440407034030390f02481500400c440e0703883d1f04101d10a02007032281085020200e600c0c40e058070740da1701030020864401c0441c1c0c810a8011024100391031080d044458011005040c0f5480c108a14079a444004130740d010780320702680c40d14010014003140070b00898124000b02d42240c61410000806403078080d00d0701d13000744003c0d228400111016440341c1620a01b9800c01401c60050b425420b00800106d00c0420000000c9552004a41d8402001090741c0a50701d568881018030f44150302c0301071005070b1232150b91003819100d04166006131000d0204000500664850040c400f2100e000002650010380000800341d000744204044006901107482e003010590402c1d00d04402141082014200b0a1003000d41240c1d50300000201050008020720890300c46030113841155481140d01515200 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 452425629 1250 452424379 452424403
    0x20c07050f0f0d21050307120b0d060e0304091a030303130303020c37050c06070501020d020d020301050a14010f03390905030708030405040e1005070302070b0a022803141305010e 78
    0x240344210542078009a004042e4000020841c0f0710705d00203a40c9420568100c01c0300c03300107400205040000c00841d00880000d0120005400440078403440802e5807408002c00075425200c40b8070b080c5042c1402036040740c814030108810381d00304044000c04c4420285203814100c2c034070142c200600f041c0a4003c00030101069105019107040c900100411026410002b81921595400c00c4500b543c3c125900c0240b00400c4404009601c07580740200f001801e42241d80000001041100c403024560f074402841c00c8000e1090a0001d094040c120859001b01141c00e0101c292004d641c0040c0340c00c00003034044402100c1d0b2941c0b01d181c95034481042c1500c6403103d2040881582c02800700b8040c91909410250f503e14882040701c0014102c2c0145005581741520b48001199000500006000e011280194822160541545021050901c0e081034501c403518230901840d2600c0e0180700c2d00d22941155414078442e910095081c100350401921000800f91b04071020342c0707410104081294040741c03100c1404 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 452426879 1250 452425629 452425637
    0xd02030403110913023a02150a0207180b040212041103122a160e07090b0304150e01060608091c0c0b0405070e0901021309020c07050f0f0d21050307 65
    0x141c0e017542031050040d6928803450345404048405071440b0960680c010420b814480c61582c0041d440c0140034143c00c2030001e0580c885000c000030104240c0000300039044840c040b50110000c111412540014400545059409030002030b21090100c40c00710203d010301d01812030b65403c401d007030040603034443c091170b17469215045c2444083e04100780f0008036254200a40001908260003602c140c0c1030440790700b082d0302e03d504100010302110304440440d0742c2c07280103802c004d407101f82041c1c5190b200d4000140014100041c40310b20b0318030051103800c05044007400c0c0c0001e028040c2c68081c06000000126180b44040c4a803a00600c280c01444841d83c00f4120135403508001303190aa01c4e0302d104024010800d441070700c6036040020783c990107220f01034411504400016240e040c2640300249079401c80e4016000940140b114841d280d00115140c1d0840c2c80c1113500b0a058889100444c0c45034010f41c042d01e90209440c1d850509000102d0300c42c60000780404200840c0820410302910b13940800d40f00c00c000a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 452428129 1250 452426879 452426911
    0x50c1806041503180605160806010203040609330c021318021c05100b21191403031f08031e03180a050322180209120d020304031109 58
    0x50295000a000ca0b03028001280c1c84083c2e074540c002694030036201807403900081f101c2e191009034000c0790705da0001c1091010750702c0e2500e8948010400c102d00d0059a4042e10b444003c00743c0c102d50140c961200e450030000c034001e507040343c00300984800c800c030074242c0c05030100c54420800d0030002d02c200307a50407070583c029506e01950b5400784140401860809000c03c4550382242001c00d070304100d604400c100981307011603001d81c108144151801280b00c201980480c01c41e90030359200000c1403000071407080d10b200340c1c529100d50900188990a81c051145507010000602400007a002080132515184c3c11a040b966030b59408850723500c0c070945c22001c584006055820010100000045401064000070090b4524807401304ca400c1281c9103d0854059100165056800354035070064200c207001c2d54040c80c801c42ca4022001e1384501c8420741c0b40170701980003864407402d59407050381001d2030918104072403210f60f51900c0a503681d4041d00003034031a200d54003400d940614040b9082403281061584640305 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 452429379 1250 452428129 452428169
    0xf050a0602151f09060e060f06070c0308030a0b0d21020d0807140d020a0804060b0406050306040609020a08030f04091d0a03030b21060f090a030801140112050c180604 73
    0xe0754070041490080c803022003c002a184604d0141c00090010607106400d982008070400c030110700b10700c903500d00400040c448400070680d200c1c03c00003140d401c005856625a1800d00c0c80300140001000345a008a401d080300e014000126440d070901000c5035001060f030700311160b041c0e0b524405c0000300717000518010001080b4038071440000c803001d003542030564207185502d01644180d030072134010100003420580402007401201d015a020345101030310204055820000403980b1030000900140910b61501014011500c0301c12084005085460a4940b02d6002c0035850034030340e001c1c0c4511034505040c0481405403c0010f1001c2a0030140e10005150030300741690305602800c01000c455a100107182c0303c0d0041c181340b0740340f22010710500c04003601c1145450f0440c03540e030000292102c0301a5200d820501d0000380c010507098191404524859000e814910040b0b030b0341c5650070540300d403407802c007001c0c004114928001707011680b440314851013641250106100b0680501d120780d0030340201090782c01c09e03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 452430629 1250 452429379 452429401
    0x4050f010f140619050702101d01200604150c0206070c030809070504021b161d0a11070303061508090706030c030b030307050601030209100e0f0c0c070f050a060215 72
    0x10802c805007140b1306014022020000d20451400d811001c1900012904110300d4250040c50006000303043c0740d41a100550038072410b180e441106c20307040c041d20a035500807140100600214882141080356031314600381ca03024208480808040072014204400c580c52a400031911034400e61051b601e0800000c4280c030f0071601c00d50f001d014040a401180008241502c407400100380b0007802c44070b04a02070740c007451524617000722038284030141800003500340408001071b030a07908140300748503075011140c480f01001c20003014804200c1c00c1141000504c0c4041640541040b002c840d020400043d81003010b0301c09590000d07040741d501002c2c1e000000d0a004040c000d5110340c0d545107940c50005120145040840d10b10751000b102540c2d00d41c0114010411864003100f1942d1103759030700d5003002c036840e1040c0141e000101030b015012040c0c500d0002000b040c0f0348800d450088a03854116003050b0ba55040c0d0314070b025118003130f5500441d081c0b030020400c8c074000100c4090f103000c2c07242c4502040c0d44841c5101 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 452431879 1250 452430629 452430659
    0x60f0213120818131d070602010239070306090b0606160b0703150f170a0f1205090607060b09090a05100903020c030f16051c11270604050f010f 63
    0x80d61180700c100c0c4c10403182d11503224004000c254648201703811444640100d14005050f880760f4116030040201d070000445c07122184079144143c1c450b0711030340c0c6800080240e4104244005040314403940d02d00005005503900100b118500231040744403162203d500340710040c80f0701c0c1c10500d0a41804100c4000091540b882c166014004d0319001131040c03108100107246000c10350140007081c805107018460007400640a8003000c030350a008050103d420f6a07141c2440d003803c0009001a51780420040c00e07030340240201da1550b0360040c0295980c03403440c605803004141c0010702c0c0d0f000d0085100003988500d00040d1000085070010000c001d0b01c21947c064401501c034a2a08500310300900500c0d416a450810208140308000300c043e0816000c52450392501c28142d501140c4104107207a035600c440d2407461980c80d9090b400c0b1050201d10066072010401c4409009281c81d603410000e040c6000c3c05150080290040703801b101e0501164840500343c911015003070040481a80d043c001c01c00c8505c40401c800e03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 452433129 1250 452431879 452431927
    0x20109170304450608030d15090b1f120903020d030b0a0501050f0d230108010e12030a0213030804080f07090504050c091b040306090b16050f1303060f02131208 70
    0x1064017900d410b04903065402c41c000421205e61a40d10344424440540501b60280c02840010003001900c0e0000039044e4184950002211469915200c90740b0b100c0e00bc5188005000b14062141803290b180003581d50604101890010b441c0034031951541c9084100c0900300c460581da1141080c000410503042907011803031071410540c0d61801e0015201140010300360740071108844916940c03400c000390742951a01021504550098602003948111031300c02d981e000090300d803005880d4081c01000325800303043c070780005d130030b88034040340000c0e1018000421401d00c1100c00e0640369200c2d030700c0204a05490003500c005003a0f4112207038103081802c20101e05036224043c1301801d6090701000007000581c0d032003a081610020707192030100d014040340308100341d0058881c140900c52103400e200024002c2c01030203240140e045e00012490a030f9018107a5810140d90004030403c00c1026801c0180b00035800b40b50740c00c90000840f00d001032856541c00181c9041c1c0d40104629203004040d0103d04c04001c481482c1c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 452434379 1250 452433129 452433131
    0x70915020312130212150c070f1b060f021f050919060218060901021b03240105010305060a0602030304110a03080a080708090c030a0f02010917030445 66
    0x1001a403202c92a5040d4000c841d02d048504800c1c603030f4014040180c0341c030b0400a160364842c0885101d6890040180c6900036905080c258a980252405d803041c00c001c400041c00d000c0342d04209080801030400400704407109074503206c103540780d891030580e240c6400c040c3d000c8501039000802c065135602c54204136031021040c001c4e5404090300d007204d0b000d00c82c0782c11300c02e881c650303030114850344900d803080b404034440401180c146080420b0000003d640728002080610341240b40c81c0119480e0f2010403004400e101c00c0515145200701212298184070401d11810f070001e42004003140050400409440070b0303880d541e01a43c41c0d66201e40300d2050700c2140684441d0000e2803100b001022540840140488144540d01d0602c3d604001c00014000d80001d8074142c1d4507001490042d2583d40c00140426246900000d0707508140420700050300e500481d80e01c101c410f10082c47c40a00401404001041507668402d5450180c002002851102400818000c1c12500007004100c00c40740750160f42441c80000320300 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 452435629 1250 452434379 452434387
    0xf05030414010b130e01060605030c0306040e033606030412080919080d0c0e1e030309030d2111030601180504060b09011704051f060e01060c060c080709150203 70
    0x1103100c000090944e05802603980d2280c080001007802182c004028902c2c03e28111f05001201c100a4030014210340c1c13050b5540c0c111092440010300c1a1a501440350016003000005081c0da003440c00203181c0c01d03c51500c0c8080001d0318514003001928007590300a102412400500c103402e540c1c4400142010b0341c0380c8113710104020b001950008645544105001a2a50080c181079400d8661101e02001071286450020186440c0c0001c1826114000c1c4000d140601c0604007007402d602c1800704443d0035005480d14040f1083d0896040c00d07584000702c0a4000a1801c60781070b0303044800002014030f41031010804208590702c03c840e055041c1000c98020451282c0d00e400180444000e50301028031504041141006907800c822128044d0590035000c0d0064682959410b444800300800380210051a101c030840040090780b100c0c001d40003d2254800c696110003014009040802c8212605810001055002c0d0301c00c0100c1401014103403280c451701c5082c01c4200d111a0000001d400c21480184 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 452436879 1250 452435629 452435651
    0x51b0a02060412061a06090103150f0806090607030b0108060d1e050c1207050d0b0c0705030c0c040b01030b0901052812120203070f0305030c0c030d1401060f0503041401 74
    0x340c0100300920514449400000c114a00b0805483c8110b802d0540d4400c43e00c01c1c102582c40700c50487d22680070929002482a000a556607210461a007200e0142c01d410040440e940c5130000390640a0700b0010111641c664072750b8401c070241c0703121800c0b050000d0a00c201150030f50034100c2842c46540d00c9080c00e000702041801100b194045052800e441a60010142c06080d082218100c00f42e9408100030b0252036007090003242110001c103030000e05000c402c2001440203d0840d0607a41034542c454103a965030b50f00c2c0c540a5584480ca40c6c6080d209504d0f20200c41171541c06441340481c4118051b160000aa04e00710401c81d8249103c410340c0207240746141c0e1440b00040b43c41d12000900030044901e50000f00c9401c00080c0c140c400340d410005e55100b0000c0d103005c110074050301ca0741c1d280d15150040e0f80e0781d60480008058000c1e0000950940f0000c20003616040d110f030851040101101070b40c96040c1c0ea0307071000300c07620000c000b80c040c041181040481c1c0454112401c00000300d01c1a800820110060 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 452438129 1250 452436879 452436889
    0x15031a07030e01090317100509010308031302060406120f1a04090302010e0327010f12050c0d09050c150310140a1703031602011e0b040917042103051b0a02 68
    0x214228002440c800b141c002d500c240101c182d41148079071f161410140d040c10041010100180005030621001000080c0000b40060f400001a82d0103400c090721141e9618026010b40500700000c16094200030700903408090501c0303618003507a000c0c01c003030351200e042d10107000c010700200d001502103541380c00034002c110304200002c044a03000b05821000e421b04031200c08042c92040807036541001407050b0800c00301a8008205020440081c00c0000d45c0d84540700c00b08080c3c4605c0c50012512400c041d0340006118000c00d051009940a9840700e141d08016031a445803840100d907a100c1c0740864035800d11180000002440c5c4489002d050600c45903120b02900385015002141121254000010440107005602c00008684010f000078412808001c03420351210508540301e04c0001d03036603200c4403030319682d940100380c2c3c3e02e4001401300101c0384418407a5403280e0207405003611001c00101c1e070501d03185500120a240c107400d69070307283c00d00ca2020101d5100d10309196000c00b56206070381c1d048000d6502c1d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 452439379 1250 452438129 452438141
    0x60306041221020c0d03060506090a0510210204090e1218131401061d030c010503070507060606030c02120c0a1b0e01181a01020d030c14190315031a07030e01 69
    0x139050060a030b4403194400102501c801d6004580a0b50342031003410074a85400000c0c10070744c1c42c01c441e401465502c09000701c890b80319040340108030030a4569001c006410b154010001d035500d0150038040071603840b00d950b980c2c0a18281c0520a4071040140c0d281d201d00690195802d4031008140c40343c2c468258075030344241c45001c600074081300000001000415000800001d5407260b41c90340b10415040070340017944030300c40801e1840c1403002c004000307030748223115500304e5419a1f032060040100781d071140802002000072800d060003510400b40e044d4960b400c0c0b842500e00c1c1c40e2143c0001e042c0400c09690b040f030041802c1c9900501c045040001244021400d01c4141c080c0c20342100311190900790b81d0591080d030b0f0300e001550007002c101c0340100b1103d0742d01090805401c1c0c06d600380480c410848072001c581800340da0f00f818007280804140340410042c86044420740c03040a82d0306001180e040955032100010501c40106490810720000109404540c4000e61050042c2070019944d501c0c01c0c0c1d040e0039182 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 452440629 1250 452439379 452439397
    0xc100603050105090d11030405060a14131a0f03061201020702060d200903031206030c0d080c0f1603061e09111305060315040c1703040e06030604122102 67
    0x1443d00d080000c840c0b020411002c08080928002202c0d0001e0300340d1588a01c581d002c0c0c28000d80c0001101d14400b8003030501603603521503070307130440d070740d0700060b040c0c000d0341c0900c1c0e01403010b4418000340700365031805003102610617216203041041c3c074540352941001010304a1540403c4595002d000010150351008003130111420015400b20340484e183e070b441032a80500544038525504240f00070f0086490002c1030324131490000044800f00d0700c510f000207241c294407804d01503102401d50004401c00c050300c400b03882d0808154049a180900700d0f240140c42e00c14007210000081d40840c002c0010801e2600004103003c401e900c0e10b00a0b00c20044004144e91028005440c00c0760704a0403101309040c00e5018200c10144814100b040d41400c80029494840c18840007a40e0a02d440200d02072114204501340106440c841c0c074202e501e50111080d803240c206100e2228003000e140006800c42c1808070f5964031423684401c0c5070100c020440303c15100e00002e1070b03040d0080c40008044104085c82440142a508 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 452441879 1250 452440629 452440631
    0x4050912040609080f0102180103020a09050301052a0408060402150c1501170a030504090b040e030c0d08070906020a030c05030c010519113a0207060203040201030501080307170c1006030501 83
    0x5804d00840c58908003242800b204039038410000762400c0300e605051110f0f002c9091802581d5903420020844516000341c0003036902d54a0f0006101004001d440d020846070104eaa240300d003040c81e031014141c1d40c0900e02c900101c40d004031000500600e015042094204c0485174024200b0407020003280c0b8200c800841018125100b00050203405148103d401d9600d11030781c0140b62503d000c0d07800814a000340e00c1a400b260381c8400c0654055034403a0080714510340c0b0390003280c0e00c0340c108030b008580c1c1c1c414542032900482da0700004600c13283c1c440c607080425900d964006200b14042550b085800e05800f90068600d40402c3c000300e52100307020f0050f54040c5010b004180141d0f61041d0201e012144442031402138002c0c10003044402d01c0991451300d112084100143c2100032910010640d01004040070544546c0700051400030005194003442c0128001e1740c0800c00c4e681c8400507590350384556803010707005201c2c504100c1250f08000700100f00c070145203029101c420038000600c806807a06600100e81603 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 452443129 1250 452441879 452441897
    0x1b0c0d020c211f020702190f0e04050606010f030204031406090d0f021e0a0f030315061d1e060408070305060a0618020d020708030112030905030c01020705040509120406 74
    0x5241c001d500480091a040000201e01560b240c21607036450400300c03c1c28403d002c45001c042418140d07040e180e84c0ca8000d009104503018a082e403110703c100b01d000c1c2221590604030003207013020300341959900c2194444028800c030740707494005640c41e410040c1c5039020182c080001000107440d055184180184e850014521810281c0119082811003040c01c0104400000407207940755001800c901410150800342c2088a60364145034100609000c01604240d11001d060040640c9580005802c900107103400e190981c80700d00484150030003803802c2c2000300301030440f8400c07460300341d800e04002c82003203201c88031741140c100109100e500076521058a03900415000c0040c00000c0c070002d54483d20a51007040024144207445001002e01c049208681d640440c91900d0300a05504843d5000d40080b400c1c0d8aa40c0c0d958481074000220010072400650303400d40019003810b000030134000d49481600540400303400c10007803000401d00180034046510500d902c058110340400c1c001c0015003071b036a031803080c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 452444379 1250 452443129 452443153
    0x13020411030403021b0f13090b0c030108100603020609011116090e011a01081602030d0f1b17010b180409080a1b021318060c0e040b010e091b0c0d02 65
    0xc00074002a0202014268031100386166582c2510b84845082141c24034800c035011000d080081230b45440081a01007004280b150002c0d03101c010350f04848007003048403845600054070740b007610003500c070003500500c0c240b280300c0056009003a505030391150141100c018941d549500b00f41840c05a00c80103810b07a030395404a02c3d00c1c500b0b00070406502d40d91301e00700d2901015100000c01001e0300074161021803010b02d074061307469482481107c00420038002e0510a10b681e80407548010080801c1e85450322070118807080704140990100911090160b54040047c1e20b443d43d00681c0e6840005402c0350500300191140555455205101400d805802c20316211a510400604683ea03007007088400d194980040f0001607441084200904182c50004030780c07142c403410669611404044000c2000d410241e481104503030140c0a840004000c0310184940e611f00001952a440450b074180d400c51414400a102c085008803610081c20600c0d040130700c0e0440b44078031281450003040340040180c00044001c41 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 452445629 1250 452444379 452444383
    0x7111305010501090b190e03100c08011d131211011e0b0109080a030e0411030a090b15062d040801020a02010605060c100903020f0a080c10090b010605031302041103040302 75
    0x4040c0c1460703170140b480c200c0d00709400c003a0464142507440c00c01141e03c0b00d074481d070388060014560380c070584001400048034090000d01034032024000d4400c0e8010725004002033340c240c00d03a40c60042c0941005a980d6914035140e84031030004c495442009e01520481d040d03d0200244074000c0c00310711401c00b8884200600251405640180b0340c110304100750b07070030140031500020880c411300d16803504000d141c07098840c01080140503403102268994070080208008504507401c500c0b403503803091103504400c1e0f82c0c05c59000000f41d0400802c0d41c0046081c02504501e06007a041e501c130100c05030700e492000160507c07450b00d055200760002881e5940115000c04c105809000c0c0f2006440300315030090401074003690b41a82d9040c40c107500d0482944408a02c400d15009001c5400319200b003100f6207084840c6810903000d40e500032b008001c880e104039011101029850711404c0e20455020026072026440c00800710f41d180c101811007011411402030403001680c80c1d02c52a204e010791540c440b6120314260134064 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 452446879 1250 452445629 452445647
    0xf37060201060303080f090a0c030b0709050901120308040602090d241107111305093034060603030e01080108070501031d060403090305070603060806010b07111305010501 75
    0x1000c0d603062040910010340c100001039405503141715110b046a4651480c0f92420800010182c01c59506440110600c0100c4041c1d0344900c0068903510b4005640b0703410300031200303024468580e00311140410500000e2181100942050280e980941040f0048001850307803a04a10b04072048950f5a5801000400800e001e1441d040c40210070840c07144101075061051182c1032006000c02c0707803505810815035404010381da0300214000100520f2900c41400c1d0740d80d0a40600003d0040600e035000f003880840e0030201600781c04a41900c90808040581020b860a0108034880e50025164121004110103a040300401801140b010600c5032960801030103084210080705d041001318001440000b000060303190459030700f0f180006041610040e0b0040d04000c024078016507000f46020310041c0340d400304503441540d02500135101800d5940700c0070350480b071103807042c0e00190300712200400c101d02c2200c02403e1118003803101d0001c030301360400000b4404c40d1040d10350601c6940d240b0043c0035a5074410300c00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 452448129 1250 452446879 452446889
    0x7020f032418060c0c030d060e060a050402070f111c06051909050c010e03031c0207021c0308041211060a14150603010b07110a06020d0314060904020f37 67
    0x4104502c2140c840700e0b202c24005080301c1a1480010740807603102030410440b600c400c4183c904010060b240e1203030305020081903030098402c903140030010a0742c6c40c0c14401c4030a821f07409100380303c92101c00d070b0320385000649080c0c044d548411100d0355242e48010409404d24070600c5008001030b903180684c1d660306442c040c006c03400703446490f00039510001440011b805041e0300090822000c080c1041000034a98881d40b941c1140840c649030f91030710040f28607009080307441e09c202c540310030f5260b00168031054220034101c06030010b45124040780104141c2210041e00c0c591914202c40c01c021454002031501e85d040d2044222243c0c2c030300080212924400c012a00a0f1102805000c00109038000907654003060160701d200d0040020004104a001e00c15040140c40c054110781c0201e580d044040d445419800310440400d0401d06d8480e0084603103e002032141c0e600401940180d00d40d9001c0c8119488104d032a2a0811030451081c488443c80101d1200040102842d808104072000e40c018800c0718981d1003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 452449379 1250 452448129 452448151
    0x40303020d0305220f060e03071a07020a02090c0c0102070b151f09060e03031603021630021302040906061106070801151b12081803030105010507020f0324 68
    0x14408946041c0006814080c0c1c00c00d000c09184182410610011f008100c0500c5131413000041d404100300140020424500095443c0b0001e0758070300e201079880f0a4203080c000d602024441c0050030b030402180c040c007a8144250001404d000781c654510310400310948080401c0303d41c00c0c0384800c403403410060864260319410000d641c0101e030360002a241c0f00c00d40c0220350074001c02c0d00451905407020011386c0e00c0c0041c405040c042c55004d5040107500d40c1c40c0d0b240400070480c2c1e1070001081854105100c0c00600109800d601041040500305203401c070b00f2014100d0b4000d802c0a0021440d040c40c0c0040c201400c50140002a654030344070000d8050401c0003425515a0054400c20070b16942040c49541103e05950400104000c03008046071960060f07c0c400c054038840004943c1072022041400112400740d4589a42c141c8908128041201032422001c0c4154070400040c001940b1940c087e18040c3e1024040e2103002c0141e40000b810704100b8411085c0c8081c944480e05049074a0146d0560080e2080803 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 452450629 1250 452449379 452449411
    0xc0c01030603030e131b0c050f010c090902031e040b1e1e130501020409020d230a021c020415180f03020d0213021305150c0a06050405030f040303020d0305 68
    0x243c050302094203140868480e580300f2964403140e44e0550010004024041c8070f20070901c08a50028010000081007542c862080f802052038820052041300c4600096031039030aa01d52400a110f0065400205034001e99842c900714101806035640103140100d03c600c10381e4149141c00b0403290018451300d405040c0c1920711500b884481c50f4404144951158070100080e0aaa1040411206856102e0004265601c00100040c500c060f641c080c002004400300244456000f00319180c0e0100d0325100c4616200d0034400108030104070550042c5044101020034607001e4011800303200c101e070007030790080000c0b501c0b400511035007652144100020194040b01301424505118100788200078a000c001d00a00c00c104490042d5500c2182240b070400c020a001d41da6a02107407a486100c00d580c3c03040c0d6008001c1211049581e901801c00e0390b90040490b0000d10105107280c941320090100a0000d4400e804200310030045120064024006507000f90003c1204000495006089030710003050341040f00c81c400703 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 452451879 1250 452450629 452450633
    0x1a060708160305070b0903070b060d082b0c031e15171002030a2301080c010302030a14040309230a030201080403030b09010f06110c0603061c0c0306020c0c01030603 72
    0xc41954855900a49030720310007121460160707124814402c001d055114148104401c03c040080104995803041c001012252590703c20720201032201140105002002cac0124030039802d59101e400c0340040d0b404c12304014440006c1c9900e0445148030a03050009454a182510160b00484c0c0b0b85c090b03010040c004c010301c80f1004001b10b200d40f02400b030302c081801c45d61510443c200c0c0412201d8505140f20104560b20300300450350400400a01049200580300c80c2c44030600c418030100c04038121030b000c81c040e040c0c0300710120044000703600c01840103154650720034581944190b19180244510321985811021a0500d00340440340b00100200240c0400711005a06450700e480c43c120b030407694207007000c400b25200e510b0154050420041c05641003a0181b00018a00c0c40082444007180d585803200d00741e628940390001d0b01d401c041840f40e41c00410800c081850341c20b14004030a45071b101d20f00e0050350405596100bc44181d010343c070640d0035540104414850600038482054003450900742001018559 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 452453129 1250 452451879 452451893
    0x2120c030a0809160b07050c061c0506040c1209030207120506061e03070302012d080a0c021c14040801050c030402120c150d0e010204080114060a0326040503101a0607 73
    0x90142c60717004640410501c003006810001c3c0403407500010441c035290200c4450201100641000c6409140c1c1490082012410284204000140d0b940c0d01c0d0104400c001a03c14007a00142e0011021845006000500d802c2040d0742505242c1c403c2c00076120a0601134100078140c41e5600341c91400130010758072007159940016101c811030343c0c28200000d0180454402488410702c00041c4200c00381e00d540d040441d50740c004011485000406020820241e84c0c410480e40c58418810190a0040707035803500e56010302440c41d140c401d0001182075440c10351a49192800c1d121f00303071042d2407450800b0051000f180381c40451510390403034210040810008090000d80c00e46491403d030280c0c0100040e2101e0600099040a4070080344600295500c40e03a550700d55009007a032102c800140d206a0000c9852403422040000440390003c01d1461503590049040d01c1965405074280280d440800000032103440601501c940741c0203040c00011109105400c0b09071000d243c40b06a0f101e03580030040b00001600d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 452454379 1250 452453129 452453173
    0x504110c1b0d150e0d090302030304140409020a060309033e0309030a0503031f120b1302310501050607170c011401030c0b030103080702040c02120c030a0809 69
    0xa034881c4810044507036010a068002181c03000c1e20b400000002d9003001d10994001c981c079442514220380a01c8004141110210306501000754141c004000c10130907101c10344031001e074400d40180001100b801903400a142800d03c0d6100070302180c1c641111105050308070f00a42070040c4c1800b03e00740d100c282d00c00c8000d80c15900c0c3c0d0600041035144001100344080070001c0d5039040d080581100d25040076400e2031a030b84d800c00c48460f180c1080c0080d145404a00b003080e08410ec0c0d90010760782400554035035401e440910014850340d40450005c80c620090fa0f03414590b11040c40c541c00f4100425004598500d000c4400314484194050030310380100001c0c3c45900c00c0719041a04101d150b107010150714000001c0d8807888000813015802c140b8607940000c80d00e120b0f98103c2c2e1240d5444444165100c03d1401a40024400540920018055030025050035000707042202c115106035030800e0b40210604c02c1c03035048421404000c5d84003040d280c01c002e0f0450001904000700340018000d1800c1e29508502c0801 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 452455629 1250 452454379 452454403
    0x1317090f0111120a0512340c0203070e0a050907030506070c1b1e0801150501050903010f0e0d1716030c02030f040303031512032003220504110c 63
    0x1428002c541e03484009011103d012100c0d9002e0a54503410108001e000340c20203c100548400c800000ca140d521844501009402000610228a0030704502004152804070414824801201500c2005980910902018202440141005060100e00c0104548006040e9026684407960078008568001486a401419482c002c022598140b6102141e800700900000c0c0c008403604010412111420700c8a002d620702104c407061090b40d910183d42a1520000d441900b00e40c40381e010f2005510480013042100d20182c0040743e080e00035441d01003155400f21440400d60030400450001c02da005031020500081c1d850b240c60b0740d00b803514030741c0520060170f40c18100b415a5440c50103050f134000e006403074a11a140954589890b600d00b0042c010b03100e0071901410408428402080c1c64882003001200550182d0300c42c00001c518000d140403081d2032121b0f106152100f845032aa00841c03041e084120380146580219606141200340402d40b001820384000317600080c0481892041c00048030030000c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 452456879 1250 452455629 452455637
    0x10f03111909060e01050d050a14031b0a031103040324020f0c010b010e1002060a0f0b0d0b010503010507030c2f010f0e0c0604080318041b020114160c0f060f051317090f01 75
    0x9040158822f107107120302ca1409043c01424180700380c1c03052000c510104281c0c081e80b6506007a5080c01c07e0703a5100e105038000105000c1c4e6407880c142c00300e0110103240340e081d0900140107241c40c082c0804104980c00422400f40c443c0e445140c2004c465921203507200b00b500041d28655231924040314082c3d1948401005404e50943d031b4001450b01e124560441c0791070b1400500321041801141c1420500013600340503050080d07081c1400300b035483e4464443c00209012a80d03e42e07400409105140c0425007980d26a1820680d00c1201100008004e01c01c0c030319020007501000441c588000101c0341005800064107114107000d1004101c04040403084501c0c01c9190704803154030646090005004104040e008034110b42880d4001c04581d805600080800c0030208101c000c80e50b07010741c81d4004403444007000d00003c10081a00d800549903218122029100d00c00205d10451030258240454808503542c44110522040441c01c1c450b000c1031032030b01381c80700d216070f94030f44250080071940810350164943c4c100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 452458129 1250 452456879 452456903
    0x1c0f03020f040e040311060702061e100305100906140c031f0306020a050306030c040b03030901050f0409150303090e01060503040b06031911010e0603010f03111909060e01050d050a 79
    0x3484101c01118041d02e02c0c8602d515080c01d160800422408032006412280c0c843c0d00b02140e482c500020303d013480742d10780742072480c0300c41c01003204020221809010700800f03403075042000c00021801c2c090f89030061402000010004a1401c01106523107540b180c14410031002c0041c420401561011682d100041c108a0111172807140e0060005906d03951014010a1020401110340f9a1084c01503015003011803c4684075007101081008803035031141c0f4030354164000c0050740c1195010364040d010131540d07458050708050f92020000113030390f88040340d01d81c0300c640c0c54401e10806400c00c0b048000780c0b10140c07809640d0360404501030110301c030240001e0450051180000c0442e17401300911060b1411015115004401c1841d060120540086070030f4041342540c0c1c1c00744c000703040c00c4080da4100d84122400d0840d9510f9910340130618841d1103c1240c00c02140760a86071410030f03045001008080d0250001134640c584203494101c0f00c4180c000510441880d100c000201d40000f8810070000e40080c801450 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 452459379 1250 452458129 452458147
    0x9060601030b031608070303080901020909010e0901090f0c0f0e0c0304020618100306030506062d040b0603040309080606040e0a030e03012004030c15020304060806010507061a031c0f0302 82
    0x13038081c44500c0404410801200401c003c4404140c420459200e501c46901c15240c1200e0300d8282d010304810036400080c14001004107040805180b500042c42200000e01c5442d251190f40d00341800d07400c2039a040014820411030302e60345803070f0107000300b685a5420759607051860360425a4400039002034410000451441c500c0c500b40b200c00d000319880108501c2070703503240c4480580500b0b80d1748401e07201e034044c00c40050098140700282003421012002d5000350140c0200119100303601440c120703a04542e60b000210929120403005501a9019403120200f991078822043d01d040001803102e40105d06002401c0780c0d100c00003481c0ca1101c0d5050901300a40c24890000c2801081c02441c00109850200694281025190010400c1c3d9001d0550003000544480707074035602014050400005a004200030800940310b040d00c90f030065014035202d490010380b500c8805c10b0b18003042c42c1456480841403141101e1070708000c040210341d10040400300300c03a40e03824081c046050811882303052580029070707000d07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 452460629 1250 452459379 452459383
    0x1060c03031d160b031e0a02040504020307020f060114090403031d011802090a0b01170c090904030807021b0907031a03070f1e0f0302010509130603060e120309060601030b03 76
    0x7046050580507900750312401c045666070030343c544100801d040100c1d0100b02c3c4c4015000300c03886030f55000400400d0041d8655408460342c00200101d0003039909000103d0b00395900e000131801451035a004150404000c40c580e407c00d20103a05c102e1080003006001c114036107689140313540c003e40604001502240031602c1415852411501e114254a00064407800f200c0c50386114a500d4000c0d42c0398481d96481c0b941190031100418203ca02044080d119465002901c00c1b10680c04ac9103000c00b94104400100403d1000b0000d4800728041402d0008011030a94108003c05041c000c0c08102c50361103500e100402c0c2852405032500d001c01d40c49550003220040c003111820031601015084a210554400009044608900489000040d0368211011311180301d0002425100400c1201c3c0b06949540d005540c00d0740400300e45504011441002c1c00f240803244103d00043d0300812020400c048034161580c1001c07141e1006101b140000d2050284000300081c496500402c2800e00052000f03080c0d00080c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 452461879 1250 452460629 452460641
    0x50702030a0503041a0c120901020f060703291e03010e070e150111030d051909060b010207060c0308060d03020a020901030c1a0a05190e0301090f0b1e01060c0303 71
    0x2a4140c41041585410010000010300031610204030b0f2401000b6802054115481b40c2650030b05140c0c4242c05001c10020b40100410a081d8140121018580916102400c1040447d00306001c80d0365081c982140341e1203c803100f0112090100c954045107000c200003004801182400c81a00d82d002c0311003600e40d142580001c81c6103400c001190f1310300b503031a402040b13521000c54001c0c403200840001c040865000302041c510a2030807602035070a0400c8944540c0042100400283c46c2000b4001840c5e110000342c880e040603a8000c55000c2000034448002910301030103940020100a820b442d00008264050a2075400a0088880ca207001d605410124a00860b620000c0d50014400c4000400c010301c3c00c403640100c403802c41c0441c60b21904803602c0c7c1418000c40c2c1d0640301140081080d1805581c924441c5520010076040c035100f00600034000ca407c641031000304440100141024106204034000640e6000707428020b03990550a580030414413001c010b2044005000c00c4030a003c04150107a0414 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 452463129 1250 452461879 452461883
    0x901021e010b0a080105042306070302180915030105010e01140409050309040e060a0b06040e0106051c0c0207051302040b04030222090b0412020d0e1003150b071b14040b010507 77
    0xd08004c2d11a40440d00821099504a0703201001c1840d001284911400c8864460705c0c05020301b0859072440320580107544421786110700650f0100d51035003150365201300340e03001b82c0902e12148221034070b041c01d040c03c440c41038005024070403090004008184080140e10300110003a58007255241c1207140280c82c5008407003040340d000381001d411325158038000400b0303485101d480c0d03410f1144c810030b00103100301446240107000f60a8082e00062105901841c0141301644200c040002c0700030142e208442201d5203441d0000058015800c20415490300f404006000c48449008500c0c0c039241a0544c2414860780c1304c020702440102a25032804010000c0c41c0215610134901809051620b1a08059000c4100d40880d6101340c0c00c000300c000544002045208100245c6075182042000010850300c4410301000f881015115400c444028030205000401000c50081035611040070f441c003000c0d400e10349024812920b00011b0f0401000e802d070010400f044506550000e514481d080040b90b2900c901180 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 452464379 1250 452463129 452463139
    0x220212061f090b0907030b010c0b09072d1505070b090307031115010303031e06082d0a06020304021f020a0212030702030c0906040207120806150901021e010b 69
    0x80180d9050800c60310310300d14619400d80905a51607150b51412110851100b940100c00c200014605c0d5000f0b501100720b01405060440c00b22500340e51350424031500f142c038401d0681000380c0802040c3d000f501c00c0d070719240d040c1100e0361010341c0c8030840642000350361240740105903c0f16000c013440c0d0302039400c81d460250003d40e0140d6515280c0c01040d5280e012190440004009a000000d0a4000f10300b00010309039043c1207404076440c6480840c09000480090004016920781e41000f00c0010b10903200102031b40c40151100141000701c00e40740d10720307039540d001c9813116440d89011406c070081040702209520850058890f1a140080382180803041541444500c001801300061500096103041180c82203030205030b6146600c100d15124007a103480290150b101803a4071409207044911250310a901030001130800c11240c441d1021b03c821140d1802c0480d50340c03410f22400341050401d101003444001c240038030b001080c0e00000e540d014807004c0061140c0c00620b00c180c01207800c2d0842800120002c0c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 452465629 1250 452464379 452464381
    0x1181514040602070c09060605091212070515060d05210912010e060a1a010c0f0b01120314030f1302221e09050c10030209030601060507060507020622021206 69
    0x40d00b0002548501c1c3c1c26114a501244001810049030003440b0540352595070f001e0030100c640b000e0081c030300d950310021890350040482d038095104171480030300300081c020001001c460781d040240d4080032101600c0580660105403196000c5000082c0e00d0300c10004250400c040042d1580d1511014040c1c110f445a0141001501608584054000c038041c98034240c1500c0c550b4a0ba142079004803030f8001a40b1800104141c0d403603405600502c4102c0340c0b54042d1041c240c841e0b650f50b880194100b0300340c0042103580c0b6040c5980341071583c04016407800001c0f42910780d280d8142000078901ca141d00400c1d640364283c00a4076030085480f01e004d1404009440404080c44075154038680020300440140b040600111030095603031241c49004880c540c80d0460081c0450300f410600b4808624244c601003420315808100f03618490701c0400c0b45038001c0109035589629000186000c2c5e0680794003511072000c40d480070090001c10a51f10b9600c01480c03000300c44100c2482d5a84c40071a240d44201c2082c051180034000c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 452466879 1250 452465629 452465633
    0x50c0a0603050103060510060f0315091508060f0f01032a03150f0207020618190608010e0906160f09030c0801090302010e060405071a0d0903020a020a080118151404 72
    0xd0802ca06aa104d500203000c10760310f904420700d02810368070070340c00050f1920068440301070080c0d1054441003650002e201346c01e0b460303002d941e0070799412480740001908002c000b00803500e000d100d03032034000600100d00700640c1030080101c030b60210b040c080600703018068815174011061075a0300c0c03000e0720100c0062070159981c03414954592030200700d41c58126410100b190848000510845170502c1e4010709550070010b00e60240700046054201c040d4000c0c0c2980c12000c000b0303003800000d00003404141d64124013903040c1101d101c00c2010242c29980e19a110100744a94903018a104809140c0c01303103001d8001504141c812654022203502c003400a1b480c040c0f020908010641100813210b000c0e400034000d450100301c403150b9568003103038090041d4128180a10120418a45901c50503036144d4034075051200c83d03400e51040310b18100c821409a0312440c40601181071414003c001050014004c1004c00020a545c070040525401300070314251224080030b84039281ca40c004904455280411003581c82c0c14 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 452468129 1250 452466879 452466881
    0x60f06232217070614090f180403120614040f1b2a050615180703021806030c0702010c050307060905100608010b01200109020316170f0303070c050c0a0603 68
    0x28000c20303140b22180703a80a8400c10001425034101c2d40c0c1580d40ca076000d0140b180c0c0d009540c2003c0101036000c40e40303103c0c004050380c4035950414441c2c02d444001100e0304082c070307010740119a480010361b42c032401c001081050a140040401c410b62040e1004141441d1a010a200034215480c0d100d1031040342034480c07841c8980c01020030f034440004440d0580900c0c07128864030303170b0600c04100c01416640181c0000306080034007000206984805000314581600302c403408010103904884400000b540400d6004481c40c0c0741124034008101034907641e19601b00022014080d1140c02c8000c0d041c0040e03255000d040201c20011582c1e159080b4508002481c0ba40c5041038444180b10803540b10340e404d103a8040f03050a01886042440d0324141c403005081039800210310a00030f91317000440c8095580b03000000150300c040c00001883e83d000f51444c1c0c0450308148900c000b03404620480a0f4950284e940030789070401c00000c60b0b400c0042801c006000c556030f0714149140c01c405820807504907a198100207505605 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 452469379 1250 452468129 452468197
    0x20a0306180204050112020607140313030b07080a060311150d050705190e1c081e0318010b06070f0c15020a020a060e09041205040b03100603060f0623 66
    0x82120f050115980c1c0d116402d040c080d0154020b540b014003007281fa40081c81c0c40c0d0030b05030070b404a02c041d68207040b807010060086141d2a8011f03182d542d8284100729540d98810403255000c0600c0c101008080d00b561200c2c41c0f5807002850150085030194040103028050900761105840c2d003803012710a5241c2110002e210f500040d0b04004442070540794600d207140641d07115160031102130240e20070801d5041003048e10031a00c0406841c03104040020001049240342081c0c890156003070815902e00b000208484447c04141c2c05403480d92401002606998614003103890840e041201c0c0420b1009a090030f80001c9503550083da0340c01443e6410001311900800c0c05180140200c0341c43c001540e5600d0161412540114460751001c1000009000150001244c01039a0403d203090303410103032107030900300c0241d10660301910290440d040800c0f0443c0d01d40a000701403c612488206424680200500300580d40150416a22054400c10991207001025141c8140720701000d02c05400490b0213030182905 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 452470629 1250 452469379 452469383
    0xf09060e0c03040803060603040f050102130509010603020f0d0c110a0f030e1002100903030f090506042108070e030a080d1b0f0e040203060307030f050607120501060f0309020a030618 80
    0x212500064403103401c4406403071055130410a030528542d00d060402407039130f0008008880507030034120544c0100d802440034083d8401900c1c5401e81d07207420a000c0050110050b404a001c25004000748500307070b0040d805841801e0f542010100b1125042d0500740e40d084925030386045503104400014042c840441400d11a0078001c0e2905640ca0050342c0910031300c50100304440700540d00842a07a44c0e541500c0e808211094001e24000039080f114441c01c00075103c503c01d090300c440d40003a0a000501036161984030300c50032942140c0103149400345e005084080024070300814415031490034030b0541c4060084202c00d5a001c220310f80d0318942c142e4140018038006801e400c510180200710b4201c1e034080d40034100080c580703407135a20500003a07404020280d0f00041c20b180e01406598400000038038103600348112644250045c25042c81c0c03405008000700f1b520b06030700c10f5060502e001003206540003407218042540518000c100e810081c004103a030241642d00c028800c919040000c100002d6070012006a14 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 452471879 1250 452470629 452470649
    0x3020c06090a1a0424090b090906010518190515070b040201081803040f060318020109050d0503070c0608191103010e04111f0f170a0902120f0313050909060705090a0f0906 75
    0xba4036014001f450780114032509411210b002c01040a540c0501c0180041e031401214085000034400c01241100c1650000c0b0410007c05810034000d0385401c04054005030640758176107041c8555074940c0498820060b00c003905002e411000300c1c80e109000c140020072091908216981c548e5910105807030030815100318400607207000407400078501340e41001c07500c85805075207040f01c00b402d00d8204103c006403000221200e00c001c11540d0005149250800000d00302030b03c54050620700114041040d01d40c00b00d01003801071811a203050071075500030940341581c4600200030b6080c1da03927144c00d8030b244940c42d08241e07002c515009c8440d00f4051a1a400748804a16aa4104001444502551040b149812100c51140800c0024401c40703010303480703c079541d400186a180200c00008600d800c2806421a4140350f400004602ea2100c0144480d20010042950141c000d03240c01d0318000e895010103070450741044000035890406603509480d07900500300c518400b542e50b40c1d07206000c0c8014071070f038807a146043c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 452473129 1250 452471879 452471897
    0x120c3009010e0606060c0307020d0c03060e0d0c03180e0405060402130e070b0c0c1302030108071203022505210708011107080706110d020703020c06090a1a0424 70
    0x9501030040380341400c4020014215521071008204550300503440034501b500c018082d001c096030b103a03400d0701a414042c582c1e001120341141000d00594203284081e0220340d0055400060b000c0d80302c00382c841e072241c01d490840d20542044144100041855000348442d00d900824001400341c0490300e240510b10880e00104401100c44c134400580c0c9000085452681100c40304100b1442004000c108201000b130541e04020071140026070a01d0380c201104107079a601000500030b40074100140c1000e043d04480300074007120907513002940c4104400003440048400c8001d00d602c1424a1000809085e000b0910f00e05840688180001c24401c48a000c0040c41080c400041151040c40344042c2d41c0b40c2d010348a0701d030401d2911914180e5004810407224250340d541c5101010404d0400303401e240455403805079403100d55007402032038003a007800742e14454403041003180780554850a2007021a10212013a081900200c0d00100a43c025580300aa60142c8004c8460a640998101c00041207290b00e0390040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 452474379 1250 452473129 452473141
    0x804060f1704140c120714030102220303030b0105030c0f07020409170a170c0f070305090901060507060c0f09092c012307210e070e091002030c120c30 66
    0x1170034082c0c05100a5070400c41d0300344910645000e1010300590081e00151610280114100c00ca041c0f500f652a000c00a59005104042d891302074a41881000d107440c50640c10901d03d030404601c58145280c04286001403440115200d035082940031365002030150140318040c2c02440c1c0a13911038160310703000079040000c10303a600414482c610b00604000c50020700780f106102c202a0700307501810060b01446024440742c107040c0c1e91411380d540a01402e039205d0762281c2c00d928101b000d50f110042c190702130000b005203861903981c2c00054001110040d80300800c0072015220a0f54020300c1c490b40b504115800c0300c4081444c44c10540241950400005c038504900181414101c4c0c0d45406440e00800621070100000e4101c100460360b00d529121840002982c41e03a80152515028041d070003080c00501c1d2008210025005202008050320301540a5240d440d145006502c01c1c4102c60000600c43c1050001c52600b070400d40a1343c842d1640c000b180b6440c3e89001c842d040c00d9403866040560128803440000790 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 452475629 1250 452474379 452474389
    0x1201090816140105091f0c0e15120c0301031101170402130e06041a01060219020d05070314011a0d0203060f04020f100806030d09030804060f1704140c 66
    0x240854205035100e050402880002400101490042c2c034480031509035038814910a20941d401040004020b10b10300203c07240140d08290012410a00c2ca450108940340c420b401582070100585d045585858010445042c3e048500a0a1084400704400780c02c01911244060086050b28010100000103017a030400440c1da000301c10450580c401c801501080040c00d10100c1692860803a03080807d500c101103000610709882110162951a4203074141000703240e41c0c1540718054150351000d860100445082c0c44501c02220b24000c0c0185941a40314090000c24002d010180d40e00c22103070b0a6039007200000d14064121160060100c0146021104a51030f150b41c8503440541d0241c080e0075255200303050b00380b18550080050740c200f951400c500405554103048001002d01c03e4032a507139242480e0082c54944004243c0e083c0521103030502c00d1021030b52400540d030444030585490b4001584c440411900900381043d0399a100d00b8a1b01400b003040b090040d0709640f07150381d4081755003040860701007003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 452476879 1250 452475629 452475641
    0x21c0e010207080423041a040e070b0a27080307060609021305040b130c050a020f0a020916050403020307090204050913020604150e090906100905250c0614061201 71
    0x2c3c40f8100c1000100100b6009038140f40c1e46180035000c245503102600c0105084da40c44902c124005c854014000c10f45141510400c1c01c041f010800424185041c2140010584201852070003800445040c1582500f182e000e215181c4a21061460000f0b40d121040350307603900140c1c1c044481c3ca04041008c110342003a84260f6640b080d90f00a403504c01850201131100074000c03030101d9a00700d1403d41481801d040c850084500001c000d0792800d59071003035030074001e00b40b15800d8000440758000081507800750782c6540000d500b042c0d01c3d540040c84142c0d44078096865104692001f901400307405000603c45025038050012644245c0388900340e6910300d03800e00324815400400951042c8107010920138112044c030f80c0c20481041c1d081c01000e0030b031100002400d2520840d08221145d000300304100d401002c001d00c540040c048140b0520240c209101015181c40c282c959541a80720b007981080f42c986d1046601840440c0c10120401400140c0c10a8164401d8112a16402000c2c481041820420140b0540d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 452478129 1250 452476879 452476883
    0xc0a03090e0a290f0312130b03010e0705160506010e0a1a0d0b070e150c1e07052202070b0105010315051f03200c0c09041a0604020409021c0e010207 65
    0x1030f000b0540c0b400301500340c038001c4078601c07604941501d10303000440d01c04105802e010011084e1003525103a6081c040105040e05411003802a1414001002403106030700c1f049030402d016080032600c0344000d8800002ca0703c5841c4000c0c2540c4103010000900700c960700082c0303000e5804c5820a105030158894108a070844140c3c005e9000b81216040c900070407180102d00c0e40050092504c0f8001c0c4808000150b019500549107001c0044002515604480108005d1020040742070070740c60010040d41300725842d4034188c407400f4080c010368031100540040c440070441016109020441d22007030641040c01000009004850204e46001c48980c0d80c4489209a1030450700c2c004c0c111828903500b02503161922040c0450b50b014075071285458010482e2403030500811104a030800c94545509010305858017600c02c203554040c8103c07005004c0842c1c1404801b555500700007403490000c1c3c4a0034049030091149070310030b40207a0f102041000049982008010b0030740343c03400c4280711814000028500701c0c0310780140 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 452479379 1250 452478129 452478161
    0x6060905030c0918030a030209040605040b091603020912060702070503030c100e1c020a1e0209070503150a0801060f0e070e190503060f040b0a0501081f020c0a03090e0a 74
    0x2e402c0d82d510b045a00c05034000e5182d03284659011682041ca851074003d110030001094002c05c0000d52420300f88200401014212000d0200c100c85101060140c0310141070030318110401b802c00c103001402074045428580002d4450392000c3d504444140d01e6501c1900c4050040c00381a0000403103140000c15100b00d9080000a0003996aa101000000b40742044142c06d95014080c0190400140c01144503030600c0c07030380c020f85090562482d000203210510000c04415643e10827060004d030310388160031782d400000d609003260340740c031344c0b8110b080b03030306079841c12143c1c44100c040000c00c4440040d003080c1c04440410340e29071602920f5842c0c004440304100c41000c0041c0d00c0d001000060f00d440000d10800c5003000c0c0740c80c041c05881e480400d003030400c01c036021120581e4076000d11040240b41031200b54005c0c030501c010002541010b500a440300c892011603034294201210800b41d803241030b4101c0e1041801c0f002220040e9840345000742906209202d58802000c0000001d00c0294450245041b00c0c248554 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 452480629 1250 452479379 452479393
    0x11706010b09010f0905030706170a0207031706060d0509100c1704110a0f080d0f0203070510050a06090e0606030c030601030b041e050f0105160315050405040501090b0403120606090503 81
    0x80112403d008400c07000d0704001006000240b02d8a02340000d90103010715035504100c8100290810010b00000342070007020b03900c10042000841d80c08140c2a2500301c6508015120b519031100240050040340a030074100d520340018002c000800213101c80740c1004281d024404854801400daa400c071000016005a500d90340c002000a0070351801c403200100014141d0041c6a00c031584a0000b404680004d00d4640c45240b05824468000d41415180324061000314035001c81562602c0c4c071882c000301010303880d81e150000302c0c20001c91600044047c18694034100005030051040541d51001900c040d4003134052200306c0250380c200070602c40c0c16a60071400800850304c9903a201c14820000c28844c585040100800600080003441010520782068002050506040b0360318280b100055405100385403800d100404568006aa00c008560003184c0c0010b150391541080c90240c05048002843c4008020400c0308158010341c0d198280400c007007041013080d85490003580c81140314082c50358503600c120 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 452481879 1250 452480629 452480647
    0x1303060e01091b060e0f06070605060a080a03030f1a150c0a080a0e151e1c0c0503070806091b030403110712140c0d141204030b011706010b 61
    0x2400003080c044030354000003503192039a1500402c81c503440c0b081c0d01090380c491008100083c1e00650800014604590b000c0070031000303400040d01c81c411800000c000c00d4540c0009401551201c90140080c9440c000b42d485042e83c91600500070301101d4001c1c2900343c94200400715298405100014070640a4a044a01101ea01ca400c034150003d0a0840d100c0c441e0001c0000018070074405042c40304007540750031102d05004c80800101e425880c0c9044100d0b08107105490480ca02c202844601c0190031407507a595603150401c07030520641c881201d1220701d040030307031040c5250303444801984034020995540381c00c1e0711564204052500d06603404182244038401c46000901003800440d0407030300c40e00b0b2080b00c100c1a681c0d150700b49052076000c552000e884c46120030620107074008261072445c8407006480e2220507000002e95003070b80608040e00b10510b034040102d0307018040001c40742248400d04100c0e26696645051a40e0103800d0003140080030020165141c0c0c4a00014460705840000c0140303402c01d0109 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 452483129 1250 452481879 452481881
    0x10b03060d15020f04030b06100c050309101709030319110711011b060b10090e0f070507050105130c0e0412080c040b0d0b120a120309030302041e06020c0105130306 72
    0x8600800c4030302c0d9003000302c0c0250710140c100500046200303519140040c90140b04002c140040c0261540502c8003250802000540c013004035801c031541140d6500203c2002a070482d2188075101c074148503c00b4550034841c207810004082c0d48070b41c50383d90100044000c0e00c1110001d540503012001500e0009008e200d0024800045030000c0203070615000c00b641140c1a008002c00640b07083c00e90740310366140e000203c10f062800c041d4510042030308141c50400e182c011030001c40c00d8010000418001c062004c640307450b10400c211140290031500030702040c144000055506131032000200e0b081807508200003004207800340d0b0f6a00c900d40102e06a4409007280500352030b5110006d11081164004203c0855035900c00800750042881d4030304001249000c42003403014212103044031840755400b49401200088451600701b00201141c80c001c48c42d8140380c602078010b4003854110440e052100000c00c48030040311401141100d00613030848145800c500c00664051190040c41d0342c5e0810b00e188240003242e80c03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 452484379 1250 452483129 452483153
    0x60a0f0e04020d140402010201110702130b010c020604080106050f04091a15150d0e0304030210031515051207030c020703020402160f140607030b06030402010e040e030a03090605010b03060d 83
    0xc003510252a0810b0b84031500111511040000009040c480902081d035030309101e0700d1005104e00166038a00505a00054005840802e0400901c0e880c1c00c80e034a5075034440c1c0b142110260703014092507100c40c1c842e9100c03400ba103424000c80380601c078110301d0344503d4035150003a00560340d0004503c61f000e454040100c601404010818080640d203004506150b0f11002e03010211602c09603005601d406110480e8019074181040c0043c8aa000b4402480075a803904045a808030160800140e14004420321440c3c0b00d4031a4040381d081000751510141d8107403c04c00074044600a203401c40443d54512400742c0c21070740030011030340059204507400d200500780795004202510b0460000b03213a403c3d03a5981c2e40c82070346103c08104c4000805040d941e46441f4104200390704002c26013014040b610a03480800ca082c0002400030381005580c04801c0e02c192100d5100034012070510b0700f43c0b5941d624a010250280c5907040b02191a180362100024100c0c071501c3c15603005501c000d1030090090403a882d64162100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 452485629 1250 452484379 452484407
    0x10306090f080a0f03151d071214011d25021e07060f0305130303420522021e03010906140405040f23010e010207050c060a0f 55
    0x15000210002c0b03501c60010308000c100340e98640c10322840026004041d9a0320802c001012030140100b03000c4803200c2c0c03401035035007486442d040c101e076610860121030351051001c1c2c5a03584c40c0b9014110301140950751b40c4178141c03001e40c449010b52040300c8885445c2907000302d41d0042e0303082610b21007108030b61502158400c000050f20458140d00c000b0440c0700d00001d8040359213032496210304001c002d40740c1c00c51650718101445040400180c50702c0001c0c10348500b00004002c04042c1e0f54144a48510300d200c010030000303500f51140c000817600320510b040f0340c065070b110842e05e00d44603c180010946811580da50343c2c0914940740042441102080300043d400c40740c1404900c000c4120884400c0d903241001d9030081c8482280800c150f4035040c45903040014441302a40194280020003020038801d40d00c544c0081e90190301c1640c002d42384880c410030310603024140101542484411404620150050603849010b0f0099400400d0300e9400c02040f40704810360080402c1c40b6013581c0c4130080c0901250780c8250 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 452486879 1250 452485629 452485643
    0x1080a0209060408060609010f06051806071b0e0c1e03131707060f0203071d011206030c051801150302030a110a0c0c08070b16020301020f070503071a0f01030609 71
    0xc000d401c009803154000f50044000e90303012500b007060f18070380041458010704244802d00b01c000d08140009181e4811800c10310b03002103030075000c9561603e40b101140c0100d42c011148003002154440790995100790340c03180c03100203403906001c91071850071081201d1000c00c03030b000624154501100700030a1900020038982e40781031511240340202d410706c46040c0c8a600e815501b15985c400703505d055001c44007180b591510041c8103204000d40c541c2c1102c02d500914600e00d1140c480c00c3c001d80d00489015070085503a00c403990070120001704000070304c5078550030b07120229036282d09103e100406018a4030309128842000e040c0701c0b070801040d8001e030700a40e080b0340812008a064401c0011402c02780c0e01c0100888005817510350711409100e1401103170300251480101910f56186041210b1203980038600c0070942c041115980c4104650b42541214880c50030002d0454a98419061044d00c0e60404501130720001403e61840b46a41d0007a00051b10541020000b0301d074503425030300c8270300c010031280804503818 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 452488129 1250 452486879 452486887
    0xd12060806010f06031a3f01021e0a0503060909070302030d08070e0307080d050f040f08030a08070201050c07140c130b0103110715020310170c210601030201080a02 72
    0xc1081030100c1070180c0b103603400524010b444d004000302100e61116034040702d8001c00407014020754806d554680e8000303409510501d02102d464424007102c0303000343c2c1c0d11440c4020728548880041c0640203011040c0d490440640700e0f001721a00201c65129001507000050400c1000600d00e1030400b02c426001080300b0221a91b0644960100740f4000d0420226000b0039800010000c07c29840541e010756203000b41d02814519103045601036540c5500c4d4000410301401080190941c03c2070305c181c800803d2100c0b80e00812580c0d41102036160b80c00344000400081405c400110098014024980a0780000c0400c519203459500c40d038a1400c1c4d0290619802d008000503200259941581c4228a1042450004e82c0720003190000d01140d01c5a0400c41d9004800d002c00e40102c2c1d0018501e07500351041202c090395983e61261250911001ea03040207103041424114241100b0700042d0080c240031042c1c40c0c10b0184d40340c0307924241d4107010702000c801e1294000c800500040d441140c00c2c98202c1c908203409410 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 452489379 1250 452488129 452488139
    0xa033305041e051b04080a02091e061002010905070b030a061502190c031a090618060406020c1216031d030316050304170609010501050402132106090b07030e0d020d1206 74
    0x80d4070640c00541b05502026142080d8604041030300d81110814114290220401e8900c0d0341d130f90310003881244203181610402c5802c90007900094491540141683c403069103400241d8010303001961602b1010b49042004558404000803a0344900030580040031aa5044138202e524a00d55050866607180c540600100160b9040d00301d00c0041c460703044041c401d291030303410130345031007001070514034540c100d0f500e503a100d010b02294554001d5000b0f03401580e00d034651151246040c0600b050070b4610304000079081c0d40d00420642c02051319110f5511000145505a481810b0328043c2c00c895030301d500200401c800d54040748600012040c418016641060341d202c051505000300001880d03250b8010108010758441c1c01e1260502400048804500740f92840804441841c00c500405142519501c47c8035581e19550700500c8003168000d00c01d0003110250b1130314814190064440c03502090400900040c83e00c0003054a00c0f04c41f4003640101091060a035044400d40c421854003000a90b8416000c18 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 452490629 1250 452489379 452489431
    0x901090b07020319020105070c021302070f081206011d0907090b0301080106050312030709051c02031c080f1911041208040305070608010f0b0a033305041e05 69
    0x84507a4079034000c0c64642410043d8213882818403007081085914203c03c002d000c54206055030b52094054070384050b244100149100248122900541004005031451041151910050009451003a145140c0361a0f00307005407032031455515440906100c291040029003032030121180d00c00c550703181520145039240c80d40e918592081c0c02c040d5059450b0b500610040c1030420032080041c104454840c61407a2501008180803203e0007102d110300307012201c0b0300043c1a0800401c040350b4004054810226208010a040d007001c41169800f00b103140c40010080c2002555852003181044000c0c0c0180700800c05ca04c00400701c0c0800350008080a00020600c001225011030400f440382c05410382c6e0354250b00b0a1440d01003168810010000d146005202c3c850004141508407803400700090780300c4285200a40203003400f4901703001d01030403450f4042009001549054003580140741c103500c151b5160002d2100390369844a005049503c2c0e208000c210784465481640d11201c3c0c0f1500b050700c0445406442 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 452491879 1250 452490629 452490631
    0x6120b06121e2d01051003021c061e08031207031d0f030714030f0d0b04020d09050d080109091e0c05030715200604021905060a020106080d23030901090b 67
    0x503800901004083c40302d035080301003011262920f0501d20300c3c3d0f1400c800950000c500480100800d60007050390b1502000343d00d407400c82c0852459051000a032550340021a40c1c001c0240500f5a5504800c0000d40d00008411100c2e820110428440a90fa801400798041c200b09289c0704070740300700021105000795040c001001035a42d00d0f4050f5603128000d0a0145900420181c00085a041040740d4071404005404840c4042c9400d0400b041c08041300d000a802801021482030301c7c2c41c00c22103260304014010038280c070003012a8940e0725050347c941720250101c1d548074000801c0c8824000f4803d0103041252441c8141038480c4074480c02003034860022a007001c01aa04c030f600c00f200c0e600e109901c4541c10208800081c4c0a21004e03007260b1240610441d81c98001410107806210032071541d95104551800b010080c10014141aa0740d4880352002030080403507100d15101030044884109241b84201e0b200089000b6041030071404040c5801142d02a81c0003509140007903607104014000180e07151581 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 452493129 1250 452491879 452491891
    0x50916060503060406051c0f03231c0c09030f0507030203030a1d0d0201120e0f010c0f09140d080a1803030c030810060504120203011103040c06120b06121e 68
    0x125140e081007004d200640e0010b400203480354040d000086840f42101c00b4a00510350080103a1282500700d05060b5044180745505c0c18918800b0481030302c3d074445500040103030545031740c60000d80807100710f026001c41c1e41240c103240005548450401c08641d80070030ba500310b94020400e459a9644c1ca0340000d20b19071101c4c003494046020711603070003104013007881119034102c81a10720640315072040e400208810310050b44170040641c0c4400300d8121103410062901c000c000740008020100d8140d1011b803e5144030b010b40d50002c1c0c02c0c1400891000820010a0210308028005850080c429075409040d034004c55002d108200310b15140c400700144446129000f5402500c031a8450780c03a50030700070000c0200510116502c0310303004d0f040004607070010848045480500e22035400185a1000901414040d5080d0a02e80e1000c41440103204898041c441214072584440400724070005441055585c009001c691144081c405c10b0070118088120a03448409a190380500750058000100301000644003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 452494379 1250 452493129 452493137
    0x40b070b010e1003050d0807110a052a060d020c0a06050a02070c0b0304050601170309061b071a03040803060a0e070806010f030905060103021014040b0315040b090a05091606 76
    0x421214102e0082d454110803140401e091040c2591a9950350740960704144c410800071000044504d8803507919500348603041400e0728403a4000303040c072691b2000c41c41c190298041c2ca80c4114040170402620840001d000944118107059903054284005c0d00043c4c030007011400303074500800014801d0320440348507980103013005858a0850401c1030100f90705801084001c0400c02c10701000c21400034011341180c03191541320490520b00100542580104855a6000b03100843c0c05241c0081c1ca0401e60000c50800040f900d130b083d901c3c04000c00b45451855034943e0044100301040100701840c004651000003c0d04500995548110350b03000124215240f00000e403c2405010142d81c0c4480d10445260040ca41440281c2181e00c1e070300d032641c806100080c0703d07a0b1641034000c1400c0c00b4404000b455064a60303081d89035607481400840300e501c00c0314224501803c0096451161406216110002d2005010800d00d5624041144024000601045481e10500e1740c00900050b404010034060328143e0b507 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 452495629 1250 452494379 452494381
    0x7030201140609040230010f0902040b0a0f17120705030304060c090f09020d0b0604060f09050306010311010f030f020c010b010306080d050f030c16030503040201080f1b090402040b070b 81
    0x148510003008042c001c50701c80d841081c18840540d4030000e030031060b4241005074aa4a0301c4600003828103920703038801c0594650034040c00c3c1d0f8540540c0d5120000c3c1900030f0701c040c4440d04040302040680c090900558030000150301040c4140c800740580d01d83c44040b01d400f1607040d003144242c0c4008581040908480c5503100104100400a45005401c1240094281140310f2400c042c0103a04500c0c0c10300400b03141a80c04580328450040c81e801a110799180581820343e100e88404000304561051ba03d200081480114005118200041c040f8100da401400c0411052001c100450711000145114820540c480c079404032a0007041c40105580c11508000050780c100e408009010f541d601d5103d540700d60001200280030903001011900c1d9886d038000080d5899803002000545809803070303100d031203060f908580b1404142e040001540501c0c000d0b22444040c0d40c600d02d0781200302d0030440d29142c000e48000300b103208640e403400c050090f001c0300810160030203031516038007900c0c0d4110a5007a1503d0780c1f000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 452496879 1250 452495629 452495651
    0x305070f061803120f090306051005031209010f0f11070e01050a09151a19020109030809061e09030c0312040c0b1e18030a1407150801120302070b07030201 68
    0x125120424140188035181140e103907495481c0442641c61540050100d03018905d103d03184541040005154040e804115904013080030001040ca030b80240c0f8001e103d103412200d420440201a0360516105030f56580604032000801c48a441012604c0418000e00c40700542440c2c0c4140400001341403102c0d90700903558074001c04c11400d09000e600c5480110300c0c0840d40020100e00c0e003c1c080c00d075044100141e40204c0c460b00840700300c0c841e6041e004150312030071325a8000d0f281d044d0003101009001e9900ca00342ca464400d00d5079120b43c02503c2001d0001440c0303c161080d000b40840080e4404108003c0c2c0b0308261800b076101d419540030800d201d140d440b4030010002003040c07254407040a0078141c0b601c00c2c2440d0320a0030b41c500c510000c4041c580010800308025156101d12031349140c1210029058aa60b650705103015071080c0e08004d03100d210f032b00540754045200610040c011142d04007070f0351466061303461300030102e0400f030038080e06504500464001286490741540104070b4148607500000b9092410 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 452498129 1250 452496879 452496887
    0xc020c0102010b0f03030d1815060e0c09090f09030c010603060501030507080d021504110622091505010e06040e010f090c0e0a050f0301060f1413051e0a060305070f06 73
    0x400c001c0d84030b4040b40c0a13200e99601e0000584d00304250341031000030342d42440d80d1000098049000300400a42070031981c0e52410150b50000030071a10021601d0802c4c0d121540e0003006030080310b034800d4110020301d00280c0d4615420030f1141d0006486810f0324a0034088000050a464298005480158a0700010010008100240c0000302150700203031025480044000b0744880310301005002c505a10701c003107014894082206000b680c002042c040c0e071441d018041008138020b40da01b0b0171110444200010701101e41d4054558415403800c0e2210403c0c1c00c250040d6401d000e4003039039540000341031002060721010800b81d1030107480424010121545840b8503981980c01c68045a4100108160220f10b00d45030840d480d003c0e03031000c80f54071518a03411004240142503550000e4080e904125000a415001482d41c146810065075020400e000101040013662001d944064000104c00742500150558280341500908408030201e10709a480c0c41c0d043c036004203904008205c02c8803040400146401c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 452499379 1250 452498129 452498141
    0x3021c2409020f03040b1f0e06011e090504021305031b03100e0c090705120a05070f0e030604080f12070206060f09070e01120204090e0f0f12040b1b010c020c010201 72
    0x5041c41c10b602d0300c10030031940c120501000c1d20040448130860003061044a00303511040b1500c407412000c04c15140d64181c0180c0c800820b4410328041782c1c004040f010b030885501d42e41000c0c2d01807a10b0310b480c820300e0902480025401401d07002039503402c2c504081034954080c001806a80300c0c1c1219060700719000000c00d4100804059184406441d100444d42c1d00f00d00032030500c6000e4000c6030100f03410b940300030381940e03a0310424402840403001101001244000355204070b004910640e2504809240c242042e80c1e0241e944980661681c062000100058003200c000c0c00d50326240822941481c5400b003080a0b080c0741564840e0158004e039082001e9800c21003805141e407401216114400e091040f40a000044d280414604110010840c802c403070395a0b0b01250000e151513941000380c8a82d02c01c90300c0d00c6503034880d0320340964094601c6403440304100080d000fa0079403003008100d107010300d0080341c140301c2d6012034080440700c0d130910f08100842c8402c3c0b04036042110b2039005414200344400c002421280 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 452500629 1250 452499379 452499389
    0xe0a140312071110120213060207090e060f07170c04050411090108040209060123131a0a0509040902090112050706032d2a0801060302030c0a03021c24 66
    0x6007401048003040c00301d031050700c40c11026582c210020345119401c0703030700c1200c2c0c0544514440c0006403a20801d00926507c0c4c04890a80d402c3c7d82529440e911a601500c042490000d4070368803c001040d081640003044540040301818013401c4a86803010360b000c941d5044452030a95803000c1010440e6040038010003148034a552411f07072500d400000007a0001c0f8010f080030780607045c188005050359005542d038001d08002d000d121518803556500d88145940a0030726a100994603c0c2c0005041080010000e91002d081122604140b0700c00d00446145e000340000541c0a500c49c1d40010240c3c40740004903000e010000c0c001440040281025460300302107070711a10826150881c0011481c8a00401c10f031a600400040c0c407a482c03030180e07490f0192005011000728811201d4007282620303014038103500410b0300d40e2141c0d410341e0381c2d41406030203c1c00110f4129512400400250003001d110360b00a01c00a12028400040c00001e80d0000e011030b030100e05641f50355034522025483e9480c0c01900140140 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 452501879 1250 452500629 452500663
    0x5060d17090d0b0708100f0b07140f030a0e0603060307060507061410061e0906200708150a0603030c02040e0102130807050a0b03040f0816051006090e0a05120a0e0a1403 74
    0xd1f16003465851588030710f1180103542072000c1501810403201c03002d089286250001201c0c039848000d09000c0e02d81c1e00820321003012400300d6401c1a0141016420340780310b25002006051124609030044da201d500841046600c10381d16030848480804a0b41ca482c004c440503602c048901c1d0a00304080d201411060020b01c2c02c1407100384a180b45a030080141050b0307107062600400500585441c0b61030702160f0038200680c6e014824000c6030419001031914000b400c030700140d02291312a201c804003140c249003c09030009202d15424030150406421222921001c94001450102413032401802c1a0f031301d4005c00b4854022210401c590f2a00c403100030080c0c004504020701d541400da4035544040070342080101032500100711000f07440c000d502040405604403040d503008905d000b141c000200102e00514018500d08135840020610018141d440c0079030140042502c507424508030b84d0550400303140700b001c00c05100310381840c98592111000040c40a48010850f16082408050412020074242c2c0148 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 452503129 1250 452501879 452501911
    0x50d0918050f010603020a09050d05030a03050f101505120712050117100f0b06070803010e010b1615060510081e0423030d06030b0a0f05060d17090d0b0708 68
    0x10402c0b40b10818111055400c00582e607032090300090714a0f010741d03030156900800c42c80e003c40c203010740400145081c280302e076420001541e440400c041200c02c16207a40c5c50714800c0c180c090181c4910501002081e0f02c1ca401d01c141000c580c0c4211070f0025804503000d000043c8082c0b00801085201e015041c090071540b0f0084802020b04441169189004007804010a4403001c000000c2d0001c3e80c00801481409032800d503a07190303a802c00c209168000c0c403c202203903c1d50400041c0c070000103c241c07a611440900c82c00710042441e1036410031903501da00c1d4030a886a454900041766a14070800488040190303e0f07502c09450550441c40c43e042011005143e0001e00c0e20401c070009100350b81e01960f16042004040c00c00f8038080d44c02d03103140501035900044a00c1c080001c0107000390100c00c24450003020100f4043c0056140c000d80035200c05451890300a21508506000100943ea00201c080b445486050400ca120b0300040c95012040310f0555046034181e062004280d40540e019603c041001d04098503 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 452504379 1250 452503129 452503141
    0x20a080a0e0d051c0615020d03060311040902040e0303011e090603030801050d0501201c090222020906030a0c090e060d03050f070210090620190f050d091805 69
    0x10b40c003030a18001d04100c00013686459a5402041e111030005100d070007004560740b202000740904135484108005442031000d0042c80c144280500c0023903d44c0451640c42011088080c88040c119120040b030780113440c2c4c14500c142c48000c002031402411310607450080208100740c2c182004d0800d42003124460704240050020a401258250466030280d55100309040c1078145507004144000d810559210990121620503d008000e00311450285505203c4e0101055100040380c100e41c01c000d40045260001386403040031483c0d1a960740090000240c03400c40c40e400050700640c01207070302c00801550f6006080d40c4643c0002c2c0400506400101c0070b400341443c4002440c035a02c0b840c0700808001c00001d000207050303d0b02c01134034042c0707a024000007200840305101505101d107902480340004c1c071828080d00c680e4100c0041000081d001c0f406030014005254568080310100d4000382d8405000504a10010740d0070006002c010711070313503200c104280c200240d282070304103110007405c5118200f10501c40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 452505629 1250 452504379 452504383
    0x31c0905040630030207030f0b07140a020c010e0a1a120907231c060f0f09030c060b0d0b0a14010611190507090f060e0a0e06190f0906020a080a0e 64
    0x3d940451885501111007482c40e04a142100980006042d0f505060201d01001a22662503010341c2e8242c55150300e88040003904541401000b00d0000142c0c8400f0a01c1c4165014800031198072034042d11345800b803915031102c2d5400c824800c40500450b04001380220a04840700c22064000c20500094a201407030803482e1070080f0b000045608020801d00d2142c1e000d640d80003d0000000e0103c0d0b0f842d10640e0103030500c48002c2c2410b07800715051074141820b100d0fa0461074490742e80600e03031580b02c070218100e003511070000a101742042d050f0403a22041c1600003007042020800d10400c070040010030000144001725280d03c3d810380c40801800307c41c00c0c050281c1071020503040c0107810000441c185218460034101d141074016401880a5854a1403848607403410303030020015a041e9250a40003070b103c80303100c8000c445100b044642288c1100020941c402404840386040d04c990803800704030607a01c1080c0d8403c0f62810310044810302e0380003510618183e00025055030009121004000c00d81507102d08507 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 452506879 1250 452505629 452505689
    0x803040905060402040e0f07030b0f060a1d0a030510200f16120e030f0c0a06050309071e0311010c080a0e1f0207031707030f050702031c09050406 64
    0x103100c40c0e1540002051038075242c1c1500c00401d0140c01d410464100b01800c0f20f2010000c0c1c0f03a0f40002070400c0e034040c03032609100500305003401014107580c0c6010701c1c00c0c20455607819104400076510142002802c1d4965072074112401860140c005826036074038880e88030080b507038015445001440d20701c02d55540018200d06031181c8041242000f5034610048408003592b21060200401d051b10384806200c020b031303120052140e0480c1c00c1d4100e40b42c114001c03208543e500c02c1e1080c100c7d40f060344d101050081900c95005544c2010540c01295a61a00c810301c1d07080d00085840765060b4144199010014400b540c071602c1c140b6003003821f254940eaaa00c2d112820b4910907428000c0a206940701581c44548074100750108801403c4401c80f0080e041c00301c000d440711000e103c29500e4013010440210740c62440d408880b5034039416200c0d5240105200c03011345468200420580c3d040c069400419064500244669800c0381c41c1e5852100f25030921003040101d032030395040384209541c0040c0008180c00001548 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 452508129 1250 452506879 452506889
    0x52b02030a120b0307140a08010e0d05070f050a081e0703090902031302061602010906020303071205130203030304050c030715020a0b3304050f22050313080304090605010207080304 79
    0x1140242042c2c041500541050005290540304102d030000d0b040d81d05003040c1c80e43c1079080300c1200300103030350b50b5059003a0f0380c200341100016000403440314601c03070140e00100303003c5104034484654801e2607180c0300e013481400c4009a801c1c06c07002072010303d80089203242040000060b00703154240405510001d1504502e4020032a100c0c0d40040880c42e80419109420700d8254028502d035900c203003440c8101009140030368202d000c240700100226100e030010050381c0c42400203030f840d100d1640f040780c00380340500b82c058030703240c44040c81d00b440c0c4000d601c05000440c4618001c600510f0844d90754018103140a680303a10241200b0440f00525820300d0b4082200440f15400c0180c82d0700b0f546880001c0030b902010030300030011a1110303121881003150201c18840200728203d40411041e034904a40e00d40e0880100ca0803150035007100c041a480e4103100d6180d00c0c4250080c0116428081d0007401d10a0404581d0400c6a4541c008101002401c120740282c078080c100c00c0c0f000d41259481d0a100760703170300d0065000b5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 452509379 1250 452508129 452508137
    0x305060412122d020406050d0c0c02060c0f0618070308031807030b072312090a0209011e050402071115190801030213050c0d0b040603050a052b02030a 66
    0x19080c030441c4281c00c10b5040682502007002110030b00081a9034920341c1c00108680c1804042030042480014400c3d24110381c940c0d11418a00500c580c8140300a00c1115104d0081c0002d5122400150701d80da0068000481940000e2000c0580c03481118504a402030510080f00d4042d01a0804054082090012070398411410794903030711501c00f000103031035440d43c030707296039207e564000801d000c4141026405284283c4850015074804404030401d103558040031000e1603000c0080810580300d414845504c10030703071400c4d10340440c426070004203848001c2e400382012840310400101f806001170b108000604048400b1450841c00340c1d21000034102c2543d100c2d201d998904d581e4507480a0000450700365042280080b5007000c00400040c0c4210001e00061b40240c1ca88640314425007a81d10950b8001c00c12005218208404110880c028110784941550030613142d40c80040000c400304a4101e2062191000c2d22a0283c8000c04c564200d201140d190304118401043c0381c0d415401104941d880f00c52460 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 452510629 1250 452509379 452509403
    0x8070f090b042c0c1f0813050a030e030a150f0c030510031403041502150a0b0102101104030b010e0f06030a120e01030219120b030d0203161406090c180103050604 71
    0x682c107401c4c10026206950041c06070703000340340030403000d400e009044055a1200300c8113032540800107940035400c1c0402406039008110110100340181c4a03c1103007200207040b03c88070805035640d040da40d50310b07001c4070280c3c40e1904419030600c44103018130546c0d400d051400700441c5c50b0018190b52582e11910015080c0b40d00c01d8a5210021000c5c812603000c5c0159509035900440700c00740007542c8001a4640c41114000c2c8004a4000b4403a07020318100c040c170581c001c0c0341a0001405580081c2960718840b6101501044004006004407010314020a48100404028645420190400100141814402c1e0030218400c00002d22880102c00d1002c00362800b00144620800181d00034842c0c05501c0b4036048040e51601c0f0300f03035030010308003001d04c81e40c1d01c0505c82c188079501403542d03e00a4080303880143e0000d00c0b0080000f142d115507041414003d5045030700344000a403a081c2450f2042e41d842d0310640000c0011282410580a1569181d207034804e0b1168030341c0355844030785d00c0d03c0340500020080141d400b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 452511879 1250 452510629 452510711
    0x20117101d0a15122003100605030601140d08180901090b030c03031c0b0f061c1103010b0405040c020a02100905090a0b150a020708070f090b04 63
    0x18600001416a46042000503808400c0401c00464125800d515403410700c0f0b0042c1d1402040c04076001100c58000c0d058090340c0303165440100e45040c403036050340b281c103031842542000c0c2d800700403140701c9103032415000458508020502d400e0110503000030050540207014075070f080d211300304010b201a4100d044507454901080940c4181416030392140c0d0300c4010f038000403039103c3c0c186c1d01003803407040c0450480d02011a00d405064a034029000c1d10880080c1c0d0003038502e020501e80e080704024002c0204004000d040301400280580c101422110104111801c41c1556450a10500d1111412007020703d04640c034044c0e15801c60b11131802a9030050b602ca0390210111402048810003c42e402801c4405135020754500501c4c551692043d64404c201c1e1030085015090603110b84400c00e8000b070300c581c400c1805151501c190f5400200d10704118411908002203140e0144060130280040ea50340b000c1d41071401e0800400c2d650307105c10340c5100718640b5100038012401d204403030314001198480f042c0c41009403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 452513129 1250 452511879 452511901
    0x30613080a0e1329090601030903020f010630021f0c02041103191416110f010506010e0102010209090402090c040b030f100f03080306240c0c120109020117 68
    0x2002050700800c6032140b0042c1c0005540141c08034a003d00c082c100c3c14642c603001404d07000c006400a6401080100c042a0954030070781041c81c800d4040c1c0121403144031001c1e40039003140d005601500d4402106001e00c0d0150100c42001504026211824201c040301c68000500030110480c90f054045a0803013003e04e40741c0229a90350b8901e03001042081504000069031b641984103e55001c000b03084485040c10b04110361186480d40e0f240e0309084030b0241c2d2489020b00f00e01400107442c1041c0904001000a00c810820000101d40c40010020426040c80c03070000d026021084c0101d419640103100003c0795440c0c0d401c6260f40540c040b40c102c1865144c00240c040e4510441c1c01040104100104010b54100040d0400c2d00414180e04481c1461741c2d5940107408941d02400010300007841003011400610700b986100c01004044a01154881107076800c00c08258090110070409400040c050b95552618038144400b80c08890020300c0380b522503600082184212101c07030002002c4c0030000c283e0340d1100c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 452514379 1250 452513129 452513147
    0x1c08070309080c06190204140f2206080d08010e130201051902060f01080705030601090c02011401260d200a1209080c0d1a180d0c11030613080a 63
    0x401d640e58400940c0f4a050300c0c1c0c081120181c21101040703031014a980d24520850b012190382075404107042100b03034204480785411169055000c203601110341555501d140760300300381500d1100c1c0010b107030380b51210180c2401d54071031038203042c000d201c00100584820003100a5002d4003851100da0401a03910060b1500c2c050381141107a046e080100c5d00003010340001e2202d000c2c6143c044500c201e82e0341c962803160b80d00344c0b030700030030707030560855401000b10240a401c4802110b016000109010f00c616a1040207403a003640f00c0c4007640101c003480542a40381410b11000604681c0181c4544806083d001d460340c5141d10b400c3c41400e4004a410000e40d00034440340c0d40307181d0301c00200460b410f044c1c403009280c82c0c06805220590301076409081010b1910141c5100c0090340028010b400c1c6505004a524480780181030420321107990034002c29645c018014280040300e40d80311b02441149a003460b5840c085050300643c0a0750020307007405029119002a6440c25501100790780e0703550042d83e000c4804080c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 452515629 1250 452514379 452514383
    0x11070c1e1511010203070203090f040917031509040f060f0c021e010905010609060611030304122717100614090c0c0102040f15020109030e100215040803010501020706021c08070309 79
    0x12021080c41301007507000c00208110a41150301c0200310807512b04200850b0b100c0c201c024129202485003619071030940c1c0c09181e11141d103800d0000044a0315020950074402280e003110320b240c43c2c3d4100020001c0600c614040f402c03600d40108400d0080348c1c130103075850042c011404140811321421050000094010503406a1f102c0300a01210f0381c0c07640501d028002601030040460150b1803882449000007080e00e100d00d03000424410b0844940d0310036202082c044503407200c254080c806030130702c0030101010b04009240e8120401c042e101c9400d9034905208803000059400d5060040401440450030790380121604103d0b00742005403140e4140c0849446a4014042c0c0b40d40007181c0011040291280704048a0540740c0e99448029000c4049080342c42d034050090104d50001c10400d4941080da1b555041d02c982d90046680c4888000403035061150215001c490040000005102ca540e05005030030040040e070004201d046c0c80c03440242401c203204031810702008035072000105013a11030303009060703126 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 452516879 1250 452515629 452515631
    0x918120309010216111005030702030409090c0504020a0c110d0312022d03010501091401230c0a060f0c0504031e0f0b01080a0302011d0c01030b06070611070c1e151101 73
    0xa40c003407806070170402040300703602d1103034403100c840c0004240501c08880c4204000e034065482c250800102030020220b009044e9004020584040313401c3c0c595200800f40c0807102d0f252441d080c0d50500d48840d00d03a0710b0b1011035004000680380c010020741c2154a410035001e1004001da1070318500c084202448603034412100c0ca1503100c00701c25072401d0614000314160740c002e0340e44507240c90710740182c1030a5030748101019001521865403003000441c030004510b549240ca65616213040e1a4038a801d20701201c1100c00e64072a50703948608943c1da1a507110f951400c0166042050400e491a116299951001883d030308801144101c800100000080800710040c1e000051704a1303941c40307041141d0b031088078220440c0558645503074152040050001c4502c101030500092009075210401103010340800c200301e5410010502030341c0300003401c0d03020b801950702c3c41121b425110703405401c0c00c2d0f0039405c2d103900c200d20482c200c4225003000b45482c00f0a00c01d946c000021000460030511086030300d80011300c0f00070595 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 452517985 1106 452516879 452516917
    0x911041a09010309060608010c1808062818110108090303010621020c01021c150504020a11060c1902060c0403060e16030c0509181203090102 62
    0x10704042c9404182c821480d40c0d4102a0381843d084501070365111005142c22650182d078038908664000d1482013414604034003582c90300e0014100c402c241e422031150021840446942e00301c8036139104400c11001021910301d01d500406d01404039141c1691101981d80e035846100540c1c040d00540c005140f0f07591174000c0030384400841d40a03e4402d5005c4050034001100f451010740200e0750300c1c50001d690b921419070b045861803c00070b91380c84800e14100c007080e440c14011110f1010740b401a0b400680d01c40202c0e600340c2c0c442d61a07401d44a124401c000030060300409a8010b41181044400d041001800030b090517601c0304000c440d803110509090008002207400e6401094401c0d086a05888407181090842620408550802d451a90700d0450801850070030f0f560041c0d010309400300c0c00b003000388940b0740e0a86616800b140b81d0355011010021a520841c01e5040f54214400a0a4007000c = true := by decide +kernel

theorem cover : BRFrame.Cov 452338129 452517985 := by
  have h0 := BRFrame.cov_init 452338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 452338129 ≤ n) (h2 : n < 452517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
