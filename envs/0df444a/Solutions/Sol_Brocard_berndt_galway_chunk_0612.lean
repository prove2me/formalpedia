-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0612
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:44:05.807378+00:00
-- url     : https://prove2.me/submissions/412c234b-7b22-4dce-bf60-c13e9f18ae12

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 109892086 ≤ n < 110071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 109893336 1250 109892086 109892089
    0x6030b031c0804020a09090804050916020d050a090806040b0f010e0103110f01031b17090304030f060f1508060103120c080909090f10050a111213020d06020a020319090f05 75
    0x1481c043c10507640070340c4030840400e00306400d10582e02c416105a0415549a18000031b0083d00d190013404d8100e4080032001c1810455004a28009d000c03001f840d005030f64644000303040d03803c80e031030790000f4003140b140104100030006020401409240b086c018800d40d80c0e62010009080c00003400300030106194220350340114280040c11001044050501250b4100000071098081e00c40040000c005016038680c5010f0400c1d44402c2c60300244154059460141103484001d08071481110040956075140f07021405829194441c1c55554040441c1c0c1c560159500749440e61100c0038001627a1900c82c0c40988101d45001310840c4c14501da110703003981d0a00b05603108210031004020582c145502500300344058a00301070080c07803031403210410300054074140480840c080301c0c2c03100c101007c040300801680040320189400f00d43d0080b10b200c3c2d050368000301792000c030300701504440005206900109520000640100c0603114410f070100d01201e03030032800d001c00c680002c12441f4045400004c01c009206030b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 109894586 1250 109893336 109893347
    0x20c150406140405100509120901080c090909150105010504030b01050f03010902040f020a0315121e050d0309060506040902060301170a0807060e06010f1d0402031e010606030b031c 79
    0x10500900000500b040700040c041110341045408580d2504038125034020646903101e01a001854840108000440442690741500c20348128906000081d00000c187c070a14200700c50340101f000c0c10070304143c20160a8195030b284c02100c8401003503d814008034042d4481c0c0c2c281c034100ea400a0014482d640f0340030030300c400704094046654055481c0d075002c0000d6165409890401000c0a42c010303610781d40720f100101100e198008210701103424800800c4810040d1460b10450b5812400c64002c04c2d92110842402c207500c400002e125000b15002c1d060b01e40e07059030104103a180941c0060003595a401e0401003216200c3c003000f0750100d0244014800340400c014011070151780705046956034100c58427015034681000d4803c8070300d00d48443c40382c51807001c284070b02c030700405201510005240c2880c0a80c00000e40c1c1300085010010401e00042c2950f40410046808401c030343c4052840044498280307002c1d00140c020000402c0c18400008503908001480000038022280300c282510410032013141e0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 109895836 1250 109894586 109894591
    0x20d05030c07020607060614030c040209030604110102070312090e090f070e0606071509050c09070219110907080f0c0c0a0224030c190306030b040f0309080313031104020c15 76
    0x2003241045c040e45002078064400c0c40c015141200e0f4109070005690101882c01c2c901c003405501690040c0800046a2000a000303600207a21082c0240e40c4441e8400403850903c1070b0b0f00c00703400d40c0804900f8004254214113440c05440c08010784045a030f640d20a45070380c62005080b02403907680400400c100421218003082d800ca0801040c0c1f524040040e02c0d051803003c01c512000c40480d0740c0340707000010031004024100380312a007540e4070a43c614000303201946401204c0509001c070070a2070000020003840c192000e030356540041420341c050900440084c40716004455200c40d030805140400c0c0d020b0161000c0e00d40c45030080b03004184c10030b000c2d4240040400300140204c11100d0b2170080010784031103080610b12584d4903145c1c0b60780350300c1003120181602d01252801000e2510f00380051021402c4891f003d644681c011801211005042c901200c603140e442e441048117001c04038140940e074015026080840c0d020b10300003d0600c4100003001b00300d205a11076070525500c00340180030703041c09209400742d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 109897086 1250 109895836 109895839
    0x3050121061e0e010c02010c050d0b03030f0304030c020102060c0313030e0301060f0e04050c011706010509010e040615110312071206080307240509030a0e190e010312020d05030c0702 80
    0x1508030240e40400707002c1d1aa0049500d026071904a5480b609a00b40301c2c842d0704031032602c0203000728440c0080150061280c01642e448180d21082d440c0250b84082040364043c03043c1c221410340c4e038546824010010405110105c0c010b0203481d01249001c0408420303a400f441c6500ca14004d215040d55041c0e8151a8400401d5015501c07403d0010f00143d80c0c04402c00104400260028603180a280c101d0a0504580e40c0c1810300941583c012103014450420562060083c03d0107a030f10a04000183c601d496030b0781045900c01d06000c3e0104074035590741c0d203212486103180c848000b03a16086940540324001c09401480d413614102c00a8051480750229094102a588000500300e40f541c40c00c42c00d547c0003010503984142080f0074900d10540480400c0001805501d08001c20b0a280c08200d0b10707480380a1100c41000030348441340442d5500c00c010742400140c03001d090024680d07203ea200054030340034401601c00010345800c0c12541070020070b00001d800c44c9540e415266550f1224484e10640080e101607 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 109898336 1250 109897086 109897091
    0x912020c2808060c1c020717030a0207020901151205040f11131415030c0d03120209030708060412050304120807090b0a0804050c04090206032a040603020c0d0305012106 74
    0x2c0d04003081c0116809080340611036581c40c01c0c801c00a611802e110071400407500c0c0b04100c11000f0410003029458462035920f4416581d0f125071950402034050fa00000c2c2d44400352000025000e8240303036241c190000d080d16201d04402a00040c00c045450880c1c002d0524940070728480002042559046030701a8020500392408588601c08402ca40c882c86261104c40c03154010300c440e10019141088260900720002d04181581d00041004020547c2004003404002c036070810004040b0b0701610004c0c58081e08031043d05584480140c1c0d280ca06075001c1c0d8480c0b10021900a0180c424400c0706d02c6079070440304040070f0079081c0c201140c1e1920024030b000708110075008082038901070400201030510859071035081c541428140f4604045032400c0c514412450704940b040182c450800b80c82d440842040e40f0401400c0161030304c402d4880512120140b54000500031a50f42e4065000d0032842410300120340c11002a0541501214000e004440d400045000c890603118034444d0040507252080102 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 109899586 1250 109898336 109898339
    0x607031710030506100602030d0e120f03011a090a0303050901051201150905010f09060c060b0303070c0f09061809020f0301060b0a020105150916021f0912020c28 71
    0x850800c00000e9504400c1c00c01298001c00500c50100705643d00860150034083d91203190040c007a6881c4504a510b2003815110340c80070782d6008061184031100342e450b01d116070340d540ca80e002121441d8000d0044035941c1d106170700c1030640e0038050020341d190600090310960070b40f425510241c441e5084840080d0401c10200f20308103071000b4800045008021038050384542c0240c081380a440e001c2180c014030704000707146840c1c1000d254000308600c101c03a41810807035100110350408078007800f1462260340c1c140c400020644104641542c5403070444139100310710750b101500c03440c0c0341c41601c01c14454030481501f018404441550076611048065200800a00c040b038411400b0a0030360300c80e03a01c081104034004c211801e00903028050705600110161803205401d1080c1c4c0000c00d0f186c8040c12111030012540c0c034100800b40200090701c034294a05070200341e604c032031022440103829524800c036500c49460704007100f050300010f8500c134103200c0280000c5007503030f03058100d4240042e440c000301c1244406030700 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 109900836 1250 109899586 109899617
    0x308040e0a1e0e0f0c0105220b0307180b0f0d0c05120109021b160b0705070b1c24181119030516050306040507121506020d05040f05060703 61
    0x207100311001c0c210500843e4070942c1c081030034184070a4442000f816044505143d4007a030b401000c0b1f0b5054455005040e52000341d9840b031000b15001c0741c103c2d10791a5000800c0c040d259400039107000c0240c4010f80c0120000762641000ca05a008604500f11007a100707014074031404e039003900040c50094081c902542805c00c3d918001071956800e130711160b04298000b40207101c1803071800184000740c140000400151b10381052860800c012880342e40c80510020039040704002042c80840010708001c03200c3c68070742448d04250340029034042c010009a61514948100850402e0400003456404281800c140c5242440055608000f400e441c0c510990b10070580b4803000f1080d02800c0c00d954003e03403072040080700080240c100d03040600080d507141034060081c0046984071084070790040c1e0030368000c61141c4907450b060b111554648050780000c2d0501c00201d9200380003084c0c2c0c0c4200c8200f5400c8419612aa1109490b00d20403030040100521041c04144003c0c00d14400910280b88a40b1b071481075000c4052 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 109902086 1250 109900836 109900871
    0x1219080a1b0e0901120209010302090a1b03061d040b06040504030504150c061109090c070204020d060e0604060e090307030e06090405070503010f05010206010e06010e030f06090a0c0801060308040e0a 87
    0x5401d0004075500c00030480c2581001c0b61500c0c05803501c1c1030010030211981d00003d820381c2c814407009108170b4451001666200301c2c2d80000084602c2e400d92080c8503444090058054001ca00400c018080c0002503035411812100b00c04e4015030f0046400681c0e40c0794241400054400140194140f00081000050a501000e0130001e008041d0b610784280f1031981c60050140c4402c1c0c09408030803a0300b40308240b81503072400c107801c2e001180751600c0c03607481c0103500c0800c01074080c2e50102560180350480000d1031000e1000c20b030b4400c10044a040002c0f03a01c2c0e131210820001d0030f85103100e82d548248640740009024200c0c104048000901c01800c1940c041c0000d800c0c0e41049583c00c0000e40080010003020303101149100240909001402c4558140801120060001042e1a04002a42d4a4450310751420300031490504944402c0e111031340f501044443da1b55010303207012a000360b0450000201041c040c0304d100190fa0340022514075245c50500d00c020300c180c000e0f0206845603034852070265111000f0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 109903336 1250 109902086 109902131
    0x3250507080706050c07230105070309050a0b04031a0412050904150603090c06020a0213020906072a080c03060f04140a05010f0b01080403200109050f0705031219080a 73
    0x1a501c1079170300e42119024030300b03120307455004517000d1102010722015060007180200d2110003e00c0c1950f12941c02c1d04040724a8808c96024a800c00200310003c641821000010000e0ba8010301d80c0500c101d9000c2544007050034200e41c0503010050704056040080d00c25801000700380b1004201041004980070302540007481540000d01190351000c1940401000d000c540005102500141044c0f03d0a13401103103007810103600400f1101d40c005004481035a40d50305441084ea000f401e186c02c3e0b5410003403031034201c0b0b149580d510800043c80c400020701603800541c85001c0c69020b4090801d6440304605130070784c0c1801074030844002c1c116a1046010301000c020589071240140e002040d260210404503003243d003081c06880c100a03100c1c0030040407980003c1c54800700703069894008202c11070b2405680c0140703144500200303030707015850150300880f03400a6584107641c42241034469070f200350180740f43c10380b04200c0044250b00511141e040c0b22401550816400305000c10301041c004010f03c50740141c21400b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 109904586 1250 109903336 109903349
    0x90f01051303091208031504021b0a0309050a05010903141c08010608070314041106041a0c1b130203100b04060201020c0f0601060210050a020f031305010e032505070807 74
    0x4450300381c414141e204a14400034040071621031a184030b140c43d02c040750f21005141c44514041104124019111981141c030181c00704c018500d41c441e0581e6100e500d81c08190001d81c0000c1c55160041130501c0c00003694000c43d00143c5910200030300e107603203a400700000d90070080c40341d000300640c41e003280b1144080b0a000800d10365942e401c6605101d0003400800d030107454a020140703840200400c0091820020360825009130840304284204400600300303110340c0e00803900c0d003486000322080044008005d4130700c141c0303484140d4100b000301c0034200e0500107040c5a400d9000d84100000356118040f680210340251400180f410300f56181c2e0b00440b407591242d8400300050b0b500280d202c0c8850024448020200791900240c00c080d40340c2132000313517117190f22002c440c01d19a4038004100d02c011960704586100c603580138041e49a24240400c0e600c1000240c505039155400d260504030351000200445085c031220051017110400c020408803101c2c032082108440e00d200b041c0010a01c0c00d010401007005002 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 109905836 1250 109904586 109904611
    0x40f050f060c07031a07080112080c160b090111011103042603010b0702010215190e030d060f080d08010317030a0b150405121f15090e0607030b090f070305090f0105 72
    0x409170303040e001c10341d030050071a42044006030062040c60350a55140c0550740c1c220320103907218500c80228504086080e03009900f108454140081c1d101585009000303507440c02d0700e800d00326404001c00c0350f0030384001d40e840d0314084004000041c0020743d440e12440c035a44010003015012400d00212100c1c990080c0c200202e80203011450b1030440d80e041240d412000003443c0702c0075050400e2000b450304c002414000002054540405a042103420015202c02002c10001403141980c2d1700241c0307846c020350b4020140c03640076440b01e2080c105d0082c0c4100d8101c962080c10321040b1a051510000c840d00050185244c4644a11406005a03919004041d0849903a042156aa0f00d80002c01c8445001c1201807002501f00d032070342c0107412407150041c0940308001c03c00812135500d00c03589190356411179040042d0301840c02d504009043c90010b03c1c40d128000b1a1800c0115510010030814080c030111804660300c030340000090600c40c4603802c11500811900225101101c12904090940780700721100940b010707 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 109907086 1250 109905836 109905863
    0x30903060f0207030c02040203062d09010b0309030a050703171008010c09140405130f0f03030f090818012001050f070f020303070c1a041b050402040f050f060c0703 72
    0x619881800c8140c54000421883c0094030740e4040c26520a449019202c1e0341d0200004240c1c0d05c40084905000300003d91084010410806070384402101d0907449000c0d5010500201c1e4000c020011680102400c2c80118101230b48580c08503501d6021042c110104420000d07808500b18200d030650307001e40200342d0008c0c02581021011400c50f83d00302001d008204010301c04002180b4141010820840c0540c0c0215007540c031034201884004409100500045502d0310880130302c0680d08180300054400d40d020700241e08241542019681c0308134010b402c4820800076001049280d201c4144440e20605026000c044ca5030702d0312144600383c4a102c4443d944890812109502c184445680126070341040006c1c1448074100a41d40c0c040203020b607051082c4460054240140181007104044801c00a50304600c0c103450010a001503404410070003500003032021445203041c0c000e07941030f21405048001914a0482000022410076902c50740014040103410208001400081e01540c00342000f01c8a99 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 109908336 1250 109907086 109907093
    0x61c1a070309120f0504120204090203060c030921090d0501110c0307050610120813081605030606030c0306070e040b03070f030215090d06050c090406080601080f060405060a0e0f0109030903 83
    0x1600742d030f0990208620302e000848a00d030004140c509540403c92a510441c04620214006205500000e503141c400e600420107100c1e43d500045100b0820041035a040c5c1e1a01456203500c80309081c01c9030b0440d5400c1c8200c110780d003000351011803014050030000c0340414046023146c0441d4402141c058140c0c000280d60401e004081003991f4202502c2c540703c04509203802a461a41313651800000e22030680003403009240d900507490780c0d02801f404026036040d5100041280f540552610075280a03014000c00030700035203804650750b000c024024029010b15500e0240c101c4503103c4031380402d5400340d59110200c07816201040f9550140c07081c01f400030350150960041250701e007000c0c00544110b66080000480340c0d142c4650b00f1450607403004021076a911034081511081c0900b0348055000351511000098213440003c2d024100d8001a041c2c5224002a49420f5103d000846001d00654000c40111b6031150840d8011840422080c040d03491241c0b103c400b035400c1d20b0b007501c0240e00084040c001070052 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 109909586 1250 109908336 109908353
    0xa02010209330f0301050418060f0b0a060e0904020613180504030215010803070b0709050402070501050a0e01020c0717161401030506010905031902010e030708060114010206061c1a070309 82
    0x2d0344002c40980e0501107a08103400b01da100500540c1d01aa8489244ea0311a5039051850f43d4441e50150040c4808450700c22000000c080c1c4900052085500a0000480c0c6020b5103100505031000340c00c19109641e0f507002d103c0284d00500c40300603003059030907001800d0303003840c0d001e0030b442400b4920214150405040091918440300c902d8a10b070100c0400400100034000100c80b9002e40c0040c2c03068065840c27080a4410882e20340c0010b070070600000712003082220641c0701034403680c51b40d0700402c8046410041c144c01c0380a181c010017482c0c1c0c05031005204205083c0011082404260110350f82d4041d0041e1071901403210b5846046e030a141d0140d540b84547c2c140c010380341d10074420318007075150504d00400240d83c1c00321000a1162915281e2040041d64460716521607401c2002d000c4421081c0c3d5168032940c1c50b11b091103001a0f0b0075620034190302030340c0f0110780c1d140144402080000c0340b141c561f00d24030340001108000c8840d50a02120a040a500c020aa40c81180a034900151101050031300401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 109910836 1250 109909586 109909669
    0x4050411101701140307061101110f070302011109011d0d060e0d08010806160e01020a060c09031106041401081e07090314151603091403090a0e09120a02010209 70
    0xc150724101c101549840c00a8030700200c4d08070f0308c1d0464609101001560040c020036001800400d80000c6240c0100c0c511401444114840c0d0300801c94a9605d003914042400342c5011203000070a10050503004550100800c0801c610080014160701141e030345034811540c1c2d0000981d1203800c20b1103a0032007107400c0380455004044e18006400c081c900700d42d84a000880d402c018406000f00007040c001164402c0000440c15603002008200c0707080001006452a8807030310088541c1d4182d01529042814020305580449400b0214040f4801c4500010345841d07800800103080300e8000c2c50000ca140030030f084824064801501c40c1b000060444c02c05050300b1411056100c400e601400c9120304001c1594141a030002c00001841610480d51790100c0103806030107006000891911500c1900c4d0602100030704c10481c080790395154003592007203ca502d1250031100d11989401c400710180d6101442d00c0104220030301440010300d0000350740005003100103075001c1013450390401c44070303d84c580114142080 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 109912086 1250 109910836 109910849
    0x10f0b13021204080a1e09090b030705030304051c06240501111b010c051b03010c020712032a03020601060305060d02031209060c1b010e010804050c04050411101701 72
    0x41c908049102510704000b03020300300410f488000100d4031082d42c40749100c00d88070050850341c2c40b55090181402007070310b8241d0085281c02ca20f8184200039070300e000110b80c1c0403540041c002d1030400c0d01c1e0504009010703a54041400075100003045080000703a1520580307000485a22a001c5038000d1060000840000303030700001c0c11704c00f030010f1510707150000246811080740908030344801580300600480d4041c1e04081c0041203842500340340034409000f20313040200314200380c000300032842c03d018049039a0880d610810501d0490310a441010900c21035020b641894407038104692007000344050600040440015001a044800148000b41d4980580f507001901219441e5020045400083c2c48014200101420882c002200e2110b0785a4a080e40c400003003501c10f070750011640014014039060f500c4451400038010358460000380d0700829a80713000b140c011006040d690106800e0000404001c0c209991145070b102000070700769203402c0307522041d0503a580c13050514081e074242096200010f81010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 109913336 1250 109912086 109912091
    0x180510080f150106080606070b09010b131b090e0c0c1f0b15040f050105090d02060a110606030604240e070801020406140702090f0705160b0711070509070f0908010f0b13 74
    0xa510ba5424094230b503070540003496070350380e500c41c001c0260050943d8070038150081105000410b233803c0c26480b000024074a0503401c420f024944c4811511907849006240e40581914086401900c065000c0d10002e03440c0d10440312242102c56152202000e04500d0041c4242c845840c6501800c00740b0703a50310f061041a1509003400d08003d00544413500d1805940e041100100c3d20b00103694480282c1000e003500030700016919481100010241710000ca40d140191141070301007885030a001814603c6507070010b03072901e22107408030320659425050380b4441c800180c80e22810307a011101802610300030400740000607510f500d0304001174099010f01080c04c0c814a014801031001d40c581c05c110660001d111441245c0d01c0c0d031001015201802a15100410200307444400001c008841c000940100241c2e102c420805058400c5560303a1080341c010150003905047c040764240b8062100310400d8030a90400e0300d1519102c803149800c403005001c0f0a2080e617114404040d4509010b82d01580340c036040f0b8011f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 109914586 1250 109913336 109913341
    0x70302010207090905070906030f0c0b16021c0506151302070803070804080c0307030507061413020906011101050a02030105120303040b19021b010504020103050907180510080f15010608 81
    0x40e490701d05501c500c01c183c1c0e8492541c042044030a100000207820303981410000607860f400c02e28501c8101900c2115021901c0c000459807241c0441034039172040f0f000d40444100b1045900388451620000e4084031129a030341c91460000d0300c14003c042c840c2d80e03840d8000d130b02c010b0f0480800004100728280f190030140704001c0ca05c04242d004040305d9100a141c1401c20642e01c4a01d00b1402038130803074031007072040d00000c01e40b2010554400c1c02040c0d058000e8070203010b020707106086030f40745c0c14003a10940c41a075048901440141000c884042d840a414101100014454040786081d82d00c04c03211425081d40c0000140010300e8100740c080d05802d00d003c021421032400350b50300c00c8100b001512440c026510112004c800303124030f030102c4007040132803400c00346030541c4080c0e0940a0b0809440c00c0340860704150008400c00c074001520011200488151b5980020200080b0000c0001074000e2004c20a602000b062003902000b014240b2041d1500500400003000307010100400d068100c0c000300040c4509 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 109915836 1250 109914586 109914589
    0x50a02030706110702030a110f011b03120f021308060705030403050301090506131406090f1003080c100903170c0a050d0b04060f0906170a02031c0306050d0b09010e070302 75
    0x1600e20156000500003450001141401030134015810002d50502c640094441085505401c0c0c00c0584c1e003d0304c40d41c3c1030380100001500c001c2e000240c0f4440185107001050f021a1040561104482c84544001b03180c2d5003140303110302a0303032000101025041c80000200894001040030991240c120300d0101e0071414030340c3d001000c034441071180c10011a00e03a40468110f80e81c0448444144903015010054a040c104212018510480365a403007000769500140503010030546c403c0c0f0a00ca03c407007a00046080d80d8034003003180c010fa00c00201901c01da00d8560212070941c4180c0030b0301c0d03001e134903498442500c0503056200c6202c002c0848400c010188509128a50070500323407403842d00400c44c0400c0780e00686012500400722a40030140301c10b24040001a12807280d0300020039078500c0c820100703030440011140e50751560700c400c0082d0035911040d400d40340c110780d034411608240b04074030700030602c0b0b55500002049401b80f40c20a507024400c0c0d0080c40560142445211084003641c03018260701d03880c640 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 109917086 1250 109915836 109915843
    0x1103010501080c120109050105031618020a0905060309010b0310020a08070c02030115060f02070605090a030b10030803071206090c0806040c031d030403170f1c0e15040201020706050a02 81
    0x1049a05104068001c110301e1400b01e03044c1c680e0302d4554010b4007000c0d80d5440404014000070b10405d030103402950480e0400e4003802100400b520041810442e02011407040c441c020760181118604100c41503802061300d0740c0d04401180a89201e000114120740681d04250404030128030b40c09010344100102e0074140d81200380d040d03200d590741c203004090150070b00109002d00040040c20b1900e0509003400300d84075800507410507601038968200e07100d850711004252072900c18081c9055200000240410000e510241c0b9150b0018032036582000241d9a55a01e000f2038205580c100085000060908400403152140d0b4000380070201c02400a10382400b406490703190042c0c003650181b03482d0b0031401a8a806030308544548003d0802070040c142b20300c802a0b07120340160004481031840d481c0c9403048241014251076a0000001c1400c0c5464a40340204040c43c03d00c40100f5426038955040703c1122400303000c0c1c4020040205c0580d07001e23107454400241440c031300b81c0010091240504c9041c5a0b1540003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 109918336 1250 109917086 109917089
    0x2031c0b01092403020313050102270103020708040e04020f03030703050d110a1205040615030803011a03010501090b0c0a0c03031d0103050123030c09070c05011b050a0305130803010f140301110301 86
    0x84c00d0040e034076205c83c0c0e030052a152240d08042c09a41c00012903800440b240d042010005450a020010780e0400d580114107074820340c040034098000601046c05007100e541481608681700904001d00c1ea0b00910110741103410600082e004a180407030a141005843d000f4101c44101100059141400d80c02005c3e0200803882c1c042e581042e0350304002410007450380d11171202e00c26500b410f042c80d542d40e072404480f164800d00900c001928081e84e064908403212055038180c0d4016141c0400403818141e840202c4d4109540c00b150600c2040034503404540100141c40195000c0e90754941c2c00301c01c004254144040780540c6604052609004104035071794009010703551000c0000c01510300c0c04840000b4035000900300c040380d200c3c101d103080c40a140d400801b11070009209500034860301120f11900140460500d1840c3d0100741c08100d400316a0f0700c039921683d884440700c01c10654040705900c90280a8100360448500c001e04103209001443d00d8040407110410110003d003d07180d4012019412800306 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 109919586 1250 109918336 109918409
    0xb0f0a090510081f0b0a081504032102040504150f05011808030313050f0c060306010c1a04060606110313030b04030215160e010f020d08060102031c0b0109 68
    0x3100042103895640c1d2000314001c05015007113072080c03281203842e590300000518111401505d0982d80a6041c141041c014007251004400b41c0b80c50200710450918200000303201301e0800036076a0b26440d030594110050b00c0d00b040e122000589650600c030174082120320300c6408070f5504010290030840c413080c00854a0980b4428a8152072155542030361090781c8100741c1045007030740400300400070f1291400f1800291240602e04841c0224254040c1b00d4407070700d84070400c40e040310080001a48950080014295180c42600c0c2121a00d200c0100c9008441090750b0490f07000c5e858803010002e0a034000c14281000e62200c0c0a10f00e82003644c0003850b400c1c0403a210003442c100b50b0300001003d240c0280b20010400207a044d082c880c52500980020114400c85c1001c00030030744040c04440d0f19441010444c4041145400401c2000c0c14180c040c1c9182c0310044c400e40c11403104001c60a25500907040d507003210fa25445d400b02d100703d50b900000d8000041908018541842d1030120781e6014424403004000826 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 109920836 1250 109919586 109919591
    0x40203090c190504020c0c04050c04060507031b0506040c03052109040e1501060c02040f0203010e0f06032d0709090206071e06050c09090106030c090306050c07020409050d030b0f0a09 80
    0x5034082c1c1c1a03160301031039002c40c0d8410720100f0103610300360340820580041801290f00f04043d95403c00681e40d60300031070090200040c010700c541c07000203025960500052075490350301c0c4dc0301c0380d2507902c2030720f00901140e00700c0d001c00c9160410820444200300324001c0040c0e6103180644403920700207020980c00741132199840f86841e00c0c3c02c1c21703240b1030a00915151010100c02071b004c0e90385a003400341045040360b208034052441c090203c4090a440e20943c0d0503180503245908140d01d502d03003040d011000207007425501d0300131040c407040e141e070302c0e034070256030f01600b01c0800142c0c2082d611034181002050341c00503269900704404080165904c80440700404d41c007580e0501c4907030704e000d8010b100b9840c032200145550315001c140113101d0380d0301003e402026012141d401d00d41e078076503000318203492081d04214041000341d50184001403050f005280e210701415a2142020203a4000806442c00d05c01c05580541084400d845485d515005200c081072007604e40e000240000c0c800b0544807081441000d00490313 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 109922086 1250 109920836 109920859
    0xb06062704060e090d0906051207030905150a0b040f0e15072106031101090509010b0703020307051606020601080a0218060102010b0406030303020a0905040911210a0303050f06040203090c 82
    0x2a41c03540701c103002d48a1800d081c000ca24007465403d0b03480d4801c3ea00040410000d800c00104107205408441c45c19a442440d252a5103030740318280d014144002e011034090081400f01c081c0d054214011a100b00303000314001c01d6581d50003061000f21003680e10b400300c10600b040c2c01101180c600081c03883c0403080400d000780180d50b41100448201d05443c07a90041c0721901660400481d0b1160070600c26030380034442071010314100d0001540d4001261280c0f6400132607460040120b81b0211015102081c0a07005483c40e1590070340d40c050400c400030340050312001c94801c0a2014550422007980500a50001029021940d400080d090b00314001c0c0800c1092603940080c3d5240d20030f41229801e400d02170400d000142c3c0360314000d00603400200741480021911940040c9a1415010f0506015000a42040503680410600a201044621901316072401d0811101100e2041040d0303400c0601035600040c807814140f01c000e1109002810852140c0d00600c1440700802c801714420312101c00441c2e0130203066 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 109923336 1250 109922086 109922089
    0x3010308130e01031101090801050730021605070806190917030f010303030509030f19020a0c08060405101b0c05072309060d0b01030312020706180b060627 68
    0xd4500d600b0040c040c61401000004028245800c0600d00100f42c0b030f4405017544035010103081301c10440b018400100380d5031401c1d008c0b601081d0b0981d4908881881182c0c2c64021000040503a4891611000c41808a5840d202488014800a030103024400081c2c40c407414842e601028040c83c0c1291800303141e40d10110071040240056401700c0b4480c412120366140d140c031900d041150b09003480142d0103e4108400102408808000c42c1d40040711102d80d80d003801c014000b04d80c0c00100200d07520007580705401010300420700e07440b0484010541c29006003528a05440d10134180b00c447c600703a400303c038209a560510308820314100360010f9030a1401100710010790501a01d0405268414010300d044804042c00c082c49213858445020010384010150b6140c0c40180558801c3e005000b4000d4041c0c5401800024072414040306c54407040d40b0b005d808c0207000d45603d0115400603200c42000c10f16404c0780710410910141d40c66100400b00c40340d909140742c099004e0380403a80e821018425000d9148000c859 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 109924586 1250 109923336 109923367
    0x110708070305160b0708090c010f09030311010b0409050706030609110403120903081801080f041a070201020d0c0504050f040e100f1104080705010210150b210403030506010306080a0803010308 84
    0x70f64002480b0a401e04007404094108202600c030403606d4096200f5800305035000750035a14821a0300d99820408074610344086580000c00d103000c51480d520341c1060081580d45004255030180074001030100180782542c003804480740359016280050401c43e0110712004410f056030200d9810489185890b4088042215080c207190401400c041020440001d40444185401120b003000c0c0c0b00c089950300c41f11030000d0910350440b0010300d0404000b001c5912030001c89681508050a03000150401d044e05003014140c4174450782050005201103010400c0d441d01c144441d8600382d05842c104040030300d07048050b40f515000400c0d0030320a611005140c8200307440d540100110350764105659216520340003215140c0701284a0503005101d054520702e5005100d12034414094003100d24041241d240017484000d5802009a01007000d0034141902841c440f504100c43c8110720a540015981c0b034200009803c888450300007410b01d520800c0400000b41129040302c0c15a9082100c2940f41c1081500e103404 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 109925836 1250 109924586 109924627
    0xa1b030906020c010606120e010e0d030e07080a0b0a0f090507050603100315020406110607021c090e040501060501090b04030f08030402060f040f0e06040911210d0c06110708070305 79
    0x1404e61030080300151180e403000d81c007002c00d03a04030014000c0c0540886190b0036205240d10420350703904969903050103e4080e03800303821081051015950030303130740d104066803c00e000e800007514034420300710412070040194402e03002104040c03101003040000c5501d179103a84480c14090140980380010110f1000b007450541e010003160302c400a04807520a8400c00030194000e44101804180426801d484010f00071495910698440e4004c000f42c0f6040c03810340500c02c105155640c18002d041c1004183c101582032545d110741c0c0a0000814240d00d0000010b0444035280d02044605000303000c10b00001f220b06480ca080036410104940e140c0c1c6940c0001081031040008141c02d40c1400540000c031000182601030450754660020816683c5090501042d550f603a0f40c02003030755100b10464038040c50100f030140b616030140908800107000c40c015503480d1403030640c0d054000c50b20100c44442000950b000d010700340040441ea190600030103032b6a552040c095031000405202001c55100f5501ca02e5820425 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 109927086 1250 109925836 109925857
    0x100e13020d031209080705060a090218040f060507030b0a0b09010f03020c0106120b04120c080316020a02040e1b1e13020c101406090603061503010207020409050c01080a1b03090602 79
    0x883c01a8620780f08029501046c4c2c111128000c0a0001e0003030b48082c40b071000302d81e4003d003c5840071903402d003004105c10001402140e9400000c1c00ca40086891441114440e80780c4d520300080300604078040102034040c0780d001c040d290004100c0070042d641d221480360855100c81c14007588030a244903840b03014110b03d4200c2c5141625603542c0c2303014010340f0764ac0140680e000d48070441c030381c080c03178402100c03050031145010703000500800c04181004081c950389070900b000c07841038503c651615030004090342d06581c04050703640d21240c401c5003c01c9411002d0540900d049862010340000c25880090359401c4044851080e90002008a00c40e51260125858002c1c544240c54100318080c20140042c0602180505214845c900103850390a0120403140660b20060043c007080e51196543c01961201c9403006806540070b0200100586650181c83c082e184504040c009880d601e80c001415900d005007040300242c10308400c15910790b041078003200c101189180101d039010031410a0700281c4143caa100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 109928336 1250 109927086 109927091
    0xf070e060d090f0305030412090f0501081509090105070e010305130b060607060203040c0905010b0a0c110103060810020306030c030601031e06020f13080d0309020105121b0f03100e13020d0312 84
    0x1802013550040042d0300c290f1003001c80c2c2c1c81000741c00504031500a441d0182501000c02c450381806103600466000358000040c0242410851703210b8082405010180d0310220940e45540500c50300c190072a5000d203c4102c00c0c41c082181e0700c1c02032000880c014000340081d18a640341e6010800645580c405c86d04002d40202c41559242040d240001818403a8070a84118078640000401c409030703124112007051400355581029140d89864000ca41485902200d06041d500d000006880c4800d0284d5101c800080f41c0050700d0380f40c0442418181101803c1c158803c0d0070020050000484c2180020100e2004050030540c02c440303450104000c2c0700c1c1c0c0307146514448010546841c00c10703100c3e00303034000c2c1c4084400740e8096680145041c0d040d1098214003d01044040c40070000d1007564803542d070b80c01050915013585008414211180381ea10200170304022645c000100300d007148200e264580100010002c009561030319885a0510400310301c0c0003445203043c00700070030500d0b20a4038800c8040c010110704 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 109929586 1250 109928336 109928363
    0x80702030a050607200d0e060405120a1b08030f0d090c0305010b2107120203010b1909060e04020a0b09040b1e181003140313030b040b0f070e060d09 65
    0x3e580383d074119281c9000498600607071114114800c1441828803921004048103c4041c1080c2c40c0d03030448091250b00070714140800541583d403080d55070040d80303005014110090440c01c02d09490b82d10b840745000d840419010800c078214000048886c46004240400c0c0c80c1d811240b41140035061800c00606a00d826000110902c10194040c907241c00c000c81d183c0d0700514130001d83e1060280c0700f01d0100f01c280c0102404121482010314080646840100001130010f0183c0c0080c0e0a400c80c807202120f81c00322110f007030101001d24400c030b04c0940b00004400c0341c1c078035007a4005004424680104d900c1424041040b41058580b5000060290402002c40000c420b03206060642810000111441903080e21000719400e40000f101038020300200c485a9192400c5885264114001c9a0103560603c401c001c994000e4500c001c0303d002442c0700d049040c43c68102801d0609222602800c100079010540083c0504035402503120f500ac1c1c2c1e015580e5030341f00c0900f107642600811080c5030290110802609 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 109930836 1250 109929586 109929593
    0x2040306050a05010e0708060108061c0206030a0506010f02010b0307050d030509030709021c06031e081e0714060708150310090f0c0f0602030306041e021303150209010c0609080702030a 81
    0x80b8140c0305d0000c99000240c0d581102164410406d64140d0302240d05c1c4804200e85007440d08000c000b441c2c030303800381349201480f60b4007049140d40126041441701e5568400c0c40402d44e4072500050b20350880e80b00902001034140c0010b40c403900a40304092051544200640815021b07009550485100805581440d0ba894200704041e6000000c1c0e200c01c5410025180a0b0648900c0780c00300741c070740094618000f8109400948080780640c40c048e90100014440d40061328800710140750381d440450080c83c0c9a500a203001181943d60840e580003e8110800300b01036140d20204075a40b24070a02c0002e5090b401c04404a0308107107a0401001e10182441210010f200c990054409560320070745540141c180d6a4024447e0035010b4040c800040c0c0080000c1500c07858980c02191000c40800d40305c26800d4852020318040382d2149039000601900800b0410520551a0f18001d0403400000158a403003480c1e8002000c0d030200c444000c283e20b40e201101c0d020300075040191105598044c0c00c65961410070304 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 109932086 1250 109930836 109930841
    0xb03100905010b04140a18080c0a030207090204081c09150207050f1f0e030304120f060c02030408030d111306080108160311100201110f13051f1202040306050a 70
    0x40a40e030390b40c02c040e0200c0300c0f0b04040c403c4000680c0322003440c01c000d481d1440042c01800040d840f4070500002e403002140401c0343c0c0c0c401006800049401420720420600d40a030408946500100c06144180020803003c000860f41c44060b0161401389070b0040249070042d54661401d41001e00300d80d444d1400034180c0f50700010030782d00b62901280c000265403a114104087c4003030790600c290034a195a031081c0c03803003030145030300103990030005060728201911042c5840001d40052810369035104820007690a11900b44140c00c1d84013001d2003d140307042d00309039041e0703a280b19400040194643e1141c1f03081c0c030355160300c00392000e250780202c02c0b442e4603a0780c820040c00c91000f030003002c00c140140c10211444245800400045a0303200030341c1400505031100300720240f0b02050241d420355480300a0346131000c0940000385100244e403c00701f929084c0213020f1150303001c46c03034016274040d548100b03c00d48040c084141d80c6400321018a02601c50f06010032000000c1d000759880200014240414840c100c103954 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 109933336 1250 109932086 109932101
    0x2210d0e030a02031c0509040c09090507020105010f05060a0311040902190906090314010b0a08011a12060103023a03030b0306040c030204020a050f18012d030f0b0310 73
    0x1035542040e030355244810903480d41100c51000750305071700c1810345040d041c40c1400c0390140c0000c242003031410005150301040c20f45402441144c0002c081280a010f2281036104103a00100310340b00800a80d03040c1328000480e464140110781c420940852440d030018441d4106005100c00340c246181c81c0c0e941c54a851001c0d4200c65005603102d0040c0540c0c085441c4102003c4044964503a14200700c146540c0300c0d40c12021065800108554071162210690307110003140100900803c0000110a50181921401001d225007000d1062081e9106242c40747c00005026040d80d40454030b58951410344110703002c001101c1e413a076598a42001c664071145080d121220203460303010380c1301441001c0d01542003548880d01128000c00b05502d8100030300150034103034007903c60544a82400d5103080140011000540c00004c019a003da00310700054a095030305c01855402c0e8023840a41d010350440c0414111790001030010244d0400d80c1c0ca040101e0800b03038035000301740d076200003400f80e4032045554200c02c070251050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 109934586 1250 109933336 109933363
    0x220807080d050708030a0c090528090c0801030b10080601030f02010207140d1b0f030c03050709090201021c03110f070c05010203040506070f080f030906010e09030711010c0221 77
    0x40007001d12250380038204035521968480d0f4198516595079603154000e250b0b413181001004000c0902041e03503200c0c10b680b60030320700b6140828802209800300e003269500742c580210003c85d051610441c2660380103c116410f49902221400d8699200030034442e20b0304540d403080c41e0500c500000003051014420700c0c60160b45c000e0742603424181c0c940c0d5901c00251503c0c040c160f0022820a01d56000c9440d802181501c0c00350175001806059031141842110f052940041d02c40103c103040800401108000711401000941c81c2445518103580010f13450b250030049401230000712000320003140e84a03074041c541c4140c401840c5070300d41401203020141904412011108185000f001207020340c0004103607021110000c11003858206155908050360108000c00c58420300140081038a020000c005075100b07006007030041042e58980421400c61b50300140201d07969410401110012403210110410064002c0c200078040320031a2011032080751440e25005200000d2402c060ba4004012034204901000d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 109935836 1250 109934586 109934593
    0x1f050301140604051c02030a140106080f010c090e0417040b03040210030603080d0e03090405040305091e0901050609180406020c0705031207061d0304060302070b0a05090703020622080708 82
    0x1840a1180078403650003000e40c030000304200306861781c1100700c040c2403241c07029098820780c60103a62140041240b001ea040b05c82d1351901d0040c030100004100740701003003031a00001c2c40b14060409010f044030346e81e40110084a144a40080c003800071000c1c1c5c20041c4248074072000c1d52035503102c40021003030700f040d10102c0c810a100090224054401d00590b01030b82c2d040045d0341d2400c0f800150f8000217081f403541e440e202d03003c207001844840d80d03030317214640c131482c01380c0c03900c9564000705010016104481c3e10401640c2e140040d650381c00f52254108241076403419180d00c0c3d540c1d801c40c0009040540402c40c28480803c400040004001883d005421040000021500c02c03d0311141010344403002d48846081d00801480214003248183d040400c01d400704420003040043c810903118156845a0030503c0481e400045020401008040280c0d111142d8a4100514204840d04989507500c80c48040d1040300b01250f00075a00c004281c2051403200d10450f030b8044141e80d07002d0075490348074910941d1403c1c003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 109937086 1250 109935836 109935869
    0x1f0902070c0801020304051c0309020405090304030c0602060c180a080a060b0f01020705151305030303090102040618050105070308100f030b012301050d0513061d0606040c0504060e1f050301 83
    0x50b05000307986c051039100004c1c1101820b100040e0300e4407111030a150741056221091200035031180c4c410b05004a074480080d541d61415410141c84100c3d40e0b51001085610079010440340e1070044042d920b0a8003145820150102c010700010040c00064020007083d014403806007040040b00e03481102d070b24100395900740c8030740c0b0700e0f0f401642c41e21b21070711074181c12559800402003074800301b0000b00a04e071001880803001c65201c0303020910759082160303181843d81d80014107112542d0845061506480d181c0d070314446d030a0030440000c04501800a00800f80060100894480003403000d242c009082400d45841c803095880c1030179604c2f00028410031901c078026140c01c0c42021600c0c188840203803c10385a1700c0c506055502180000c0c02c0003400d08018008201400e0300203480b6000d455841c408582600c0b40c400500c00000717081c000060450b40c80b86183c01c0c08414881e400206641c01c40340b00e4182100e50803002d03004501c00c2210003a12401004020b0801c403007030354010010f1416980506c4000710440c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 109938336 1250 109937086 109937099
    0x10212130516050d170409090f0c150c02010309170a02150108070b1605010b04020703080f060118091518060303170609011502030d1a0f01080f0f1f0902070c 69
    0x12000c1c020150054000941c000c08201d000d545c0e480391840700c0220b02c1c90242d07181c000c50110360419500315200e50402010701d091068260940b0b02401d00001d02c040b1802440d58080c0056507054002814540c650020390240b10060801c80160026101d84a030b591000c0c07203000b5107130118842410600118100040790398000090240706682d100c8034024580510300c15071096140c1201d1003259250b480d0302e142051500c030b90001d0010f1912031303204c0040721309045040011000d0300602c05410404003814550b104c690030303c088411130383d600c3d0b400509881e1580e820049121990000c0350f041d941d900c0480c0d141241e42c0d0180007100d000b5a20181400007148030203188020070340f8002d90001e4480c00510010704440094511070003a401120300e400d00c140c044070300b941c02003004169040c034800c00300701c0c1030709080007100c0b0340f00c42c01d10706801d00d440e0007810800d1402000d8003504d0f0030011107000650108803540b00c00890b030480c49907030f1421036540d941d0340043d5114581c02c0392165107191000902 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 109939586 1250 109938336 109938373
    0x1501020c031c09080714041d10050a05060904020108070e03241b031510091206051b1201030b100302090405010b030d03060b07020409080d0204170d020f070e090102121305 75
    0x40d503141d00d90840500240d04108005046069042d03003107001c0723103041409500c40c200004100e03404422004100361510f00c1d411011a0001401c0034054040f01e410400140c0e4440c0341300c0c1d88600b1a080001b440c2d0208000709103002000590580f00140009999419a1005240506c910300c0c0c1800d500c210308800500b0301107800241d40d1024202c0d0082103501c0a03282c59042c4504950b800d1130318000180d0f407186481d050365400c1c1c5095a00c1580c035020b03c041d1004081c002c00282c04241d548a14154603d49044580441444007400d101c05020100d204040e90341c141200540c2c00a20007000c600305400d03d54024449690090310074424804c0ca48030182c042e00902040307074900c0c0320140c144038081c2c00348800303819084400c80303110a040005140541c100d2000e80b000d42a4141c3d218403602c400c1a820f442c0911201202055502203450301400c000005902810303200501d090303410a0b100c10791600d019000b01d0300303020088554002000b4440000400b00e40314203000b503044038101c00103540180302 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 109940836 1250 109939586 109939589
    0x60105030a030f050d02091f080f0601051605120c06010f080d0801060e0d05010c05040306060b030c0714010f050a0e1507020714120a1b14091501020c031c090807 71
    0x4941d0582260304194000d1018154405d4401000f61501580d44001440890a941c5080c0003c48000d50307124000e038800d801a6100c2c0c014000d180d00c50030a0000078105000740e01c51490034201d40c1c80581f042240c1404040f224010000700c0c1521100700c910280d40b607000900440d0040f0109460009004c0c10005d041c034156529600d8407141a424080300321401c02c014440590041030a402c0a4001402441004100f000c6640d40540321400d51406e03105980c2150305c0012001003e0050000c1d412036081110181a0700c0ba000c00741030310003601d03840c0c09440303c2102406040d02d000c080010780059038016034414003640c4241d80720b02e80b203035841c03074403024055680000580c407d02060024000c20b0000221410700201842100c82106031803d15005611200300c44a1910140700d04091049601c0c100291a81e40801c400d24400d402c0403894082c0e0060580c00e00c54075038090228140d00922000100342d0019054074400011803070751440811080c03032160000f510f026000995501e02141c1c960 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 109942086 1250 109940836 109940843
    0x705032d07030209120601090e1504020609011b060513020f0d0c061d150a09080a050d05030604060305010c02010c080a0c020c0f010302040f0e0411041a011d120f060105030a 76
    0x80a4031808002c900a401180081e90001c041d10190b210184081101d54001e08170700f030f0081401049101c40905240b6481100c22807042140107020040c1d40300b20a0f0b900c1d8030804e10384040500744040000136070440100c0d0241c021032602040c407c01d00200c01d00c01c14924002d8900c00d40c1030038180103009401d52030a902074034081c0014402c0c1b225070b00c02c0c010104070049007007900c200d00d0025030000d100c40110120f0001c94810000704180010b810504180080001030b01034000f041071038a840c0d40316040c2641e05804c005000000480307603629644020041c581000081001d105461000307402400c8941440010400030000100d03949514001c0320388a504983c0501480c60629003440080c0d942708030091b044c0b6800b80008905102480701c1c03200102804e080b5403a4500b003508001c01c40022080c0c801e4021811300824043d2010041c0402103009000e1078140c0c000010b0559941c0c0f0480d5041400d80c0c0005100e407965400280029000c04440c145002da4882d030740e071101015600d203900d52008 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 109943336 1250 109942086 109942171
    0xf04030522090212060a0f030f03030e070906031103060114151804020c1e071a0c01060504020c010902150a09060f0c0618031701050a1206090b070503 66
    0x3081da100780c0d00803840040c1d20402400d64055210312890090b81c0002c0703000110060300c0e5080080314540b140c032910040c1044910401c0c2c040c1141c444001221800001405040e10381221200c562001c01c10a0001e2241140401034952285094656010312286507031207403103203800110300c01c089170740c100042c880018040340300c0740019149488941c12111714491259990380c2015181d44a5000404c00300300b00f580903000416400722594100c040041d440509544980300c20310411031104c3d10380b05401c81000c08561540035604415000d01400e8001e00e4102c1c0c004216a21a0601508121901e42c42119000310a034617607007d26103030380600c6a024000640e43d1404004244c020b1242c005901c0b024a00408120341c2500c0e02d6064580070f45040d00005000c1c41601c0c1410350107001c1c2014402d090121900c65407418000902c0c04416000b1b13089200d400c807205108100142e0300400d0190340c84044120289440070014240d900308845a90150346002d030301c800303403a80080202160702c480d00d07001c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 109944586 1250 109943336 109943347
    0x21e03040501030c030209090c040e01080d02030a1b06060b19020f060103030f0c08030f25090608090f1605030c0108011206020706020d1d0f150a0207030203121302090f040305 77
    0x1103000c0c02d0700d130b603941003896030810a511180e00c0703250946105000c019074071659036282010806610070140d01c200826040103102810a59022086400c1d2481500c0d21850f5540c0844421050110304c040c010180c9141520020340707240880041c00c9208408510b0131800750310b00201380e0f1240c001400583d440d402040c01030001070300030241c06a60210314030345040d103508a0b55444c140c60348151095001c055640082000350a08041c0f540700c008010355402e01c4e0180e00d10009803070066240030b05010701c0f0b18034000404030402040b00e10303a400c48100841c2e517103081c1c2000c800600b40c00c90141500070300520900c445503500078444281292214620350380010580d0300c6480c02034000d600c0844205408004081803c14107015010703440131225000c150f56065079684924100d015496688146c11400c0080105280e0040c1710754408010800560703a80110700e004ca007148180d00086411031300b04002d1005240011409c550b4191003039031a96100e85903c002c45141c0c8804440003400140100325 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 109945836 1250 109944586 109944589
    0x30d0324050a170c0604090501150e0f0103110f0a08010e0601080c0301120201031d060a15080a021e1210151202010c050f060106030b03010b060304050a021908030301090606021e030405 81
    0x10702184003c2000c003035500c0c0300c102d8000205198415030102d00d0158480005020000d100d0100307c29001290820b80040000103020502d80c20400d001e0700d05140d910020b00707035204134000440c0e40c005000c205140c0e0380c03255503030702408141003070144c0c5028a1401d00003d00c0c0c1e5000c1c900300342c0100d00e4071401c5815a840c019441400001070340e0201d042644038040c004100f814116003106c054110406003c0601e40700d14440c080703540ca0080708c0d00c0c41010340b20400107400003041d0002429016a1032190300030025070100030320403440000c1c681109079071074800b006881c08601e940b0701c802d000c40148488002034040c921550322078002d00c5105903c0f403005800541c00ba003524600c443c03044054602401921340c109003400400d9211501282e00c0300280341d1180f07000e11541d1f000c2c107070440b100f034254109601e9295485100e00720090203204050303800250740210404040040c402c440441c0e65941c0c42c2c24101021708400d114681c0580306842001c0b84152403502c600a0004032007000f107003814503160 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 109947086 1250 109945836 109945859
    0x8030a02031902070b07210e0f040c0903020a03080306090a0203010305071202180108071502031e0f0c0d0201020a08060409170d0f020403050f160308070b060f030d0324050a 76
    0xc0c142c815407145441c0000e02101c00805014090f0040c04d07094051440034015426030000d610051042090000c11560b10769507004451840450640700007442c0d031401c1405a03078800e1030f608065403101a40d0b4001003004018402503200700001d841d400720f69210b078007100b4103a020038040200560451034081c403c645852010031642030006103d0301007026445903880c0030302c00a030420300c00c54000000a2100c401c100d01d080c3c0c0020303072520045103810101412405496413805100d0703a80f2100080144c500c15540082d40c00c0450070b1400d039a201000c1402c080d000790f1101d00c90002040003d4001007280c503203841401202a0401d029002c481c1c50100922415401100c0d9082c605030f80d64074001e840a050320180001d184500c008007440064904003034500b1840b014007140e051031081013800020031a500703489211b41c1c0450502c17815189c80002a203104805802150544101c148601c1c1da5941034004c1c1c055039003100c1c1c60203149801c9810362090303116a406415080594000c0402c550721202c03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 109948336 1250 109947086 109947127
    0x11202010302160f050d02030f090d06061502060403030b060f07020904060f090503040906090b01320d050a0b0103020c150a14100e01050102030712032f0d0608030a0203 74
    0x501d001460281500141000b4000d810019540090b120b00d0f140100603080000000002c40790005601b011400300f00380440e4814400021700074807100703d4078001c00020741c011501030034004c0070710000160328103402955400200c40c1640040c0c1001a503007001c2c03d015049510f0780c6089045645082c0294090080d00d10740540129a51540c0380f40128071303d5007030711039254020b102d80d0241da5280c0c03a080074a425036045130483d0032000c1c41c054600555a03042601200d51055080298028891010344a0b002c80000c00032280810400252040c00101390b50116201e0207801904000c09029000110201d01442c00e0b4116a5803007003121a091480b0b01c1d4209500c006130000c0411548140e418910707030241e0544428000c2c11161009010641100c040c5070b000d040284021800c10ad0036440302d0015204a10180c414565600100f014034a000c0041d4444110024280c41c910a5003000229141d8041450080040c0c901140455209408012542d0190056000310f081900d0b0032440d0a001140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 109949586 1250 109948336 109948339
    0x609040c0305071d09010b09011a04091b200607051608070303090b010603050c03010e04080d09080c10150b030606071209050111060f0c0307140d0c020114040803011202 74
    0x390800040001c408114003030142006000003201448602c04130105200068910226641400c01742c81441d11000d0015045665a9500711221203a651103034046100c1c0b500082051410000c2030161440ca5041681421405559403426000c004040b41d914224821100c05a0340000c0c000c1420300e4130032406030028544400069004669581c1c83e1b504a900c40c1c07100301d01194448245000740010106a03500401080c101030080b441d041c01403d0b070920050142003d1a000100810203100b40c80c010b0710b640c2451031904201c1a441d80c00c1c03401c225040400c64281500c00d500b425010582079024224060301d0313000c0c02c2c0111505240b142c92440d00020403054100f40c060140b600490000c0318a50210311603a1940c94229081000040c4122000f00c4002c2090b44072a0a000b01e45011581c12540456030388182038694448680845600048280661903841d001c5402062101a42d001e038814400680023003015125460941d80c072420202e8000d805903809000400c5140000e02640a12910 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 109950836 1250 109949586 109949603
    0xf07090b0a08010203130b0c0c03030403050304060b090411150a1b02030a020319170702010c03080a0e030703020f0705090709030b060d0b09010b09090118060b0d1a10060f0503060904 80
    0xb200c502e01822a00125000a2000010b415180912108481841d0440700c801035061400780140c41450356480003a00090420800200003000d001c55607000d4400c200c0c0c000c00c441010304090500c1c89856201680d168030804103080356090381140a000c550b201401ca0711840d02281410b4070118000b03000d000c085c0e03010300400e06880b00503541402201021140426121b9100b1124140b960701054482c40002640a04210850141c0c0e0060043c002480e0b1600d0210800e681e88000d11f0050090b5041e410344c58071004c104001055004107103060365216900489440f19a5802005200c0c6800c0c0d911074085100902e040c40801c0100c110543d03c000301034034006012a090707507401051042220701e0355480e556805201020b140a40016410015017002401640c1c0e0f0300802c1f824044184000038030141e5240a180490b1700c56060091195801030f00400515841c140440d580d80030403540d004261249007004903a860050b101c0310240e1029035101402d6a480d4024420207000144c02038034484c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 109952086 1250 109950836 109950839
    0xd2109060c050316080402130504020d061a120105010515070305090a0f0503010f05150d11030a080301050a0e01060206160c060f020a03061d13080d020c070e090f07090b0a 75
    0x180035018449140c5119600d81e035032881c150f2044074480075603e40010070040a6820300015a641d04e0903464100951034000510343c859200040043c1030303280004260b94100040600346200e6002d08600001707098807161552604a1165404c90790240203495000324110b9903104000005406004024401d0400d81c2c981500f010014144140300e6103c0e0008a0a5400a01c240e04007802500340401280906000d076040c4a059400d512000c80441400b50080050002c10b1107031100c81c1000300c1c40c010f003e41f9601d01940c10504259030090107410b0080a1040b400103400f40c0755900c00307040301d0217607000d08155190001d40a896241301c00e400d50030403800c984e42c1c10201d0084d00c600c001500300843c0050303540511765005001d41d2074a40c00550340b4188030343c62000f08502c0b01c003e0359114114000c1856208840e180480d094094038203451090341c0301040480c505100000c000023601d0341c40d01030428030350f01c110100c1d540ea1004d01401c0c019410092007005000340e660001070b10114024904007026 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 109953336 1250 109952086 109952093
    0x1305060d0615050a09290d02040911030d09120809041b121b02030f03060312040906180c021c09120501050f07050c03070809010c0f030e040e0d2109 65
    0x300c0c1081038007444001c201030300f00014540030505030000c00304a1402d11010350980c4009081450070288071300007419411102d4903564420102030320603540100100441c44082c280090300b003510201040c000d00c9940b4007000f183e402584240102c2e80000c640c030100060355512000d10350401039410350819140c3e8143ea04200c01c404082c480c1e038403543d031011418103401e1440c400ba1400130403020071060003400781303924840d4044103c604040c1c95803d007680e603442d65400700780b4210060b41c08145c1040c01250208410040d6007010084402c060326013041800d0f00c0e1703511800c8454005e0703240c0250f480401c281801405101c3c080c15900040c1c100000d0456458040991100c0303a40c00440b620395580003040800c900860b5040d4001c41c061070040c1c10800e22081d00c50307592040000150580102007528282e0340c0c42030241e008000c0d44800088090350151501505881c51760300120b2146080c0740300c07030414220020f501040002695242904030350940620310700042d03040c603841142904d42380000c012 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 109954586 1250 109953336 109953341
    0x15010314031e090102071a040504150806070f0e0a230102010902060a020d110a050d080c07120f030b010c120c060e0d170108030a08010504020d090f0302160f051305060d06 75
    0x80041008025640c1e04100e00090520502d50400d40e80030910047c0510310030551003d60f4250b500c2a80c00281c220700000c0c0955580ca525400020030784599400c00c0301d181e9104d60103151540c0d09885071a9030205910411000e00c9840c01020001c1440e05054258580542e5240c040c0750010700001451620340e4010580c031b6031104004901503407100c00c1100e0741c283e100d607001005400c1d00740584844000d0340e1701c0030b41315040081c01c801000511004903034086091811103e00c0b41d803000160b1114281d459010300006140035030700380403900d0020100c00550107490349804003940580084411508070805882c10034204000795482c582d900d1b040400d440d020040c40d1000c24081e02c40c1c2c1148900a51030300b2401005801151440e08144062001c040d000b44071141075410455000d0384501104c030030180103000c0c503a40540440a603240c9001459000f190605000005203940e502e1076407503401350180900940b00d038a0300a1000740150070007042d030354451074202c10014030358400d100d07507500c2d50b070306 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 109955836 1250 109954586 109954627
    0x302070f0f0c1e080303060f03071502012901090b030703060b070602180d0506131106070308010f08010e0c0607020a080609010b09061804030c02010302041d01090e1501031403 77
    0x200029545801c1c00961900e0210000d90301c586010f1148281c10b140ca0141c0701d01010300740038040c00a2100020080d0350510409000d03024601001e4409101054000d000c1d016821051180817420100003402c0144190088551001a101c0003000345c80c1c41c98014983c2d100400300c80406503035180204a407001c200007030035400d000e880c1c090b07180c00d90f600303141c41a101c6640e1000c0c80703004007401071000654007243c4958824021b081c0302e004c3c46103d00340900c100d030442c855a940094001215420150081c0d5102c0c140c3d1801d42c0301c0c1001e00e84902d4a1400c844030a2603044440c2d000c4d104030310840c58200e0050141c1031000c0c041c0d10031143d072181014608101034424040e6079441d84c0b15040c60341024840325620410441c0c070058074100d24070301070f006104c000c2c00103400c00560001e20025a4040c0c0c0440b0020410714022502658404400d002d9000c428041d81110b076044c1809a03102100001d1064080c1121810081c040e900c0c50780c40703800c0f50729038a846288a000a004074030004144000e80e04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 109957086 1250 109955836 109955843
    0x80f04021008280204030209013303021b03220f031113180302060c0708090108040516060906080108070e070f110102040902041415030a09030215070512070e0609010302070f0f 77
    0x1a01c82d42548100075510b08d05030032400b00036140d0390301410356012840c5840c0c8610071101500031189a0503004501034896221f4004980501c3c030440071940c00000000e2003c1c414145692031284001c0c202e0740d0340d50442d442280d26040c0540828404120984c3c549810408000e00c0d407c41184400062002d941d43e8448400000e100c80ca034845c01d041e01404a903521090300d0a03e103142030300c0d540c0c840c032240c05104005810807602ca0000f40400c001009101486040360100340c0b15956502c800800104517405004001682100001410f80001070b00d8410746044280214082c0d8940400312040481114060100020b03d41301203080082880204007411801d4005650b95003000c00c481c2103401c4070316489005544002000315601c03202004d480e00902c0300d410204080040341001c038078140e201035040001c0307001c581c280084680c11100a00705061210407003201e0f0756030a2400c1d903050550041c1e07207800100401071885990303c2a0b00800000780304002003c0040044d407030f005d2131406c0e5204c084 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 109958336 1250 109957086 109957091
    0xc060503100803040b04060f030b040f0203090706030213090b0d0c03060b010306080309010c03031a090108010504060c050c06070804030507080a03060915080304090f06180c080f0402100828 83
    0x150301c6a0301c0d800440a0915107004600c2c052600e00100343c1481148182c204205100c84010340c024425080010341c080c0060043c000081403101e504000d50041d0fa40308940d01c02d418002403154028000c1d81d45c0c1072119041940300b54900031041c0c1c06085074800960b8059214a1000009240c031640c4102541c0a50030014244203988009402c41d034032031308440c01950050003841c0050381d00407058513055900d0328000c1034840b400e115a00000480710b00c010b40c00074580b0700100314003070150312580c403950064406014201051800fa01c0303600c54055420025000031002483c0d4a0003416820782107032007440c0c0545080b803035894034840340e00503210340340000343c850030208241c1289008031500b100307a03d8508644c2628040c4890740c0c9206070302c41c1a40303c0d5100d0301902c0c0748039100d502100c0100600000307920001082c0c1c030810000c1c2900103c56002c0349801d004204001d101e11101c80c0300300d501400c03d80b640fa900c3c1c5010354010b0b10080000c00c0b0345034807005140032416040c40071004000c80c03d0b0003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 109959586 1250 109958336 109958341
    0x4020f0d14070806010e16110f071403010f050c0a051804050106170a050118090813060c0312090c1e0f06111b0303071e08040e01150e03030919030c060503 68
    0x43e41130940690124844c80d42441c1400804248030000016000d614141000c0c2c1d06d054590003401c0100404540c4094043c0320301c0024110449400390499100450082000c030188100903011510144c802c2101a0760910201d02c1080c0103000800c01000c007000e2050f0411100c500040903140260490f0f0001030342d10392402c9802283d00001500810204406c5c1300c0c56051401054070061b80c0b01c124801241c840c003100c000e000000c01103c00c0d80d20010301d03419000740c83c0c4401501980030601e0480000300d40828012140246108241d03080350700541c0c03443c259181048403680c159420800d61945019464000b4500d502c10300303543c0043c5529141d5500340d41c0d6070441242000050001410304480020307034240c223980e0100482d0100366216a90103c04220585005041a503006008100709800240450f07140c1c403138280c450482e203035042e69440340e10446804407040785142222642562090128001c03a01d0803520392465110b41c051100384441c0d590303d49440a483d83c3c0d103d1404120700009 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 109960836 1250 109959586 109959599
    0x40308040311010f0f0f050c0102070303051b0f0313020402160606090c0203030f011a0c010509010504060e0d020a080d0f02030a1a1002100c14130509100e04020f0d1407 74
    0x500b000c0c900b80c02d0074204c1c03241201d28006444450031001401c20841e03010702d0588450300607415110745040c840021074503036000b4a8060000c0106a81d100820070300100c020803181d000741c040300c0710304aa1190141c1951900403030518000c05400040340c0c4a6000e120300d138905c051081440084c94001c05001c1082e03450001088200d880000c084030840d0000c01c03c2100c2c1400805002d41107030f202030141c410842860f24410b4031402a1103a2210039401c007018040b41d188150042c5000394001d5a007041810320110700f0503603901c14001c8030360241c0c10940120f00421001d40183c41c0e0034003176420100c0c00c940501203100403a84100d40501c01035580e901e024030202c407440c100300c0305000261860070005032000e00181d503480707030300318020039203a180c81400700414801e010003e41001c0b03490707846840345c280c0c84030301c8045035450180a00841d0329a0000386801c002d02850340c200d071003c3d1840e02040c1c590b40c0030700c01d4018203200541e82000e1f41d0040c00000805041c0d1620784d08150074090b200c0c4905020707 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 109962086 1250 109960836 109960853
    0x10b0306010308121504020c07061202090a03020d050a05100c02101a09071413030b060604030b01030b0405011808090112020913020f040815101a1909050a06031401090c02250504020403080403 84
    0x145011082f41c41880044040c0c0c481c0a218001c0da501203800803040d9440e8906a0b180c1101c082c001400750050301c80f140721a22158010080c480d0300b0390250381444003c41100e0b41120724016000103214a00954880b90381004070207150850001d14050103130140c3c180d951403e40d8804180b0b14031104400304200f0511a003031044541080088400c54a050b1940e1030f03070034500c40103020242500c010306010408201d004d500c580500040365040102201e02804c0003011500304440c491302140d1003035004140000e1510844442c0d40000b05a14200300030740215100070b4100003981501c85000300720118225004120b8280078075140b0003c0409441c09002c4505070310305560055142c030b69524002c2009690240541e0000281901210f80340702c1109412038440745540c1c40150041204103001c074000303a154021419100c1c0ca442050003a99a65003550210303524080640f0050700143c0e040400540024123146094412400c07880c601500e07100002c0407644540c1c8100c0d440300000508108002560 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 109963336 1250 109962086 109962107
    0x5040503070807030506010b0307050c0105010e0402031c0807050f040f080c01140306060414041803120e0601030b0a020a11010e010605040b0d0c09020a110a080309010b0306010308121504020c0706 86
    0x50b0142040ca465640d60950350070040c00b9284140c0804030001e25003d20500a4442684521009000651f0340b4002076403e0b18058a09034002d008040e91100d541301050400b80c00804280c1d22400c0c103940741035048915410807882610b080340c04100c00501a41d1240c0b1440250403164080d2100100540c005440180d400d480c40e85180401d004010841d0303204020b440854220f10500c4008200000000f00200f0244a003080d540340b2350907944050541c0041210918900300408002514086846a55400b0240f00041c517112105000866032817a80c0c01502c81c201d043d081000704440135900403400d4902c00318181c082a9950170040007540b9050045201100007562080c40d8061242c90b03030b5820f01c029000d00c40410350000380d018a514802c4607944c00702c0c4140010364418060078a00301c40b0319801560000780039801d041c1d1002052a01242032412a5888805a071400030040900c0385450402401c514185441c008103800031340319800104840103680e8042e09800d410850301800c98501c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 109964586 1250 109963336 109963349
    0x7020c030607020c0409030e0310050708090c0f100e0306010303021f02040b0702101b1406010f0e0f1f0b0309011a06091c0f0c08010501060203120a0c021005070504050307 75
    0x920111075000b003a04403404109540100c6d20340d0082c01c09486944000c13034a0f64140c4100011580d21141c80c1d0700c183e004d010507030341e0f655a079107030041443d68600729001055405051108031025134a0004a0108805044e041071400540200300003420b24400341d10540250300200c0d08141c4d52400054007003600d40c075501c0d00714101400d00080300d195000304a002801850214040400d041c06246140100c42c020031000b182c02d0b00c00d01d48060400340074810f00d0441d114a000200d001404040101e041e01c143c1d018000103556039040c500d0540030041c00a80342011203002c0143c04040c94198880900f8420045a0f56420486040c42c216051028501c415034441302c580d507400e5607003504841c2c0b560304c111008001100421700c80c060140d010034008180210303042d542010000b524984104079441d2a0082206a0b80c4140580c3c491299440c107440d100100c20001d101640d2642c0a41d0940000c0d10440300004001480207007248c0301924402e01040e00410208014038003040b4540107841c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 109965836 1250 109964586 109964593
    0x30203011508060d08030a060618211a07051209010506060a0f02030408031306020607091206090501200c010c180b03071b1a07050c0a0204020c0c03010207060507020c03 74
    0xd000c46000c0d0210140142034100080c41010030320f00e544410a19060760f13004101035a4a040820f011401400c00b407203200041601c0e42550041c003410580034408070b5403a0842c03a044204264458038005121400072280c200300301d45115244401a0300c668450072840c1c6a05035560000c1c1d43c05100f01318020300154043c0e0510080000d0b035141e070803d40e0450041401e102c2803416140034140e0560040c2c0d081449a840007180c41041180b40d074110200701c8141d81c00350b4044d03450381003003281c01d0a65400741c401060000c07124840007950940c040c4401030f000707100005c0c01c41c882079175018650001030320107450703c9804501064045000e200307088603400141441c0300180d52203101105240920321520301c0c40407020001500082c043da81402d5219000103414144507901c1c5000c0034101410008001d008a1070000170b6402402442207420a00b1143c006207400c115503800c00010b0f5100840741d41480c040c1c42500c05440d2000d0014000b00c82c0329010104451500f054020700d00511206290b1080c1e0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 109967086 1250 109965836 109965839
    0xa080309010903060f0608010e0a0c060f020604030507241b03180210031104270b011b021c0f020f0103021c1104031505060a051002030405040f1508100c03020301 71
    0x2e030400345400450703038090f402054045041075680020281070b8440324555090081311505000040f920040c000e10490000d8909500c50030b04480d11074140d4108405a0b000c100841c01007400344002c0e0001e14890b05e4140c00d48080b26141c103010464491802c900d00f43c0721402049040035803030005038214074600d8100300c0490b034000e180b40e20320300f002c0703001e40212070f4550100c5216110f900940030302e51820b020690703129a520104945414070180aa0381d010603c41300c1140505d4a02a550a510301613544002c2e08050290402c6e480c521480e080341d0101100d10b05c2c0e4130030200040c01600c082d0107202c103210408406d005002e003125401003103504051042024101007207410488100c0280070780000607511803a4505000d540c4141e17000a04442c040d4061210040700c2500304611034142660b10b4100540d40301c0034440f00c600703800940c1001d60000d20050142e420039900140d160300c1c01541c0030495020120641425010603007040100780c03c1080381004054080c0603403812415030380b80c21072175507 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 109968336 1250 109967086 109967089
    0x40f080123061c02041b05030702150c0d05070e12071d01051f0c0b0f09010e060403081b090406030303060e0708100504021b102003010f062303010909020a080309 71
    0x43e18100e0380360466003810102d00b000e6484544c40103120b50302101c880940b0500b01c00024001d50404c45102d030043c4a01910302c0c14921440c404203004a0b002039020342070008071500300000e17000c020704440400a205582da103043d9240116009201620005045000e050245907444108a41d80c113070004003161004002980310968003440c0305440c0d10058100da440094221b4190012850180214200300184502903014144d003500650054000308961a55141c00380d495000132540030b004504403000050040b0b049404a80501c000c02d06940e01d8410880300160072900941c0096001035940c0000740000c0d40e0601c0203e8000001c1e0034182c0291400c0e40a54030501d5042c020507009a0b00881c0611208012400c0080e0310100c003000c1d034101406880ba500300030802d01142d00c0544034202c00404a4010410440b03040c2e90440802e00d01c0316041200c20784d5280355030380d040e080b01d140e41c8001d0103164459101031406400c0c070f841c000c00e094400b4010480380607d1600401c0d541e4004010080d000d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 109969586 1250 109968336 109968349
    0x20903010c0e1014030c220605030609060306040528051002040f08071401030c090b030f0f0115020303010302100203090904060609060611030a030507030204050d03020703060e01050717040206040f08012306 90
    0x840e500c000f5196851042d450202c4e0001091f4040614141c0040c201240c4250000041d600c10407040e11714600e10b6a0304001c0550720704054170060071540040b14400b0482d10300351091300c0d00340c043c114192890034480e92480e1070464110003042c2c0965000c9002d002c001c103241e11140c000e040b05401090403505100c51410440314203614541803517641c00d5040c0c803290195004100031300103805405c0e221714000f404280004011600c0303400000b109000030480480e03402c514403140c20154002c5013580c2c00d50303007407201c6000c01c0e040a00551000b4450040240c6d215082248180c0c0704034000b19056262180b200c09807803035a00038400f44000d0a0440503644000002c0c1c42c1d801c103030313450b001ca07454941101c1600240310340e801c0583c20810204050051540006940045920039a0200403803007a504485080b1001500c010340040d994a8296548403c1000c119401c5800100590b142550f10722021900300c41660200740140d449422034100090a01c01c60182600c800b23000d09814503000d000a41d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 109970836 1250 109969586 109969591
    0xf0604090210120b0901060c03030609020a0c02090603010204080a08040611120a120603231902100c17070b070f0c03020303130606080615090907030c03020f0103020903010c0e101403 80
    0x20050000c0342c403400f080241d0003804d00080090214900c5503110340c8024070003040844141e0119007030820000e492101842180c903410943d5444694190343c59081080b908406044564551b40910002c142c000d001c0c4441d801140c4105074059a8500d8040044c1000651701c0c0b03950f046800c221080440c4012080454141c40c04d82e240c189003440d80803100380001d0181d5000549080220408884070b03160103e80e011402c9a10b23422103d40507400318030340c00071001801d4000c0d004401d011010703200500501c0c00d0900a44200c10318141c40701c05003071850703980d00021025140da810703210a20206035000708001d03d6070711a41c40d00190302e00702628040c2d56480041c2c4400003184180100b4028043e4030750000001d0048242511a40d0514070301403500a80c14514a038032a407821b8000c43d20344040001c2c66011607600c0441e0740358443c41c640810440d1100d4176022414190204000010303a6820700c2071040c2c0071140d40350246031014034024041d144942d4a410010301040e400d0f41500e481c3c0400c00c5d6a03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 109972086 1250 109970836 109970869
    0xb030f061b090103090f03021b061305010c0507030609210302030907051212040807050405090a0b01090b06071203060905130309030f0c0f0b031e27071502060f06040902 74
    0x350340381d002c07100480c010400e00801901c0c1101d440c1c2c0d0389080660102d0f0503c41e0482d804448202582c9600c204181031040809035202c1c0e83d43c1d42e40c00c0141c1e501411280070110f0040054408403a52900c8101c255003144800f115680c1d0030021004c1036106c0c45d200404a42c0c3d0702c0c0303400c508610301500c600780d594000b070042c10b100d400d02c4181094038000c10045080030564081c0d4054072180e44042e003e030f8481d01402580d21580c1040300281d6407102c0041c500b0000c6811110a500991a03c1100402030016610143d0003007803c2000b40042082d04c4045641002183e45c0022080d1030500d5040440350041c00d13080e00101c01c1009840801e034003c84c5030301620380080d00150541020b00e080701c807950856002c1e48001904510010b1100d918402840c451003003060503041104041d4071f030100403241280d80001a4074002420284658078120190142ca004000ca4110a44071601d040b10303503100c00d4a0b41e0040e0700650070171211542c11400d407500148156014004045550300003038604951001a4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 109973336 1250 109972086 109972141
    0x4020609040911040e0a020a1203080a18060e1b09011a091801030b150108071d030f0304082a1008040303201b0708030901030b0d02040f0b030f06 64
    0x4005001d02c1120f48019818020b004009207660944a00e072030707460594080e803041030b680c0c80000300c90340c071450f4482c503041d07055a40800c103a40d821204401402807618408168082d95503031000203c040c41a80d9115126400800f109840228160400641d054051780940380a0004000c8440d5002c130310700060b200190b00a440362542000b0440400400003919408107400d0000400d02c102408420b00803282c0300040304040090701d0054800d40c209490200000e061203009100c41141000300f4800020020144c0d540e00c200311810070325540060b0010714441e0000e0b4181c145003907021124104041d2038440701030001da0b440e80040c80401c00c60829800340070401b000642014030a42c002c0f021902c41d40a0340c0003c8a4803100c0c3d01d4103400128040410008200000e8841940011048101c1e1060401036203400f0122004402030500b032034105803c00740a5096030f005036520b003d80040b00c001e02800103100c441c824105840c1070f400310198442600a142072041c000301003642d20744080341c014030302c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 109974586 1250 109973336 109973351
    0x906090a031d0d06150620100902180f0702100b0604030b070504090504050309010e01020a120516050318040b0a0b0306090c0702060309010510080f0304030f06111605010c080402060904 81
    0x41194260b072044001c0c031303003460240b0040c80c60554402c520180e808980c1c1c0c1e43d04d00000313240d9055003001040307064466940005241c8002d994250004240c0500c023130070445030340403c8849600071800a442da001800c481d081082501681004003030720305014000180100c203200404120544a1404060300e01a07541c0c2c00100c0c0035018800700c1d001000403003401c00c92441d00c0d08000d501c2c0c2e0442e1840174001200300154154a61001524529484d0040c111001a01c508041a41c49501c0174001c02c0d989818403921402003081130003d84000c190184451912440d00c804100031241140045440f0f40440141482640d20041c192503210310f0170740d102c00d2243c65140030b10116002c1c07000025070001001040017500c14040d000f00380107140c40d01c02d01c00581d44480540380c41c3c90415540320440e501c20b01040010810004c03022140901420000031f51150030b00c45000c807507010710940b124a84400c103a580812100340701c0c40c0c14682d0980b814040d00d040990000d90148580540366200c1c50301c5501c0c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 109975836 1250 109974586 109974589
    0x605060102030f0403050d020d0305010e0a0c02120a02060906010e04120e010c06091104060510120b0a0906080303010e0903090f0607030e1306050a0909020105090d0f020a0605030906090a031d 84
    0x48910f20700401e4003683c0c5681c2d80740b0303050390f172080301480240040c014640c0c0c2e00440c0d40a401034074180c171600b00302400f4555070060513100821108d42c13940c04522440e02d070000061078041c002d0907520441e0340500074500d00078188603e040c3d4181d020030080716990081001140b041d0311400b11034241071400309038100c49500100d0718070101500c0548107614118100d0f04000341c4c00d07184656081c003541c1c00d0000036565820402d98000c19200c810220f19200304003106e40034030ba8412260000000c1c00d05681c0c584a40d4503030100c40d010340204990741d10000040c030012005481007a0300c4403c0782c0046280001400c0400c00f00d100101029019010210750142050b010750700c1000b02c61000b4006860040c04613032088041d100ca8400c1c94010783c0c00300008904044c031030141c0d010f01c1c0e4045e103810b40f812110a00f4001d400384d40a001b41c5a49a65440d00b50050b913810750711f0002801e95640e00f0340c40381012540e2501344030001c0d00b404203c1c3e0001825100084d08901c20b03207140100030108815641d000340 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 109977086 1250 109975836 109975843
    0x1d1e07050a0902121008031903060305010204060504030533090f01051914010b161401060e160c0b06040c0302120a02070c0f0e0f100801020a0f031a0a030605060102 72
    0x1000554080460031010900340b40c66070203451142201c400348200c0781c8980300701d00880112070142102940041000c20904519004100401507944c540099100c3d903030b46a45003280c105802401c00104005000c02c10310808200440091030041012104036034014444400c0700d00901c40000d1000d00348002032401802446040752060b20000280304030701d0310020540c1c84804910307006e6a0b0b2031900d94000500343c01c100000c0e0585080e1001d03507192a844909103182c01c00d4003d012901d109841064016608080c0108002040704907041022800c200a440303031032040740c1c800741b03040010300d84941001c2030b110107926030402d1080d00c0008240b458541c08401902c2455140c401c1600c410050140b12012980245081405007240010290703c0c1c80e0214210f00300c0b0301c280c2c690f125600012902c0d0342070340300c01182c104a8a50301035440960300c0c40710b542640c0280c501640403c04171444440031a8050007201c80783d13010328919000c00b40c0240d0000320b01c5407680c007010300b0305580c80000540c0382c0d0080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 109978336 1250 109977086 109977089
    0x60807050c010c08090d0f0801050d050f0f0102090f0d030f031a04060807080d020102090907120f060e10170a030323040f0c0e061806010207090509030d1d1e07 70
    0x1e00900038409201805020010165500540c41c0300c0c005048840c248500380c0036582000c00d40d22600245d181400b048014100d5450981c0d1a01800002d034a0400301001022040550100007680f40c500800411010b039401d03c008038010007004d0302c041d0010740e118400c0c265095446c203000074284c0454401030805c1c030f8003048807608136203008004114100f0002e0284120744107101203c030700c4001054124281e00410420344c2d0404c95020100d051140191a0121013013030304000000c103c0e403d8000241030781c8050b444940011241810700c060901c020040c5406403624002c1d00300025a41a105075039407110300800341c201527440000115520b24203902d0310301c00c0214070b1841502d040900741025031914000040710600018140000d02d42925488503129800041044000e041036520704020003a008094904502812502148024861007800e01950b4035100454403050086d52140840740c40030715400d8405c000100e500e035241400030308025030f1100c10f00e4100c0389040384d405841c0b070184107 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 109979586 1250 109978336 109978357
    0x20702060426010c0302040801050a150b030a0f0218040b0f01021b0d08030405060919080d020a11060106030b0a140a050f060d0903050909010611060406050705130801060501030b150406080705 84
    0x9188004500302d5054010f1f10030f5545079002044151600d021141c01c4942a00309502040c104031020000005100007a540c01050300401040c034111440380c400c02c0303901000700071300284060f00100c403950a20b0701c55082c4ad91000d950341004101c030340002035620901258034848103000c0102d05900c41d2179492140084e40d61220f1850345908241c41d1543d101c601c1241d03038106a12540420500e444001201105031a41248141c0c0c030701068480e203000603500101802052141d210501040701c0401c2204a00804c036070351b00051112201ca0070002c419185601180c0d0801d025810034200b5a61041c4072000c440c02213400d03410300704500012441501802c1c0c10601c040d45420700d10028513400000078194841c049560036500ea13241c00044d41c031022961045d80c0b0365449000028001185940304a40013551828510f04000c1c041345624810100c030f0f0030484c1683d454002c100000e5805000c0d581c0d0300c6000715030001c942c1100c00c0301d06a42d07000f01d12a0300200304001c804280306500510403100b14410 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 109980836 1250 109979586 109979591
    0xc02030609010204091104150503100e041101081e1302040b1003060801061719050f030c07150908031804090f05010903080a0b0a050114040b03070810080102070206042601 75
    0x7840c000c1c41e4001d40051140c0214103007403220040c100e11000d41205d050720503101d09504080c95510049600da000104111034400161201144c00104c02e00624400c03407141d10200307448070f8550001010070700060003a10050234004000b0000c0200142c0c0745511003c0710b103241c02c1c18940341c00040c0251050100315038000b94404c2310400c1e565413603044801610400d000030301c03c2c0303541c0707a60040c0035030250111000305400c50b0f0040101c00320000341000d141e034042c00842d010002c010700c60a0841d4400fa1820340c0a90100c502005a1104070045100c01041402c0c003000d998074181005889224507005c406851401680c000c6080d6156448030000503004401b1b20026003041c03801074001c00c0c44800c1500800c40280001d484420a4082c0040300c800191900d0105441e140c01954010300021040560140910011940c83c0706040694410b44c12a50303800d4443c2880500360807461641d0b008090715900400c92400540c4408040313a04071003050440307103d140202210003048a1200c15801600d50 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 109982086 1250 109980836 109980841
    0x12041202150f0c06151c020603090c100e010216030302030306010804140601030f03170601120f0605090a15120c060e0402070c091505090f0a0e10090f0b070c0309150c020306 76
    0x14000380092085c90600311400c0d115030700c1802c00041100000b07100003d00316001c4000010304014014640044070b05007102d140170b010100242e940e400e105150400205151a40d10096a0405c1030150b49840c503807403a050b150540e14004d440f444000d0074941407002c400046800c002d281003000c50441800415101d195860745480006011800b6080d00020019141141002d100c1d6552601814058440600d000106114400034003100518166a5a84c3e0300d40051a034a44103c268891070020a0010301c0c4c400940903a03074226401e8102070010100449141d00040c211640726040d250b16050001c1c01c0100760000502070f2080000c001d083d000000800036550443d03412154200f071103202600680b030b845400b4090b03c040103d03100f00044034940c01241481065038440e2040401c0b034001d442c50340e0041c41d0340c082594801581203403113482e0403081005100110700c000740c11a0143c0340186220365192802003006c41030340100e03000468403100d8008054081d0a0303d100381580a402d542051 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 109983336 1250 109982086 109982107
    0x106060903030f030513031805040f0f0e070b03040818031006180c1d1503090606010210020702010f0305060102390a051807091703090312041202150f 66
    0x503150321046000c81e03540c03c640000540607001e403500c5211854158210303401c280d14210754012950a840c80b2001041c140418140c449000f104c56601e424900420203072324003142001180c284076039040454200d000188003039080801180d8202da002041c142e1503000000c401703140203c1001626606124509144854407515081042110014041d07036540210741080c49047c1c4040b40e400070001111501d44000e101c0f0300301c02a4a20203801f401e1594182549881c10030154003c3d141c010040d0320600401c4003540c0e04000011031401c4181c81907083c00b41e1540003030400d000107500c00c3c05160f00c1360009052640300308103094154000d00450741e80e0700f00458000c410700c000e86c14402d100d698822800d810303030b0802c984580112880a0b0951102c034210309100d10385480c0143c05d420800000c004001041445a5691109400000f0195a9680c6050308141c50b1000d900a41500c1003014030040188003800800c1e102459019a9045082c8030311489441c140e01c00c0d4a50f1101d43c40001c240040d12 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 109984586 1250 109983336 109983347
    0xa0e0a06050d0302010b0306060103050105030a0609140304081005091207022419200604080d09051006050f0409050616050706060f03051207051c020c030106080606040f020909070e030f010606 84
    0x6c643d420703010b454843c0c48000045060340c10034000c0942681c003c40102c80021110351140400b07900903040e4009a000e603c480608591165003d0301c280d5002e5034107080e041c007407841143c1c0c12078032150040c12500340040012050b0f008420019119040d08a0610f00c03c039424281062a080e2086e401780d900e200204050405120b0084a2000130ba503029000f000380c030a02c120341040e13117034500080c00140d4480d911400d455000e0000d059002e9115451400000c4040040e95441c2c1100000490458109410320000350388907000c151060341410b480d003020070740210389180c00c06403025440c0d030003450300b100c1590750b845400c4008140c140781800008060505100ea40c0c1038920400640d60381841800f03090180e406040c101030142d400000040301c41901d4810803440171b115500658034a0001200002d003100e1007588100507e400210802207103290500c50080c0f13600200700300318144400c070800f195800038000e2410082c031880c1500d90b0b045640810a155540c82040001d004c06510703540000d01 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 109985836 1250 109984586 109984601
    0x20a081815040f06090311090912030a05070e0402030402010903030807020c1e091305030307030b130e070608090703031710030209010f0501030b0607050a150e07060306080f0c0a0e0a06050d030201 86
    0x303c503110031070100303000e13205d00314510403280c0020401c040c084420003001920300d4003900282c1c103442400c016403403d00c0040007039482420101c0e000039441c607150310090010960190070a105620400400c4010303070300b1004c030740140c94151404c0401c9642da01c50691401506004455000b00502174204041100e4060a54940c3c0280c50141c010b40302c4800d001084045240b00034a190020700004e800d040c826440300010000042001400096044014084501d9410000800c3c3c002c50020b200300ca42042d82c05400100c1d49005295003461a140100b2155203100100c50548034400072a41d15001001c0301b02c051034008103414442c4d659400000c0821b0418490180441d0030550a90b4007441c00f80190350a641d0404090405504269a802085a0001d91034032403656242da00d00d10440d410000300000d07200d1307510700040441c244030800380790110740650f12a159021302c07542c2641d07840e040c000f802101e1069801d503500c0c1d02c03050701c10806000a90000c58114180719615014550305421454 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 109987086 1250 109985836 109985849
    0x408010f0e03070c031403041706040b06090c04030b06060f0a0512010e04151e0501140a08032107020c0904060506010e030105150d020a08161503020307020a08181504 73
    0x810000d000c41480e459000340302c0040c1c04c00e0f1141c0800c001041c1000340300710580c40c0c0c000c15246019100d0304441440100c403401e200703d0764012404c0000700901c0c039001b19008202162a404c8520700440400c0b403074402d500004000503800c001080654650509a807158499030003066154056000c0052440c0c006c0703035002c840340c042c5600001e5041b042c4101240100e4000c4034110740c0800346100c601c0541680c10020002c03542d9a025550390354a9889464040e16010800d03503443c1800030f0403ca0542c00c15041420319402c10000301076038018544441014100710055144250388500341a420450202822504559070a04010801240d50f02507032040e9000d80b1800601d45aa80601d0300302d800480301900e00c1142e0b10000341280ca03080340a011280c0c070040c083c03880e19854106c1c05040c00561000c1c21582e440c83c02c0d062180200c3c00a0741464244540b0701141945000c1c14025900d00d40e0390b002800e25400003685140958000080c20581e040141c80100c40c14504889413405601910841 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 109988336 1250 109987086 109987091
    0xc0603370c020d0e0d03030209061b012316082503020d1b020a0b0a060f08030c0f0f1209010903061401090f020a0905122802040501050d0803040f0311030408010f 71
    0x101c041a018504d1909011009070100000b10070343d640540095110480c416070080c3e00344003030491200300c0c0540e5045004c0e181c0011441c00c083d031003480c03071505e103090a41d1407400d40d580820804107440140303035840340700c1894600015103030200c0d01c1d9081c50610000901c0201c0d015021078200c1d4040c2c0003040051030322401040742d0b01c0e075a0b04002025269035417080050304a9000d8102280e84040000d40041519a000a50755a1f409102c0c414014039071048402e03800124100b4441d402c140180c00e10040d032000685a12035292400580b18000c440c103010540f44045120302c050307440b03130403060055980400b04100b031082011074240c60356000d20841d102c0500b06180c41980364041e0083e00c00c1c0e020f554070746655290500d02040075003d80c08034404058800c880d40010301ca045410112240c0d42e03401c215100c00d075410700500c0143d90050300110700500f0007000b00301c00900c00c041142c0e40190009100c03840e490807403030111142d815082040d00284404a4040b500c008103502c610180781c44400d08 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 109989586 1250 109988336 109988353
    0x8010501090503100c050408191101170408070f140a0c08120a0e03030f040608040303050c0304030804030f020c09071205090d051e070210090302030f0c0603370c02 72
    0x464051000b0b00800303400d031304605441c6218040e6a040b01c080c042203410403608184c1c0320310b68130385040b072907010708080e40c200b900500b401e101e00131000740c6850000386421a442448102c116107070842c040d200501d15000020120b0038030000e5196041210740c000c041410058009040685e1512841010f44424804410000c0e008400042e0102201d9a18910604050780403505480200c00090065014001040604010001500200094030094075200080e08103814010b00303c0c0c40c024214041c038001001030201081d000031002e0340c081d50502d442c50b9850402c510482c02c01007110020364120310380000740300fa6540c1104c203010201681490801656a590020541d40c6203162480008148104000140c0e507815010356007000b03140001d030394074020466001c941030301c1d03010140344000303091001d05008610b400d00c21629204501030041039a1021500059414800506005510322010101509040d12442c0c02d4110441c0300003c01c002070340300b804440c054404006c8280040c0940f644 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 109990836 1250 109989586 109989589
    0x9150501030b100e01031805010905060f07030204230105070b1006020d0c0c05010c021f0216060c0b0a0506030a1e050d11030d0f1409011a040b090a0b06160f0201080105 74
    0x1443c40b403120940d403080c1c03a070403100c4019401024810782d01c25840560381203131030100380240110b40c030080c440c01c014406403820000b55244040302074080401c041c010001002030796205040f26450350413001c03949103640304690050342e07070384102c61000f405864000100000c44113400e0228003261a16020360f1400104100101c4440b001100c0041141d500410306200315481042304207103951015290f040c1700010075020482000f4004040d000603400840c0e003540107400d220b070394401000e00e8104500c0c088640c0e40d920386451001000f180819a41d40700184456800308003100360a074008119840360720282174400740c804004c0a003034400d40709141c0201e2915100d03060b40d000020410011303504240a103c00e12012302519072003e4492a100c01d00035042005200a807806440c00b01e000084c80c03040b07a1040c44180c2c4c42100b4031445540f504418028a07140c0195075135021401120003d07082800800064190050f000e01103e0340140745040340400c08800314010071782c0e000f40c03100f0030395a03030380d00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 109992086 1250 109990836 109990849
    0x31203060303140c120a1416030f080c090103150f0605030609010e0408030c0702060918070f03060501020712020414011214030405010c0803060121020406120c20030409150501030b 79
    0x28010540c4082d040c0c3c2600170340c210140c45000c40c20710708a03860f0103001c4600081d5821a81001e40d40101e80240d01c0308044d046680e022460295040c101e109141140d00f0303600500031032440074189509d0b5039a0801d41d10030b0b080644042c02c9d0820402c1c0d8241d4403800001c0c00b40c2c0044072024050880040041041a4811001d42c8180c3e4405441459a9100038810303020741c00003141241c10400501c0398504c140e40b250140010b4001505d03121059240c040c000901d01d0301c00740c00440a052070003106021341e076400301c0e60400392520551002c80c09046440424020405865064083ea40e108004607000b40c03004011a42207005c0c0d401d4910804c140301c15251688180c0c410f81e400703c0c0401c02d03001c0005032140c001d10b6000748141402000448200300822038100d880b240d410041d58001810300c00140c03c00c0000880004022007004040030020000d0800004041e007040d43d942c4070076402c00b104c1000c00c21074010b4034051000340070192001300d0404c405a002d0040d10301190078684429807034201362 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 109993336 1250 109992086 109992097
    0x10b01020c040212041e05030d0f050a062301051b070305070b120403080c070209090c1207290408010204141305040308010e060d171803030c0d03050a0603120306030314 74
    0x1300110400e51143d5075281c900040001822401c42c0c48010004042041800904981b480c0c012021409085c44401207040390b43c024641010365180810501c184109007500381c00f900f5901482c80031400358000143e17642d00503441a406001c1e80c075150504501c1380803e440b0112403140c003c03544440d8880845502c1070003a00c0d40944c014002d000043d010030b100f87c2030381d0341000d100ba05c81072034413070203402150150400701ca10200c2d030f5100405200140c1885089104050511b8000d00052800d0000b9803074410281540d0f00b0100f050001455000002c00007203078000d040c0e580c000c40d502c1d50f42d1440360305c481051a001c5c61284c04140d0350a41c40c402070303024591040c0e90582e21105141c0c2000c0104c640104041c0c0850f400c075008084081c0000d900c1d01001c1c3c20035104450341030722890b040c0422215450046440b6000b50001c1c4a103041124002683e01d004910505010070295140f040300720052a590340040e0180940920782034042c0c0d01075101c5019640a03a84a43d10440301c1410303240070340300700c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 109994586 1250 109993336 109993357
    0x606022b080712090b180a02150a030204380f030a151505040311010207051309050c10050703020607050415031a060403051b090c0d0e0a02030d02010b01020c0402 71
    0x46001100340c24411401c0c40e0303201a042c00d00f2403909003280000011501500f004840e00840503042c403124a41001054218850319002446070410300d80c040340d120900000b0034a09008003203900b000c4607000b90140c0307001e0080d052142400c1c260300403c66141042c60b204041200c2c0c4200d0814840c8404201203424029942c0c40303607461501e0711402c0d40002d00300300f540e4021001c21802d011903c006400840c02c10b105565544507191740c00c41c14001030300c0654009880c103662210408004540303504d180c078003026822880000301d15481e41481c2e42040100901a9070202000c001010020b030040050005d50307000e03a089807400e03500c90f442a69240b14500804000e43c04a20202d4201442a0400d10450f0098010b400100140c54003003246604950811182500407200c10500a00e6605c007502e900c41c82128500c0c1d49090500f8070250321300c902c5e8168601582c030391042c003928810421030410815806021540040000b0b030000f4020100180c0c101d005000320404900720b85814025208a00314 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 109995836 1250 109994586 109994653
    0x604050307031236060203090f0f0f060612030409060b12070f02061f080a0303140709240507050a050f01060e010302060a111204060302090406050409050c130213030501060602 77
    0x1480c60507212101c880048000c08060310741303081e40005000c1c0c0043c40c0a84a070030001d00c1c0391405540313001d003001c072485c54003211580080008032500c0d400140d156002081070380c01d0180d6070480200203056200325000b00481505000001070000e00c180000c08071410b00d10300400403a22542e4084860f81840121140103a106401003a00100c900c4000350516a504204000d03855a640da41030a01c11080020390200365521403520b6024615903082e45e100050b0b1804492980c20305400d02c440402c44158444c0302450000d82d440c409021b28104e91920350484101d8940494600c0c0140c0c0c0c2d8121003e2442c405e500300305002412880301b10301c06044c0ea130300400c07541c100000244201d50a2a00908041561113001c01400003002a840200050140f6075000b41c0c0c0c540700141800f0075608a41c0c8840d0045242600e5003001c250f000c56a8001d00d101220500010208518020003034080d8211044211000078400400c21405600000845005409582100300d00c54195624514032942d50102d004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 109997086 1250 109995836 109995881
    0x602032409060d08030c12012408070c030c1401090c03061802030a0210021c08010303030507080103021c020402250c080a0c060804080f121005060c0304091a0306040503070312 77
    0x42243d070285d135010034200882801d200454000c4910b41c07a00ba0300c0043d460302d02410309004181000d2082d031220300c080c2003a6003141007a00f030013000d00020703c00103406c01026103800c100700311810064039001029200280404407042c04c08450b402098441240c106103402007031301100c01da03400780707502e074540080260400450079002d100c10840c03041c9215045000740a02d80c01c140e039900520442101059817440200d45c1940303005401c0b910050301c1036050100c0380b001040103075a80e0710324010785145c200b000c4451104610126000e03000d0581c0781d1003200c00c0300654210440002980a1099002d0191440440e0f61103c041da120403155a018000d004842c006200301e41c05605081e40062141d4903c43c80c104a1540c001210340001b20b56081d40c8a40700c09001c07602c1ea0210140000e4401141e01c40e03e0075140c0070130190381e0310440c070509446030b0312845d4083d250300b440c102c041e40d40b4101a0170382e001032174030f0318000b40c0766404030f14105d0210301c600c0e0086403076049c0340c804c0040300c113140300340b811843e07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 109998336 1250 109997086 109997093
    0x3f1305030c15090f04050103050a05010c020a0c051003140114180103080f180402180108070801050a14030a060606020a0b070e03060708220506070e0402190f0c0602032409060d 77
    0x2a4803038821550007103a04804403004c1d07200c0d0b2081a000714040e07005084068524a052403d4a10a4891800319409640030201007203801151500301d500844400c130b2003500c0400250301501039000120125907004000041341820304805000b0120100c80700841126020015082002c0038000941280418416500c00b041128000e000074403201e001200b402c44070800180507030340710f1181d58401c11040114910256000300403180c03c0303106410444c50303541c1400049016501c0a10408080d6143d01c0d8030500385032401d11941c2c18154200005200e01c0791900c6000e50340b5114810202c403a200c030b110000342914882e0524010742d840c010013034185500c2d01c45040394051000740c00f821030000010062210044410640311081d0711980181c2000c4c50802c10162148a40c8460540903500420042c45d000100006c00380d04040c46040103070182808103030850f418060340000516091001003030107010400c5110781c203044200c40b0346a0b013244e10140140440148240d0f42c040d001300315861600b002 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 109999586 1250 109998336 109998379
    0x30f0405120304080d050405090604020910030f0b090412020c03030408031905041e030506130302060103060c05090a030803090c15030a0b01050d0f0b041802033f1305030c 75
    0x101040c10489042503100e03802c80f424045201700d84000314500140410a03410070244081c0d00c18802c40d0114200104e942c0850b29240d4181c80140803d46e031101c0d031a1003400c8030740c4034815107000030300340e40b03100d18052030283d14404407883c0000151041070740d024070600d0000225425111500c028500f401c41600300c0314030181180e4a11018814103120105112403418680d000d412814030710590301e81d01d9414100d04040019140e00c5584100012507400300e40c001a6180c1160741c003420010780001c41e03036822220b50040c54516940000b032100008240282c060203980201d64800a86602c28803620410000c0c03481106a500d201106200040040669910041c412070060504918089902030500c0848003002e0040d0711055030f461130000c07642484c0c82910216102003003d41c614011940020766a52700c080c45000d0700455054920700c1e084041d40703d4414291170405c03a00310815074011701107501c1c0c10141210300302c003041c01d20020311403030b00240e2a03002250203086400e115458134041c021 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 110000836 1250 109999586 109999609
    0x8041e050f19050712050c15070b060103050106051b01060b070b010603050903090904080d0f020f040609050a031109070302090a15110d090b0c120a03090c0e01060914190305071502030f0405 83
    0x10240511401007d0a4540c0d200180040401040d03483c0e4401c0326142070b5040310005403480741054505801407004503000000c440300800300c130800030750554000540c20701400301508162490794011039182d00704400755414506030740c0c40303440a000558448200366602e025402d902c40d4030139130840110340410030403001011840929000031841007502c003982c6080e64000529008240d500080c100510b0368416130303e10180c9000c45a41a00c1c6196855100c2e0401c03810341c5003441791034403502180d0f000e400380c1e040303411601c005408000c2036695007000200d012582882000490040c400f103582035040469007e81404454680000f0141400310b04075090b0400100c49409201381c0c0720540041c0805c41c00341040f005265804140400580380101f444201c80d0300480d602026100140110758119071420103032031282d03040003444031100300004c41c0f481c0d81101c84100b9100944010080c0040401c4540c255605c503040c407500090b84d41403c82c1d480c8102c0703a650b11840c41c1804203100d0740c0b40c0400340c0300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 110002086 1250 110000836 110000843
    0x102070218041406090f0705030f030403080918090d0f020307030906110a0f1506060c05060601050a090308030412030b030708061803120a0c020706030605010507020108041e050f19050712 82
    0x860b40f40061224680001514201070583c446040b8031001e420421104020305016009013428440c6400a6603403400f65000c0141410b00104052030151190380b4090001c2c10b692501141c01c2c102400c12a44401d0203610070740c0000c600006440391207000104940b509941a44c44c0d07024a483e0200444000c1101611020580139102107607020454180076800594040d165410350780e1000c0021f00100c3e030031503204c5414000d8004080001c42c602003684d590000b42803c0140d502c0c00c590344104c030a02c00c0d940005040d01004018002131015060000d208103450340c40c10030122550008040c2d4582140c85110440c0d80020b0008098a0b824155089001e031400212400c140c1c00c51601c00418004a91441070a65117140341070172075070b0410900c0c009180b90b05042082e141080002170907031144a038068180502c81001c00c042010100c031000c00c681c054804c1e00007200c6145041603d800c22107694001c5403103200101d00c01c8180c181d030b114034400e0340b003030040a481785040059501c0d00b502c1401038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 110003336 1250 110002086 110002103
    0x5011d040c0503100b1009061403070915020c01030b060306030c010c1a0412140f091908030f0a0801080d05030403081003020307030b16031e020d060302030703060b09010602010207021804 82
    0x40390b483c03c12640c100c52000c880301081401040c0c06101c1660200740480c1c01704840c4050402c0740641101d0f10303038910102d4000c1203a41e60f8880400b59518442d96100070303907a00f4004a0103011590120f9a400f403034400742d0b418802d21181e40300f04181c6000640f440340c2d15400c140400c0308958080c001080b16903114556884c100896541c2e80940c1b0a0b089030252001e014015401d401158090164215010b04a06c4a801e01684c2072018800e8001c07100442c0c00782d810500c840c103031956029501c500030041481121f556420f5004581304030f4200402d06404039280708004242101d010400750040d10350755450f281540d403962000c5491002c05410095400a4880e002c4056203050000c1006180a030511221500301001082a800c903810700910030549031201c0700d806440b00c80140c16208002b008003503290d025400e00030005080e2a0300095051207030002c0007081100982214108440440303145600d81c0e0785120607400e038421990000c0d4000c004c0b0880ea0710a0b0a4001c42580060040425 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 110004586 1250 110003336 110003339
    0x10e100b0d0f0b010501110f19020105070b0907090e07050904120507080a0c020f0102030310030b0703060905150a06080408091302040b03150a050111070504050417070c081005011d040c 81
    0x410360103420a94050f1207148030a0014051944c00c101c15410320030001e4014281140e4251050b40c84d000061100036550036100410005e5a1207201510700e1a0b810002c2143c07030341080100c0316a20185881003104071781c2015010080d40310f02046910881d080604410b169035a282e5600104071130490481c024804244100c5001c2103102c0080d05410655072200361100101d030040188028075510014115401041000302d138814640100c82140d078480080d5496071a40c0301705030041c1c401a00030408007440c1004003d103644100d620340310064401da078002d00c059141d00b000c4a21490440e00502080010480790141d42040c40075134540602d50080141840d03215016100e655005840c1e404600660040528180c500300405500400003400c082100361a0481e0341e0f502c0b80314502c215485242d0700c0d0001014000d200c4480401d00300d1a45080350fa81600f0f10b000c1415400742e001c0e0342928031600e091340744080b525200c0c00c2c0c140e400081503410319104044202c1c880980040040322119241da40 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 110005836 1250 110004586 110004593
    0xd050603010612060e06010e0c1602120d030b0f0303031e0703090b13060f020c10090507150801090e0118020d020409060f140603031e160b010b030117010e100b0d 71
    0x54200c0713846008003060076046100d03540d2409006030003444910381d401c0c06000c0303036514410444001328014440f6206000c0030740005442001101b02140040c007070240101b061541c0760f4407502c0d1881040399040074040400060580e0b80c0400c50ba00400c103a0040032a9069103a00c04400380c0c800600d1601184640581d6200307001d03100140d40703916070000914074910070800e00e8080c0d1501201d80200071410b01d0603030418680e071404007007014944a90340b40a031005100f8244003240142031420307004049074205e2000100356840c00d210b010012450320340d1540e50710006000300500203500300483c01c1e50789c1042d020400a001170f80c500f281d0250317940032050300290881c02090010441c80b034000404801c40c069031080e941e8000d00081c480c5d002042081110043c407080c04841c00380f140b02003a150142c0180c0d07100c1c485109207024203030200110001904030300c901c00450507a2211007492086d600a080403c1c00d948840c0409031817034008851298003900d00f507100c42d0710b081000b400201c080c0d07015103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 110007086 1250 110005836 110005859
    0x12030c03110f0a060506030f0a0b130201030b03010903021e0307170a050c160510090f09051009020708030403031d0c10120e01020702010f090303080c3f0105010e060d0506030106 78
    0x40131500e064945e4204200791600703014503540f500c10003021b0910655180d030f80754440d440080c0030038030f170100c440414005c0d64071030f40c4442c00011024008011200c16410060340d00d01c0500e40c0d00e061140c501e9244100c0030400720903030302c40307039406192054505070340072114402d50850190a01084014010000100b0702009102e040801c117122001c801814070051001c1071500c11484024031240c0c00d004c0007891004c404036001c8031003001d0002142c0e02e03044e64903520205140c0c8101115400407074040c0c2880420801180250700c00d07142001044000e80340c030b00c088011450701ca01d180e000510342150b2418101e8042004941d00e14108000a00f550f1b00780003111010040c840103603601003114021540c0102030941030242e40d0520751500707469640d0060a0400c024002e60950300e01040f80d840c0c40c450040b40d09412010032004c0000d008100704840030401c3d0040d044040300c0040d200015841d4042d540301145008060409417411740703000b06650141c50041d040c40d80540d6111400030f02804d044 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 110008336 1250 110007086 110007103
    0x2070f1509030f05040f0509060105090d0303051e0c07060b0102010615090306060e010503100905070b070b06241204050708031306020606030318040b0102010b1e0a12030c03110f 78
    0x12800940030075503060003824603600c54900414018204400d010b41d0801c1c10700c850480344212131103825503543c0350040b5090301a260016822200c841508000c00d070701600102e10036040c0d1102d4001308414400c1161510f64141c480300c0042c00b003000703a0b1007c140f0030340010740d0039032043c0000b040c0140d4440e00c2c81005031098a9040000c1d810032014010084039014081c014040c920142a8a504080000303440c0d46c1ca40201030105684c80d9a45410000c00740901e00041c544205850349561103030500404a0004990043c442c804c00c1d548104407240c00051542da11542c2ea980c203040030181062403e002802600c1500d151141d0400060f90760b41c200000c041c22600c1d070581c6080c00d403518070b020745090000380110344031740c0003071201040b00e03c00c001401d00c00b000301702c80224440c095400142d004102e070b5105c40360030072402900c034400405c00c9030002c0461031307044d101807180c41d540d042d01c0f810026071000001d001a20b91042400807a100d610403510388140c001c141d80400c2c490301c3e003a52900213113 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 110009586 1250 110008336 110008373
    0x3030a09030611030609180a08030708011508010317160501180308071409131524091a0304050f0d080a05070c0201210204052706060403080304030302070f 68
    0x2140424010010ba5000700d42c56801d103150310b5402d5043c80d00004202c0303d001001c00c1c00d1610013908003110340204000100c2007a0300141701c160759051100004100217024019010000e403c40070700c803101403003440c2080c1220b8024016076845880c01440304413a80c041e203407400c81d5810b20310444001c01c0c020b10030340b001c860030240c002d01e0081440ca8080c00e00c00d0000d021205103e1410440100d9021034022034000400481d5074401d418145159440244000280c3c100040ca10300000308a0210300724054203802c040e0813980c843d01c00701070001c0b101c0f41204d01480031031003007030400c80329208003038009580c1080c400d006440200b0f007016400c40c0b0b003034002e144110001c0c149509029880c03045125603a00a000b51400000c07401c0250006000c0000d4440e0340c80c44400800c081c0c107003050942e0b041e54094a801071484008014180e451010001c03100300300950165114045038061170218103c40499503c616550b0039940d0ba5203042d0300a4100c0d20080e00c0a5000c00030a6001400d4030184c030741103406 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 110010836 1250 110009586 110009597
    0x1a060f0619030b0414191b170c07050a030207050415050f040209041e06090506010c0317040c050d081e03040f0602070609020901080d090504021303020906030304080102041d060a030c1202040b03030a 87
    0x64400c1b0f00668800c240c69419050003130442c50750055020960720401000b12160007240d4641e040042c7d0705218804014005004a0909004060380892104111032080f02c050055414130900c0380018000e510645900ca026003018404c43e0034990060700c840399006000144090003007000c1351000300c2ca858140c1e60143e0710141800b205000d48502c68002200b8a0407685c502c501303683c05040303005210740405084c60354800080c208030f00815440003404019040110b104c44034a840c01480c0c01c180c080d05041e240c07803a154001c080440007920300c80c98008041603520b400d00e1702c0e400000c2d884000c0c00c4e281741d42c40740c850901581f02c1c81c5140740200a104c00800e400a80081c0c024000c40b4035803c13140c420b42c010000340c012031480f0513924041d20740481d0f5142e02074981600007807840c420b43c2d00111030707035001081c0000c290481400d9030b585848461200c16481c2e55600800c0403090072030000a040f07903004503041c03180b02045264591064030191001031801c0001002910319046032084100160 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 110012086 1250 110010836 110010871
    0xd0606090e10060f060806040b040e0f150619030f080c011a040b0904080d0b010339020f0d03020c0309030a210513090203060105071a060f0619030b0414 67
    0x501d01c0c843e00c4010f00e1004400c030071182c00c22000030080c040140485206940b5030071094a50364440c0d0000781c0145041c0100d8807034a041c00542038031031411502c82c0080d50710910000c7e445040c101c0300140f1040040843d007545c5070a55640c4490240401015204400709108a4200110910030b181000340d4107080080301c14240302c01c0105071424407128600031184001400f001580f40c5007034272055150001c0c003092590800e40100c00504190b00c0c5c1d9128161a00b22221000a00051144005402d4038903410911031800d1300380ea80703c4144070004400d6211041000b4140e10a0b8054510141c1c6602039a10307041d201c40000749462600841038821081010303159450b8420142e501400760703005c0c1000ba040510440030752a124031544215114990000000f541d0741c0e100344101c56149030301408840c0d2006116101c003c024000710b0f0300c039004860020300f01c0500d1401609582984621100b5228240e1800804802070440b984d09030b1303000703502c2d485000080310900c09080d01ca851480c29541200 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 110013336 1250 110012086 110012113
    0x30804020915030d11030c011d070e0103031b020a17061006180e070c02090a020310060804050c21012906120f0c070c0303020d0e1e0d0606090e 63
    0x28100940702010451005a00c2106903c000c984001505071606110241400688040b4114811b4a02c8040c0f02d51a100105150500824180d50f291455104645d00a52101c01c1241d48c000b0a00000c0d01046d0304c03422248181c2240425500c3e00c52001e071540301d58070b5a43da60301c1c1c1198500d0240800f260451001c2000c0d07140390303400001c0106150310b0225a08074040d41c81600710319250084440500f50000011201401003600740c4c40c803507000c1c01d60f00541c50300103c808000c1d0401d59480c0f160003102080000c0103403042490314081c030b800c8006041000c00741c2c82085031220019503408a804008640301c1c11504080c405c00c1d80c2480981d82c40c409002030344c900e850040050240b818480c1c0d1003403266404002502d03440310784c850101d400d80743d00c03911000350080703080c0900706004016682c040004402c066000c0307605100c01d41d203034036124440c0700c10004100c0980f4040c038460040c0c0c01d5103d400c1e956450450000285140540e00010300641c07105000d0042d6551640648455030148a4a9030070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 110014586 1250 110013336 110013349
    0x403030e070501090501050705011404080a030c020a030806040c030b03010507050a031b0504061d0a03030918060e0a09020f040c0c02031c050901030b13060603060f050d05030304060c020a0b0403080402 88
    0x35004402628600703082c40d0010300340c80320318041c0904101001c03a8030000c11500350300002e000641d0300420382042c030306460110040d03030242d0344040019043c02e6011720f01c203000040c0300040e5541502c8984480d5205020b0000500d244107946c01019201c03145501e240e00e0a1046c1c6003d05403554803d0b503140116140034003602d5042e480c03402c030380f20300c01a08918103030300070b054900b612018a0f049015144038245c0c0c01a802d120f10311140e10407001c0d03030000200364010080340101d5010780d4100c401480c123070a040341115050301c2440385071210180001c2c0b0920b01540031554041c4020302c44403282811070f0109040790321100540700414a038004040a500c0d0801480904801558642d0320f0000401401421401004c52060506885024203643c59481918050304c0d001421020081030360b0316040140a00704601c07803129407500c410404581400c0c090500d04181da04000254696191981c03480d004100304612a002c500400708281e0010360010032840c06540a0754901c8600d06050040124 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 110015836 1250 110014586 110014601
    0x60109062a260f09280b0304140a150b01090915090e0d30020d050f010501030b0312070206040803030901020403200d1211030c0106090605091e0408090604030b040303 73
    0x1207004003400075450041c0c40c1c5044a8190400b0b0304c007170801005a142003220011050ba01100c09a5006000b1400d08606000385100e14040c480c21002148000c07082d60322100d4800d00030300f05000402038000039003400e410a80c01403206150000920f9910244d020840e40700c21810030000c400c400f8108024003d5004141c2c0d411003000c05002500000d6a000e0541c00d0714480302e8040200180b0350115110150202c0c4e004840138501c155591012801440d0040408964415410a800c000828a54864030603140d00c6000034005060b0600c0c0d120540c6416086040d0403a804002000f0224081005101450054005400168840e0b0852400c00c04850507a07480101000d00103002400700d6682d03a08400590b90061481032041000c82c0702120302c0d0021050900451100080381c50810005610140844411400810001f5121010000d104c45c0c1a2007083d5a1801090718a80d61405001c080390081c1c8242a500d00c3c18152070302040c1c00d50415801039400c0c0c0504000c0209140d014054a40d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 110017086 1250 110015836 110015903
    0xd0e011409150a11120405031b0609031b01090503161205090d080901140301080706020618120c07050d0807260f0703050409050c0403140105060109062a 67
    0x701d01da8455492a40300b020007840320500c0c503150314200503403449180803190074080070ba41045180c60241410fa0740e85c0d000d00c0d030745d508003400c004da12008000c0c0415214060540c4001462900283c1c803100303000308840032207102e040e542c2c903074280d400030746c0410040c6500300b10385111020204907410946852940d49040e1805d2202c1040841160396900201001550340010304507150101407004941c2c140600c4030f0302011304400800403d41810005030601207914642c2151142d60b100b08083c80d0b2544212103140303072907101013441406125400041c090b000c80702d504498a080c1d48100180d116050000c044e1401140001c07054117201480f44411402d0700c1541c0b85010158210440507076a01c0fa448000b900c000300030600c40200341c030402c01c440041c8400507061005080100400325242e2081c841195007844c0c60400b0b410340b03001806440e105080584400c0340c21840c1c0813094441410503010250740340c00c0c03510480c82803101c2d16002e1a2160090601111603203250303614080140803002e00c038 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 110018336 1250 110017086 110017093
    0x3121006050a09060807180306050604242c0106081602030c070b0d0908040906050324040b0604020c010e0c0103060807080604060e0a020a03060e06070912170d0e011409 74
    0xc08282d4014250008494085c500301406550789a4201d9400f203004007208400e00d0440000000d002a80c6c21160085604a034200707c0f0150081d0740503400c03050030240c0060200c0d211010401c407e00280010468403000302d21880da54015400141444402d8102c0000301e0302c039006101800026000042c1c01030004c0c00114034082da042461583d582c0d1030321a000c6482c100040d07581088a094100038400756000b210280c4032a200c5403004007402c2a801003030301900c90600400082d460b10f08c0c6c800e200e0b000c9500c000d070b801e1b1215259504008002042142c0158007041154914482449042c00b11200070024140c0010008001419210581d0010b0160350060300c080c0258040410140d4002c0e40c407078000075441030400802c1e801c01d4120070010354083d5045100205129854102c03140071000902982c0d21a500c1002c1035a001312036000305040c4110b40b90705030000070b403036444c80c0001c00003d850712410540c141c1c00703682c181c89400e15441c001da5141d00080c000368030040d40460b00062000c018 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 110019586 1250 110018336 110018347
    0x9020619020304081207081c0f021809071b0f05011509090c081f1a09010b0a08010504180f020a1a0409060b09030607051b06040309031a010605031501110312100605 72
    0xf0100703d230044a520f104000c07440300310100040c0d4186d11480a2000d06c034402c2d0b407103400c1300074240d5100070207440c0140280040c10004140034810443d81c88001403000c003015010400e900c8045143c4031b6440101e0345d96503640346034440c0361481c40c221001000c103104082049001480c180755460302aa01250303050384040716811120307030900004c00c2c4190142d00001000d00d580e2008000f4070210b0701600b03410131020400410380c40a580700034400c0c803070a03031500009641d0b0340c2c1c14002104c818544020120720900150000603a522182c000546d000070b10550120303444080c004000846120064402d00001804020206450042000820102038080e05016240c008a03480f8640101180108900041c603100700c0c004611841c039a400d459009c4449620b0b0504c0c0c080c02c01440da004c00e4031320f0b0406401540b440900440440d041e03656070741e41c541c21911503c81e03601c100140105041d040c800d403112039030b0340c0c440100040c00d22124610030040c200d0801e06910000c00f2100d070040341c00c101c0100322 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 110020836 1250 110019586 110019593
    0x10090305030711030708030f0f0106050405102d0f021b030d0509060d02030a020304170715020903010e030c030310170613060b040911030709090308010909020619020304081207 77
    0x25a40c1c0b0001500f000710400c11012012403e41c03041000c0100030005c08010300c0302c1c00d6000ca180d5032080c0d00501242003d039880712800d07a410301903031044c184e02084900003000c00c40e1042241882040c003c2864011040030810303481d454a00c000e500300005171000045c4a1004c0d03041005030307603950000f004c0b00d1340e92a1043c0800c1e181c4c000c20040b02d00340680021a0081900e0360001c42308101003450f0f00315128244076054102951003642d0584480c1240c01d00c2c2215810400d08032203a403030707220080b504001d10440c60a8040d411041e440d070ba05550302c8540d91854103080c030040000c54541c8011319981d18081000c3c040758411504160309030020700136800a0044c002420302d401188200380c1001c609590700d400d1020b0041a40e80341c1d00281441c00b401d04100080c01d40c0001c280045080d00c0016840c1d0b0141002c4a03415000540040c400b013004104488890380942c1a890000c0d200320f00d4135058040b0500c0718401d0300c0c048001640000341c00c1105460501c85119504040d405d968580f818944 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 110022086 1250 110020836 110020847
    0x10b01090f090b120d1d01050f090103050c0c0706051b030301060903060b060d14040b0916030f050f0d0504030501050a061505090a05030708030408010b030a0f0b0903040f0b030108100903 82
    0x2030a420341d07503846459400c2d60b1044c89454000203904100c0361050740c501e80007000c1941c0108104014810b82422000c42d41c003810a80d0450b4183c1c00e03985040c2151f0000440280c1760151242d401000100f0207041340d00c4081c04048040c00d01c030b4451580c1c414442e09100f10303280e080040c0201d250018001803000950080da480d04594102e00c000c6000e40e1311071300150310791156000003000189000c120074100140700e00460b200c0d901403101900c45907201d400341901c031181041d091003500ca080d0030601c00520314440c004a8280110100c0c4c054416403039030a45850300d6200602c02040c1c4c04a020008c01109000395079012141c0082409118a022444500f803581ea14042041c04070200d010220742c3c540190040080500804441d850f036910b0310180d4580e48030340035050349275081000d003c00f02d0a00140102c1d6256001c2030840304845c40f5100c40740f18003006005440c0300d000407c00064104947e034442c0000d40091000140d0f01d502d42901c0e1464111009039030b00001381002c07a004042074100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 110023336 1250 110022086 110022089
    0x10e04090b04080d0f15050415050a0b070f0b0c090a120f081c140601030e010e0d0315091e061203170903070f0803010806090f030301150516060c02010b01090f 70
    0x800b09503ca040c41007861000d00080101560174a2400c84001017a0f0381400c01c400460307009407400c00c07110130450080d010001240c043e080e0484180d85040208511600080c90b100d030041100c041c03134009a9a034a030858170b0540d0442c1c0100c00102d050091460700d13080d15801001c204010604402582e40c91244909905001034603041c0d010601d01403c2507801020300c00c02510407410420310021015140c0d024809a403030783d00213460f007031070040410014866005421942401080d00101e03050044024040c0b2110114449100c0400025118001d008a2003110700c007070410410424040000d408940a81d80850a000032241401c004240c00c0408240303c05250030082c0342548d546d011242c5548981c10000306072000003068202448000d202840c1a6490003007500d0440d101e100d075203035980501c1d410003501a002040100840d120461803800d1817121401d00c9400d041684455044400207031a00740d4442e9255140c044401e83e080c03184c08185242401d00d20300c91410294007400b01c250f10b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 110024586 1250 110023336 110023343
    0x180506031503010c0c060f0903020c130b0a15032306040c0908030a0804111002120901140a030509010b0103150902070203210d05150105070209040f060c030b010e04090b04 75
    0x40460045080007140394a02500600240310068413200c004220b00d580350003c0d80c03d20701d440d0a003070380d12881b07010341d524554155005002d10082d12080211152441b2011440c2c55a031301c041c0000344d03c03046189801001c806204100b40456624041c0544d0105082c00ba01c4070b024844030307011420300e0140719821400070b80380024810300300c9409982e854003e800c048800e01c0003040312008980e0014815202e988914490090200103009015164031980c0c85580903800c00011060010b886201405027044149091415041c0c04100003c80c0d6000f00f1010303002a03103c40411a803e4001d00880b1b40101c420320301000341c091145600e03032000d10b01d801364031086900083c0420955500708408003424240c0700d24240103031181a600e000319030141010b81d8080d03040c04006000d40308103140710719200304107031182494204541e00708164200002d000311040c060180303540300070913828810441d01031400e403400110740d00c180300054a07104418903110300c214101074248000501a240b10360b0416072 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 110025836 1250 110024586 110024599
    0xe09010e04020d050105091e0106060c140316030c02040c080402010e0409030504050303030a0608070902131202031c0201050105032e020306010c0807050a0201090e040c0303110f011401080601061805 87
    0x41d28070018404440100e4090415824036081c403113801e03c00b069101c3e080714056a60514030300c001d030069080c0ea80e60700c01c0c0310100b0540038414002c00c1603d0101480c100314041030f6032421030803a03121350894039050f50070740c00504040d4080c0114181440780d41000c5040d0b04250000303241c50340c0001c0940c161100c2d03290003551990004420175000c1c0041c0c03405008000d007942e4680c074260744480028065445818594400c44e0400280c000241c800c8600268442220710115814415136110600303600c40201d806102d50300d0407107042002241c51001604241d070001c103455140a04041c5814076001d00e0300446080041440c0c0580e20400d08441011109403000d6145da07901801070350800d401c0b00b0080c00c6001c00091507401c1000208200d10340a20076254844201d45818091403020000c5134000d000c690402001c1c0b011a004800b41c4070008048002c4401d01a1102c0e1030509403100784409203018003000f40140a03c01e0300784142405452986041004a101c1ca400c112007d5542e1090500454 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 110027086 1250 110025836 110025841
    0xa050f13110a0302030703080a03140108030403020d030509060a081503030901080a0f090c06050408070603021813061809020a0602010b010203030106180f0602030307020c220f0b03120406020d0e09010e 88
    0x21034142a80b8000c5030010252131486580e070030008910390200580c940040e14082502c0108039040101c18184c4802070700850525045900f4070406403903030001602400000d00c148180c0740e481c10018003800740031790f9429040e8108000003000d2034003000305452183c4c200b440310400c2d80c0d0340000884d41c001002c140201d202000105000f0080c0070741c0e03202400c8100c0c40c01d0003050382c9802400070b008462078002100c0d01c150b036a4004800728001c3c51012240e500764071041580e98500b02250481c1c3c250820000600b1960703e907001d00035134415110b00b44902e511101c00c40198641025400001c0545000038085406c5400000f07460740b1050041400b17024820165211005290340d00b003003e8580000041c0809450f00d9010750b907500f04980540043c440c8152510480c103000e030580c903812100d6800414520300c42c007800e0000c0e24811000100085c1d59280d19000342d42e08100c0b00e00070707110741240140e0f500e0a01100a0034041008104d0703007445041c092040346d40e191403804074119a031140c21a4442e8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 110028336 1250 110027086 110027089
    0x3320f040503010606021b0108010b121807081b0f090415140411030105060a0b0d111905070302160308040b030405010f060801060807060908060c0a120606080a050f1311 74
    0x40c011900019010b62a0003804260142c001814006040100180d800c581c9120750044a01c0e80b8240102e076000002482181414240003502980040114000c4c1c109483d24850705840c1c503031701c3c0d030100c8800d034000390014035001d5104000e0f1000c0441520442030981c9903201007094000c024100600c034540058100c103020301160311000c98900e401001c14814180390516000154a0706841c0e4840c3d4a031401003006803400104c3d000841b000c0c6039070a4101072907007420f074009040304640c101e0804001c01031130040e0b13251251411028100c0303803290707910b0f1b044608000b45450310301d00345c02000d41824101400030401c08001e950448046048032a80c81e80d4034941240500f2034507000e01201c60422001244926041d04041d042d2012582220340f0a541d410044070500c3c5984100f0540380c100ac40440c08490a95004164008050a200f036409046005540845206a201c000011320072020f0050300107650040580002c1e52000d07030400c50900c180051148514910020000d41c1d911803c070410303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 110029586 1250 110028336 110028367
    0x9100c0f030e0406080604110105180a0803040303030506060c12031e090f0613031704020609090a020a140f120403030e011a0405060909070e06060d05130332 69
    0x46610000034140600e280ca030207080c1ca0040070120307129a042180108078880001240c52003550803040c00880581c3d401d0041d1003a43c08004101c400201c1012989025254050540e0003800180d0080d42d880f440c41c01c00070b04a540142446218000400c121060700d0000130748107072155450340c41d40f039980d180c800da5155582d0340c1e000031010030f031042c0040050201010940c0b545944215090b58260750320a040c20415001821009001c9100050710303015958092602d00d40c85403002c1e040c00d240c40300a50026203a5042212514000c540005614901d50792162200850114041100341400400c8004000e180070b0041540381807a44600042c00f810320903003285014802800082001211814a60b07900fa1003680314640500d0608011a01c1401c142c0807030380c82a1051400b50076918209442d1002a44024000942c044018801c8400d130250510461b40618441c0380510890302540c600a0592a500044044244620003444054854042c1582c406d034002c1c02c007250b9100f00f2170003c03800 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 110030836 1250 110029586 110029607
    0x140102120109021b032131030f020a021f12060f030302011d0312090c040c17090d08070c05070e010b09090a050108070504020d020c010e1608060c0910 66
    0x403818148000030b8400320b00e0f0700422200503a043c9010b44c81849014041d076910070100f08409000303002c4504500300d658040d1154101e01d0075000c1c80d0002207280111013400c100003102d8402040c7d2080716404050300075420300c0b1107407803900240210504680010790f44c0610f0b081c40d800603c0340d10010000191044158949034441000308005c09074445000c014420340c140030480240d072070241252500540500001d0300403054600951a20503188460301c840e010103003810036240305214250900703036240d0089850f000e05554841040c0791008420a071100310251000c40c0715000340c0d80d061526540104c003030354000854101740312051018500710f031a1407440c0d4400e40000a10500100e00380e9185002044c0c0b46104071607103101034481040780011208203200e44100c5a00c42e03013003040f95050a0300904002001000014145000030881c64252160201241100d4000310742c0500c050a9110600025018040090800d880e00c60000c14052160105451040700303440d040344c0c03100c2c7c8110341000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 110032086 1250 110030836 110030857
    0x230922050a05070801060911040302060702010903080706020703080c0a080114060d1a0906010f08040f020d0f0b0106081006021b150406110709090f030e03030d0e0a060617030304140102 81
    0x1040611281052502c3c1c11041c01140083d50818900090034455400b03420440300c55250b03000d10f0300380b550b420021560b01884049051001580000020031290005490000c1c002c407809640d4041d24035004110b010003d00818500c2c00038080110090391060b00141510035140075030362140d00c48000034105014a002554505041001d00140080c200f440114259800c3e42e442000e5107a544c01514000360250a200c0015810b20000f07000c225509803000055002506050000e0f101c1e4443c0c82c200504600e080d116038140100421920354010b40d265030101115224100c03550920100a445840c1d0600042070742e00040145c0c0d441d5981d10078120f03015011041c280e5542c603500c2074054040070000710f107040b050146480000b4a0f18090144860941d8861000c680c8140c43c1d640c207480113622030341c6240e09448180200840030100303209040101c01c00d14000d0000c5071a5107802010344031107410100d44245203a01a41c10280000300381d0f0b404c643c3c00564001103510001446009004211401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 110033336 1250 110032086 110032093
    0x309060a0903170403050a03030b1f0206040510050115031a09091b03160605070c05030d030b2103091302071b090f05090705060d02090402040b0423092205 68
    0x288034a410a140e1070840307204a81c40c401440400c00c540300380c0d000b103100281207a0489220100068481e62221201c01001000e0f042c48424449041c0c0302c07105080b021b000507a12003401c1c80180001002500d201d0795600005000b0340d0f04008900c0c10502030f80004070241501c42d00c0f0121009150210f42028104c040d02c0c3c0081480c0c2803504a580b00d00d80d0214030b00c00d05807000520390340e080114646800d062901c0c44070660928200040750150700c8803c054a100c07943c40f0011819540904c090100c0004a50b80400c40310a241d003082501480c110010342d481c042050314500295001c0162120003000b29a40e412030a00328100c280a441000c00041080a584009000320801e0001803001c0d1038028400308071514040c2c0d0381208a4030300f42d80840650307203e2042000386140a0008254424100e08003501b03210f0713144085000d9070415040b2002e44100805c4c1485108020300200224800d00c0800b41301003070201c3c0102c6e031088405000302003021100180c41e0140819143c0010140b030b4080b049 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 110034586 1250 110033336 110033347
    0xa081608091206101a03070f1107080105010f06020106050f1009180903030507030c080f0c0d140108121804020f07120c030f0e030606041d0a0606050103060504021614030906 76
    0x10207807078000031149135410724200760b030100b00707080841404850450b00140742c91840e200c25009a409000d2000302004200c24074808e41c084035414032240004014940c00801c06504040903190311240b0f5410090440e80741240801080c0d03a900c0410318400800d0340c0400342000402c10480e0722903820f0300115585200485103158146691344008100780c00303070b50b04108035151400202d0a5809100c0d10341c0014183c000030074110980156810b801940140602d0310b0030720500710400583d04002c0214003140c10300380040021035024401030041e00c2d04c10012924010701c5480c0c100d044242e10300da560042d9030124a5402507030310401107440c0141c1180068003210000315005124009601089002410041d4030300c850034080c034101c0701c440d40001c018000035911202480020304180c4550800d204540300182080d210600550100c01e00070880803491900f8000007400362b0b81d20713911060280c0d1041000b25242c4003e400380d03204a5500502d0460142c2c0b020201901e0350150b80503042c2c0c81280002c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 110035836 1250 110034586 110034619
    0x1803050405030105072609010f150e0a02131203050409090506150306090a03260403090801050c0307050406030209030a0215070519030503060111070b0301030f11030a08160809 77
    0x1900071181d044000384000e80e144141241e80c80118850440d525895007104103074403220484407584a130418000054107503d0850304810b0752000c2c92000c1c02c05a0601d03003801903134007460f440c640c4409444170640c581b0403004280544e10520b0f21600104036048003003581014410b200f1036000740303100c1c4818426000982056916100700ba00e80c1e17100301c003d41040900c9410003048041c030404801c005402010070b161402c2d2403036454440c040240e50186070120079004100c0010714083c0d80a40e81da506410f050083c2242180c1300070306a04112103040c001c01c00d584e940a0202d80c2520f60a1401503110580540464a047d0384174074020b6120101d0b40c11107080501c804090490745004004031540c08000052500d080b07541098090000f41c000c1000410550191120700c0c1109180002c4400e850b548107000c45403a0401c1c0c0046402c0190100441c05004d0901c031081c12036103045001c1c050000b203c2d51081c1040c07040701030701c030704110800b003070b84080c00f1088050722030807000981101d2154900c0c10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 110037086 1250 110035836 110035847
    0xf2404020d0b011b030212131d07120e0601120221010b030c0105030103020622090e0c0f0102060601080f090f0303010f030605010803031005060f0408030d0b0f01020c01020a060e011803 81
    0x401c01c0c0084d0f984c0c0184d01d2129044c804d0f520b510b94054020f070060301ca2841008095030702000340100c41c085803a00010b900d40fa00c150100c5078043c012464009401c02a00003003801d010350a002030b440d03003448640c517041d0324089450750458801c010620341b01010340c804501030003058080c00000d4540414032104a1906400081d00c800044050b21241845140103603000c0c042800b0107034002c58141701c4a0750020750031010342000350b41c1c1c0c00c00004455858880700242c81c1c81d81c01c0000345400c000300c010039504242d00040101042400508607074900703040001c2c4042401402245800502408508104410b000c64004442080c040e82e42c4c17503841e00d0941d00300940521007114a5854507000141c125000b20640340a14840020390300414688001c00c1201d0b000701d9621a034804080000007042002040102049400c040d400710302e140261040203440901d0340600d6040d904440f070310940c540c1e800300d0040d000d5640320fa00062106441c00a45004008000c8400c0060b61015040402d05070800c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 110038336 1250 110037086 110037101
    0xd060207060b0a121104020a1107120204060e060607020405220c0f0812071407090903120b0405010503151b03010303021e01020901050a03051506040b040513050f2404020d 75
    0x162810480f035640d800729203035a44416600940b003000c4241080080e440c1c40d8004080d10702c064500b88060410900b001d604090142c3d12030f45030450980c40880450405000300300040c05d5a0084400b1031800001082261081000003031095542d180090310007625042c104a0b41035580c00300c022010441d14261032811800e000e40010380c580c0080001c0c0c1c0080001c1c641809000303550b155403c01910350b5601c803484000350203c010038003810303101092824951040440460080e560100d5080828804408071012010341c02d00690030a801400640c500013000400c5881000d2a1000e81c0e41e415941000440c40e01c80d01211204000000402c0c5613001840b800036070184d05541c00103220fa1340c940c500301e206440070319012035410302001d00310741d001e984500d620103613500075600303801c4040d0000b1b01142e22a4001c035100c000041011b20660034561402010341c1d2541008100714100740c69004440780d40100060f0422460750000145025004c0542003c0f02000d0700c10f5480e41110704e1100c02508a0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 110039586 1250 110038336 110038339
    0xf02030106050a0206060603060a0b0a03020f0a0f030c02060106020d0c0501020f07030305250f0c110d0c0603061e03080c070e0906160e01090b0f040308071103060c0c0c040b0d060207060b 82
    0x103178400b10f050303454a4021a801210014404280c051a1080c289941d400c0000306609040e03081c410700080001c032030014401005550348050001c4114003004e8219a9405102c00c115444072005202c0b10340c00040080e41125581400c002010b02e503d000c2d800f84c440c007805040c1020010500c10101501034204900400140008102000b0910b011124842e14110700303000007842c0005801000d406840c00c012800e01906114403905a184081104c07004810030841d440d85a40004000007503241c40303510b0140810b01c800d800c045280c1000c0621455041c0405040d1800004003240704200801140c40102119495810135142140f000740d01d8050444a511a0824035800ea0f90500d01c0380740412803583d8161102e900712070a08582c0b520b00d400940c1c44c001c8a482c10003020000c01e542c01c010f402a10b101c0c980a02c04404130f001414208900607200000d2000244000394001c007000c910381c2d05101c402e80e40090780c81c400c08000791140341d042402504040c030000b410380074418aa007201a98100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 110040836 1250 110039586 110039593
    0x9120a020a0b072109172a0d1e02101e08040203060403030b0a0506070f0606050f0d0b0702010605090108030a0908060907030b060a0b0307180909030e060307030f02030106050a02 78
    0x295642c01c0340c1c0d03078400c550000b40900030b030702d240410502c1d0842144059082600d86419010780b0746e000790901c5d8840034068a12944000300034429200035062861100e84401c070070302c8002d0f0030000480c0484996400080c042e000300c070201c03c0c044000e08044070744190002d1000400028910014080701408040610308600c0c8225090b041400f60701e0081c001c03a4080c005140c04d9445880860040a182d40d040d94002001500022181e031400003400b4603901880c0030394104540742c07910100300d030383c2c0c0c1c1d110b1070007290384000400140d51905494280c0741d402200c180c1d590340c0c407841c00301d00508250f01302c10b500407440400490800740c00000b528000b039007522101c1c0e50036140c1d01c407d541c68400701e5071459241d100c00000e100043c6c6104005410183c080d100c070342400d0702e0f1a80d083c00340d0411210500003c207040000850b1119582d85500280b2070300c40b0400881d00b41d80c034000d2242d110004070700e00038000000824195440303548010b0031141e55030021502c03541c5801008040d80e1042d40303504014403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 110042086 1250 110040836 110040839
    0x1205010f0204050a050603180708030a08011202030304180b0301050a0614191203030e010c0302030f130302151510030b03010c050c03070204090212010213060f0201090b180309120a020a 81
    0x85441c070849007a1a801051001807601c1d003820402e03940d100811443c84071484158407460a00c0410003c00607041c0c1001a5440d0644020002c0010105074400018045101d28080c09030700c0200c11101aa405071074005a404518810b0202401410084503003561030b280400140c0d20450b8411401e403401c40d44a0610400c00004000c0c62050b84062200f41402170801004101105030218141502c20300700030403041d40e00000d05007103482020b804000700781c00000300701d004c00600d54a96800410190152001e1000d03440084d9580024103080000d1415403002c508044080700603030354004001046045007030042d80d0014081c00e0140d081900a42c01e2100001e045800340c2c0c01d80302c6c0e14203039000460401c031803074007000042c0424040607a0049460108050b180b88203000820300c000d00e0300c03003000b035144c9481e400500c1481c800c01c0100c116450f0041341d10001c1c841e41c440c1034202c1143c4104032240380c2045549070640c8103000400e80d0142c090092400c0905003c540b94076007a000715a400202d6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 110043336 1250 110042086 110042111
    0xa0602060f060402090d051009050d02030f0a08150d050d0206010503030a1b080f0d05040b0a0b090402010806120a061401080f0a0803311101020f0c09060d0b01120501 73
    0x9220a5622414141e0301030005501c41c14a540a03100001000304203a001c03035519200d56041c000a20640c5500c5c54441a0810500c00100411003100c2414030045150601424890300f0600800120390208544030000c9920352840c021034011641000b40300352040249460320b19921101d014030b0801500030300d00001454600070003a20a1b020494813803080c0410450310a40e014500404100c603100c030300740f0a05001e55001e202070000300324000c2d0001101c3c10a820500340024000b014202c003281000c0e0b00c85061f8459010103a040f660a080c070f0307003864851200040503c0150f94082e03803107100301304810051101d540c0040c8104c4100ca40c201019980300c200841e1142d0076005000710b95404004c24a000070302c040e00440e8015245481c45002032049410095090320086c21001410810001030040c41024441d103492184240020500c1003c104005a25880e42e424070038400c4218000040b825141d10705020085680166000c810790b03140d0b07450401c81030416100b51080e40ca132201c00a41c8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 110044586 1250 110043336 110043343
    0x10902030c01030b0a090f0f06080f060c071109100e09100b0a03080703050a02160f03030f3b04050403080702061b180105130f140301050f01210515060a0602 69
    0x68101400d21700c60107080c0f01d8030300080c01c1242c2d00d040b81c0700d6030f41c0b183c484690707000d103d0607020b450100003804000c0c03903081ca018645400070b4640701101c00100042000940743e14009500030405650100a940d0f41000c0c034680e400f030340c1d880281041410030400c2032800c80030410090540050804201c0c3e44890b8051080c14000303070100400c0d2240c00c00820001c01e00550207003618907418412039208070007020240d50304070481e5001950042c01003906008264110f0448080c1c9185868a001003a19200c2004281114802c00503081403043e00102602946c0764a03400c41400c02504c04d018a0400346402003520404a500d20014010340300407403415002c0c10605103034644da20341d10605008007101900407045249800301d050000c100580d012019461005500810f1740240303480c6401c1c40e083e40d0344901148451060b1007070740b500040142070309207200300c0b9054519401d12030094582001080c0560441032034050420f203d101d490007492038036406c0c1c1c41d200750400c2e40c000310380646c1c1c2e01060380d4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 110045836 1250 110044586 110044601
    0x2303031e030108120405030c0405091c0201090b090f0a03030519090b040b0f07050712090302030607020c04050a0e03030a0203040206040317040501031802010c030819020a02010e1c050f070609060509010902030c0103 94
    0x41c150010b0759012110b01d412b40240760408007200a0318000606400340f030341c1011800040030b025035101c070740380f07001d028140050b15844103010780501103484103040d446880300c0c034650009040c140c0d00c0001c242400000620041c514082c1001045114603a003003d100e049030807101101d603000a4800a107150000c003203024010315903511214245040c9955510b40100702600803000c003c420100000541e60410869020b1691030b0003400b04a5a18410302c402c1e2400101001565420500700c401c900c000003084a500140c017600058917520740c2e100154041c402c030340c00a0b00800c2d5011180f51100c1c1c2c1903000b40210385003600e003040940a00c5819108800c000f01d80039001c1294040340c43d020034020400194803640e6a8409001a401d2680e160100d0b00328100d4800141e40d610240007011004100d0303c440d0251600020140c3c46001000070401e00c00c0c00c0d1340c000c68001c081800340411819410100344a41e01c00801d100916008483c40d000f442c003000241d2291040d40795003400355009109006 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 110047086 1250 110045836 110045839
    0x40512011404060504032a0c050603060102211612091a0406030c18060e0111150705070303151202131a0402070203160e0610092303031e030108120405 66
    0x8040d42e11902e401c402088010420780c14464006650304400340442020801c400e1101c4c1e61449920007070604084088103901300600803801042402016a0005031107442d0208030a4881000420004156014099000d0802109030350501880c00c100300c0c10744004c1c0070300082d514600102c1d510014400d21040440101040f048104400d2100e1842a0403611070b080b040c7c100948102c1d011621000c9012040c0d10450000310827681c0c0450310b690044a0401d0240c1400040c09030341c01512541c900540e0141255040c4800002d0782c000f0180a81c009040d0710b01204200c4414659071400c120014150000403407240090190301c1e2a106401c0c4612814000d0107800c20076030850003020301c00254040c40080c8e90500c115110f012452812020f628054411040c2e44592402c3c100244012100c140001d00244000414144550060420b2a550350072400080100d02c0b2000804641140b00710140642d840801d8201552100310820046049402c0c000495030308148a49001c01d6900903402100d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 110048336 1250 110047086 110047121
    0x50f0304030f120c150c02010c020f0c01031d0f0c0a06030e15100e0a020d0b010801080a030e010c12180f0807120503281b0b04060c0e040207060204051201 68
    0x1001060360f00948250b6000d0f07070b0a01180c101c4c900d80714050b203100d40c07070394680c800c40d1100409007400f035081c011035000a81600040c0600c00c181c0c107941d51521202c078105810940d44222100010344000c4001410002d05020f4807418080c81c0811921703900404c00b481d006081c07030310740050100e10078440d00891990b030300301516010300c45426403a4031100c0500170300c1000c004a200403030a003030340c01d2405000325115800169524100d01080c0c0913512901e03000f506110700318004118460b00810040c0f1441c4d810718100030f01900354001a5094044000d0190042e8084401c02c210b007600305080c0003161000f0758010541903070703e00e0040120450390003120325a4010701c1082010030000c5006601e03552081d802e803400c2c162007186c0280c034085048031007600c41041a04002113507410140000000080007801400d042e4a9118026148409080100030b07030380d00c42002c050b551146158820344800107000355941d030341504106000e50810b000e42840748100c50b40916200c1014031a40703120b0382c08111704 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 110049586 1250 110048336 110048363
    0xe0601050304210e0a0902030613090c030305220e060108011a0a03020d020c15010f05031c050c070302040e0309190f1806080102040605030915010b190212030106030504050f030403 79
    0x2c5003000d0940400d61000e11000315a411515030b901d0171010090040090016203d1912004204241e6421603c030781c03a030b62030004a00f0220740b25090b442c003500d4240c201240c0c2c40b040c8422084c15001003014513050340d030481c01d0101e01070440a48103400361fa000da07111100d60b600c0d1205200d02d10108440720007108020004080101e01a4002d003001c5031419100604200c28141060309103000040c45511000b2401c0051101d42001e41230f590107010290000c0060110440010b0f03600100f8200c10303c148503012035006041c1c3c0c400c01040000d142c0c054001e021001ca00b8007280d43c3c0790012079009101303040403024604032414020200045851113a80310280c0d62515505a220b14030b102488480700c1d488140200c0e00900900041c0300908582d55055a685000701080b418511821310752424004400010080c10b907100c0c0035070704650308040ca11a187d00c801c20041c0d2a1915140b00380f6070380c15000c4000541181c140e80107a02c00d9008600f6a4071159010081c951039210702e0000803c4000117008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 110050836 1250 110049586 110049623
    0xf1a04030e0f0f0f060f0a03021308192d0b01080f060f0106050c0f37050c1302120405030307030e07030b01090c050f0d06030c050307030816080403080c03040e0601050304 75
    0x8540325544c4029100c075203003240009402c80703140e001d102c0c03c03004280c0001340c0d9070540c0104115030700200200c1000c0c0c000c510503125076551020300d183e000b41203100c502c3c1b100130b145a01c001880803071500a2401c4c1801c03158601d0a4801d4140c05d12401d10280101441a0a00000440d10520030741c84007148000ca42e0a0a109480036000340c40d1305602e501c203420101c4400346080000da00b48038400c403102c00500350340707a40051050480312914280e41d048600c00d2400101d0028001851401c1283e081003901174404c2010000d00608183c41c1d4288071110511040c8071001c4021409600307aa901031011250029a13207955200e98030005110038502c40c0104484800703503102807100a040e15089180c0407100c0c0f40c6421070f400c60700c42e03916110381d121010410042843c6021009090990140030345500c0c6445034203950140050009a0503185d0540d502003001c04e00880380070315030008410b503c80c040915480c4c4d481d00302d0300071083c4001c0c1c82340110342150301400c2074074416980015965041d024049 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 110052086 1250 110050836 110050849
    0xd05070c210503030a05040c091a101103070b010306060b040b040e0703020d0507170703050601120b0a030611180301060e04110a03151406090108190f1a04030e0f0f 72
    0x303079000410010100d4080c00610188000e6004004041c0003041d00c0c2000c4c2041e82d81c144040e17115203451882c0040342180403040c004070003040c42701200c440d518040300f4081582e51a410340903440c8140400500c0c80704201c1c144d903000341a03900404041000584908020940703210f540503042140c0c605000400122146141c8560300203143e00e809810542c951030403000f51282a030b003800c00b183c00311003071034040c2400c2c005584d48450359107000d01140c1441c40000e444240d400040d170401ca600e400c0d10201035141d05284038021036001804120b01040c1d0701c4404140d0b000300c650040100320300e5803803140d14038050080b01c05a94450041020545407603546e00c250041309116a42c20880805000010401d4400048000704010304041205211101c04034400e0078000d00003031060000e40010300020400141000c1c031200300f40854052a501420201c2c5070038a1240001d207911703601401000300051f1040d116026501c82e0b110481d848568004100300c113800c54031201d07005126252001310920702070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 110053336 1250 110052086 110052119
    0x1061a0706020403021c050c09360607020f0f010603050606010c02030a02040608061009060f0303230c0a0c050301090201140a030e01020d0905120708030106030f06050402070c080d05070c 82
    0xa040c01440e084e9030350301140031a21402960213028646883d01c4c01884400d1000d0b8100d40801c403500d80380c91030701c2c0313040d03207280c046910100400c5081061a000303283c41101c2105104031045040303594600e03000c100250b0700c540d010154079142c0680c8012a4041d41c05004100580398460050501c81d9619001103924400d010fa042e44d0511420f02684003585071072045002170145240a40881d240039410000c00740015842007641d030349404001c002c032240c070701c00074000e580c2d0525080269210484481c2040d030b00c1b014148851110028081001c040001444282e09125068820762117903110b00301404c031004090040d02040040e03821142e6900c01000034425480c890130009034003440c0c8400c46003243c0002c08014841c9969603480028040d04002400b03007159003007142c5280c9500e42d40c920540e400103210385c20905446a0018088c00700540194014040140045444584a0601145c40301035485400454081c070202142d803184210110740d903017900300711501f880078601700e14045d011205c0c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 110054586 1250 110053336 110053343
    0x1031a15010e0f1215010b0c0c13020405030f0d12020406020d0e04022a010b0907170a06151d030d0509010e06040f080708010e0a020d120e030706050a03060801061a07 73
    0x220503012040d41e4070182c0410403203446000500d0045ca1080040e42d0080c010382103078414480038810301d04119000a0071000c004001d41e0300200404880701070310080c0c000c81c0c00c4540d050088184860040100160b0701281c90400d644032010740b010420079104a1055001d07110041e000310100c2c002c11409000e8462402001030801071510218201101c01800c1107000030590b1000803440c2d0300c280038240101542800121035909030385c101a00090a2502120a4482c1d01d0450200083c81103115510020082c56440ca0706031003100a004020102141925407281c01007080d0229001802c001039806640111602d40c54170348100c800041d5600041b14404540c0100b00704400300f14610803013248801001c0000090004505040d80203003510480400c115944e40403080070405030b5124100c0c400900c1e046807482c400145031020895a850f02103410542521640c6400508030358010010a03003884155020008103031924109801d07904140309444103403008104022500c4030020061070400d20 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 110055836 1250 110054586 110054599
    0x204140d03120e0f10020a020703021201140c0316020604030905040f0b030a1407061805090406142a030c0a05030c04030f1203050c0c0703110103110d0501031a15010e 73
    0x80a041c440103a40000903152140c0d00000c41204d101d080410450201c031a1132441075040c02d018070303002551070295100103441418028016009203200394031000c02411a98143c0c1418a0303e068a602c01b1b51081c0d800d00032005105404100561000c52040d0055a06039203d43d003451500307041102a0010110380302d01c2a9950340c01f140d003036500b00090745045224824001d802e165001c401420410254421001d008910047d40c9500840c82c3ca401e05a8070308661003821601c550405800906031040407480c0c20b000c40c0244069a1500400031080d104031000640b0711002d0b002c3d111000340001d07210746241040500c141d00c05d40e401480510340c00142c900c0c0682c01c00d942c0c0e0301d502038450302c010001c0d00e0301c2c0034040000ca95590315008855000c0030f804403081ca440213000c5101d54403038041c030002e4403900703000350050700c176078403d8000040c54078814a410340c403055102e00e400000c02007840221110420f80025201144080180900c202600c010040200042c200191082d6051401c1d240d030001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 110057086 1250 110055836 110055857
    0x303090306010e010603060f0b030703020d1b0918092001020f100f05070c050c0103240f090f0c0c0b0c160501290f010509040209040507020609010f0204140d03 70
    0x2202080350500803c0c0c609004100c5514008000e8100c401c0e580122050031840340b410b110900103e4100d80d04080140740050b07071111481d158030018500480c4c0f80ca13405e80400c00d0306084661021011050300c10704242d89486e145824003100803241e804200401c0e1840c0c45854540941c00300c840850940c0f010300541e520846210303a00f42c00d0184250221000c031346c0c0c40d829007041590905c29540c1c41000c0c1d04200070704820f00d8503259650007419035003a04064640b1132180130496414081d10740a0001a446480076031141c3c0d81031442c5005001d120411440c00e0103030200c000c5d00c0e00030713203111100607292200c1a10050315042e03074102d0014100700c81d44408200381400410f95129000c03180740074030000511054494050810109084c80c5021410172401c0c80006a07500c0c0e483d46905900c090030700c542e81c0d68112000c98013a001d41204507600516000401043d1500868803a21541ca0000204506d105100d0400d08038000c6001e42c9026918145421040d0304140048510703142c000d0504105a1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 110058336 1250 110057086 110057089
    0x304030b1311031212100905070f03050c030c0708070311060403050a201002090409050a06060513050c1207270f06030e1504032007050a0b09031506030309 68
    0x4040541d89044008403210050040c060000c6620012900071009410110403800d5203203101c3c010806a60b85030704601d8081680d28804000070b2006000c030302020301c0b4502d0309100c05030140030006007c00c0400d051000158007902c0f65801c60388611000c0d080b550804c50070340c661a00700d420242c01241404801094603030b040f07908000052080d4171a1351665038176408482c0013003a0441950011071440e10605884009410102c2c01e0401c410380d600340141c03500d0f58140007c0150841d1200a0028050043c000381801200d82018055890690784030001403c66100d842c11100100c4203035501c55400c1c411082d40c1030000c2034064101c03206141c0007100300100d0000010b001581200d0300300580c032945041081003007211580340100110300b001c01410030500300e00d940b141c058410130101c41401c4000113080500880607400000307804a03140d072800e50301c11000341d990b400134003d95115034440e05001401c00801021250301d81c03405405000036075005103241900b15005010380f80d00d80802e22041c10213 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 110059586 1250 110058336 110058353
    0x403050c0712241802090703060b22060c050d0c0c1d0a060501020c0603010311240d0b060702060a0f0e030109030c021807020a080f071707060615020d050705030403 72
    0xb090b0182140c408a90344600c82080b06849854042c2c03001401c1074843c3c1c0b44040d894082c0f02031a501903800071410380d5010340440040c1185c0c1c020031140c20004c10300c54050a807054614428548290302d011001e078560400b030700c00540c4000004e00d170381c1c4514040442e40d4801e414412003980f01d011020402600c0d00b50001000250700e4041d0010011102080030318032150040e05d00401e402e001030510411000e010420601c0140070107080d020a0840f6040152542c0312075640803c00c4a030319041817a0f00c5400221198010386244561500f0300390290804d00e031030002c5030b04099004040501e018440001070742d100b0400300c0c4540a01181e0202015161030178000c0e06040385c8281c1d1303a0001c7c1407162040040c40610300d002d050042d0322850070024143e400084c5e0f1886960052091601d0b607203646855181845600d400522240e64803840480324440d1901805186100d074205204050300c0c0d440c401d507a10400601400180e000303039101a0aa03000b04010a03000303002e0015245041d440f038031360611 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 110060836 1250 110059586 110059619
    0x70303020702030105070f1d0607020907020f060603030406090e0a09050f01060302012309150c07031a0f04030906030207020402070618020111010c05030a0506040f0c0521010e0403050c07 82
    0x400d03000140c0304210f1400f0310600d540950302d400d0040502050280003484802d10300e021246281c0001948034050b030300c800903a1015030340201b14156038940588025210114140c4001c280c1c0f1400011854030f1a000c0252016650155120308040e85861040d07181c01d00c015001401c05a0364515580103c1c0017406240d50707030300d0800001f01c4c6241c40d5100041c4929443c003425004120802120a2002c00301401c403120107008850a621486040d015141c1a00c600101c0d840703103204032000001008003030f01c2041900006200300b46001d41c0c5181400341c200c03201f1900200021062981484014003030380c050014107001500060928016948960444503101d42011100961485650031503a20004030260440250000c0c04018903044001e0708a002c05850058900e03200c03400501d107616158401280f007080450240001d0f03410720400390a5038007046a0203044280c0045518461401c0c080c441c0c101d42c0500c01e20241503407980c070200d0307017900b00c0e01a03400f29000d100790006d88002114800074 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 110062086 1250 110060836 110060843
    0x30c0906041404063c090302160f030c1706011e080307052104030b060904060b0d21052109010e030414030d080c09040b0307080d1205010e010b0d020c010f0207 70
    0x515054812120a100900d0f00083d103e05219240c508000c417480081613450415445001c034a10380c0c03514061f420061084910080c0343c4a50000240009041e00340300e089074020030b080c210070f54072810f01d5a0664a100c82e40c1d45140d010343c00400004000d8402103e00c03124100001c6491600c40b010329041d03a00c2031a060361300e50b0007005a00c0400c0c90300c18100900c100030350045071820f4507650312060b0010000706000c1c0b00301d10b1040020288109508001ea10705001805004000100c0c03401700045249802605d01f40c0000740200052a40960308895903140800c0c802000c000c4211892205444002c115005030754035030b040700c1e40884080016102401c400c0381c4003a400811030042c14549003a1001040412140e41d0600c90007171008011190003540070344002c182c2d41e100101080c90010980d00120320ba100300c0240d5a82153b1000940c840740d21801010311042e6618085550245028015900ca00c0e0040001c0e069680c0b0a500a00e507601141d000070550b4103c08020304101d800100c001c1e03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 110063336 1250 110062086 110062091
    0x206071202011b052703060a020c010b0a0902031905010503030d0504020f0402030403170c0f0a0c0302010b0a080d03050c090306010e07030b030d0509420d090c080f0309030c090604140406 82
    0x448685030919203112800e10000302c00c0d01c8205c0c0180040e5a0703d10241941314420390000d8000386c2c0310300072b400040520038043c1c40000300c1e95a80130814000e51003100c0c0640000c150b0030080072030018600030b49048841c010001e508112540840b0402040040c000f01e82c4071101e6805426681c8031800903500c224040e4646810082086c29000c1490400510903a0945c50070807030114179a0180c01a54480305075071130200c590803080d141c164014100900110340c842d00300781c0005200d54002a00e40c4000c4941e58040c0311039210000c20002034001d10401caa403540110300140011030a460b02551322012614001c00c4840580e404a41801a04d1440b00009400040c01d5a02030610300c030707010b40310807028035101045d00405800380c8000c61550140111110107107a00c04490901c1c0342540c020004a4030204080580c0d8607052807541414401c3c10014041c1d00c048116008010017036a12841c4054042d00301d15042c035040050182c0001e044943c0640e031041e14011014110381c60522440c41030800 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 110064586 1250 110063336 110063347
    0x603060f02090a0b072003030c060907090b0102070f05040c1206060801030605060603040b01050603100305070e0402040b0102060c090103180b090609011802010507062007111009030206071202011b05 87
    0xa01400800c04e41148662900c200f00e850300042d030b0541101c0c003401c0d9110741c1e0480070340002c0002e070541c8a51608010148034000901c060400003040c441d0858401e0102007205005500040e80c45080c00d10901c40170326000442005a401d04d504281d07500300312403604505d02026213801c202117503a2034001d00c0c0050010070050080004521840b45c01000032110603080d85844c0e030b2401c04402d414003403140510000b00200e0000700c82c00a00314080c60f489420307a500b007a00d1300c2c003880540e00e086030180c1c851403c000c82818594008521940541503210302c40e86041d6000e00150040c1c40c40100b6028243d41040d1310402043c01c000746980900c501401a100340d040052245094034002d5120484001d1403022100043c0e82110880d4070441d403004000c81c0b400d0700150460354086200049140b0041c0004045040113920250b08980010803144003510045100341111b0500480c00000c2d000780c0c00f00420030116941d00224140080d00d807001107900c0c440310802d048009001003400e0041b54020a4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 110065836 1250 110064586 110064589
    0x40e0a111803150103051024091e050103050304060e0102101803031505030c0d05240708090111030105010c0f08040f09050105040506061603030b1f0e040912120603060f0209 76
    0x80404111081e40d43c01c1c501d541103480f6541c0306c01e10302e4642c4070b4456840d00a404003008001d810102c00000504180a0300c0d070740e00340e80c1d000e40f01d03011112032106202d25000300c2503440742c0b00d400e043c2d0340c00800031804c06007002400d0300c2c4c403081c0c121b00300d05601c24440301640c211218040d8008980ca4122038580750351461074040c0541c2d41c0341e00400389002c0000c500740000d4034005190481990100c075280711101036410101c3c184004c4d0149c8180e4540f142d101c0d02d84281c00355044901031036040e91400c40e03550340c54107128204ca003a04d08000c2950710810041003039620a10080d52240d02030707001c0c40890382e456558126554030541c0b04023000038100208001020f01880b40c00c0c0100320581d42406546403641c0014070502c80c9208150f070200b000d80c021410f0600c642d1040c02044d0300a00b103844403c0552003102c41230a11240138000007100d0032039010850138103020b64491503a000258281c414090402951003030380ca0900c0d41a41c6584040000c0881e1301405807080181d8980c8005030b44d41c84250 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 110067086 1250 110065836 110065843
    0x308190f0c0b07050913020a05030603150f0403210507030b040c03050c0a05030c19030506040e010902030a08030703140109020702010906090f05060702010309020907031d0a08040e0a111803 83
    0x54a201802654800940032622801c62543d000b03505103400c940c1c40c4040c40c0080d208081da0305110546620129141041941000046004400840840348450302920f801441913008403a401c580340d02c2c040201d000a80510a520051245a52110340c11050313640d0410071135800b100d44a000a8a8100303484503804c0c03078464098ac11a6505d4203201514180b00303c1e09007440f40c06070000c00c1001c00000124858440002e6800c80d4013022b054940ca0014080d000f03011740307401e85c2e001d441240b0b801d0a030580749505100382d60f513007030740034000c0c0405a0203500c4031075503504001c181c82d09141e10b407611a44408410307020207000c2c1c009a84e00588580c65400018648110750700144140120102c040c02131407070343e0b0460812140c007282d0003680d9042072301c0102d01600a40720700941103070401c0140408185c05402450034004d500a1400d80c0c1c545008007513641c4c0705121000760610a0401c002e01a144580010942c4100c9404012400114580036928154440550810511041a50000b142c641807 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 110068336 1250 110067086 110067107
    0x60d05040b0c0f03010b0d14010306050a060e19050c090409081b2d1005180c091302121e0304060206100f0504021c1a03100c0f0c0804030819 62
    0x808010b403c0620001041081388010302800900440100702102141e40c550400d0542c0268042d0605280d40d4a140003070103003d0585068000c0b90410101003044440c03030b001203114a01094541d44010002c1d0042c2008050103030001101d040304112003103a80e1600c1c081c40c07041e9446040960340d00d201019071421480d402400c80c080a80110100101101e0380c03802d80c001c02c9945c9034580311848600100203141c0390700c40c82c14010f0a401c2c142001440700010840c68044074448081e544061450010040c5100044a009254056556a04015003401c8041340f042c03071102e8044449014100003682c206070080c61050800750b200150500c030440c0d0601000741c109262004020145041a1000d0400308a50040b24055a40469090703140d109a622030708031401c401d9002c104002042c0c85081065003c5841d2900034072590740c1c119000103540c840c516080c0620358400200b9034900343c048072601c0c0480c800b59425041800003102080b40030b4010181005914613881019564000c003030047e601c0c6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 110069586 1250 110068336 110068351
    0x21b04060302180a091e060c0c0510020711030307050c210304090c02031b010f1a0d0204151e030204060503160605030c07050304080705030c060c07150e060d05040b 72
    0x18003900700016154207082d01d034120110703c94040e1550b00d04a1900040030852005020411255000c0707400f41c500d0795000480314011001030010803005035007500c0101c680c00c0d006100e1380c40303900866010b1311a5800713400402d10800001d001ea2012200291860b044160b0548058120300c0c1141810315207400c0f41c46900c43d0810303002e199420078040346601d90140e44500b001c0c4948031021160b41c2c80c8244100c540d4800c2e00100045255804a00346000740210103007208442c3c86c2c034401c604050509041c5810f0848010880d1509401c0c9509102c0504408144012181c0c09100c000c12011450004228032164000341210124594010041654801c0e404607000e908615030901c074803e0074901c16001d80302c2a00740142e07252501043c0e8403041c45072600c06041030002290100307400001288080c02c40340c0803000c42d10782040c0c410421003244108440c500c55a48820801c025814400c0113422050740076041c500002d80f084004121a64003884074040e056aa507410001045000000c4a0b0050072 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 110070836 1250 110069586 110069591
    0x705011b03020601062604050a02030f031305040c033207080106020307060504140313081c050d0c1b0b0a0e120405190306020403050607022109040b1906021b04 70
    0x840c1c401039101c0e04107005034004c008080d454240040c1032003c2e100d01d031001d007414501262030103041040e21004038500403840f034016031050360000342c000000e588888403206044018203180c0350405c0014264144210145601c80342e0942c06419a1001d44c808508421081c2021f900d038030511075940ea50040c404400c1c40070242c01130010301c1e8000141c84085605c10400901030302c50b410141c800d51526110003a081c03100107070000b0720340040000340c41128001012214108a81c40c40c4000350500000c00d100051024801044040010380095000c0104d90620300e641d82505043d01d564120604810b881d0b030b491541c103014420100307103c2e225101c0f5500020b841011650011485c8600c40d41c4a164070524003021084101c00e00b0380c00306401158840000c5581d1035492806949a40c02100c200003d0300070001d442404c030002c03075a200702c0312103949140c606c0c0c1182107041000070542c1d0045190001000d421401605404c01c00303030b10160850b034000b000880d01c4403501c3d172280300856140c030b40600d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 110071942 1106 110070836 110070887
    0x4060b0a03091a0c0703050d110f18090403050f0702120609061608070935161d0f04030c080406030c080601020102070506161101060305070501 63
    0x14403c035500520b10300c0281c10060307002012240c1100c0c5040c2004074400280c03140000381261781072140c0010354084684903003030054111191222407500b0015220941104004001d035248000701c480300010314166500525600440b2a4400b034107501003240001c541da60503034a140e05400d0412547c00e0b1400c111411782c0c42c1c43c1501c02c00c400c1954503070800e841912940040d8800c00854513a03505652403c1844420107024024174010321a40c0400c0104022000c1d00021040710b2180042c40050a05203154010000e07952003105c001030416490f000e24841c100c04654080151449100c060b5600c1c2400e569018100305c004041d44000030b030204441c0e406520072208503a89980e034043d590b540c0d90040e4200e219685000d0b002d0390140002544854020004441c90f04c501e25114100c010032800160940f0084d400450f21030304008410300003560700101401c10761031241400c48008 = true := by decide +kernel

theorem cover : BRFrame.Cov 109892086 110071942 := by
  have h0 := BRFrame.cov_init 109892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 109892086 ≤ n) (h2 : n < 110071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
