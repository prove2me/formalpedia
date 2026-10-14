-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3322
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:19:25.050915+00:00
-- url     : https://prove2.me/submissions/a4b83dd4-8ea1-46dc-86d7-785754c04304

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 597302158 ≤ n < 597482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 597303408 1250 597302158 597302201
    0x31c1808060903040504150909053307050d060f08030414010504061b060f05101a040501050d0b030f1c0f09030203190303021b0a0c090e030d0209030a060f 68
    0x4030800a001c9019800c19800381d0306040c200001c1c0001841c420665220820b82030300c00040758000d910038450040d019901a000d195000742850101e405a46441807454401005135807000010809280c2c0200040c6419075585c030904590401406564201440a0b2000540011004000001031045804114000007264000703001942e1a010b06c1c4144404914600f1076002c1c010302001002810310f1142200052501070040004e0845004840c000104c030b01d20751301030101c800100507100320b030440c01c0c9070703640b0b000d09000008015011f004045903109488071b0f00c031104d594003030200180720b040020890f98074814042d668030102c4040356400b0049181c102a03402da8522480c5500c003035907001350080445142c480c0303c3c0e10700180c00c6c40d000e404250b4280030f10294a032820781080c84050b103283c000e00d440c04040c1010003491160354803141116241c48120b91140d040841610a01d2090800c01030302d9140030004a801d00c01e0001f002480c02d4070b880400c4c80c81c030110740d0016019000c0c440b844481c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 597304658 1250 597303408 597303419
    0x7080102041a07050319050903010e0c0d0b090123014e0b0c1b0f06040215040b1c0b0103200a030603140304171605060702031c18 57
    0x807885a4081c0c1d0304169a0040002d100407a020003e10481e0b102d0f03801c503440d03c855001c00d1244002440070010000b0b10000c2c540c1c1c02c520b02401022040050000505600021700780021030388481d0000c01483d154444000841c140c0d804e5103d00134640d500900403500308504411022024001d01401103280c08020481102c400c2004130345c401154003186002506c010130000050408444511540ca04600c0c03480c0c2001504074898940102c4405a034686c46001d21070348041c2901e41303004c0840e010303030243c5002c210040b40010129080f40d0180c4140b40440c2401c0c40b44c050030721854020348280180000c142010709105102064489044032082204101410044060340c4040880501110300003403180d10006240004145004050074000740c007640d6565100f0b5000c0c6200000d00d41c5400215041207003084882c2d50029030280500a482001c280c070302e0400c2039402c036005107801880c000c5886011500d007007011601880e40416008480400100020000120070900818881303440360002407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 597305908 1250 597304658 597304661
    0x90b0a0504031d0303040e09030910051b1204120201170712050c0a090603020a11071e0b07171e07050a020f0a030b0a0c0309290112200402091c05070801 67
    0x3d28240080141d0702d450300d00400401e1140703010308010450301080000500584d2540b0048806840319100c25840c0c14851411200207040d0760102001900411070000c1e08030900c40481c0c0550f5000c1d250400d90750701c2400121640b0302c014010003801e41d000c609001e02140c200c02110380c01d04a40380140301c599622441d440b001c0c0100c034260f40c041009400300b845980d000341c01401420b1500c2c501038400020901c08a407500d48250300c40115448647c101842d0440c44030324010160030400179240c54072400350390311882200207449059000c1e50100344040d6000c00d01001078190801050b02e5912511142010740d12181121000c03842540c40c4224043c241c1081300c80b440c100c94001c103d02d0311076a0f400b4911800742000040c10001c0555444105000a0000604110001110880c1d40d03040116002941035202d068221180200b07500c2e413074800140c1c1c4006025180c3d078048101ca4041248440801c0290080c0d40c0301542c408801068450740310310303040c14a940c95010700300f2521505e41d500c8000e070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 597307158 1250 597305908 597305957
    0x210309040c1106040b160e0102151f0b0c011a0a1406070803041202070806092d0102030f0907060e06031611010e0c01030b040501050102120f040b0a05041d010609120204090b0a050403 80
    0x74094ac011250b100c261142e02d409181d40008031018840d401010080101ca20401d540c00c607603100600440e02e0844980244605d00d0400c2041c00b0600e0741d10001c0c3c000a1269060b803280c00c40394024110b441c072203070300c0c2c010954120f00d900c1184591a41001d207030411000a101c88001c3c0103103d40840000c0c10400017070350600900e00000179210841841092240e0821a401d6000b02e0030115824081003000910086100300c0c039041005c101403c0c8401c03514103104c4294401000c0203588086540c103a69440c0450f600242000c00780c00664003000e40c10313130700170040f8030592500d5440c0c0300c0e07050a001c03c0861035101c2d4480990b000c1004507544020001250b50030b0040d180168841e001003454029100700400d401703240b04800c14103180da5410640150790051031200001b4001050420200d044098520240031082d00345525a60410304000d11469075445445050700c0d00c295102c040d911154007100703080d50007000745101844c2410420000e03010560f8101c000814442291840210003031504 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 597308408 1250 597307158 597307187
    0x15031209040b041e0f1b020c01170c37091505070b0a021e030a060609061d0f130603083105130e06100302210309040c1106040b16 57
    0x601c0d44c61894003c4002c18844c0444540c06564004e050640181e800c4060034000d2a94003c205045000000615082d0400498440441d0030400c1c00302c0310800500b95091403641344000102c0100000d0b001c1c3c810211000d00304001e0503144041d241050b8040031840590701c4112850004001048c005c0300c03284a80d00380a4494222200862866030b0180c000300b0748020980a001c20103642c3c0303a140b0b00e460344140e0702ca860b420390f18070041147caa046a00d0301300800d03050030284060b100c0101c1c502520400700185ca4802c56008007416115a03d851202201c1403010100b046504d440b8500900580d200da1051220030056040003064149142c1951101021022a000302246460140828003d111401116190300c0303200110042d01c0030400341c2d10404036040406203040c50f40c018802e58101001e003940725650355981b0b00070700d614004210f401c410825a800903450700c0f0f101040b50300865000e031241c010f0081c03e0074402400741c500720045c05401c030b68440000031040000c0685a152604004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 597309658 1250 597308408 597308441
    0x2301110703050d0b0f06030903030a06060c120807050c0102070305040e0a02043b13020906040b03120c01021317010612120305041a0a0c0206090d0801050915031209040b04 75
    0x3200f002406542200441800143c001d02c0720026a000240c4250030407120229036520100030002000098000c440080c030081c01c2c0701c034900c1000c0c0c540361071102880041400b804180d0b4041035680348114101c034030010398080215117a140b58500100035500038400d6441000b50240418100b0030b20384201c400b1102e80b40044400440c81e038241c010b101d07003201c4400c0c0d0000549440b40d640b00b80405080c1d40f04142d001c44900142c01a48108407480b103018140500813460030390400380780d031400030392403d10030184003505488201711041380d07003e0f11910314070450700c01c540340001403c0d0040100d40c4144002810090001e65101c070b52034043d18140c0a805442c201c40c0002c042e01e0303640241c0c0b140390041c1c00380660059208500880e40a001d9080d00d4900c6120b60700e0b100561555414081c0e260001c3c0040040c000036280403c00038000c01041c0500d511480f2002c021400305147c0102040c011880a0242c85070074281da160300d06650000640303035000e503061400200003407a00788180c0c90380b81600303500d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 597310908 1250 597309658 597309667
    0x2270606040602030a0f030b0d0303050106030c030e06151f02300d1112150f0d080f0c0304080106240201020a0f0e06040503010203150406050102060103080a1803230111070305 77
    0x3c08840d5403041b45040000c1c140d0320226841540c4503100c0c0c1044a601a03240483c0b503501d003840007011603030f140d01440c0c205423809d403282d58603400c045406500300702c17040540c0c0400c1c038086001070000c05148034042d000c85101c05001100b26004a0103410403100323500440c44000c25001d66480d504001c03400c1c03030868001002050381c0070505500ca0208050001c0d0003a0404040c4031038602c00b8081550300046901058207803483d2840c0c200b0040c690303190161485c4041d04100d036904491400f03401111120300301c022030f0a8011722400c01c180d80c01031012400034004140c1d545a0001d01c1f42e104101c0c000c0d88800c9000c010b00d40c0e40140200c4810003242e0703841c060082e52854003140c10a03916522182d01950030407000603140d42c240061400b03500ca1220700c2c005001380004000c1100c1880e800541913400c8000104081001c040544007c82031a05150020f42c006a0190852102c16000100854860012110b09aaa0038644034100da24003008011700d0810595000c0c650091190040c0010030400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 597312158 1250 597310908 597310927
    0x40506010603180203061905010803120f041412040315051e060109180b1201150b0708090d080c0625030f02040b0340020d030c0227060604060203 64
    0x40c80f03d40714896810610700707038526640c00a030600b4425910040284403401c10b10000700030a12034140141a13803030055190070b0043e171410041042c0180300b00d408010507070000382402590119011200810002d03160110711440300d94001e07130000d00064440c07000031000c9031a40020380c400d40e030084001d8440d107403000070000c20401c281c10008000380d040002d4048000b6081e991142e040400025100c0301051496540092040d0f0b140070480d00748850303040c5120074011b07400a14080d42500c8a40c0740c10fa41d50111402c0c40c2c1102d1040c81d800c3e54028030443c0c01d00003441400c0000d007054400344015140283c4071043c0c0c1c41400800400041d1070400c900c0c1d01608020300941c03040e1700713413540d02d007016003055541c2400c4100780c0c100316020f030201003105040022007803946480c001e0750094152110724043d0203c0710320803800c0000760000c2c0511525030045060600a008005d85982d00501010b4900700c420341306401c4036400e4200301801305a000100d003c620784802507070103540c81580210704000038034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 597313408 1250 597312158 597312161
    0x20f0702040b010c06060909210e010c060608120307110106050a050f01090302091312020d14070602121f06081501051308120a080a0e07061d0a090902010f08040506010603 75
    0x80d11150521401c0c0c50543c0000c0c1751401104014034040c100029440258100500303d50b01b80e40450007400c00c1c1c48154094550003290842400c0300c2031808480860491400740028403003a00700c000301c0c2c0f240d466640c048020300c100662203920380b40d4402c070304910b020540600340d409074010300394072039407050b0305005504011440059203a014076042c84c900c1d0790381c1c012440d0124156010368010725856880c00c00d0000941070007145480030701c0100508000508004c042d01c40c050203810701102c2c0024081c040c400c0540540b03401082e0188103810b17a0400003c200452020400c1c0d8900c1741450200c00a034040c040c2d000144501b404042450503500803100456007a4084418a02c41d1400510003060300313401040380000500b0b011101b583c0e03590100c00050840c64008111220f00c40c00c0805074500f004000c5070703c508070341c00350030300c2450070020f11460140c1c0781070400702541080500e01c00186105680d044070010710300030b80760004995240341e8112620181141c001e0105e0f44040b004100d064800e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 597314658 1250 597313408 597313421
    0x3070e1504020c07091401030f0b060a080d0e120102271c151a010c020d0312090c140a030305030c0f072301060b040513020c0106081903080a020f070204 67
    0x4094031420402500000508a0300804034590441e030100c84203000c1c0384210b1003078003402c0c940d91200c03840765851940d44118001800800600c54050000410304545907445201c2c00381901c002074490061403050700034069040c042d00288030f1002d44e00000c0ca104410300c21039150407048080f10f40a02802d5444008100c0036006041e004060100d840490700201601006c0e00e620a240d0700c0007860b01d1182201c1640d13040502880340202d0040d4140c540d030717000300071200741d21f6041c0d8112090031014141500c80080340c17000c04d0780359070070503406000704248001341c1c03002d0300c0c200125100201c18400074025020b0075804002c001c5030b002c001046c0701d00c4581c4007400080804698143c0307801840e84e680341d0041308207040341810b0544030f1403500c41060203000704c0b030280c003a8140460800303180c10005440f014658104007900c950000e50000c2d0100203411220280c080041103c00d071000e41c0120b03a404505100301640010216004207088150f18000c130380c0206243c0d091a410480316400b0000103115 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 597315908 1250 597314658 597314671
    0xc02100e120705240a0e0d081305160611010e06010b03010b07140a1a060102011109011b0209010e040b07090602120c010b0a0f0f0503030f0a0305180f0102090a0501030b03070e 77
    0x10403110703406400581c2000740070102d01c101252134500f44101850306a500410420b45c2c0c4d03400440c2c0e42461998005d10240e404031400401d4040b008450500340e08201d094015000748403601003002c41c0d0640c0041004104001070002004100034068815841d030a0a002d51070001d2400c0004102d99074004024051040c0900e031806c90920202000c02c1c5841708840c8102c0e00120803000d0791024486032010a640404280000c0c4103000c5004412907591198114580c1400354a45004014403040c4000301081ca038040c082c20780558507125070003c01041128101c41480b4200001405d1910500002045038016001030a08060b50b2801e190180c22002a2024540d030340d80102c3e945640b071070031002c001d082041c0102d8100303003819544000c8142036041940264401c20241d01c424100c9000c0311201c03070322498009015100d5101d503900c402134192401100c0d2240d1001311400715419801003680030360844200d040d060366200154251045c213806650b16130400702080220740015520705502c9030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 597317158 1250 597315908 597315913
    0xc0b0c0307050d0204180b061911010b030106081c170403080a0e031801120204120f0203030c1024050603240303040807030b0c120106030207110d03030c02100e120705 73
    0x100d9010803841260056801b04020f200070302c880d80ca60032150b2081c0c8180301400e41e0051314160a0707003c00721041810118400c2049842000140109001e500c0f4820034135004000303000050f9940003540e40c40740f40551040740c040e000b03440c0105440c01250416026202164854490760b80ca4605807144031000b04440c24894848444082144082c07000b0440403200b04a0541c01c107410b9800144a50346d40392540fa1402d104101c1441540c104403455144e096001c104040031f1a400d10100b802d41c06030810140390351180640b11245028680c006040c2d1000c0441c01e03d80000301e5071030704405120144107554001c00c0400c003041c81541c0c042244da4904c48420342845040008101292031039000da805060560842c400c284108410309010941041c00d8a80003428089441810700c04e10506100c0d40d001d02d03500049401c100401c03420130500b5440001c14528698116060103005040006a0580107000360100020b0480c5544070385614829040c004040aa480c6c40410380c00d540842020f49207407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 597318408 1250 597317158 597317167
    0xc0e0703090b0c070c1a1602031204030b1f0302090a0b0d022101051003030504060804110607060506090a0e071a0c100209010207061d0405070507050d020c030d0c0b0c030705 76
    0x4141d0342c04103014078040d8062590360030a505050100360103541022018003441410443c0912610701681d40c4844402c41c01d14140440b4030000c2e20b01100c070006000c0762040481d0001c00d014610305050710805c007809090111504041d00018100a5404025844041e003c04503020390500c4d03101241c0040e02502c4200c0000b0b05400285600c140e4401303030010002418000a803448081c01159007141c1d80318a0140c0381c0e800c5542c007500a010364000c00040005810001d004d00c005441c0120007007034042c2050b82d440e026800e2840240204980075401036810340301040d0480214481c00000b002c4001c050b1120908040c1021710420252450b0400e142c0140300f09000700381e0034001051584110344005a03107511000000e800c01c1c400e507000909124490200c404950380c04407410051050803140011656600340064406010f91040030b00f0500c9000540f0121340d0300014640c0345107070101c0031620b412540e00008c071780714034041c540141a65075401c0443c1e286050b0002540d0001c1803070800c035003070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 597319658 1250 597318408 597318413
    0x913060f111c052a1207050d1b090302040e1e0f0c060f030a1808070b0103171312021f0e0f090c09220c0306031e0c0e070309 55
    0xe440c01104455146000098680010a00c2e2034080006800c440740602c00c902c0e000c040441201e070a80a0707480e040e01014403100740d09069000b2507031124000c0300f0f901c546090444009000f07400c00d0380450f0710980303020a01502070811010440420145039118280d190440e802e01018100c000a40600c03807007880b000008255200c1045400c80c00b02c0380c0241040c81c28980160700c0c0c0f4a40c200154000c1108004082c100000a02100d0340103200c0080807814840004207607040007007903c80601001c50108010040140d10710311141207030b0050420752110700400d407000b40325200d94808030701d00e250001410004200041c580301400c900003404910148544c254810718401da40d00300c000020711008c9602014a00100c05400031303e0306540c0c012241c03600c0c8201304014401c140b0580e02c13452620983c0b400110105d0401d080701000900140400c0244a1000d0041c00c1180001c9610b122242405e0301007903081280c4000700d03a081111448450700c0e2040803804c010000c0c110004168951200d03101 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 597320908 1250 597319658 597319661
    0x30306050a120506010506040303051914070501051504060f060311042d0b03040b061e04111b010e3403032708060c09011e03060501120b0913060f 64
    0x10300000500e0303082c2c60000d151040c101901600010303c546d4090200b800400d6001051350741c00240c0d120040c111007002981a11000a502c444110f41c05001907603904105040d08810302801510310801d241185210400041d81c0031801159000d0f07184a900700300c4180300b900305c0c1c50081e600c3e0080e149017075218a142034801e13604115010341d10b01c0c04800343e45c008101c0071111008010021302035055040c1a69414a58440900141d206901c03503507800d84c048068500c0c0140802000307104004411501c0d460030001c5c0c0100708012900c080026680d4a0040d043c0a002c9000700d062005d406401e200e203460003100700c2c000b90105c2100114074005000f11000c401040051800707034075260100e0b109408145002c04841598a4003880b0b80c3d5400c1200c244001003440d0440a1590401c4d00c910050004072080c280002e5210075540c180703010300d001150940d22070019101e007030ba01c0703038610151030600800b652401001c0540102980300021001e086100010803154400c12010a410f003c0121100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 597322158 1250 597320908 597320929
    0x604021e0708120a06060801050f030f0a031808070308190c120806090606090a0312030e060a0b0a0b0705030a0503040c03020301020a080f01080f192310060f051c03030605 75
    0x100d08000000348840118140003d29a20640703070001804041d00340350004100c0841840303050b00481d004140745926136002d002000c0c4100c80e600403151088414200100494400300164001c140e40b0140450441c0002c208407080d20341000c20715190500c1501c600501208200c1d40408001d00d2600d400c00003005800344103ca041243da960010307041c003904100c504071025080d64411403080142c00c8513034441c0004142107a800c400e02c106440d002c00700035000390000b601e41202034001c54040160340c02d00c41e84060090703001070702c2c40e89401e604c554030104140720b001000b8000760720500c201d65201d48034000440e4007a20a910a900b003543e02e030b01003030980e00203400c49004566028200b0000903100d10301640140303803083c001c015220000c11100d44406200c00d00140c1c0d8842448114144075160380d9500d10b07a41740311300940001e078801501544841c014031010f0050313800c1000005a074199080003509444000f03203106680507081c4400e6240e1030b1081d80803820305440d00720004441d45e03000d01a2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 597323408 1250 597322158 597322163
    0xf020102120c1c0302071a101809050c010c0804031b1203030e0606010f0c080f0c0a120e0402030f010e06280618031101051c0504141905060604021e07 66
    0x5140009030070b140300e00800c004074443d1003054414040b00020036030300302c1c00801542e00240b010f08652600c40650b40c02d008503402c00044102e81710442c0d035403602c441d4443c00403075004a0030368015584c0c0303500441d0713920700c2c1d902d014000440500c001d10100b0359044070358001040412a50190f01d41d18070410444142d01c2c1000c2e00840d41e00e402060480000344403866000100b46010b0300320100300309001d000e1103100000901040341c0403502d4296040c40300115211041003400710368010f03525240c00885100a0310007040000c0096906000a04040c02034034058041c90311b441c035540c1e0a01c1c46000445500900d165801030150a44c01d0408062229034440040c08407240c5103411304012001e026964115860a2005008001003000c65a078601c012079140c1d0900e46103607100c60280f03002c40000c40c080c2088001c1d9141c1030520080044001012600d0240070040d0b5014001c0c0e84103060b00c09038003440240c0541c0185000403541d203000d5008203102c000b000946008103500f030740c55926941040504 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 597324658 1250 597323408 597323413
    0xc1208060f0904022404030f050a0c0f080a15240f121509052e0e0606030c043207020105010e131b0308070309030209010b12040f020102120c 62
    0x1844000d05081c41c5400d800c0c441514119001d0a107980450928000d1031501d00010000081c643d0b00f94070004111030095800001d002c4140300316041158407109583c4084070052600b01e00000c559401002002c103c1e195240034091440e01030b210341e00d85100700b03610f042125035100c604804404104900d41111480650184c0b825800c000504450002c40d401094103a000148820002080781c10b03402c03200c80144c4000b09003102146801c030b1504500004c00451140300c03c2c841b1402c81baa000000c540c2c0101000144403891591a17400d4071810150b0710540c1580054000300044c1c1081c3c1c02280e8207113441007010b04d05410390410a0400300f00e40c1c031b0031000d0030400700510100d99424020b80340908100041141e090400a004120f000c45418005001740848507030340003810240f207804001960009201da0b900c01880c81c00801038803040c00200d22071541e00e000400c0c030100180c07d4a030140741d401c1c0081080c2e01d0341d407030b44480b0030002e000172411441200b0300c881c07160a0361005080381c540310000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 597325908 1250 597324658 597324661
    0x3030c030e062203030f030b0d14120f0901260406110d0c0815010e09010312030204090c0c02030106060e010210020c030409091a07260403021c0f141303080a0c1208 72
    0x80090010032841b07131b503400b01400c2002c0d0794542e5940d03c5200001a500c004490345d189d03040003009003021300780d87c1440c0d0760603000b00741b0703102d601580c1006020304603099176180c880e80c681c0c3c42d1901c0b201d86800f25080c00380320240e000400148203640412040c00c610349216050203c42c800a074295888900f8a81c0050130890901c001d0b800e15940c0740307216880c2420000c50803c03041c0085050008144006003280d80480030200c00c00740254101c0340546041c07a410700034600700e00d102030030050b0030701c404034000d40ca08003000864070701c107140744119003205901800100026020701c5000e0b4210455980643c0410003002810045034401c0780880c40c4a03030301e96040b6207140080c011821200406103404c1c03001c81c3c4841001c10340d403856a95109005500c1c00c5169844501b000c9180014111552101c5019003105200c2c8030340254000b2444d013050380d510440001904850211801260f0038444000345581e002d1001908a0b8090303c6000d01c1880e0140103014135480b402c40c0040c1d9035907508040b032800320 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 597327158 1250 597325908 597325913
    0x601020c060a0e0102011a101407020a12140d050313020f09010e100f060f0309030e0d0506060307171b1804110a120336030507061803030c030e062203 66
    0x658907c0203802c07400181000c86040400c9a444200f080d0300200700340d1184140080251001361200075070080c3ca11082251514001c501d6100007103000d80c4c04107048070300c0440c4000c000036002c00400305540c03151b085850798400046c41c8010204102da0010054400312076603102c6a641900034960542840c16a04001d80b0080c44c81c10302c0d0300900d03030941041340c06201d050b8108058948246081c46c000601b00e01070b0908907083c822142546074005960748a9005110000035134900801045043d10355460f6100400404085908194103d0341c0103030301d800312041c9981040c500c08503c0640750314940008120342803408882140c1c00c956880c0402c2c4030310719508000c0740d03c80162130b00809901c020f042c4e544025000c8040728601500c80080e5203c1c0c440390640300071420884005500747c4901d81c544918056032104140c0c0142d000107407d001d003280f54080304440c7d40701101d4054440c1c01e41c0c03102689045034400f01792000070741c100c1801c05c141c541704520340d014080c806e40740304000d040075030540c13 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 597328408 1250 597327158 597327161
    0x200f031908180a02090402040b220c050408190c0f08070306060e0f0406050916120b070c03050d022206020f0d0201060b1206030709020a020a05070803070c0306050601020c060a0e010201 81
    0x3074100b905402e00046584800180000d008007550380482d071500b40c3c1d50743c0d480005d0141206e040c009030400c0303220130b164504c0000300722203250880c946001803180d00c4600070102e070f01d0b000c2c42c0324490b01607000d4005c0e41901c066125070400a1030090700000219030702c640202c0c1d000c0c6025440100c0a030701c105030800074413140c1e00c1810040d004035900075410b400c000c02082035070400640f0203000d042e52a0003240095030304010b02c201d060300c40d0b00828013240c5d80c0e842880b110080c80700c0541d03905034500c000621251051b5014403445600d921036a04055040810000940180540020740310b11100c41e610204010242c0100800a80d4014007030121103200b00b5080007040300404042d681080c1d000d00c285807104d01503441c2003079070b0b030603903c40c550f50f001c006072030481036a04c403030080e61000030103001d0254081040d04503540190100c9a029540e0200965644244900035241c5140c111050001070343e20342000d07400c200148100c4a00980300070020350b040e880b003407030800132850300090003001c0d580a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 597329658 1250 597328408 597328411
    0x60206060303070b0127060b09040b060a08010b030a0b18070f0201060f0b0f120a02030105120a050607050702030a141015050a030b04052104180b01200f031908 70
    0x740c0180d420440265900d1182e020107018900a80740980d070000c2a0400d070039003081c00c4010104c0c0c103002d02a0b44040340900e6a100006460141e03080c000380c1b5101d42024411604140c43d19928025140c4c40d00c08268140c2e04090010702502c0d4585404207529950b00a108070f91240000b500b1015040c0f400010b071180c8850700c07a000075a414820202f22840010340d1401c1240c9226046a0381e4482c45e8207031601c2440307003410103402000300f541800800c0095501641c10b03510240e404204500961201c503950744000d20004101d5071040f000180f089204601400d20f003407000c6d040300d10714101a601c1100b5041c04400f00c00031540166040380d1800c0c4c0d54000c0f444101c8000404a0b0482e040c1b5001c034038411503500020b4040d054a0000c40c040110170400e180000301e200b130410801e000d45100c15400c5074454400c3d0b00e0038081d5915072031450740d13451042820f6000141c4913448050034a040384400101e046040d29464095030304124043e030014001480c41906101c000d207004400c060000d00704a00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 597330908 1250 597329658 597329671
    0x4140306060a030b18120a02010c1809020904110d0510150e04020f13063906050402060c010f02040f0605090112021806040306050709050919021c020c07060206 70
    0x56800c1c4407a9449920041e4160707a000101980941d0369003203014031a50840714030050702d03c41e40f20300381c02d9028110054101d00001d03600a000034003498004840303500c1d00c4001c0302480d41c0d440008001c030390070780e41c0113210060028101152405000015a6983d041048526003c90b1150100000120101d1081c4082c003038031003040c2030302e00319100c00611581c000907002d0b00465002841071404240300c010744032100400c55020010a440c1c010003040405171480405601d5038103100c60400d801022440c180c12910301404041110140d2602400b902000e401660040402c0002d01c0072034a082c064101c0c0030091243c00350f661881c140c5030381140c0720990301410411006100c00d2050f80c0e4058048441042101400341e2070304d003543e0101e1000c80c00701034095800400058004108601900080d1044050f40c44202c481f40d83c1c0c1050107401c5600301d0700004180c01035071400304030511a9024001a4a508440e414500c2240d202c50003244d1003500e000001c0ea0200804000140d81001035950041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 597332158 1250 597330908 597330913
    0x30108160b03070203090d051c02330619050405131109011a180603070f0f021c050a0c020603010806011a0c0a02010e06070605012403020909040b04020a120305041403 73
    0x2034203034030007503d1b4007400f058548200c5004c0c8503001400003c0000c1d004414102000c0d801d09003008001a5070380521890510b2840440c840c4683c191507542c00850103040ea014940000daa034407810803010406401e00044000b064180200300c0792560311400744501115402c8452208882c18050244461031141d540f180c2c003842d005001e0050004405240040950f44054030352990481440c00d01d401c540c0e015400460100070006010f40c00401041d0710301560f150500130f41d504840403a1a4240c8071100020110032038030300180248244001e090320881d5142112174040c0c0d95001400720703072080e03000f65a00e0340044011f12550241038400c0340900c0000c2102894420b000c09469103c441c40100039042c00321041c107005807500c511007142c1c0100d600c945d00700810b60311a0024003240309400a5440d4149041510f440302034001c1c8200d40c0e441000400d0b07110300d60740d180e071004503617030009004903048850450000b850079410400c902354036220b902c0d015180d5042c20b02078050383e001031001302c1c840c1c0e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 597333408 1250 597332158 597332161
    0xd06090f0e03030402060f031305100c030501210b070203120406020a03150315051905040b0f010b040b041502010e0312070e0d020d231912030203040305031501030f02030108160b03 79
    0x103903039480071101c81000c411800c035203a0303540c41e20649c0552207500014200340290042440c0c00f000c40e6015080e8030f1440e84040001d43d80b610141c001c8400c46810900c0e00d4900c0c0b00940d03010444c1c05a1090b030000b00b07403048900e03180115002c2810254296000c032507903074000c62140e42030340e09070243c1000d9076520304000c1055440e503103c2e1401e03d40480b0122001c41d0b46d88020410350040e412007650031440e0103000f40082e082900d400120441c08582e10200c0840507000421800340c1801150110780035081070a003001d040030440c003103065101c000340080d90350321440400e0008050000d80742d011519000503501d07103059100a02000071184074603101d02d50740c8106000503940c0e03d070070081d03590b00042e010030780b80d400205d03084c11a0454007200220307101d00b030380c18941138800c10b2502c0400c91003001c4c1d1400034424542d058003a4042500d005021074070500014007902c05072580340868110501d000324210041c5071084040380d00c00c0e00151120741100000344900c200d12811100142000c3c0c5c50107245 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 597334658 1250 597333408 597333413
    0xd0804030c060b180a06090218190e040f05100b0a150c14070807080c03190f0f06050708060a0b0d1104080106090605030f0a0302120f0d06090f0e030304 67
    0x101400400040500080000c003109118880e444004051009460300509507800c0501c0ea440700d07801c80307030480003d0410201046900c0c0c1d80c02501d5101010407940d0502803a01000c21810301150b103042c0d1600d400c08540040d00100407800207020f1801510069195103403400c22504024400e80662080da003030107110446a00c901d21500104c404210316500c4000c2109400c9401c00c40c43e20001d0140b6206e0140302240c4600843c03010126080b00c011115420740c1e0381032640c1c607054181d000e95816007100008800f44040208491140d034070074a45440c01c4c1c0c90076a2106200b0900d50019550680d956040008941d0840001a0084011103022030054580b40e140c0816108144c2042c12a0b500d9900c0603030000390010948001d080507900901400752608c1e540c50050841d441140d10030310903a20030402d059004501c4090103a0554041d100352490a85420040e82c04170b080d084c45070008004045501a40c6c4c810312028146113200400c0a40891074801c0903602080103280b5160410401d2000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 597335908 1250 597334658 597334667
    0x12c06010905090706030906240504180b06091b120604230c09120f0610271d0114090f0102041805090307080d020a140408100b2407140d 60
    0x4035981d611b40454203540903d0075002a00d01920043e8080406511811041802128031400e0700c0c0c045d5410081c0020320200080d8044040c1809028042920b0100e60a81400c41700568800a83c44404120110880c40c0c0400d030303440144450256241c0605204441c5800e0107140c1c5070786810103140310600032074601e11101d2903029002400c43e402c001b6510241d510b602c0c81c0400c629007803000341c40300014020001c0c0d440e60b00440e101e1005030711440b8007144400580180070611198001d12800c86100003a90034002c00d103042e0801040e502d4125000301100d000d0081da00540790380328103105d107800d1401802d80390031a1640a1007042e401030006102d841d040380e80e10000c0402d40c0c00c0c003240c180c4611038103604500c40c0100143c407010340000c080c0070041460b0024040b51149544002c0c0b5862090b200d186039000b140112245904071030400f00040c0c40c01c3c1c0050841982c003d19010002900e64400d04a41420410805440340040b8440051200f90f054140c0554901310260005207110b00c0005d2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 597337158 1250 597335908 597335923
    0x50403120f120c03180f0b0604020f0a0516140c10050f09090c04090e06240f010810210303050a020c0606120f070e041104060501050a11012c0601090509 67
    0x54a555070101007245104e50403c0703400c608002c90140180305141040080380c0f070704220544000c03201d040130074110309051086910404603c85551b0408045901c02c0764103034421500142000d402d42c50b030001040030b110001c030965205000404075450300030305215410305011104414040c1c240a80c02e442d08641c0100c50b1522070444204006a44e0307010407150b03d00070754100c0c41c0c0d00c07464503000f124070b01c8000680328010301280390588909298003450048424200c41040d402c035503c0060240d1550080407066003010700480048034164980383d04083c2d0a042d011900005d040000200741070513050b11406421010914080d440e02c2c4804500f15175a140c0540010302880150501e146400c400340041031600b0041000c0c0c40106a6600e41090b5003c000d94007669105420a041141850940700b10800c03510180c40d0b03942030070303040d03401600e0500d0107200c0c2d010b06540350100c1802c402407544da111018042520000c01c100800c0c00ca5501e8440140c01c0340345450701d05401c1c0410940b00240b4407 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 597338408 1250 597337158 597337187
    0x304060e0111040923281b2007180209131a2b030215040f030e03010e061503030417100608150105060f040816180c0903110f0a0303050403120f 63
    0x508101040d00d4406621030b940b040c0c16520b1510703000c40d0050301040704581400d40701b5548c240021080300842c10540c0d00300002c0b51071542c440e590400003140e0182c081840040e640308018200783c203c0000c1803040900c1082c5d889a6940c2d02d0765000c40c1640e400c201700c4405807c0e1803e40700c41450020402c020a84607000d1a01d22080d14540d0081610800c0b00640d0405290020150741c21700c0c2c40c00403401140940b040b804181203814075a114241442030982d440c4841c07004100301d0300c5000002c00285045482103406000c00c0101050b940403078811240c400307180340c0042c448145022002c20840d40303190000e00031500321408000a03815407151384d074155601111441e42d1500d6400ca1407005101da940450800e0083c2d42c14202c000040c44540e90489400b0f040d0486580d900d49441c90455039003421490101d06100018801300c3c0d54900c101d401030101418020145c01c4000028841801e0369004400280b4002411300c100401421625042d00c410b0910343c4482c514044007401105161048 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 597339658 1250 597338408 597338431
    0x40203060303071a0103021c050c0d110d1103060132010315060e030d0f021209060705060906070e0604060f08040c090c020f01060503210304060e0111040923 69
    0xc242581e40a200311902c569100250700f44100b002280c091001100348030903442204901012594440814000c0c0c4d00a91b01030040c01c0d015a11404100989001d103c0a880001c14146403858980320000140c01450044c0d034144070344a9007200b0540780500503003142c60b0f660812590a00d20104640301520381c0a8406480982660613800484c01080d06000d1003032100c90f5111f000680640041d40300818400a134155552900030303c01c11740e0b11a0500d01c40b070005903c5283c01e031515114100113400c0102004225074a0081d40d03817a210318122054400202c83d80181c1c013804050f41e00540d5500114106681690409180580c0601704d01c02451819050002c044002010004501c001d10044c1c0456074080000401d0708000a6903201100e0140510b50301c0e191303001c5440c0c0303000a000034180042c43c010f50b2078400c487c5131400e40d6401c00b900031240d090303c400c899818403900307004241e154442e200441c1c0e184c51a101c0d00c2d10640e40714004002e100d820740031481040c0c501080d405030380f00200d10304 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 597340908 1250 597339658 597339661
    0xd1212020903010606081e01050906010c02010c05030d0507110601060f0809190602220f1403030d0615120e1e0a02090f0901060b18041d060906250e040203 68
    0x9940684506460306515501c1d000002c940c050300281d9050003900705a0703400e54420400c540c560800350080c000c0341d40c0040000002145580b2030b41540828520601d804c280320560343d41c48510f507030060101c160b04a0344900400c619a85d00404007101c0c1d100e040f00404c901e5140241c083c20301d4441114075030802071043d0000d01000c1d0304001c0701031407112090b20a8404032141c140000250054295201c900c140598403452080701e444024080c0d45d0000140440e241c03600165030501c2d000c0d084100e070180414030494101c0601d81c45100001d01c00200105a02c540c4421300500103030708620300410b15490300120007514803001552619818480280078040c1d84030500161416061080c003d41c802107550400c489120760701c043d94024800d0034002d108140d1602584220781c002c0908240c507458205040047d285807641000c5810f054031050903842c01c480c548164149071080314521220341c8200140308a813020441d9540020140240c851913681e41e040c0000e0a480400b240107120360380100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 597342158 1250 597340908 597340937
    0x80c07031211071b0603060501031401091802090a0509011503031706130c18050d15020f16030c1103011e110903030301150f0206040807081303050115050306060d12 72
    0x40440d03c125400129140c0140e100d80c01001d841c92250203800300003801e100000401c2c0d40280220340c1c8080030702c490000281e003810102402000f151440d500b80489010b1644c016850b80c0c407000b400b6032a149004034042c03410760901825900f040c40080040b000c1c003441000030950241055501d41d41101b00300710281c5829001680002e034900b4a100b40f685400320000c2c0864024000c590916070b00b8121a451641d03034400c00c20f5035003440740090002801e1814203040c0c00c0441e401820f200c00080c8402d800c1141c1005da41c001041820003c4001c07640703c1560030309001d14108101d015070300440c0280903440019080c01c05034107901c4000c0340d500e6100c000d07407100032800d24241e50380c0c00300240403030361a984d551510000b800700030f407031910200b8600e00d003040406102142152055401000d464507100d080d0f640c1c40c416500c00343c994070502c0308030500840040c42c00c0c003455103000340d080d0021081d0303401c1c04201401d051002d0180b0b8820b41c501c4100100003203002d0702c10a030321519814029039134078400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 597343408 1250 597342158 597342191
    0x2010c090e06012007090e15070509120a2004051006210b1206160f020309010f02100603030e0f030c0f0d020a080f0304062010050c130b03010501080c070312 69
    0x4000841e014005c800300414049a43e40c0140303000e03904c00044401e001c4404848043c00241514941c0c0012800c201c2c690342400d0880300d119089642e90304a500c0c210340382d00c940c2007003000300780d00c0300e80080c0c0090380b40d03690310b01409080d400c00d920b187c010750b926103010400ba00c4007200000041901c0c441c1902d0944400c0c403503010020018016000305084642c1180d2a5221030303085030303151185034180e800c100150784200040c10a85442d60021450201160f0054802d01c00c90304072030f17085116440c0503c0c2581c40324013031400218800c1e00c0306102c280f044c904010b000100c003024280a0fa2203071085600540e500d9208030012207054a4155050304c16001090008040e908078003e02d00c9481c621401c818000001403007186d809a03541038060343d008111030300400145a00a105910071700c000341560300c403580030a0704504c103c51882e280841d0031045400b6440c041c4e10078244031402100401c501c0d6000103000e6400004640c13030615210041c0c2d80035055910410042c030f82a0380c1c4804141000548 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 597344658 1250 597343408 597343457
    0x90108190213020c03031510020303092104091503050d11070e0915090c0901120b041506051905030105010504050103081204030203040314030306030c030c010f0e040f1b02010c090e0601 81
    0xc4d82030307980c1c0e07250868041c0310415030265142e00880903a985003070f125201000f40d900502c20000505550190440014102d01e5404920000c500b130030040010f4090041c4100409042e5030394000c0300192840c1002c40c00c00040d801d118052041d4640a8100b00801140f05001e5902c0c00c1d8000c4419119000c41a2521200003a142c12604004050245518001882c80901002143c3d070807403a170380310580b400e1151584200203114038010004a000185860b400001814071887c000038860798460004145080303026100010417100082400142028010240584025101400b241d4555610001e03240f09802c1315051003101d040105080510a00c03c8400441e00704041800c0000c80e55511904d0358000d840291203480340b41541812420b001c00d00385c0440c0307016103582000c10104241a85c5c190264810586d005075240303680100c964482c0700d414001541c500703505190112205c4040e0854050402c1c4006125030507208118092428044c1540600c0a10b0b203401a001c01030311000d0070120 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 597345908 1250 597344658 597344677
    0x501090b010f0e0903190302160203120a080114150d0b03030a030615020d02100c0e090708192f070f1103010b2b08070c1409010819021302 61
    0x1038000c00052100d03800d82000d001e4429200c2c400c1a15200c4244c0a0b940b44107181c3d140760105031000031800340e0340c0a640a460340d0003c401071000581ea01d940024200344a91403141d00704400800e803810030942c4601c10354003402c950005200a4040600080c041c041702c58100000b0800008903840410076642180c103035540b0145c2100d480b9444400090003030b103164051980310f80621004410050f02c00a040303c141d00403600031340038801c00880c0e0100900b40e40450001400302081e540c0e0340644500c005140f10f010169038400d80c0c0e003055101940746081c070603440001c01e41403ea030308a0352000307a81d440c00e11b000c503001d810b03170542d0303140d1000c840502880f80040c004801c03048165080c80304260f0114401001103008100d00c022010400100b420703600581175401c0c540c03c1c205403022106040c0001810701541820341481d8442d511180c00d004141c003c80344c041d5481c0c145007140c0c01c10700708142c0500804006881d5150a18002410301c00c0711501c00f038071840400d08854000321650f811203082d000c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 597347158 1250 597345908 597345923
    0xc2a0603061f0c030f0f230403050a1a0108070b16171b0106150504030b0915150319050a03080601090b0406020303060a0b030903160314042603030709050d050109 71
    0xb0080e10182005201c2e41080e0080f806030811190b40501c01c1d81000418079154503803804041c6003480c00341542c00e1540060f00c008204000120100e00708201695480788600e1152100341a91403820361000c2040e4007841039030344441014030400b07280b01c090752030400703140031221a10613482c00c0195210310710700a8403540704400144a10003841c1c0310010b01084007808020311180d6070b64140954603050440b82d4000242c0240300600015601081d101d070002108011030784074048018039071003525015039580150458841c58460640cc040c0100001209164170b00c21146060740c0700d06466400d110001820880b01c80d0006205a010b00c240398050010300381d030b194880343c8034040a50b90358000e480c4240306141c026000a54054100100c2e40304090420185062011071542d00301082e00701c6204906103c0b604490040c4003444102030f100800010388605032184001c04104504c0c410844401c8058208104000312560007405440407500c1c240c650b03801c440420b080ca640100300e038103401403001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 597348408 1250 597347158 597347209
    0x303020c0a020918011118010309020d060510090c0509060a03090303240e090a12050f091903031d010815030c040f020c0d0201021821120c2a060306 65
    0x420042132650031581d600000300401d1007030041040c068000c0e00c0c103084040c180c8555442095100e90010302000c2c1c40600144000b0752150f58140680c0c004860001000324441d800b00a002c501d030040303c3c00d00a2508110f450440d1400109040c1e20424084009068a9050302806c040c420340c00180c2e480c0340c41e0308046c0400145078900c0c03c941064825000d2010425001c15002d0f0004500b07095010b41c0f00742000b5510725440d2064038560003688000780310740c10a0200c0704268a9900c07084001c40f0806003c1d0440714158680a8004010b071035850214003406003c5038041d9070000e1006d50403000c6400000c60318181ea8000901d0842d56a014076001810040d8078120301e1001c0d0003401d210080310050394040c078001d840c00c03030807130042c0c106130103450b14200b00034403450826a080c803682011043c07220000741c40403008076160a50407280703110341900c0010150b01c2c1140a10468005841c44950b00100e0509100c03a40030301d40c605030304141300c1c00300000882d03081d0381c0784034000100b1a034000720382500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 597349658 1250 597348408 597348421
    0xb040f060903120e15070f1b1b090207020906040b060403080c0a060c080f0a020a050702030f0f1605031e0309120c01081b180102010605121e010c08040303020c0a0209 73
    0x140341c0f40d21905000034201100b01840c6100426070081c24410034034002006d44c5c9400e000c0701c0e07501d0b8121080d01070010700300c8030312450094040d04030121760240c0700c82c3e0406454050012441d1751181d01401c81d180c030520000b00140c0c0c50715040c5400c182c00b103a0110b032040c446400940240300d19800240a2900041d110151000100e00084c960b0301030340c010010804000030540e80c4140494043d41c0702c5881c000000c5c06112160b01924070000f0502d08181080810307404a8a00301040b4400f80c03c42e4030030840019040720412038200540c0907600214400b40c540000300350b40c0c003442e0781c104034481085080e8148102080050703a511880c020800d40c0c0e0310200320401902d503000c00b0788850004540d000002c5d1002c0724010202d181c190800e503003a2a00e03e80707100014900c0d000240c0380341195261070300020a40d6480b00c030540c4070003030f09020b80103201a54203403100c04010420359144071f905040080c100e840d0801da00302e074002e825042c0541d540c51642c900c0e504100200000039400700310102400300 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 597350908 1250 597349658 597349667
    0x71d0f28060e01150e030d030e15070203130503030c0a060513062915120702070b0a1101060504060f03021318210801050306070e0a180e1e0601030b040f060903 70
    0x4039031980c2c010000d4a680300404517680103400d507001c0d816900142d12020b4187c400e60110300d0b01d4011034180ca40c1000d0801b10182461010f4808100503400410301c4a500d83e1000600d00040100714002c5240a4070390382e030070351170b4040c1c3c440c0076050569600000c2c0010144948111035a5440041006030006851a40c4006805141d45a0000c0c4012080c0c048500380000b080e41c100c2c09804900b800e12040d0310038042210802407042085000b01000040c0380305400c1d024003010403e6846203400a411601c11900b1900385a00c250300c11401c0c01d20400c0800b12a400040599805540043e0304000b074040100103845002d540c40d00601d048007444051140c126984220a000c42540410203089454212641c500a0040c40c2d450f800c00700200781220b02800c009030800001a1201c0012962170030b008491000c80c4911400294641b17049003008a0300703015034601c1341510030b1541c11640240c0402e944d03c1d501400014030400b00310000c0740620140107a5600300310340c4104140000d40e21443d0042 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 597352158 1250 597350908 597350911
    0x1214030304120f02030406080a09031709010f0c05070c0303030507020708070b030106030513150b04450b01060c0201030b04180b0105060a0c06020d1805071d0f28060e 73
    0x40010300f01d11090751030f42c0c80841298100c50480c1c4d60069039844108841c0014218040100d05028501d2030290031130403001c0380355208081e00c50000841003d200010025580b5260305442080420030811000801411080040c0c90300352800003482c0d40c50902c01c0c0e14150030354000e680303148180785000940340200c0c00154145d0340169800d000589441d003040c0003a2000800040c4200b074445590040281141c1c04088860030007800483c41c01d4101c00e40880011907500d140007240c441c00c0d845038402d0796565003d40c5d20a80710b04081c1c00241c90703844508182c1018002d01c000c2189a4441005580c0b20340c0100d40a202c00800800ca00c610944086910200440b01121144102c200002c0c4514109043c0c85540e2455102c18032281c45030341c3c40c64000d40c420508145000e956013132900c012202801c000081c10b120704020031000d42001c3d48207a050701185400c04500d02078900b0001000301d01101c1c40c1d0840c0000d0780c0e01030701d1076140041c042d001000c601042c410501d07080313002410648400005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 597353408 1250 597352158 597352193
    0x40302010b0405070c020405040c091a03010c0c03233a110a0c021201141e15010c021305101806030c05090406020d0c0f0206060103090506011214030304 67
    0x70000c04507501c080c40141c520854248001c100300008172009401c168001e164441d1007020000051910340c10440c0c00c85114112040c1d90704c4800030a9403103428244280700488000d41400e2211442681d4000c1405c00080c11071a1483c00d082c803400030542000095542e403050400015000c42c540c0c0d1846902d000b001043c1c540b03022411281c080f90040c403031068000020080303000e03514200441000395420110328000303d0700010310b000070340700e050400c0c803814107030407140540c0e001d150901800003d103c0d030f003545100034030f1b440c0038040c030858048580705804c000000f070a00d03d809035818000030317840440c0700d4010210241010b04000580c0d40740e8040740d06031200e518428004409000d035030803c55105000041000d00b601c20280f0040c038000c41540e5005d8800d020152401402134112000d0383c1410044401040d61902c204c800a9018098a0303807100081c40c041100d0b995580720b090740c901c811f101d1852004d901c005840148a80c82079100424840d103002c90384e4900302803800c1080003039a40b982 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 597354658 1250 597353408 597353411
    0x70602280504062111190302120711011407080105010207170331030c14091b030901090b041415070203180f030d120f020405030303040809010e090c0304030201 70
    0x105440d1a6880c1140d40004a00c0d5849a0900d0308022050b94613000c041c0c0c4448001201c039a080b01007030b14500904c251094024203ca4484003030720082114420201c82c0d0205040c01800200b50411038500b1003a4032480c24601034040c44e03e5240f1807030042a1500c03020f0000da142504101460790002c04150407504281c1c201d541141d40c540741d000c129481c046010246400c1009460308a40301460a003203402d640d43c2410208070031080c0c0d51000c0034060f501c1210101c07181002042610242c802c085c9000b0030a86480c802850105c10742e034400365120040c20403142003c00840c902038425481058200e51000c400c2905007003908100c506403141200f00880c0d803082d4442c0c51440b201010446020384203d170002c40c10441206041e1008102c2e0381e44854001c01c0039004aa9165801c01042004808607110b4003000000c0b0408041642c58070094400c0c82401008104020748001084a40c81070304002010f880d1100c140c0100c607944010301041c1d1303000c5054024060199060402903005d03600c240c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 597355908 1250 597354658 597354697
    0x209130e0601050301110d15050a151d0321091915030c090e091501230406060507111c1401050609060f04050a0f02030c0a0905030a110d08040803070602 67
    0x1050b00b070b00c81105000006806c240901c46680d1082d4029a003d186140758103906903403503101058500040760b014144642089540d8000c45420040c42404c0e20041b0211810503030b01c00c004070b41e80d0850601c0400f2203405001000026541c8502a1114940e0040c4560000c0700d05404083c2207a01601030f10200100301161402c0032070003441600c00c0702000e81c8828207154035100d41c01c80701d104010810f96450103921003c503408460a0a400d0281c110400c01c040ea4a2130b1034000b26500d21141c40ca079000b81e28151040c807115401c0320070740d0b003165403041c1980f910300449008a800004546c0702c201d4040d0085000c002000601150b001624229030020031055441508120401d20203452454101030070549080503805c00d5082254000300da4617011580d4449038214070101d900848030000300a001282c00101250b000c0360810003000100c00904020790381c0e0300c0d40745880210703030306017842410900084000c0016440548008003013090540351902c4c510308182c2c01950000301c0340010f0511070324 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 597357158 1250 597355908 597355919
    0x610141509220605091e0403051c0207231609090204020c0a050a03120b0f0616050604031e110d11120409020d0c0c050622050601180b030714130209130e0601 69
    0x401482c50581015845116511141c03401d070b5890b4031202d80312ba0400101170080415600358001020824400c04192a10f00e80e02c0108400a0700c804041025130340040320511102c141380001a000e4803a00080001c072401d1600c0010002d210b11309559125001d5002034506122002c1480142a8000e0310307000308007a14420300c042203440c054041039000b14a0250881581007001c041c1c26442c1301000c00111311071145d01c0300b074034003201140d00b18005103a40722110680c4940d0100a11590750300d09258601c2c0e1000c0400585602200034490100b14080340705810501c810000500c0015004c02c0c845e03a9a84c50344c8049001c1d60140110300075103820a40c003c43c0142c030a0a490740c141c1c2c0c0100280c01d482e04d80e142d800291400c42c5852181801c0c500e81d00c1c0d004507030300340002402009944001601d202c4100d840c802580c0e502c608a51281d008a2420400d400b0224503c1c0c02c0d1010840b0742481d90440510400028000d10f4000b43d00060381c4461240d694003594003c8200d20b02c0031085410070380c1d888 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 597358408 1250 597357158 597357181
    0x60602070b070c0303030c2604030e030f061503030715020c010b0a0602061302150f03041401060e010303030e10180b01080613020607020609030a05061014150922060509 74
    0xc00b4010322810000b0030420103e8807981c01b9a4502e051843c082900b00c1c40b020340a14440400c1c03000001c0050420207000406400c040c81040140741903006d4841207114260180e01c070351000b05900740d070802042140c501560240300b1030b292903600901c0c001860700c0f1001e181000750055410502c103903190031a218124030385441c119040ba035840c2d00a00c40c0d075817402c0d03488040300600c081c202c5c3c016400c0c05108904881807406000303039004408927141c492616007401c01c0c580e0182c0da18000c20781d152001c180700c50503822400710b066035050b050120388031901c008240c4c036241010016010107460004480c0b000d1a80344210032035a0b010764007100e000e03620342c00543d440d0300c0143c403081c498000a10b6581d0040c10000054000c5500041c035160520010001082c14008480f80454903500418100184412010440c1004c0d14089049034051070300403001c1104030002e108e00311283c00d0701045240d11680e4515a04d9a022141c684030846611091000400341c07196004148c403910150300000c15410a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 597359658 1250 597358408 597358417
    0x80702060c0d0b0103062301090509040503090d0822080d0201050603030a030c0e180103260702040207060b13150e04020a0b070201170405030310050609010206070f0e13060602070b 79
    0x80740090b00d004688416a8002c240b940d981c01d041c0f5803034480025004042402440030410420260804102e0b40c400040c80b0760025000716108140e52010300c0042040002900c40360031094074400307500125420b048240d80513260108080d803c000340c0310101c03010034125400840d628101120184059000143c1c240c0c1c1c0c00700c5a0035015401440b00f48151482500040c2d450140303810f003815050080320224141a02511a000344803140c003004104008114190f07091401c0d850b641c030700c00b030b4a02903ca00e85603c2460800391207540c01160760010b020540d480482c4580c4000c2400c264502003660190190841424003c455280910000352400720401403521071680248a070420341c1c14404010010f81020784107904203c0d0441d00380340c6000d1280010703070185001c0c3d030003980c40345081c0440041402e011342015010341001c3c0620a071503600050145d070842941d003000301c2e8000b45680300b195a0038228040340e0740020040e000380c6994a9036803006060b20240d03425281d00340d41f03880004100344030707 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 597360908 1250 597359658 597359671
    0x13030501060e07030b03060f0a151511070b030f0406230f070f02100207061404030c060b060f09121c0c17030126340f140f120105010e010608070206 65
    0x21000000b02c10031710f01c0024031b900c6a1041300c00944515a13850128070303108580c0104901882040d054172f02950428a517002480100f00100011802c00032441580d000c0902100914010b0740040742c00c0016640000100c840c0307600c003106181c01030920b03c44182400350355000070310018401141a661090400130705101040d0024080d84440c1c60081c402035104100550362196900b50b15a9460018412a406580681d03241c4150200d50704002c0110355079840c28601c11407081088c80c1c1c051b6020020340b400d0070340442d00c0c0041c0003113041c0503d0600004050005000341540700d000c1002c0d030443c001c0c0c2401c40c000c02c8180c2c1d81c01c200c070041d400c00f44000e005a002c503034034001c0128669640c040c03141c00f400043d10151000050903061081c140305100958404400c40007407d2414280f1146061004088401a04c0c0b01e42d884e000103491078030501e03c211802007640c0c0422500d01e4485404102d00911000b000700003560b9503040c01840c1307520a01840d13000a0340c12002c525002d1002403050b00440 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 597362158 1250 597360908 597360913
    0x8070204051f120807021206072a02040207051213030b01080a170c07051c0605150f19180e0615030c012a0c060210060305070603020306010513030501060e07030b03 72
    0x203041200110300540c0c0301c141120018000c00c5105c0060b2121380b10040248040c42c010300190400d9036025040d5441c1e01c44152822000c01c407006000f49076000c0d50b48202e90143e80041c0d4440d26800c0c05818070b078821b036800c0f101e4040094040d00b06a003600b000c0301128028040024a40d07200e0711900c0c0c4038824160064205050003d45a402c10700f080300502503418002c00f00c0300b0890b83d5902103220303014a00c010448107010600c1640c244942809010740c0641c14042c0304541908210001d45c031128105000c0e8020900581c811a404014014403005444108081101d8146134890040941311752510784400d80100808134070403c00b0313100d590b801c000c4010040c06003d0018001155400035220820780110b502d0000d401e22040c00c2c130307044000b141c001e09603820000e08001020f03180080e450500210130345030030000c0022480210395242542c025140c05030352a1502c00049400c0d00400d4069000c0032100003000003040815449a401c8032074481c0c000e549580e8400d01a8100e48003525a5501074 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 597363408 1250 597362158 597362221
    0x7090509010e280609090b090d0f11030903030d0e0c0105030f01030b0a06090c02070317040f0902130503070e0402240703211409300c0709090807020405 67
    0x4620480c08a411603502d440300300201c41c1a18450166070361079004010306a076a08401b070900003c5c21200754020080320080000309120480107016040403900c050130443d05030a84071440c1b00500458900690080c11a52120265041c034001000b070f08001c0c413901e1080c0c94900704107500803401e0720721a44105624580e9071b0b1840c0c640c0001d1002c0100218411a41d9040202d481c07600c611802240c00a554010100361b4158545441c5444005040c0030000e1400d0204008002004080340c00744e071070546005d620b0b0070b103030902201d000c2c210b908500d905005003100402c1e15a4044601c611540c003c84440709022181200762501038008c140c0b0403e406000c000810209001e8020504050f4803450b0064003180802814030072543c503070b244840e01c5890302092184c07203a001c014440800f40845035015402e5801e0415603007020895440b01001c18011031603407000c05042c0702c84001040c510105008164040c0380c0141940e0002d0022840386181c030001c59240c59031810000701400a0b0b0800740b104 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 597364658 1250 597363408 597363421
    0x4091d07060201110d0b030c1003091b050f190e010303050d060609050f22060b090f040e3d06050102100b0f0d080d2c0606031903030f0e0607090509010e 67
    0xd40543d048954051081c8c0e0032140041c1c4400c288100c0c8603070035aa001a1007050303460f00c43c01c0b07495042d940d03110101d004081400700343d03210301d407604100100b2200c0f88108401030300c1c0500c01d44015848505080c04200c000400d1541080007404a00d401d400100040c1d134075010103a640e02d0190080030b030402c8440d0345200ca5401c0000c184500d00f0340042c10740711005030b0320080c0030684000e50002d40c2500c40100d00b6461a0420412601d2005021078080c400c04095098066039210410340380a0f50050000014415082c07641940140b03445108914640e1074107000c22502400482c0719480c0180301d45a0490381c0544140f003003130b200c540020b000e1144400ca2800f00903154106040c103480c1140304004440c031218091207241580038901c60000380c1c4001c0d0035404503a80c43d45030410000d9801903400c11140da40c02141c00441040f0040c8003080800383c03410201d005000c03030b85a880c601841d01c2040303465413100103451031084210303550b03182d60603860b0b20502c02451400c1c031806c442001d01c54041904c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 597365908 1250 597364658 597364661
    0x30f0f081515090a06030e010e03040e0a1e05070903021c03081803040b04080705101b0f110405041a090d05030a11071a04020108010914060f040204091d07060201110d 73
    0x90000e07020b0016814a9000c00006103030190640c40017002c640c0c2c810198000540a0060220300b0701108051800e0500c0c200700a484054018000a0413913a01c0180c081003142801c425407080340010b80421a901d8803800142c941141c80c08244d1165122004402c80d42448905250505501d0355801c0c0190320381201c00300d18450305c0340070401c86010501c0045013045980c0302800040108800828440385408c0502a1818424144c0e9080040341c950740840030b050f082031600c459900410b00300808003682420101c0c4c010301454590320030708080900090007580d1440d404090262841c41c51607882e45040d180c1d45946007201c140200f582400003414010160f4800c230641441151b07030074507040e4503646211218481d80c0c0345007450060345007800203559202e940240503140010081003c0c2d030420501e00b58801005144a100d11010076182855890f11b4064400502c0e0040e010710540c0365511380400022004510405144181c01c00001c1aa00c14061406112101a0401c1ca0322180003031800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 597367158 1250 597365908 597365929
    0x2040c09081615020a02060a050a0c0b01080d0e101b0507030b070207060306050402041d040f02090702011e05070c0f0f0506250f210605040207030f0f0815 68
    0x80511400d800005044402800302c4455a401ca105045010742004400e290031640318103d1400c6600003041c03400141c854204459060140b403e100381c072220a03407412510301200000040150403800d0001400100001e6207281c0e145454450028403990b4000348039510281c0001140020744020320860002080b04009186d28000c0040e40c40c22a1281c40b010300114040d18030100607070010108104940d40742c8940d1010380401c0340d00b54909490088502c1600001e03000b4690404c0d43d6402240401281690183c4000d40c050a030054503d0078580c003a00070544c4e0a070b10f201c4400c0180c0c0381c80e81500148030b628440c04039034880c01c45018058813611031a00803502c0c11100c0034001d40391f40002c11420031005101d04030343c800c00301030412050542544003841810403014449009801c90a0300c0d003208520b40c50807041c58a00d1807100b4502c002001a0040f503001c150000d00c0007845500b815400585070711403090b1511203c8004030041300448000c3e030200e070082c5580c9028441d0003000e142415110 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 597368408 1250 597367158 597367181
    0x20405010f0e0622030501091b060e0603040b0c070c03050303060411070b0406020f0f0d1b021605011b0204020d05040b160e04020307091d10060302130b0c0313030b01051905010c0204 80
    0x1201600c91ba141821140c03540d03020380c1e451146424920310003440e91042c20103002103250030400c4030040c902181c014000030b400181283c3c13051001400c1e9220790825140790340c0d002910284d0030390356030400316225030041c0c6016008a00300740c80aa1501e400394202c81d451540241c0d070140f21354035601d80d03d009400c02c0c0019000f07048204080421803c03200003400019030300141c00548006a1210001d40c0e02c003480341c240641d001404140304c040030f8030400303500300c550a0a01e1410a0541101d211162035030a400030360213840400ca070005920303503610a62007144a0450506141c0340c06800c1104039402000c480d00090310b5004401e060305054014541201e5281440c441940d2100907041c500c0403034100307481c98843c0100c2080015a0072000b2000101010b0030300314a00049a0803001d07070301103a40154100310030000b0740403001440400449400c0455560900f01c05a01c918002d207010400713108903886603902c40480400d14250385045000c03210705031151300c1031388031540c00d00000d4131090209 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 597369658 1250 597368408 597368467
    0x160206070213020405040605090601050a032406050d2d090219080d120227061b0d02070b1c0e07170a0501150510120f090303020405010f0e06 62
    0x82500580740c4031005004034054080243c0c13201d00304410311081301c03c2ca500c003502c40c0d0044010b019041e60070004844d0074580306c5c0b5001c036540710b5200a0094070200ca01c1e0301e881181d0303843c20006e031803a0702c03d000e4001c60480e00400e00030030301002d0442c4185980c003040804aa010030b850311002d020180d2164000900c05059101c8001140607120f00c04001c91340503e076503400c034140450045030b01c0810082a102010340440c144499040303a049039541d401d07554910308258804000d0960381e0070041e51408001501c803503404040d40382e00507880e802000c27030040c054411a400420340403120300540e50a410340010b103040d08407600202d08007601203540003d4040c0240c040101d01000a1039101107512650b00c010804040c1901d4440d003110b0b10000321611652400c0401d0045035500c03000503404014516104003c0c4501040c001e00a003440c0c03210f0380000d0302c1d01c40c00d041050b4054001c2e04c00c8583c00d803520140300e00380f401b06031440c86141c1071a603884402049a2440408031500c0c00180100c0c0051 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 597370908 1250 597369658 597369667
    0x901060f0b0705063102031002070f020111010515010e0f04112203050607030b01020304150206060a060302130510111605100203190c030c24050a0b0105160206 70
    0x4000c0100035035402079400c10100064407002e0090401510340c01c02c0c1500d90304905d440c43c488110740c4900446510f5014001546210b50542d40e0400403100861008601150f44201d50702d031140d00b454540f20224045180998030b10242030b41840303154401c1807649807901501d000c40c2d00460344610402c0c440d0f036101c1c3c10303010504100c3e01e461140103000d02c2a603a040342e407698580b840182105100c060008660724018040c0001603000c01c890380c104107607060200f06c269440300141d04500454101c101c2d41041894600f201560004446004050549004501540740c1d40105e0a0703200b101e07446801d100c1001030420660400c005100300200151070004e02c68001001424100311400700c8900c2c840d00000740c2400035184c10100503603484040d00081d45401070415504020052141c00e440074803541e0340d0324400340f6020f84801d2406d0355100348420000c0c08ac00c030203c40002c036080c90000000c1c0c034090028110011030b10480b01784110584070345041c006101030300c203d0320502101c12a0403940030320 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 597372158 1250 597370908 597370919
    0x1b020615130e100b0d050705090703022214041b18080304090501050307090504031202091507030206090706020607020a0b180304030807120507030507060b040b033021090106 76
    0x2c100b00c00031100d072000d8503c1d52000380c029000d0740d07480420341d40304c3e0a103110100d0004074001b46000844e002034801541c1a5140c82c410f800900961681c0302c4000d549109458074086036004100c16112146800c00b213400441040c0000c0341d50951240d2411032613142c0b0f100342c00d4080c603004403c0e15035003e01f410700c00392102142e900319006175001c5070000380c89200601c2549402d0001c600540304044040100d4505600c0041c600c0c09034a498200d0254001880b0741c054480301803011804031001096035546142d4079009586100403036140e2418010b01102007006072020501307601034007280e4000d16a807000d42d1100188940068482c0003400c1d04c90b0305503a00c9402c180098001913008190300354070348a450412442000d01143c0c00820484200803c90010f5001001e460b002500248001101e0203c80b0100d0000c05425038040d0f13051080d403400c1c128010044801d112550b0000f18544010703d109001801076004551070381a20082034110b09201c02e84204003960301050f010000b00301c10390740b803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 597373408 1250 597372158 597372161
    0xf0f0c010e0304090b13090519111c0b0f101401020f070b09010801300f0506010e060a050306010e151c061d0a0312022b0b01031b02061513 61
    0x540c41010b649840300c9010301d1174580405400035070b8452207030070702a4512550300c45898110218064032407004890080041c002440000ac1e41d82c400a0000d010390341501240140400a18501302c461010b40000181c0f03074580c0100300c0d8080c0702c2c0805a010250305060810110b00c60301d00c01d8604521840380404075040041101000405041c215950b03103182c44400104180c0050300072040d02e0496200c2d042480f0250000c8110314400161100c82c11030072813815003140c006503880907090f4440c140c000705540350f140344018080d000449003411816035a03c2803503140c8000344900303000c40408200082514890700b0650120201c010301806200018002c0c1486008040205071012a078071032042c81d2100030184440c121038029001803500020581d4014020a28960980c3c4c0d041d40120f2102107840c11401d030002420382161062203410341034082d042c0100f42d4141d1550001341071500c00070383d4400712149500142d540390f02402141d0784011256410030501c004a03508100007161039044860107 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 597374658 1250 597373408 597373417
    0x60f03010906050301141b0304030c06050f0106031a18091531020306130606080f160b160b04080405100e030d02060108030732030c01050c0f0f0c010e03 67
    0x4001c00050080c1c24501410308480002403e021005100403d000101d0307081102c5800044c05403c00a82e41e0755507181c2282e402c006e40700c0003001d640c184000d20419485004800b130603140c95540800802e40d08002910a5030500351015421400039809001034066141507558000343c01002c0301e0230120b003ea00d00e40e150404a17242614090380582c5c1c000e40c450f20342600d050340e000c11140e0520186898002940340d410207858203403041c41c0b051041042040c0b90b0440300081882105480813054000c507111746420000403a404c85c03261808011031204a0241540c603040e000c141d0404280d40702d5521001c0480024005a4080e8000c2c080001d030780d902c1000c6421001c40c1036403504800607804081c58034103554100f4020940d00241c0060080601c00030650303059a80010140030510881c0354016108031800c1448050007204040c40b0f41c0c40100080182031203545100204000c2e0740d040340314146c0f030044c841d054124581c00c0020f001d42c50035086c060040a588000002a1480303401d107542d00d594030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 597375908 1250 597374658 597374669
    0x4061e05041a180d26090915030c0405100504151514250b06041407050d1e05012103050a03050a1d101404020609101110050a0c0c02010206060f060f0301 67
    0x130f0030309001904903031104500b080310100b041013410401b400e400240790010041061095007095007241000759001c0244030000d84003d80f0800036414140303170200444141e401510b00480c108400c10381607018403150001202d103640c403005515504084100e40766050403e40c3d9035558414407198103070402d24501c9500202504c80903d040340c1c02490a80c402d100010b04441c481ca02e0701d0300d602482824110f50310303440300307803854110781d10028165140d00a01300c0342c4c0940000781d800d2000c294000c00d9540864141c3d010784a002c2c0c1c421100101446001d40301c0d0070000c00040c010300014601a0203504481c0d0000e003030440208014400c105070281c1176010026068859204602816001d000b5201e40e004005034800040c0903480c0076000310300c0720310402d01018000ca08041240d4115403107450041c1c036080046003520f21003441601c4c030b640982002e41c1c0b29102a4640349890780c6c02c0b80981c076404c0c422a410713000361016a8440c2d0400c110a1110f60074180c0120301045109051441c0c540258080c10 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 597377158 1250 597375908 597375923
    0x15070c090902040c0302270301020f030a0f05091204051908010906091101030c05180111061003050616020d120e010e01060f0504151208090604061e05041a180d 70
    0x640794010003042c2e8103d880c100c401c1c180b0401502c5000403060480b100d40c4441c0c080c0f070950b60003034803010900a1040c0d00c026400e007100407062042c01003090700702d1401c0403000c0d4803d10139130311100c030456200d81c440d800905000c80200b10404c01802d244ea00d02c00010180d180d4104d00e141e41e000c00501b99154010200d54841c0c0d1031352030000f0880c01181030650340320b0a203010401c220503074001408510401100d108817003003100680c142a840342c0080e48030025800107540e04c50515800c0001e5224040c04126080c0c06054006024803885940f0741950782d525900810101010040035aa100c0c540d009071100103403210391a2003100d1090107405070303205024000041580c03034110500e03039134211078020383d2003079080c40d06903c0c1981c00d8030f4040050383d02a0288000c0a030152034101102d10500b8061a000341d0302207000680503811000010f0683d18100b292180004c21540031101e51145020700200c0150079008680072404006c054090451101e03803084038120280001598440040c80455202 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 597378408 1250 597377158 597377171
    0x30613230d0807050301231f050705100902010e0d1103120c010510060e09070201200702040e0a080a0c0c1a030910060506030114010512090309011b0b01030215070c09 73
    0x2030b9400759071241d00180b1032802c2030540d41859500c001010030010012681412031508041d2942c0d00f0000c80d1406800040040c800715000340050300580203000c065445014240105081c1c0c80782e4010100501d40c1696200103144e185010030694481410050700e030301c0b2244d00f06d0075950310100315800c5c15400300c400158560311b040810074291107008106120b400c1062104028541c0c00c4449030720360020459500005954a80c0700300c1c01080405041e1746c0d09407002c07020859007c0f80b100200090fa00035101806039002c15a02143e03140601200144490000c0041155107071084241004a500c030f8400b81c81c240c0c0d0f88149007040d03400d840089d092160750004c01d2141040301044800540c04420720180b0401d86401c0025030580814032507069245130400c1c81008681c0b0a0046500003550f14410003501e052010b60155660040343d45540800d091100402e6562042020041c0d400d40c0041c04001c3c81e821a800d20070300c6100c0d00c103080d070705030421701c11600021182022140502540c13803002522 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 597379658 1250 597378408 597378433
    0x1020723060c030712081503010608030a050307050d0c0c030807020d0e0906031005090f0c0109120303050601090b070b1611120d09020907080907050105031501030b03070f080606130b03061323 84
    0x7e003840e05242c401e0385400810440d980d0080300380c071102205410b266480769240070701642c0c14898100c025265501d0a202e20740300c031360068034551850f4029038130078400d42c0d51890b007684c2d00c1840c1c1c6a00310214100ca141c074401c3d440c02c1e8400301c1d4410340140c10b94032922902d003606e0b4284c030003d803250507190b0000c60184002210412000c903210f0300c01d107040c5503090700d0074480b640c8141c030b00800a000c26464000262503a4010711203000284a80f6060682e101d0060800cd00550710545682030321280c042c49200d4464403502606a510358040c0260a01d46031300b01d10200b15070f11042c08801b034130b5128542c0c0405a600c070b180ca0741c0300d49001e44a00e0290315290080d181032800d103401c0710341480804c0c02407007903007584c407046925044401e09000902d041000006840c02c0b0650b84030180300b44203190040780284001c20842c1c0a00002d079040c108540801c01e0440584610340c1c0c0b020741507070002d4002195240041c0d00c0140c000e008404184907421003074145110341c010070214420300e61014860045 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 597380908 1250 597379658 597379681
    0x1a040b03121303060b04140f06011808031b03030c251e030e030105040f02040513020402040902180a08031c24060f090303020c060f0f041401020723060c03071208 71
    0x807400e50444041160987c80c0c8041103400001800880030700e40507100103101d80e4015811403490301007400e61500034581c0d5128140d0340c0c2e4440da04982090003440c0d40304040c03041c00030903640202e0050706a00d040c2607040f05a000d20352a0031041000c0f00c15140d521001142d540a204159109120902c1200b00110305000d0200034451665a0003607142600700b00110307160294905c40035a0440c1c1c003103841d84843d01c0c1c04491400c0c181c0c0180d4401c3c40014001141c0045900811084040c441c0c60b45011280200700040c128451081c648250000c1010030102c4c03500c5e807210800045007000015258441e807042c1d0000a00d40905d9014001c4055024442d06410000c002c81814162902120b80781c20342d0b03002900d130541a0701503030180001044c1d4901c2d80f40d2100035110708600c62031400c0d17102d6a0352042d14582e9a511412280580540035009c01d2107c0220141110709996051a6500c510008180042c903030056520740c40ca40824421240001d8880c0f840b100c45420310399448800d800c10054854 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 597382158 1250 597380908 597380921
    0x1401140a0605090a05060702010c050d0f03181a070903050709051b03040c1a0d0212060906060301081908041d06010e041415040605120d030f1a040b0312130306 70
    0x1018040d0038007500d030f100d5641c0c038000400d81e80305580745511812244010303211000754040040c070f02e014140140390070603800b40c400a44000c0594040c45030322200310060600c0c42d10920058030350382e04014000750105405e1072a580080b034520307000040350384c0c3ea162a828910300e174000280703240d1554207100948103120701ca44030000400040030725508081e84d0741e425a5a42d40f04047d100384402d0483d000c207215040030303902c20b4641e0075802d540e5540d4001400180c540c08a812601c42c6042c2c5002c501107003400416281601e441038010400f407a4180103585000c0c03080178086400c10001c10011404881d081d03901e04e40380d41d8038406c1030303080d06080740050130045240040a008a00e414071100d0300038000002150080c40300e18040c000c0101780d2020074040c18044e08120740055100700308030b400c2c02d000a900d6404e515190b03400c01400d00300c0200300702614800d020041e0044401c06007925a85459407180b4001000101190358001071550000324a400880410486208103c01082803024601421 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 597383408 1250 597382158 597382169
    0xd1b0509011203140d1508061612110405040914120c0d030908041e06021b0a03120309060e03041706161803020628090b04181401140a 59
    0x4241036042c044800705845140b4009801c00030050416a400c1408008840890805040074031400f03a0f4881501403031021481124480e01c64540007500c041c10403210301d602c01c081940d400900d4030b20240e212000d0200c0070700d13009205108000001d8255034505c1410b440c0f0748250704180541e6202003200f802c1c42d215070500144010304025009100c4404a010070503000c00d070600045001d10f134209a5188d00864000140f0040798429511410500f0a07075030301190f9481e03007120491308206c0c0101c46440d900545842c2c210085c3c06080c000100d018a0318a91824980790009084015032925400d40b03036058032400180d00005402d0180b030740120b4039002d0032003c02c8010b01c0c080c1000541c0c503003a448245581d4040007580d6243c5641c401c0070350b01940040d03030020030041e150b03241e0300320141c0207464089204900003c80040a02e6103409421064102d07004d00d81e030381e406c007032800d0240201c403961070b00e04005081d5500c064658486000c0c048a0107824160400d2000000030310510109a400d41c101 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 597384658 1250 597383408 597383419
    0x5130302010e161503060b0d0207050d03021602040e03090301060f26070911070b1006090e0402100f0203040806040b0a06061d01050d1118100e010c140c0d1b05 70
    0x120075224496041c1c0d18104c070400140010ba10030a248224001d040503003100c0c803595000a9000300743c1d001c54020b06983c03401401950003070400c0f24020f500301c0c0b158000000092000344500340140c500ba52003a04030040d10b400390b80ca020740b0354001030308603492500882c040d6000e02d07400340151010024600100c1400d11030031007003013865113842c554520107445542c0302d05807030b03403c50303c02e040580080c4c1e403c0c40c0d80b0094420303103401c0901040960906501800d000a814100d0014140f000c000355203008640183c444a0341520b9030b001101c0504031502c03184d080d480204400500700208021151042e07002d0300c034500c240d00b00f4800c2e081c10b41d140390b80040e041008943c229070000c100d020414070b02c2c1409007410ba0b5142c0b01c084000f4040e00781c403640a40400130116166810f00d160301c0c030f0100c14040868640300071200d082ca05540300007402c1c20702e500040103000454009444500a903444554400c121140c1c3c1c0b60950006080c3c11090310100c03828080d990890050406540900000c0d0104448 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 597385908 1250 597384658 597384673
    0x120f17040b1c05160c1e05160905150108070c02011e032009150901030f0606020a030306080d0909180506010803070303060f05010c02040f0605090a09031407080405060c0f0105130302010e 82
    0x2401411301700b038420013811000c0c0b4545800d00404050485105041d40401681c85031500c4604081c00c1c12004d214401c4100d007440000703a140480b00040100501050710f400c200d5494040c0202d81c10b0190007003c90521481241742e00707044e1981110840484072035900414101e041042d0f9507410260004482100181401448001e0b56a03d00110043c4910162070780c43e8508140101c000d40307050403440d221185010404101c40e507003c9502854a402602c06006041c1d688040300d958000c030710c5074440064280d102c00d0014642d0707904000e035115018650f0b8141c0d2501502c4840c2028403e078080004c65200007041d00401d078141c0100e1009090704803c00110300d00d04400a0004099140001c1c2308540d6090a16482c108662018019190203042d929075440d01c8400f9600034096990150003140390f0310343c002c0c0c15135420f48c110b40e04907a1140b10075040074507000a200e240e0300a86200071076802400740c2030702040e4003403180602c01c00761800501040c200f1818040c2c210381c2e110410200315007100702e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 597387158 1250 597385908 597385951
    0x2150306100f020a020604030b01060e0d11010e0103021e1e0304080d020c0307061104180501121e170712050a0e0909121210120f17040b1c05 62
    0x264018680002d080c40c100064002000b24100b21303004100a60110b07001c1000b01c24000c0008146060710340c1d680340c0c030f800c991050b010401400d0f56940000d010a000400c22030b01540300e58802da0a040b0306040c09420812420469a91115459407140c58403c2c0400c001d14108581440d400c0c403a08000b0010740f441c03d01d40c9660145208200b04100910340005408010003420402c940c500754102104002408a2a2900800e0703400741c0f0a152102c0346001ca040c840350f9062184074103d51540700c81818070712266607118030b2030310300c3c0c100008040c0c181003c001c0410754140d418158044860651a42c0d035101c2e00d0420b400305203508078131040060a000070240140c2100380048071080480710548141c1c1d810082178640b42c410110341414920105040c1c0720940200003050080200c45009141070b5140c4c04607000d461803c1d40080c10981c00900c850000c5905a10480f000d00e840005042c540754030340c0c003080100e80c400885410b000208c0840e80c840c0da0b00c580b0030150805100700030408105c9112 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 597388408 1250 597387158 597387169
    0x90618060f121b0f0604080322090c031e0605180603010e0303070207150806060d05150d06020c06011e030303020a0e21151306020903030909071806020a080711010e0402130302150306 80
    0x404010441d8403020b21001c641d001301031090030040c80c182009110b2f5161013403000303000d00310b02140c42008000c1c2031145000002280590825100094041640841118204100a28040d01c0c064255603030720b0329003180f94014001188100c1c141c1d001008010710380290800a00c555052000800011006110307450352044115001307808038070004240c0340c8a03010442d103505d55034400154040150719031001040040d40180040384601c0054661603a40d90214003210003084503412144810301d2020300c00a40294064616007805280000350a51044041607070f200840051580300051401e044044040400285480242410300b518140c1080300880e0705180ca861002004140c01041c00c0060343c60070000e40d0032060005000c140700c1c0c1084803002e40b01c41c0d0f942681b9222404441d101041a40c00041c0a40c035031507102c2601441c6c81407a4407105064030400300d005040200c03600b5101d04994603030014111205c120a441c06d4400d183d40304000800920300d03502c04070031805000300300c40b682c0c61 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 597389658 1250 597388408 597388417
    0x3050106050a081807060c1505040201202515020c010504140f0307141206041a06120a0c080f210a02072102090618060f121b0f06040803 60
    0x1900b4000da507604c4240c80300103400e4040800055511070814002122580a415020070f503000d0640543c14800e80348142c13064800845000c4d010071908003100c130b4010000c4880a404c0d40000c41074440560304514040700c40707224409032201e00b82128800340010159402130402040c581d00041110081010000e03010b4091441960700385054600c080300300b51500d420042c0100d03001000d5414190f2200d84031000b00c40c0c0d00a18034010010320903041d44103c4000b820702d005541003041111019904101c41c9080d40c0300a0415400c0a090700f65816100310400094541d6441400b20721095410322400342e2404048480240d1030ba4843c0d203114010f203803807407040740044000ca0440c550b10700401c60160301d03183c407541c0402c010300b008400200c1d140340d884807400a900e00c00c035010210394440f8001c0203144880e000034052070840a00114003107107002403045e1803810000d442071050121041d07180d8207060301d481c03030329444034081c11668103645880c446070740702c0020495071942818145140b084d942d024 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 597390908 1250 597389658 597389677
    0x1406091509011101060803071101020a0506060d06141303030f14060907030605060a020304030b0604060b2a0f0a12080702100e07090911090a06080a06020d090f210305010605 76
    0x100090050319a40f01d07038120421840400000c0c09070907a500c0c1040e550781e0003050252103242d602588580d10390310104440780ea1a0700680200101d1b00d600080180036082c51204581c0190744915003107012604001c100d01c92500b9901e4414001c4071400c02a099500070b188070106c01d031401040c80031604440c64403c0d00024161030300f0910356101c10043d002002b0940107d0340c0b002000c180328204c142e0010050060701d101d801306404030707150402404242c03072840c019004089030030300c50102a03404441d040d04400c103000d04c12100d060446542181000800c40c40d0300116000300900c1400d2000100d51040288544c1c03500c0e4449260041009454035200d50510a0403503c5003402213501c2820001030024002141d410803180c8003c1ca80300d10a80b00b035410ed103000b10407030000600c84c4161441031400322540a005401501026075030000294409544245103640e50780510b4041820706e140b00301094858401c20032455151151100b00c0704280111004140c00c1400600003194000306450752200b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 597392158 1250 597390908 597390949
    0x240a0501120504050a1e0c0602060613090303090813451413030810180b0105160503040e011e0e040f0b043203180a03080d0501140609 59
    0x700c0d00e2502505000c5c0012028100c04142d20703111002010307070503642d0340e041e118280c03060040f540c6071410b980726181140e030b203075010811400c105414411608121503461103883c0002d0380c08010342d00c0d41d145400043c2c014402000810050080d54201500d20340035041154859415071900d814403030740488280101000e5103501039200306144600e800020092201400c540000c0c98001190324503040207540590000e802c100201d0201c0d04050324040540d54901d8042e01680001559100a0302d07412404904200303040000d030b440c038428005204041c40c401d80144d41c0d214a07111900403e0001a0018607905a418000c164000a2900c0800132141e8040c151070300d5980c0c2d814143d1081301d4110010704080201003c2004020308041a0010fa0f1000d0703005060740d078250b0b408000c0520314001c1c3c2003481d6104100008203115001011005070700d0081c48401ca40380c90790f0f142c58058022002c0c4401caa600e0700e00500142500118801210704240c0754942000c001000103018149810700000c28007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 597393408 1250 597392158 597392161
    0x2b0b1509040b0a120605150108060d2a0801060911030c04051302070209090c01090803130b0c0a0c17010b010e0616110a12120504030b01060513030209240a05011205 72
    0x10b855880a081c024140180b018608a02a00b4440c5c003400b030495643c40410015190345110b9030154900500400c8090181e5005000c2170f6a1a4412020014540d1072034240c4d050003107480303600e02c3d10300011b0a030b214000300c0c08a24044d448019507948403800d14100f0014400c0010850b065030642e421544110740c50420f50820700e5039203009108004010f90090544001c002c0c00d5040002d200428038000c1e41c462507401c1c1e441e15150349038000c0e00e40d80f425a0f0180001041480416170113420284904c0f0240e661030341182c0d0b40e400703038181507512040c0d40200550404941d80020b214040b20706a080c2000380e10016500001031180c0b2980c00e03021445aa006540f20034400700d1540d00407a2000a000044015203a082400040c0c031107100864201005c181e210700035030b100c0d030f0595003100d610170030407211a420a441075646400c0848900a0018424000409aa10130090340e01942c0e6a440c66040503070101541d10003d000c0036000f60140519480401c0282d80c0007410180b241852100001c69 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 597394658 1250 597393408 597393431
    0x1c020c061c06090606050c1203070c0b040c0b190807050313020103050417040f080106140d02121c09140d03080a0903090e010603020a12050f0f04082b0b150904 70
    0x10090741d00190450340c50b184c404031300c0982010080c106070000c40203c9650301c4407845039088901c8101d50010014042e8151003000603c500b0710f40e50003502c1141c640441c02c1d04d844084c0b00703d8011000803414800c4060012820b15000010a074008240707140540c07461070a1055600c00d14000321000307040540d960005000d12920392140c004010219045694a0f59107940384c0c00c810b41e281c01580859440c10400186010a01d000c0c5a00388002400b00c441c00403040d020401c1c0006141c040082c076014078411840e0b80b0380e00100d50541c49800b900c400c05190b003020850010100c0603c0002e0003045812010400b0176044107007070764088010740d00403850641c01c5c9401c603640c0b5001d0703004401030041c12001052650301034020300540607180e07407a20b01c0490090035030703420b0701c00541c2c81450801c01c05011421302d000003690554410301802225181c00844601e8540c00e050351403207a03a16900420512100030040e0155000e098822140705441c035895103621580c07803040200d403521440d81c80818206 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 597395908 1250 597394658 597394661
    0xf0807030b091005040b040203040213200c031b2d0a0204020d0c17040b1b0906030906060a06051309020c0f03040f0303170c07140c0d051c020c061c 65
    0x1400e8001510485083c1802d5501c10391006490003034074425820701d59241d090b07050900c2664401d44c0c004100c02d01c411145800030f0b0081c02e0300600b05116254030702c1c540702484407490003040c1e40c2e8020001035680e0325040305104811101c000103080c1c81c0d0003260100020010460060001c0c80c070300c0010040f02004602c00d1481c1040c0250000c0d000350001c1240e40560340385601c840b0344284540c076000540c0d52400c148200411044030010140008400410302d450808003030500f00350030516a0502d001040e90004216810854a050843e4001401c00609080030b00071140140300342c0c20002d04004401000040a40e16801400241c50380442c0010345a1010003488082c02d88080a4075641c03910340c2e080d600c94604900003035020032103803019100054000d004c002d100300c00410080742488150f40e9091701031718250300d01114a1080b4403804146984002c0001207a52180004150303449a1000000511500340101419908403010340c28064980c6c0f0121500b20200b401003105500203e20b6140 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 597397158 1250 597395908 597395921
    0x507200f0a06050d050a0603031e0504170615120706110705220501240f03060503010c210c020a0f0c1a0c010e0a200f031203070f0206070f080703 64
    0x203030300410001d40041c849070008000c001c0241200b03002c0c41540c1d94012002c2c196105480700500140008000300c60105100c2c5007480d80d0001890603030300c0c1035071b07400d5480b07482c240300002c0c0034080e0054001c1c07040103c1c07013422480c0003040a880c0c4c1480394002c412607030b4498110303101d1681400b042900000a0400078400100640b42c000c00100c2e0421319040000c1d158003a200c505890203103050008681184041c0040b91850346400401c490b6040d580e20495510751581400030031b15440b6100810340f550f083c01020003a00c140e64826002030700c848003a15100000c050b0039032074580342488041a0b9603001c01c42d8004650010720141d085042ca28040f50010301c1544000e03880105c01a000843d07515443c020107805500800900041840c03a400684421000000a01c440300b40318001084100034006280d000384000c0014916104e4500800e05001580c00409018a000000c00c8901a044035144610041a02c0103000924208078003a21903c4049001c8003070008a80014452034441d17040b81 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 597398408 1250 597397158 597397189
    0x207051203070906140309030406030209031c120b0f03030d0b1302040305010b10020f0d11010f0f06060305090a08043309060809010c080406020f0c070321050720 71
    0x360341e4a0a03000052106240d40126030000e0b070b40e141180d1550340c0c80d005407801000648099803905142030000e9000354480d03510b09402d8001c5d2120500c0d100e1304040c10b03407519003090301c0ba041c503982018034910841c0c903040031962003003681d040e50040c2d90b1000001e4a4140c4098600010801000400100c0460707450720004107840c00090088108101904242d44540050320804c2e008204404240d03180c12242c2110300055004c070424a481a21a600034040465140c0000401c10b05905108040c0c682060851103c40e8448000300041c036898400c560740816a0b0011704030202c003070b40c0d0300c551070712840c03180a03c1e18080110300006404092802c040340c04441d4110703007448820b1207024206042c03622944c408103800000003844404180202c441d08104c0340e841180c65561230703031004001c0d044641124007640040c001d03804007003400c02220024501514000c030232003418004441c80e00b01ca1440075801c000c800d00445001840c001650050002a01d0404d214810010041002d070011036651 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 597399658 1250 597398408 597398443
    0x625060204032109060816141603051801030903080721140406050703060f03031404030b01230607080301230301050a020c0601080604050a031d09010b0d2d020705 71
    0x960800510860301c81220f000c1a8659290700359692030251070601c8115000380d4000202040c110f41188210b10060001140139441c0b814034084ca00460400e80303480c0b07070440108200189540300c9545c0383d410719060420074a000d100d00510755900a260b080050901d906000e2144940d10145005821600c403521090700c0400241c4c40c4865400800c48041e6000c0d5565481d080c0803500c820b2190250340d0a07583d41030032107032100340313550780c1124074812455222103400018040030001881c0c040300c0314000c101e1072900303030040000e0b00841e1076000805100c1921900042002e0700003d1440b60981e41101c000c1e90329000990442502100b40c0080d00804603410751a000c10482144c01b11760181001c03041080031180240e803a009040c0c3e84440540b8098400c4d40b2804000340040e120b114800f2482c52509a900f1030f0300d108030702040d0400310a030882090700501180710101200e2902c681d00445803500c00c6440748104280119030b0b0301c1034055810300e03e030342c0020704001440310803c00e5510351480c0511 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 597400908 1250 597399658 597399683
    0x602030a110a0204111215060f0c010b0d030e09010f030c05040203060409051002040612090512030414070612051e06120120030f071d01050304171603020606062506020403 75
    0x4182aa40c6c1c000c90380710458029090200d90042d9000c4010f40740594090119417501d040ca60300c00c0025008400c0130400756490343c208041c13949032040016001c0f0312039141c5441d02c18030b620401000f1203058009040d42d4441030800c001040c625400601203030401d0b00c005a03640c40300c01c0414041e24540102404501c1740c0102c00c07980300321542c01001281c1172a0388910b42540b4008408007942d80030480a0020703030108080742d07503d0290000564005200d88050951042603143c19420095960b0020020a2003220041e0100006000c0d19030f00c40c0b0b00300c2440c04041134299680a44002c094541402500e00c80c6c051b03001c442d02584140b82d48048589100b200814104422102c2e5104a4440d030484003c0d01c08a058140501c201504c1c55102000c505940e405050045550341c00082040e10405405100400381220620040c020750b01d6440c0f05100d1100141001780c50414090a05400740c0c030204140074004951843d8a00440b05a880b5082d9030703016400c09101a029a40026001264010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 597402158 1250 597400908 597400931
    0x304030b1305011b090512030d0c030603140c041b0215060301240312050f0f090a050909100e070f060507080903120d0e01021201120c15020d080f010602030a110a0204 73
    0x72144004100a85d944074407980c444081c03111040c40c0c0e12020320140c2c014000904400310780c0d003101c2b5515100c2d103000102c00307980c4e8070b8210f461420342031030b880c15802c16030f1500c0550804e4010354440c1078007013490000802c0c0c4e003e0021740d40c00010032040c851742c600901080e002e0346c00b0740102026512000d900c00300501c03c0d001181d4107400d0791104940000001042001c100d010300250703211540f0241c20241050031860f1034102c140e00c68000c680e4011015680440d259480324a070034042e80c0450014443c02c0321180041e0112449885104802ea000040c100040300080f5041d60540e26685050364a4000f5413401c101103001c7d407446164035018589600d40c041d00405c2c060100301003903100500804c48a070003803600300d00c9a0380010314007114200052203140c00c1c1c4041c1a0501d4031808034144e040e81d4420402c88c1c102c01d01d1605070016041881c001034250350003000b07e60448911141d5805035458604080c2d038a02c2099070640c10300031500032403000c88178288601404d82d44c0151013840781d0081e14 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 597403408 1250 597402158 597402191
    0x3040203011e2f120417030403031d010e0d0f051b0f1c0804020609061e0d360f050303190c03020901020a0605101a030907170304030b130501 62
    0x1200c00540510640c58080c903c004100e0780003102c01c120003806241039030201c61500b0070a0018015255a10142d03040b200c6803958000071485140241c0d03000804a4842c91501000382030300c80c9081c0c031a8140f19641b0409000440c98150403c25410486001c01d0640b6007500d0758081c1c000c200108540326070a0394003c00000c0340784001008040b083c0c601d0741d640300200c48800d0085080e00c40020340507000140060500c40001d0500640007403809003083c80780c18030145015050f200c48114484042036168a142c0d080c021400450703c0351081d200001c1c05d40030880700d40d5210701c500030b441c040c00707024841c2404002400003107841e0b04141aa50b40b854509100c2200e03210309201103111600c2e1810640246220f84250760000c40c05901500c5107014540301d0b8005080c010b001108501e50f21500001d480502c1d80010101c0300c5200c600303d80fa4644103064508202142d0300190451000ea07440a0403404040100d40540341d0141d094103e5880d101076201c0d0407100e040c4d00401d1903190040000166011 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 597404658 1250 597403408 597403421
    0x90114010510110708330f04020a0e10030201020c0102010c050304060b0a150c020f010905010509040e030d0c030b0a1505030f041a070302070b0c040b0d0e0a0c0609180908070803040203011e 83
    0x301181034400030901540c4104842000c070403a011b6a0316440400d04d04460b4594890304280024880c9103620f44a0381010701c2c400b0103072803400f41c4c0c10301914100304550301070001c08a4184240000c0208d050a0340000d01507110080c0001c10703c0e07a503400c10a600380c0d180010381c00988411104442d01154400000d050000075030b0050b48200b2100d4140b9070190711881c10401541e0046e542c0c181403110f02c00a020240c440ca035003074902c0340070910018401000318494100000d1082c3c4d0086a10751506042c80000c81280e0080b5812502d51070a030104250007404894016484441c841035039030391802d04140b503402d4005211104c94040b0144890b0a50640262a02038003030702d250456910b0300307861455244118410b141010005019641c1c02e11003560000d00e9103c0e080040e50b881076142e0b600c1d0071200c0301c582c00c50004610820000c0c05036804000790740d841d103420004104010000c2c2d40ba030648900406038001d02945c0c00000280031501d00703402c0414120f10601d10344000411014140014240 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 597405908 1250 597404658 597404683
    0x20a020d0e030c0d08090409172a061b0705060f0a0f05190e15010303031b030b06161104050108030301081218010c03180803040e090114010510110708 66
    0x10345603180141c600e40400c00e03491070b440c01000c20702485041e594001a50308405020f503805541c88086001040400081c0e04c8800070200c00d107a0b807031100040c200c01b54540418180040d1400007003071101108002080c0fa004010036030058078182c0364503400e185501c11050014160f0064400344080c08000c10015401203940c064188812044002000112001184c211450800043c09014075031565400488040110741c00d0300e454490020b05812803400c281d108400180da14000c2c4480c002a00ccc944d1504c404c0070345428003004d2a1840010100c0c09032581e0044407545c1000014100244038514034250760015000740304a41c1c0d10311000347c82e504244103c4031240140703146140912801c008898020120401045420900c0001110f110350380701c0d4100c043c080c441c1c90340300141c1c110500803402480d4070002159a1810804c45101c01007000c0d165404607810003029041c0c840d02d450407141550402d07514502424142c000444550071146401e100d5401501c401061482c1e003c80c50001d00e15 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 597407158 1250 597405908 597405917
    0x82b02090a0e070e010e0a03080403120e120601030213020d09060e0f0a0b010b0c15181513030809010b04020708130605091c08280e0103020a02151801020a020d 70
    0x40d40c410b0388510300641107400d5400218400f440d41010b42c010100c9049481001d059042500d44a41e0342d41030300d50181d00107484031515100d20000c4180d200c04111a58203054680a1440e06c000e11865503410060000900c501c4126a030103445100503419281d850429082c24000c50300241890001040804042c8000d03000d00c6250b1100304070001891203000c3e901034039080160b803801d504100a600700c0001860381d8065240e40f104444003000301c4901600119140d00d0a462464119618010000b030410320211401e10800c038580c002d115402c0100c0d0341505050825a5907410003500405220185039030052011552400f40088000600f1221100a200184490f1102010744290103460f05255100f101041740c0fa182c1407480015020b5584503402ca2400c02e00c14241e421044416100174088581c3c0d94600c03000c03455071120300c1140440c0f00b82011031500001000c0252140c003070740303c5011420b50400200b400c2040500c600e0030005003400c0215102d072074082c4000e4032012041c241c0310004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 597408408 1250 597407158 597407179
    0x303081e07050409020c01020409020403230a03050d0b0d0c090606030b06030105060a1d0a0b03090d17160507051b030f070501022a040e0309150c0a082b0209 69
    0xc60800d0520340506503503219141000e10340020040a988600140c25080d5024400024200114005030024620031200b00c3c0f143c018039902c0700103140e25069002a90761000b2600f401080d0060f040741c4600c80105008110700d03203404041040603400303450040034040c0c410800900e61040e54403860686006035418441f40e00d1520403c255400203000e1558001010003058001c80d02920484c04207034a4005020140310290780003800c1d00709030307070b10040300820b0010801440d80024407a030221010281000034014550206196150310010000610f00300c07000c62520185002c1d4054802603503004045a40102d12140d070b0f031014018440120b0700a01c81d00000c4042d4450101d400e00507034030182c1c020080c01003c1302d080e000c4c2000040803201d81141c2e0020044143d2501e008119446202e00000c641e84c01e145814051131a4403038841541d04e002c00e00142800080201d54a01c54a4008800c80c0d05d40c1c80c2d4028449141e41c03581e08204000011807080142c04c0c000fa005007800d004101c0300108107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 597409658 1250 597408408 597408451
    0x30d0f09050312040e04031103070f03080109050f01141201022106010f021209060f070309051003020708041a0f030103140c0d030f080c09031212061906030f0f06030308 74
    0x65180700e0301c207903c03007400500050111440301c600d841d50050191078191884002490f8443c21a0b2254109540c154218074911043c180c200c19043c0c01040983c0c0308000f249481100340f01d0006060042902c030007940d0f1284010742c1e440341422a82d081070b01d0008c55480080d100c0c074100c0701d4844600c4100100d80c2200140aa6002c0c0074600004403480d0081d10441a0f00b40152125600c44401d13103511078002d1201412015000d00179201c02c40c480c1e11028100c2d03060000300020707000c100c0c500320300701401041082c0000300840f0588046800c155100326481020001b0000c1d2070040707200032025420040b0000003444050303c0d1100510f64000140d984040400302804082021a1006408260303003500f043c24041c40703186500d5001303034072150107810640c40100003810012a81c20843c56940045940c1c00c61214000e038564110000b01c560341ca03c0c1e80c0d241d01e0500509840d104007000c0c95940c01c6100104425a00700c51043d60704801c2c01c111241d102d1402802003c0305035091080f0101c80000c5044 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 597410908 1250 597409658 597409663
    0x1111f090b16120c090e04080c070f050307230603091b01020102090913030e03030a11190c050d0c270506040b1e030a080f030610030603111e030d0f090503 68
    0x402800c690fa80040d121440c030308410261518903210010095140130001d1102c0c040007104d80214800d5040c251f44001d200c40c6186000f120343c02c040e00c11008000304002681d800540301040b41c1900300e404411060400241341002208400076422100000030001c22840114214000d80200b000740b034480001100124201d00500c1d03034070b0f604801d00c0400b054407980a11400303010503100303141020400603005c020a0a44d0810754100c0c000c1002c22081c101c0d1031800307200000c0c56903041c84001c036001034107032243d84420703220b4841e00c1c1c0134580c001094004d00c0144082100981007180b0a0362110301543c515040e8001e2002e080b81c046894140443c20501c5c00c4e00a03120881d0004041c640083c5a000508a01c610941c8202da4588240060040001c032001c025211610f4005452a22880c1031810301410364071622140c003c06151001c01c0c000200b451070100002d40c0f0940d014010000b040c444074502201580410b940b602c294044000300d103030b000c0840030703190744596101c0c640d8503519001d055 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 597412158 1250 597410908 597410941
    0xc05120f19150f020c0d0306050406080309090109020c0a1a070806040e060a1d0615120d0f08040204060509040f11060a0c020609180708270c01111f090b 67
    0x42c04020882c2c4505511800d5410030040107104410051900302505441e501c2c05010164080110351510010403880c03819129050040a080740170b1490223003074800091040e0414050f00311071950200b000441407000304180318401d9841041403180303250851112900d503004654803000505003500145071801c040c050b007400703238070404000c3c900c07603e030011b01d4005000d840b0134541000201c03201f0060030040410245004004104203844214000c1d400d01c0300280700203a98602a41c449481a040d15174041c0c020201400c4903d00320700a81c07104d200107000b6020b1540100d0b8082c00303801c00d00050210301c030800d10703410f8803a05c0c40d10140076400061241e507005000d0a0008a0002503c15000d401c062004061100c0000c04510982382e0a04a134900c0550660720f40e0006007000b0100000c02c043c90041000140300020410840e039680b4546664400c260f054182c1000703840900c10007040c80400040c01003802e59241c1d040100008103c090003008102030a5401c40000d40110300700304407079607102 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 597413408 1250 597412158 597412163
    0x70b040306180f02010f02032109010c14040603090c0b0c161a0d09020a08011104030b10150e041b0e030c0405060901030206160204020412020f09071b0c05120f19 71
    0x102d00c1143c2c9a0015100b1180105d107500039070000304000403038448080101c044a48104124900604020801908450036501c0300f40a0150319405191141510300580342203840ca403070040b0f82a00589000d16480c0842e40c4203800d000400b18000c0c0c0d4481c00070074594084540c101a40400b5507407440d101001010b8041c4a408040c2d0800800e10041000d030403201e11a40040d2400c000c055654290500712003000c01449215440807409108216425001c650092961018038410500704543c01005911500341c1c0c0c000e1120340b0307800c00c0480d10f95800a8003400b246a001038a03800286002601071101903800911034020b03410382c92180d01e01441082e011398005040200184c4c00c1d40c6c03d00c803030b5074821003a402c980101c480d80c40707006980c2d90000744040c10020b00f400c40a50705510611003031141100005c1c0c030400b9503c0401a080750701c1002052030a100aa100c3c0c000f24a0b401e04504004160b0445c42d088a4070050000c602140000d11100d40740c5490220762103108104414111100e012900 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 597414658 1250 597413408 597413423
    0x9061803170c07031506031b0e010e060d0212010b0310091e03121a0109150806092a0a020d02160b0a03020c15040212010204030201022508070b04030618 67
    0x445951241201c0034202a000160489601c20344a881d2480305121113000c1c1c00b2a103840c0d400a0040110803039030314014407001700300c514019061403034480300d500d4140601880702512b440002d00d642d81d1140007125164002d0244500c90241c11251806421600c0005000e84500510480814130920403014455017011000c01710290021810089243d0f0030015010807071f0440310350b101c0100c184203016090706c0c5641d680e0030002030703800090844100780e402030843c0c01c00c0050041125401a01696000c0c0003102d003a0783e0f5a9a60621080d4242d061754006103401380151010504144400205600c428a03001c0350301c01070348418201c0e5106110f210460641ca00c2107030420510344144080c0c22512410b090242c1008250301e15207181402c3c0103100c0c2e410244501c180300a41c1092210305146010020003585041e0070340d000031307580d222000c0700a8480503c11082400c19000781c000b40020b000c40c05c05880d030b8203070381741800c10740e0350820f00007a680180340400b2890001c0007903469800090344010f2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 597415908 1250 597414658 597414683
    0x2010e01020a1a091c05040504051810050604150b180a15080a09120206040312020307090605070812010602030c0d030903270506040f0e241212070309061803 69
    0x100340c4080f140903100d40b1892050702c00e40700581c1c0d001c041054441d44c00b81d4078a91510314000402050301c1c0003a04182d0707092400c0d074650460070340c04a080109800c03400d030042078544900c0046001020700d103100e460700d9182d0a0000c11070302c60340303401461440a094281c3c5090142103040281d144800d21031030401c14a180001c0d04407d004141e440e500c40c508480c0081c2d03449103500c031802401d1075140d180005800801c03c0004141d0005140703000900030440460035450b20400c09410001a03006407424000040b40000401003480c0c101c41c503080c80210408001e59481501a60360f4001c0c802130491741c0107401090400c10310a1044c00c80d56905503568581014943d81e0503e00000030729000c8140c292607a20100d900d8403610001c00041910000420b40189045a12001040d001d442c44102140500c51070b000c405000c4e81d603021a9038101d515243c0c842207091120f203045c0e0583c111043c0101c2c00304500f000e050308284d171002103680070b4564814a074820760b1300382c0030300099020040141c4002103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 597417158 1250 597415908 597415943
    0x40b0303070f0303110d090b0907060504091a270c0c0607030b06070f030806010207090515011413060e09161421090106030c0e0c09010f0c020402030f0402010e01020a 73
    0x4911282843c000d00700010b030030000040d03002c10366208540704840c1589802d5503a0800040c072060a43c000602d1015011f80c03405c250004001e4420341c40340d10380f81e41c0c942c90807454083c040c0c80b01d5410000000c040c180c0811621100307000d800c0c41109919a401000e000056119112a003100e03201038451010308096038803084190f0050041c2c0d1009a00104c1c14461400010089121002014000d40303a41440b4a07200000920b49105900600300281c108001c0c8202010315500c4014541c1302400c10021900e0b44400d09001030003001c010650241c140c000005402e50000c0c03003201518000e0740c01f025641d035826200c0c6400c44501c8886400a6a40c540680c6422003800181c20707078014000e00d0203000e60140072595100d500903030701130800340d650f000c0c00c20400c200c602c0c0c0c0c0300041006400301205032601c14155102800740c40d00ca20f0501100341042001c0d03502c110070202e4240c0d40100115100d00340740d80d2403a501d8904a9089001c5440981000525030000402c2c058040c0c3c1301080600b40324888 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 597418408 1250 597417158 597417173
    0x7080a0909051030021017010e0103061803051e0c01091109090d140a1205070e0102070b040b040909020609281d2802130302090105040b030307 63
    0x100a024200440200081101041401114041c00660740c2c0d011065080260340e42e80c0398140400d00c1440c91801344601844942c80149400c40c0381c04803501e40c0141e00b100d40035202071807181219251503001600106a04034400140c0e4180e03401044104800100303821118039005081c803010340803900030b110308040b081060300d401031461400304132541400d4a017425207080d921481c104a030f442209a0074100581803101c0030390740c000c01c41401070011030f01c9a00058820400c03465006014003000680400960003515000c00d03441c0d070103400300031924266100406040c544c001250050095490006d001044542070b50107030b4100e41c130100e113030501d08528040145440c00040b608080705208038030a607170312180c0701c050b211141810711840007106404a83d03481840e401a80e40031030510680011041c201c04800d901c00390325401c3c0008440416800840c00b082401e03200fa045000003519194029440c200d40100c0c0c2c42035a00c40c400d0703602d880401055079403940c0051382550052080d2000701d000d4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 597419658 1250 597418408 597418417
    0x32b051009020c12160620070b07051e071a22060e011404020a08030a0e0609010c0f05100c020109050a03030c200303180604020a23040603110301150b0708 68
    0x21402195101c0c059500d01070041d40007a030307500c0c2c1c081401c17070742c40c006110081c0101008100c000200c1000f101c08194070f00315034003d06030003902d956100f400042e0382d58020400c0700d605041d03420b801082c01641013402c000a070b00000007101c103400c003048442c00e800d201c103140704d004415003000c0d000c10740c020340c0000da208010303410203445503500e0b45888180408284280e0300840710704650580946080e005010340182d5580c000040381d4800c00116050720b5100548800c28041120155038030903201004030350b00d80701e1440140c16002c0022964040141c0010900c0c1121222003041c487d04204110036404ca4202c1c2c54040c0071134100311a0031000a1280d030100c01540c14908140c484240140400d2b04080101e18092840703600c0041441900398902240543c40341c0d440f00100520b240a82c0030074601d0360144541c00e100c401e6402a01c0b148a2401030141c02200041c1c8104644ea6482c00c100546c0035460000e070307009501e0301d00f0480c1e1040828003c603060381c403880754103450074141d5943c0940c507510 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 597420908 1250 597419658 597419677
    0xf020933120610170f0a06030614070e0f0906040e070e180c060a0c0b0a02090d06060e010518071407020a03050c01080705091809010e032b05100902 65
    0x429a1406034040040409020703180d1003460303100c1c000c1c504401030000d40d050f440103a00901c0700700410200203901205140340c0c008001a8001c5641d1035840d0b022010f48519000104414180b0754001881201d01c25018032885040ea6402c44068540061001c807040c0042c005400145010010300300341019009441209406012141e40603560104588030400564070140c43d130b50840c900b0b080300182040410511041100c410b4580707004090040c08084110340010605032182001400c0d0003019030640e804106c0c050120245c0c80100d280001c0181002e000b4103860b20346c61000412a820030380041200c01400c60800e85560b01d540c0c0b02a2024030800440c0054010204480801a1211200c40000714412001099002e2098002411916006001c5000c009080c00000701540d584120910320100a00b036400c89506d03400b10140c054000490030307d20300d200000305c0c0c801c021010014690044000c4c0c1034060f0030348104406006a5a051780c3da5240443d51202c00c1c44076108503401003078600d1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 597422158 1250 597420908 597420979
    0x2a060810150207030302010c021f150b1803070f030201170405010e0304030c03110103090302030a180905040b0108060f0f181623011b170705100605040f0209 69
    0x340c0d01c440e100c000c2003020440a0042e0030000c0c08008140d024000d40c0700b0801c05d0700203484204580b42044035441146200d0103c0a034407072620003406002d0301280b0010384556081e055403960103c0481a01131710800d10704c2d00034031854000140a880c070000500c1a6030b41652207140c5d181084c3c900010801c006402520a0b5590700035600b0400b00410040c001907210303104000c481c130b15604001c0a4500c41d808007a051504101c044400a0350220072100003c03158102510045840c51051889450070340000d210545400180302c18849032541042c101c940002c1210065580c40346142c0c11082d00780d4481c0b0300501440e01181140020081e04091844110201d42c41e50f0760006040031201c000d030b4054550310340c98034001182842e0002d542e41c07040c142800c206040d00300c00d5039a1850008051000340c441d403035100f007130140e03603224404450045402200b195829a1880c4045000340300500c5658840c030701d000d681c50200320081c000d4820b045030060540e19500a44410802c103011091000c1c113901 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 597423408 1250 597422158 597422191
    0x31305150a0903080106080f0415020c0712110a06090e071209030f021e06161e0f0206060d0213050612010609200c060c090d0b090a2a0608 61
    0x1450044a80301e40504200480c6414840c10007400041041c1c000004000300c0208000c681e840000310f407070f0803d61020390301022210106508009000c3e8481a601d1409034080024290a0407950a42c02d680103465401180701c0090400c0b400500030b10903603000c03d0036640304100303250110b40f4450b4490f095090260800121851800444400b001c04501080034038420806e441c0c2d04015840e40c10306003034011000d0302c00303031114655102d0005014041400c22040c0c00f400c082e00c1102130303003c901500314100320ba0800010020300f0b450203142200c0c0041c811800000c141d460101a003407a17558014225040c00405424924064000181000d42000da88031504906281c00d101d1207005015a00300003038410302e00c140c0703201c1a034100c40e06042040c20034800300d01c03030358004981c464019200e05441e5503644001000700d6014040c6002c041c220036498010414541c4002c2a002c41080c420140d9441140f40020b280da850303191800031750008842d8013000d100c0a4040c01090740c00440000c0108101c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 597424658 1250 597423408 597423433
    0x406080c0a0b0d3801020615120a05161805061e0f090a020d050f220515071d010906080105010f0e1c02030d05160f06020c0105090c100305060303031305 67
    0x148291000342900c842034080c0758900300c103401402c059403481c00d10240640382003415041240c0c0c0d03402451a845105840c00700409a03404001d103241c0c40f6401026107102400003494cc1c40700004134403c01c0d566a00b0408802000782007881418420540100302200c0454145805500d022170341c4021030300542900b8000e007203079590780250383c454002c80d100940c1e1281042080c100b40e61028240700c0a802008050000b00c0200d00c01c071034a0103c042c0f99101c0a400c0c81d00f496480c00b620b4040c0c1c0b0060745040028402c645a00030400e0130030b041c00752083c803110060b040044410b4482d03032040c4000510740300e00512156104080f0383c403034407c6c07525010400e044682c0004511a1050840d41d031110030700d41c920b4007181014440d81c940c0d480c603400c1072800c0c0404c91600303c03164580880b00500300300340c4102540400c074943d810b680315080554000c00003480d2681c11240e55040010465100e10706150703600c90001d129000f00c51144002601941c00c60b224488040c4201d41012011240f50041d092107046 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 597425908 1250 597424658 597424691
    0xf020f0a0b0f0c09031f111c020c100504081201050d0209010905060105040902040b09011704050604060f110d0e071707090c030902030d09182702011107140406080c0a0b0d 75
    0x200352022079414910361b16030030b5118003101c8510545c4d0403500c6050011810b41a410745840d4041d03e050000580d80c0c0c000f0303106076070600c158040c04000c10342c50182400b0502c40b0a2014181c245000c071203402240e6224000c210400d014410b0003580201d18100503c004540d42c1c00250704550f041c140241469158400700050360000e811100b407000002c110310004c0e41c0d0003202e0500c1c25562002c1c0342140c0c03c0c01d1700c41d01e0729210002c201a10060301d40a815420240c0c42c0d01c442c000d0702d00d25013040c1e00c80f80b0401052000d46146001c00303070325104080000c100c84064014820545a40707000a09449140000b0100a00448281c0c0c0c410b050341e82103042d015850074072801e0080c00084d6146514942003401e02020007400480c040d10403413902c050010808185003142064a240246074100710609200407035200d02c02984250040c010740200103880c91b01c2c1c25008500c500221020f003d00c58581824503034480010880b03d500c903010190800c0100000d0000300700c0e100000c00301045084103100842d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 597427158 1250 597425908 597425923
    0xf04050c0d053904020307020d05031f0314010b090705041a120106080109050c04060c03030f0e0115240e012111042904141903030f020f0a0b0f0c0903 66
    0x1078180700b0220030fa24030710f001501c88007003002c0c00c071411815070070310503402035480042c5490b4405000b400030201b0f443c4000f440303ca400140301140501c2c3c0c481e44070701c1c018a40d8560381d40c085080d0341c20401562460314010040a101e84461703907030642413038034210040542100700c60074000c07064402c00003c4496206424880d0284c102600c0360402d41d498545404111040102a040e40900c1400244403141e4032040c0c003102940c041c54089207220720304080c44d0003001416880344942d0f203020304030003903041229021011503c0c031001d40c213075000c0400c2c5903802c00c05180e0441000600c90848800c00341d8001e1031407602403481d403039094800740c1d1b5150461003180c0030907000104540b8082000c01c11210302400074151054000002800011a140310304110b0090740503010845c030b9910650100c5440e0303054410440c00b020710900344801d07902c2c240075102450a003000001805030380302010000c10006452800d05500c0342070001c0b240d035010106500b100004d0510585800c040003c10b07000c0d9000c10481 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 597428408 1250 597427158 597427213
    0x60d0213020a020f0d020613110f120f010b0a0315051801020a09261e030c0304030605070306120c120c090507021f060501053406140f04050c0d05 64
    0xc2c001480c000a0740c0349030401c0807618104541c0500c0800689595101c070034118181d10200e003804051149c00042c1d0104004a5040d802801c10040c003524010300040c00e141c0e8102107402080343d004040e050181c1031405000c05008220b05501e402e40540745544541d50100d01d09411201a0010072080c80c00d9a05c0101c0b0000001d040000511480c0c04100031031075020026103104a5070070b0720084068aa4958178050708400c0403581800150400600407648072a0f007503c156503480e80c4034034003074000b0041030710f040002070f203082800304210120b4258a0303681500940c201c17051903c1e01c0070382801c881c0c0c2c804044415640081c0001541016070203808c0c0540e1468020384441c007030400040c010303007003400c0462121500380002000035036081000c4400c103002d8408140c000504441d051500c401c032103116103201c2c059a40c500400d208096210b00200d00210700c06031480d4a840d15003580ca503d0549000c0d0440c1c02a080940310303840d100c900903066a1090f01541c5003144540307c0d68485030400d9684 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 597429658 1250 597428408 597428413
    0x418060b09010b07050a0314040f06030e0613020a091a0607050d020f010c2307230f010c09050d050a05030c01090b060a06020706050a0e040911011106070503060d0213020a02 76
    0x80000a1a00c1c501c26400b424003012100c0c1001d16688425a0b41c480d10900642800142e4403c050072404540468001d80211003500c80496600c84005000700038006500e00346015990101d8080c04808401e107100c15002010070071702c10704100c078040c014104a10b11204590340602a00c1c0c481d05e0710400782000c0350007240540100307034601070064208902c0b07200d84007050340b421501808044e0010305125129081d0307a01c519400d00325501840c128454254003410500b056099190100c500a0301d0102030204902640c05a410744281c180c00e039100c0541c80343c045a0708000600c5141441989081543d0047c0200c4115842d82d4580c40d080d54001521000b280e511601c9400c240070028402c16000302e003c2d1002d249083c41c01400035100c1645001d101d080003c0090600e80700c0703100c1e070390740d0075120b00091041002100528210350b0194882880502140426054503069000884c0e102d1080c10140c480d1071070b60752800300b04070143d050520201d9109002da005c02910a006102620240700c65400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 597430908 1250 597429658 597429671
    0x30a0c1211100c030b180a02070203010e0102040f08070b030f1602011407020d0e09060907030b01091a0310090c020a03200102130801050c0711091b0d0606030b0a03030c02090402041806 81
    0x201035880486050f802011b806019840b0200c02840280d801400400016201d00b03651002901514030f06070303143d01560010402060540b01140c09008455030741c800c80b0b0285940b54030305100e13400b00f11803040d0307160704141c0021482c1e4103071814181c400030540300008402d00c10405400c2004401d0312044010b0707224032600d4840640082c0241058041180c12120a10b040b80009016032002032a000c1056103030300380202c80d6406604120302400c0c104000c050041400c0418004079041111180004801c03c84002840021031041c0c0031041c2e025800ba110007407541e10295124510f1021149014406400e1702c650710100788050030302041c2e0503404184140c90460300d9030070b4900281400c0c20703106040102c00000fa542010350915280203582c068425074908024440b64592910f192a0940d40002c80c0d20240c0070030303440f200a6801c652030412511404400340b106003040d0380030041c04510500c080c4400351030400107650b0f001748001c0021514010452440d002d00c3c0030440300715445604c400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 597432158 1250 597430908 597430931
    0xa06060206010f030c031e05121c06030506161103040608040c060e06030f10030c120302060a0c050901030222080307030e09040b06130605060c0307060608030a0c121110 74
    0xc0301e40100000c0360048030032815912158000d0fa0244401050102c402d11124a41d05680030600d0705240c1040603590b0980c10540250400c1d4071280350341c410440f8103000000c01040754807642c13094a40100041029640c5d80d0480019200c8040c4c01405101100a002032044000c20040001d4082c540d9143c0060901d440c102c0208085a0030030000e205108200b01ca464582c40b081c1ea500800d4101c480c0c1554881c8036030051040c4503900040c041e41c0382d02c0300228001c0c452188800007244139508039070345c90b903c00002008a4680020000020f181000f407000e8641c46900a02500310750550681c0002c684440a0700c811502c0343c1c040308841c0c0000c40c050003032582150844c0741816065502e5403031864183c0d00c503001d050008200b0b900c51314005c5a15541d080c200c0c3d010001500d00600410340d030b00c03084142c10b07599030401d5004580c081d0802c44081a1400040141e501030103ca03110f21242d228079594160040090400d11f400300424a0301070000c00004000b0030f003070102e581400140c011150b1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 597433408 1250 597432158 597432163
    0x61805070509070f05451801060f171510030c050702011b1a09010c0203040305062e03060915090f02130204050a0306060807050d030c06230a060602 65
    0xd03403140b4401c40106040202c80d035001100031040d80114940540d1b207000c0d24401d4245505031160b20040c0c0d0519166450186e40100c04242905140e0700c45c07100c0015035130b400c000303205481200074940c1041c0300004105080c00303200d540b250170529007070040462400c02c2c500d8080100460300c0c6040f00802d00225040c0d424800c0e8503601c0080c440c5004d05c111005990082d0040c495084028100300443d10403840c03005c1141d44510102e40d2100e16504030207410f0009141d01d0506949030701a5500c0c1040ca9800f00b070000040701c08482c0d0101c058242036503010314140304030440c8051088003090100312010004042c8400001440c415000020381c0c441d0782c20702c401041e09002c00140398034a44284000410450007007401c035242c1c1210070b400510400c48220029000d103034840c0b50080c95101d00803003004495002101900c44007001c0b1821190b46070700b0404042e00b000310203400b007103039000601c021488540210511000c2a5905140105c8200c845501203004407040c00041b03603540710910289606 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 597434658 1250 597433408 597433423
    0xd211503140607230f030f010603060609261c020a0b0612031e040803041205060601020a0b180309301c050306040b2107050109031a070c061805 63
    0x10010b1219141601024059540c04240801c030003001154444e90324580c03400700d89100003031107030054480c10415251060b4482c20700509020a092000100f0b450380314122910071140070607103450380008603485003d500d1600c21800102804ac480000c0300c00c42d40c0e00441c980702c1d0400d9000b4201c444807130500200b03092001d88402e11402c041458041000e0001007500c41d5007009406080e0001c00804001c20b0910441e8010356070344c003020170006035040c040c101500c3c00700d0089058540070341c3c52400482e11400000b40c010709500c01080416410000035000c02101d25400f41201d160001e00c1000945100c443c40b09529038180c10781204d40c81d000c4841c900040c0198800007411140107106081d801204928010408c0010100010b10250b44a400c0014540c5001d04001445844d039640714003451000c0e000c3c4000c82c4548000068294410104001101c0d00036060408030040d00c0c08200d0040c901801840400c0050707240c1c100494120720807807801071b00401103041920810b1800504200340e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 597435908 1250 597434658 597434693
    0x3270510050727030206030412020a0c0609060201050108120f0703170f09010b030601030809060d18030315150512070e041d070801181202030d050103051f09050d211503 74
    0x1643c500400041c3c0300c0d103080d00d802c00d80c004880c401c4094401812440d10314200c034050b00e0028103800014159030007614000548400d42d00070311107a0389038006070343d8030354445034007a10700c000c1040a192200c0084024014042c0302e440e04400303804403403543c424280341c10b807115000441548140034191600740300b285c10510065010302110362650f01e82c5640d60050420302401504001065100d4041d50b920249020310440c1c0007080003889428010010008403145181c44040c04c40007040030701e62540503540f4031425a03140c0d071400d8a80c001090200380083d0000041c01520462004160380b1350042100320b50310703141d9250b044120744013420304d40b41032a440710425074941458103840c25880d160039206250099051203100c0101c400c220b00e035100c0e0f0b10381d045241707203400000b0080250129040300500c0c0c0c220551606a40b03556115401c440101c070008006a10910030002c000340601140c41000e505460511841207001d07406005403000390002a5154851010600410245070264503c0300d8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 597437158 1250 597435908 597435977
    0x3080901180f0f2c060409020414040302070e010f15110102070609050705011404050409110d030305071707050d05060a0f0603051918080c030f210106032705100507 72
    0x144c0359100a074000004c21500402c88124500103401c07a1501e03000070b10706076405041044040b4159505000e10174040d02c00718014000d0000c00030b15003640c049840e042e1410070003284640ca18160320294000d1035011503409004900015042c10381c002c4c40901843d901034203001c01c050000345003440c1030000c0368100a0600520308240381b00e80300c0100a41d003da6a0544001601400c0e40c202000241c008200455000c00780054040c00c065050b0056402040291140c0c00181210044c400d20390000304c0348440010401e002c240740041d02c54000035082500546048040d546a120f54504020990048400320f41c0f510148407100c094100c0494055030f900c9000c02c205548a01c0d00800c5090b900342c054040107012074580c05070380c0240100c40307c0341844019540c0d504000d01c01c901801c40100c02400110105000000e4001d0190080c410741400c41034441a040c41852000b50801003090410781d141d2281420304040c2e420b07284110b602800103911500c18081412044c450715001d43c000140688 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 597438408 1250 597437158 597437189
    0x1507030306080f0703140c09100f06170f0403360801150b03040510020415170f130c03020a0905061c030215041a0c030a0e0f0703080901180f0f 63
    0x3d10040b034032074181c0750b10a041e01d501020104925261500e4900580d9110414005110300c4604101c0c0540c01c8420300818003103459601c810540358411070b660324401007044000000c240803850b17034145a005200e070814403151820500303800140c80c070406510f2143d12140d030318905002039040c4d4100041c8a100c0090042c0d074000f5200125014051258440340d0340c02001080800c2000e000428030100042e03000c6403100c6d941e03003040381400702c02551140828400300c06500c7c0c00003624403217845004040c2c46101c6549980328882140807803270000780c6c5c8411a403140440160760340d04040005120740200403400341029401c100e08000407400c075206410810104400113500441d64400840802e0070102c01c50380e503800c01400c00381d0f802c844007a4601c1088100400704040d8005540541948881003000d0203402504a5696503c1660804e8a078000300301000082d10407002840c0300720040c074024031641a2030b105058040603540001542002640007846400d8015112000030306c07110006ca550b6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 597439658 1250 597438408 597438433
    0xc0a05090105030705090c0418141501080415020409090b061c030f050a0309080c1b0402040515031e010314150408190207050d032703020907030c0905150703030608 72
    0x794070790b6100d030500030610381b0300240b402d4583d00c003610003d102204a0720010010400d01400400c1d10502c0744000c1c81c420b202288400305a54207800e62008103850f0018907840d503813608018a181c026440418907001c020215890115008240071540302d51345200c460305001040015882c0f5081381e41c2d966071040880c5c0c1003c29446165a2191111420203a41c0c50114040442c041c06901401070141e9800040c1601c0b039040c0040c03000003030b00c003200100b64494007010400040c1e01c41c52103141d92200540c01c1d43e403081000340c402960090341c40140ca03500071510709040655400309034400c0e685884200c030442003400f000d009280c0744640304001200f880c42c0694030180c00780203002c0d10300c000140074445800458020440030010301402492106003410038039006002c1c00c0004889507107004910b0305084d801544041d4007003640e13030041a8512a5550840c110000e000c280b80060801c4404039000a26858000c08015030402d0a503030305036100c0a40c200502900c0050340324600943c001c20700d4410 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 597440908 1250 597439658 597439663
    0x311040902040b0912010209011d18130b0610170a0f050112031d012708011d12040b040506070c0e01170c0d02030613050102120a05060a14030312090f06090c0a0509010503 75
    0xe0ad02d440c41c00700310840407807400314100e0902100c042e404903805909000f489192100346850281c4940100303005a541e581c00e00005482c940c086401040708007a0075041040600e1020303601c26005000000d24200c03c01c4043c0c285c590030fa02c40c0d08424407500031507081c1940858203001580c07021104c03101c2404a0030008142c10440401424070361001c110541c140e14a40f03a0120043c1102c000910540c00d091034404074688000ca41158140b0510043d158411b956a094404446000407864109494541400749a9000310710480d910380c0c005101082d100d411102d81030184c403d080411980d000e065074580e25100c0e02e040800c2c45810041158001a580002e4050b1321071120150240c03032100503e841d6029014500300c2551244030402049021601c5500440c402d0720200d649a0665940d400f0601c0c20003820079180340c054004001c00038031002c20b04e103166082200c840480da40d400c00f028a03541001c0041e100003185800110b20003156141081c0550003a0504445821003945050f00290f03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 597442158 1250 597440908 597440927
    0x9020f09091305160f05010c0f1b17071401050c060402100e0402070b040209100e160e040c030b01080c090a1202011e11010c030e0a030311040902040b091201020901 72
    0x14424034030540000c0c0d031409004078074070103a90300104031410b44104100d12680f000c140d0052103080317241d416000500f58407541e00584a103811004061039403169894041500b2170000c038074a155011820005180c0c81c9001d54624443c9500000e46801803c0006100d00c00911000f128104002440190071003c0085400b9410560413034030990b85040c091400c1e1500310110305d01542c49031012840400340040e07854420b220764400c5698200b1646ca5103032100d618451030092000c0c200c0680002019020011545000c568540c00e12000c601c1c2c1410001d000d5a07074200240e0002074455904884a58202001c1c98104095a29207400c0c40c462101240103903031244184654040c0c002400010340e4010245885207034128611b815910302c0c9501e0141c100385480204103d950311300070301c848869100740724412400360314801500000005490842c0a0b0407034450000101000b040700095829030f0b440204010040300300e910740c95a484000704000c000594800720f180c0e900400c03080c8043d80c0d104c00a40d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 597443408 1250 597442158 597442177
    0x60a030210180b0408060103050c041b0f0c0602030702010f0c0912020112021218060a0203040b28320403050702090a020903010c03050603100606080109201306020709020f 75
    0x402603203002c0211a500320802c0d030040c014000d002801240121012a025042e0f030300610817107212806a40601045400c441c01c2c0e00030074103001e010340c0c80461044100c2c0c0240c80a91a109039013280c035031110000c0341c0c82515220051703903541460126464041c02015178827002c1d81844207103d803034801c00c210000390492000f410010441e56480200d18a907043c1d0312015045500880d00345041e202c00e500d2101030750f242911511540c400a5100c1d5001c3c003c40c2d1060f94450b03a41d404517111510307040d401400031000c1840f000e10503002c400200ca030b54402c0040390600c03543d4040f035030b450000481160124111035040342c1c8108404020109800100b11108e0719030507555905159640c0b01c0c3d9000034003640040d1507241d428091181c0b0b20796450f401c40c034004c80003141581d400401902e0904210b0340d0500c85c200104e40c01100401c40511141e201428118441b1600183c5d84441c008080c500d602960411140961101040c4003140e03042050303c02400c03026802710b01c0c08512042070400c50003441c220 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 597444658 1250 597443408 597443417
    0x105070c120f02010e01110a1d101d0d0b01060f090e0f0603190804060311030415050603031b0706080907060203070204021819080c0312030f062412060a030210 70
    0xb00340340901c00d50240340e03000340b5400200665104901031207103990003500e000740012115010500c4810f900251410071100003800a1442c030b80b8001c1c2598010b070000c1304010002c0c910360f141095a1202d03a41e01000c00c2c8240502c0320b942d0b06010000d094041080104410416620020300002180d01c0340030b900b00f0381403004c5400036030320800080c0c9440103180301d41c00050b407144014010031207101c0c00781054071072588041c002d0790f00880300f0000e503020031a0701400001103c0c0c0100010442c41e803006401c0980a03003601e00d0041854002c000d0500a000042d1555001003c00c000d5a503200300907035000075058000d4108180b40c010700944d40e000d41d21010780320b00d81c000b4204010040c501d0440c000580702508040104160182040e5985444c1c40341d20310f54003c0f5040b6800600d0003090b142044900c2d40c02a508584600c240400b15990041001c1e0304400340420400c41c5c0c5092802280340c104011002d6a5a0021038180e000d080308050049809040c03101c0007840182c0c0e44981214000446181 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 597445908 1250 597444658 597444677
    0x903030904150302030a0503090109090207030e090606040f1d06030331031203020705010b060a120e0316080c010c0c08030402040f110c010905070806010e0c0a11150402030105070c12 80
    0x11000c8030400150f100035490f03c180e0701640104000840501641042604c030000c00b555500c11a00a070700c07a40b5002070001d611100f0790781c0306140c0f4120701ca03003014000d000b050905881d94030308507103068250014010080a071214004080000b0203540e4000810b50145042200d0080c05081118900501398030300745c800c0048900c0c4800841c5180000c54011010050300100b010028000f9442603100713481e0395003040c00000c003608001d4200ca400d219140c0e141b40694101420440003455520748414084c042040307001c0003e81c10004001d9036a00411610f60744003008072802d82180c2d2520719030350602581d002903102181d1007030250703a8070980595002c0756602c100302805008040440001071400800701c1c8030031a404056020850061250302281c1056413500c0740a82c5d5240240314a02d00044840c000880518900b030103068445087d003025441e01d60403002e0a400c0c0580c0700c1c4015039541d071002c03c0105518003405501c1e0400b1540c104280d070082a5142c01c0300c005103d810f02c0061149403030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 597447158 1250 597445908 597445931
    0x6040f0b0c0c0d0605040203060a1b032406030b1305040c30151118190305070308030a0c0833031c02061f050f0a0b0313060c050903030904 61
    0x24214000200f80b41c003110350741d15200b0000d0805440580c020b21400c030015070b5007940ca104500804c004040b040e0366044503658101c000d0040c1c0d102d00381c484640703007041c4200001800914009080c080d14042500728030813044c03095540d441d880054040c1e04010902c0041401d040201c800e54801c1381c40d02400e407090080c0c4154646016040c070300c010003104010000d101c40200c0b2589074607005881804121040f41c1041c115000d8204441c410342100c5030007071440d00d0200c81c00484503d0580540b090240d9030384401c8d0070300303502e940281c0341048000100800032020703115011804649040c83c100c2402d100251140b6400c0b400400c810700030302207024590090018040000007040142220f054000408031030100c241d0b40c904050152041c10086150004010301e0884d00c006107010081141e4581002c1008115031720491a4000856074404505010300d100114420001041d00c084d541c0290329202084444400701c42040010034000402103540104c2141c84845c0c04603000b14007040c008 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 597448408 1250 597447158 597447163
    0x1030605070c050f0c150711091008030f090a0605030412120b0409050a020a0e1b030a021306030b032109130b030f1c0804170313060c020a060b06040f0b0c 68
    0x440c00a0054440c5949008041d5000190b11780e08500c03d65108a00064205d290103603030040302e600070541070200b04a42414141107444075405000c54600008540c4d4800160342541c0c00421800100c42c0c2c0042e0701d40a500340024541c0007003140c1d00e041032070740c5444d448419441c0540305880c801c0181c0f10809170b6206006130003034051910000c00400040c802803074003d81d00c200020f8128051501000005041003c90302c1551084509048042c0c4420500783c2d03000142e0702c01440d0a9619900340700805072aa08801040b0280c089910300003905080c0740205031902a03246d80000c92201203540c040700195141c41515211401900d05181003000b541c031141c040c0c8052070b1002d070140314210074038401e0000051038080c085081c05460307505181001045982d28002c580161045455011020424405000550740080d0a00003d1940c00d140d603618001e4034200b980120069020802c0c00051041621540c842c000045504502c0d0a10740200c02c0100c0d802485810f080e0000420fa01040322404d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 597449658 1250 597448408 597448427
    0xb090f1f150504110403020f1002150c043605010b09010c1a0a02120a0b060f0901030b090703021b0105010503150712050a0603030914031015030203060c0a0201050c040605030103060507 81
    0x41c4140011100f0070541c89017034003c0c0c401684140b040400281840c2020342d020b002c00005540a045540440f05001240c40406042c4221206081000080111110307180000402c8480313440120303449511030304240c50300e40e0300e40100014981001045040b90f2038007203c0d030607102800c0125580c0c031581410001d030031181d541000c00345641030400007403200c140d000300000c3c2c03130440b800c0390035440340501082281c2031843c449410943c10000d84810071007c0007e400c07102c40514001c00c50400d030b000460030b0020143d41c0d0f800401e8020414800400740541c4031245001c1c0803000700019807400d0002603903485100c0058400030f190001250b0340c4c5103c1e00382011100e5044205000a0901e0b07020070b001491548015030000700400e00c003040c18400381480c10b940c0e1754000c2c0200f00c5502c005110300c0040080a4515243c403e004e040080140c07400c3c07010b984030740484083c994480e52002e0010742034075001000c0b00b00d0745200f00f006000154001007a43e0560f0b801440004840d40c490b4070944081a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 597450908 1250 597449658 597449669
    0xb06010c0507090603141b010c020a03021315060e06030609180303010f05180112060f0b040e0102040305070e04050303010905190207210318110d0606030b090f1f15 72
    0x4200003c1842a0241c0148040b244100b00b034089070440d91030000e440f00103c81820101c044807541040c02c641c404e003c0c040c0594001003000c103a9503681d03070001e108000101c03020742810f44c0f983c41c3d0381812000e2084d0b910040c0306508090b2901c01b00c4a00282140c4002001584540c00d40d001141481c066000036210b81c50a00c41245c0e900c1d40c40b0b44401e03c00c0402c0d0710400d0701ca00075101150b00c01451880a040c102c40038840002080d00701590381d400584107070707000c241c0c2050b03490f90b00700d104d95164080c000c4401480d00006030307154118100a418001d070307500f000d69030070140d44c10f1100164001007101e044a09042000805490305a0380c0001c440d8403c01e00da11a44c00400c2c0f05080c07103140d0204c0c1080010600a0071140010b500e4142c044e608a00f40b00d00d01a522100954045900206840480704001302482044041585c5840496200c0d070002c1e1000c100c0c040030403080700780410202c00c0340956100103107986001c4400c1841d0728004008070380400b54444d0302070450407403452218401342c803 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 597452158 1250 597450908 597450913
    0x240a0b2a0604051609020f0703110f07061d09061008040317010905070f03090503040504020c10020d090b130f060c2d02280b07050c0f010221130b06010c05 68
    0x381410055907800042d4909820008881310004e044e12840c030131149903501c241c0b40d550500c0c00d640c0b8240d074503141203680e0074031038064040c840003201c03030038401040038010341c0e00c517505031003040a0302c1c2e400f044e1048005400394561506200c11982c40c0240820042d895180c0391400d80c2da075280840d03042902c3c00210613080d40041c00460456800d402a40c0f00d031807140c0d40d600300b000440c0703002c0b0186c0d07a0850780030f403241d00104414049410150028200c03194080100e902d00c00a62601078120b900c02081020030750f540381802ca040154100c2c0b015000b40600d400b224460491344c8680d12440300c001c000402403a601c2005000c0a4001d83c001416525000140c2c11094420411180c01c1c105000703620005001e005490314244d0740d4140c0303072503d99840c3c1461180340c440350f03910b100722124058000b20611200f4008801c5103801000280310443c980c4001680310f0f03281040e20220020010542e04c030101ca00020483d07210f500d54543d01c1840d030400e10030260b036110000182d40d0341c0700c04c7c8406030250 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 597453408 1250 597452158 597452161
    0x1060306020a0318030e2403010f05030111030411210a0c03030216060206040b10031b1e15210c03050415290303040e240a0b2a06 57
    0x10081d8003605901e440350714103004a81c3d0f80740e00c0d0780c80ca0400843c014007203501542d0001903420400c907042806050441c17015400940c030001148150002d81c01000504140c01d0203110508007030248455021440c0c94403411420980c0c6c03101c040c01c0040400c20300510355a5184c0a40809d00041500c1910740c0038141d401039a02410010101c1a10380000e402604c2584625114040700b400401c0840c1c84603070180031607486690f030b9105103100c0034040e018140751094010010404600d2a0080300030b80e80f450855840c6080b121038040529203a00c42102154400b0401c442846010550100021450500740413032008807452900e4183e000000e8819180917031440b0ac0e560598001e43c040ca008100f42c0c00da050044034108152210050107844115004100d50700303854844c0d01842c0c010b1300050640e810181c076101c1c20030350789a0807108c0c04000d074000d100403080c130b600101d061031441c0800d030f4483c0201400d0140d0003c0b284503d201c0034548080510162102d1460b84d0300e0007c0e070510031025100503 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 597454658 1250 597453408 597453413
    0xe010219032f0c1e190c050306010602030301080c0a0609210803090a020a140a05010f0909231003020603150402070c0f15030509150711010f05090d03020732010603 72
    0x307400500c20f0515a1080c0c214452a094180302c030400d00103007400003170a03c03000703014034031030b82c0fa004040465844603882c1d00441c0559040c050107010741901d0f40290386a6250814252424406140e1076000340704440044c01459400980c4c0005d503100c051600302003641080c0321400b494504d0300003500c0c109000c0700b03001da01000802c8030740005008031060380045456a4503040c514181c5c41c1c11980c0104440782c01c01682d4000c1a441c41d0f07503081401e1031f10340c2e04e5480030f01000307032000c814140b50300d00d020b175801e030f181d4181245104e03401521000a0400c02419680450030502c005000c43c1601903130007450b10410b81ea5901200d07482d950044d44505640c0d40c41c00c002c0d00050312806040c61308150342c162420098820300c2083d125200940050a20024004401c0016040a8240c0080000703c1d0010f81d00340351b0900070051083c0240c02c000603189068254a81040d00b241c540d0b204041c010091040440d6600c002c420300e0351207081030828244054035500b5004102145659419420308100106 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 597455908 1250 597454658 597454751
    0x110a06020d0f051509040c03053003090703032708060a050708040506040201050a0c1218121a06061207020c09010b070312050612070e01090e01021903 66
    0x800041c021062180384041600142518001c59030b00e0421540701c244101c50703180440300c00b5080350181038105002500d82d101c490030151020030081c4815000341440c910b00030b079010f82511240703810207100d00710709200311300c00c1d02c1c0c10591001804026921508648810301613a149100385403a0005200c07469403603610945524003295042806458980000c0b011b44c042c06a440c400c3d64801c014060790b50320740e0300642e1103807c00c0e880c0208001d80c3ea000c1600080c00c0344603003180a8415101c0f04200054918900384940c4140c101c20105c4180c81c102b500000c06440d80d0f5110b46c0b0310b03a10003400079554400402c02d0f501a00c0321a01859070040c0a200340c1c250082031038440d100d805d03a10208560703256900c2402501c145103000340040c04805603040c0101c110b62103a5040341c8006c0851900b039980c41d07121441d008290b04611190304038000104440c002600c18400707000c149000035402c010385560380c078410201a81500b000c3c036840301d5060740304030100e075215102070056804e076602c0f000fa290202030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 597457158 1250 597455908 597455917
    0x201110f0f0106080c01050a0807030b0a08031b030c0c0906060906030f0a0e0a020603131a01080c031c0c030807090801021201031214040b1810052808010e07110a0602 73
    0x10301d9035280050100d510080070503441d05083c1c040c2c482c6480c10500004c1281e001000816080c201556010034004035540d2040100041000b540250744a59060340c03000702501706401d0600c2650310800110003402e8000c104070408490403281400c0307030360782c000105000d8440c0d02041640301d81c000007001b40c1000c80001c0c007809a04410030401c4580003d421090365105c101034080d5100c1c90500001e26501c10b01940c1c1a1150311480c8044502110000665121102070304090f2468010b4241c034415420200003900140e5109070944203c4800d02308003528248003514003130701f04800030000610b018047e01c1580000c180c020700840d9690a550182c4411307207800e000c2280c0c1c42c0f040031a40415140300c1c0a10b588003000607078102d454146880b4102d0034075480302d00c50710320b201c5800f0700280c01070f81d4202e81501d058203181c4980c0e5884200c81e04130050002500d10720801d402e41500d4000d0020f80c80703410301d415910b44050400071510348140c19940358002c400c60986520591440c8420061140c0160 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 597458408 1250 597457158 597457183
    0x10303090e060d08030a18030305060f012303040f0b040b040215180609030c041112130f11040603050109140f0706120b0621101401020d0c0201110f 65
    0x80303a400d4a03540c0e400360000090301e855920100301101000030030364081c000c50b040401d041c03000440383c3c0c62510032406c4400074101540407035070319410020981411410700030074400c2468511074105150407088101140f040b482d03d00c2650201c006810014041814258282c000103414601c2c5080c3c40e10360a003490455089002c0c1d440c5003078000c1c0742c078030741010b0781c80c2c0c45c0312440a0309000c1d901c0e20038042c4941041403900d81c144942401c083c40c94450707106209500850035486a42c1d810091290010808042c0c15050305041041007640803490143e0803000040d0710031021340100d6080750014018040540008e4203035480d002d030900800403139040107500300307820710191264900004150750711072440d0b100790404900c4440b410401c9141c0c0c0d9100302e81c1c11100904050500c0c01e6030074001008240038500030054031505082c04100da400c001c06030001c04c01d00480303c40b94030307918000039110840e181c0070307509200d0030422520031a17000700c2d000b511201e00803049944543c0040052952012180c009 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 597459658 1250 597458408 597458417
    0x1115130504050405061303020705060c03090a053109080c0102091f0c0b0c0408030a110f03090604031e2108090d0905011215170d080630010212010303 66
    0x103400c1c140341c082d940c407482d00280503080940e90084220b0101d00341e800120304500901d50081150f40e074020241c06440b445e10000d40e203520707034803050045240058000c64414610683e000d0490b80d0440b0300c040751890300c52245c04080c8850600031010b007152600c0242003002c081040c4d607000b10150302a0038100780c122244250464940c03555400d4008004601c8005403e60340442c0100c0c0c025000283c220141d401118682543c80c00c0080c1190040042d100015010304003129512508102c43c0c40d4105e640400745182941c1600080d44034422444001c04109801e0b02a0003105004403c1ca031201e078000c08542600301d01003242d04003061695909038081245040400c0c0c3e0ba0342e0024180100d50b4541e150300c12510300700001990030059034100c0e14522525804a84a481e134007441110080c01203002c1001c031300c090995602e0501a900d4001000c029910342040500d6a54003921044121661885841c41a2074941515905202c8554a42942c00096001c145203000c00d103440c12203000b5a00c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 597460908 1250 597459658 597459697
    0xd0305090610050a0603022203060b0a08032107030b09040b10080c18270304060908011506030e0f0703150501060212070209151c060e07050a0b071115 66
    0x70b06560300846420081c448014800c581c0290300a0181045081d08448107510480f4a443c940c1c5a0f80c1007125010303290100d82c50f0a0078028140c9000c2c15074400a142480074100b001c01d940340240841d50200082c40c00826420360190740f00304004203018000c2020781c50b140c24211503214003a030390081c0032403c40e00d000802d00c40c0460180c246020081c02150500001c04040c0c0d10a80f0203440702c61020b101030710201084000030800032003130400704040c50315645800c00103090311056074403c4145034109148001c1c480d01007400c000540e43c0a0030005240000424031515200c0c5601407091284a20311010083c8580b8545407804441d400f0810300c203e031780700d0008030b03202c1c6442c0b5241c03000c005041c401d410040c0340c1585080e620904450b049a4000c3e544400561200003240d5501554030f00f801c034000500240380034131104c00143c04010001185031001040401c8000c1c491800484004155102001080004100342510051000c1000810103d020a25038401004020568503100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 597462158 1250 597460908 597460921
    0x1051005191815080d0219030e0d050f07080c120a0b010b0903031201060c02030d0311070f0c0f300206090f040e0105090703020f0306250c050d03050906 67
    0x1014101d04003440442007180c524003100401d49400e00001c160040783c54026460701045502d240300000e06056000380540060290041e082c030482c5103c3c4007010b00380a10540111b904400f00a100070000d981c60a0f106034035003001c90a0084611400703910b401100c200145001c130000e001c44100070b08544075140c3e902d403800d800307035034541142c0000d145d035110380010018640c040c0050301e4080c41c02317010303645000c0072100c4424801d40240c00c1200842c544102c0c0e0019803d0400c00c84a9102c0c140c10204a00780b060b500c80c407114040d1540c01080c001c1d1244485042020256111000b010f0013203c900e030341034951141251600215508503240c55072640c0584810070301c6100f031164035401a011600d00310245003440252500301d55025002034554a028044403424898648200202005041d0050462040203c0b0706140606188243d1010050200d0b142000400c0308000c0407200d1b410060f040e10245c291442544818040c1a5028600d1114101e07509a00b260344644108401d6a41c1680c3d040c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 597463408 1250 597462158 597462169
    0x315130c0806150706060b04030b09010e0c10020106030210050301381b06010f05100908190c0e0403080f01080307030c11040f0203040c1d0c0a0c1a0901051005 70
    0x9504210000300070300041186803c1c03d0052032400342d00d40400c0d42c43c0c0b4031161a03400c2a0380c01540100c0446070b0019082040c0081c1c252420f0304104098001e208512580104564031400700c62000c1c45a0b1051503210140c030f0003503109100450703014005100324200610060003c1d00f00b4882d0801190224405010361280046481041060002c42103808066408400c0441d00411052001c59181d100c11003421070042002600034216042120303441800d010130311109101c0310300110180022268180801c240101c2c1300d4103184841c0041540c400741c0342c20b0004160030983c1c001c111800e000002c1c0002d06a1019040d8411070b00e505e0000c1c01031740d030384411070380d07034400d48034007500041e540647d2a0001c9c65064402e2020580188003294044945120b03070200c0c0d0040d03d04880d61199100204600e1032452503282c0c0d08925000107103068038000c01c0000917845486c2d98002044a0b0f03400700380c00c10402c46030364800d054541e04040114500500e1903802810b055514140904254800094503c2e06 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 597464658 1250 597463408 597463421
    0x140906070f021914100b10030903050318010605100324050102060f04050106180b03070609030305120601050712050306040e0607020d03020f091f030b010914101103031513 75
    0x7035802411402070314100c1805001200b40100d135400b420350030224040381c04101408070701240c11000150b10013504200201c0b51440c83c5440241414a11400007094001e002d5a41c0400d0b0315041070030410007640b405006040c243c0056620140c0d50030015903242e03065100001c0d4940407002910200d2440401c0080c803d0f0502c14180180d10020000364250381c0c82d406150071a1152001060b0350b07403154880210054001403070a5696980c1c1c1c1c042180e440c0411200b001030001e410560381003810b54a005240d403040010800600140c400420354991082040300e030600d400c59182c42840045100092456006403a118482c0e8204080c1c41d100345004a4a1805003586400400101c040280300f500a5046042100c1d200c030028845441c16403503030b40c10040045480b01c581145a030303030220003808407100003d03035a040002100c4c00744240d820382030007000861011a80443c1c10502e10703174101c03410800c00035000454000442809040c40014031280c0828008441d51032012160044040480d0003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 597465908 1250 597464658 597464687
    0x1103150301061802072112060e25020c1003020702030f0c061603090305030c0106061205090d03110d060b03011403120304060b18071e051206130e0114090607 69
    0x340406a403d60040c0742e0003054141c0c0300d244206010b042c40c04005074071204401640c4049010041c1900c6020014451000500448003c1c08002c0c1070400080c0c0300c6070b100d0660151501c054409000080303008129840303002100606000d420082c42800401075013111008a019208545000c0c40d4550003262407101038030f01410050500190b1070f07110324060100c5c4002c1d011b1050381b134400f1010174814401010022140000410013501d859001071144290720b220211aa03d40024803104890100d43c0404242c03d9140c0402d00c0c0b0917000303224180d40324801000c00103030b01e004400103003240050041d40c122004040000045580032040c9174941c640c404402c1c0d10040c2c10000640010066802000c13840006010b160b072003807240402045140c0141c0d0100041014100380751840304811801035400c37441481c1044c2448580e4206640800000c0d0a483c880d03020181000b00400f42640100401c080c1e0398000e001030600c124147d0100302040d105500c1a01940d0005904140100c8590703c0014 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 597467158 1250 597465908 597465929
    0x609051f080f0c0702090a090b07091a0a030f0e07061404030b0112050102070807150c0512070e04020904021b0d050c07031509020d060c02062a0715110315030106 71
    0x80c1d401d0442e01401c2001080010705010501801000d40ca8820050b4410800b481001403c0b042c2814126980c8100402c40410414807410901c03003160000d518030804002084c00c0341d1900b40c00c0034141d0241070b00c000031a010a240410f4640181d82c002600380072920117444d015048502240000035901c41c9010103490944c83c01d00401903448400580c841040c0214001800c01d82030390345403401075100310819a40440003411030303d00c590080c4500e021082442c100245040040e544000501d0310060104c400d0210b00c118013540d58840350100c3c1c0d1201c00c000d108650303a07400d914691000e5601c10029801da8801c41c1080c602d854091011a0013040d507000061018078903550b200c015403000341d048682c103942c440d0100f0340141c0f62444d00014051040d030b170101d003200425100030302d4060014220522508145c580260340c02110803491408220b80824554a000d5030400b281c071035601c03075544258580b4203c900b0b21034940e648083c502400c4860746d0400d03081c95440815003650018000c1060b10b1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 597468408 1250 597467158 597467161
    0x2003041a0a12020405100e03190311070503060f060409050c12150105060705032d07110907080606160c0f03080903120f04120f050f0607020d0804110d0f0b010609051f08 74
    0x1401401f4880300e080005084810140c4c1640c4e000900e000c0400d01140411340411003030b031141390180001409418181e008108a1803d003c150564030b20140000c2e00850340c601101013804018071402411800180c40c1800d01d140300504c05941e40005104018401940740001c07961b4502042164072140c0c00030001c40c140040c01d417113244003450100c0b005410600405206c080b10303152501509a080c051104d9400da20000d1003800400340700184080c0c104001ca0042041395580c2ca0b0a0f00c50748400e600d4040c443e01c10600d040500a07007103400540030302498050001c1000344000041c45050700503800c1d9042e102c2104041180744c01040090349035600301313000a01035651082c0301d0030082d501a41144410b01c00035210b580c20040729014540007a0402403c201c44690100701e03080801c442441e10f810b0030714060b25865001c41520094130720540c45541c2d4817040c05242c099204046402c80a89000b9596406000e082c0312007610030203020744020040a0310301c800044180b201c600458136000c495 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 597469658 1250 597468408 597468439
    0x60a0b030f060a0507052809090c0914010207080a06021e0a02210f12010524030a09060209130c0206070f021506060d110315040209012003041a0a12020405 68
    0x113494001c20450400806100207403082c18011018110f100c50a091041d52103900070004001d5101c0d81c000f0003409040a04904400b58001c107007504840021040305000d01c07074400101d0a116169111031124400d880240f070900c80c2a03030007042c64803221007040848618046441d480c030f01801d8440700240e00041e880c01d100a044486404c00d00c110719000d949804181b01c2c82044d2070b0050307284010050107140040c89241442d08107030051007440882d12107610307800454285644001040c20064907124113030001002240e8040e52a41c0318010001d40d400e0500081c1c48004080c110307600700051042002082030540100d6102002c0e454541c0940002c100c80e4a030b131501c0680103044290042e03410040340c0801d0865200301d911000801a015540e800c06074802170103000e440110905c9a03204103c040000c0c1e030030008410b030072000b41320488504c0354030b0805c103030079030045034409600f02141e0f0004404042e00038005229944040e03c60041d484d00c9045000d0803800f503070140a80004506010042 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 597470908 1250 597469658 597469661
    0x50a1d101802120d0807031b0c0206042409051504060f09180213050316031b0306020703091503090b18250305120c0303010b2a060a0b030f060a 63
    0x40106050300740318494a400c1d80070840c44040c080d4041410307045400e507254150b601c5407265421001c0751505000940c0d81202800c2c40c14001c3c125502400301d070030408070441d00c40c5400e0781c005000b0300760800c0404201101d16040c42512a5401001801e0450042035500d4070949014400c0050344050341020306020301501c44e490b004003c2c4040c80303840c2c140050003800c0d40c1264400d40101120150b103d80c80c40c000300011404541060703101e80c1019203080c01c001031005240342243e40080800b10f1041186401194038402e83d0070103006140005080814075401c00004030844072072810b40600c01070020030840c12505d444000401c0032079880c021981c40591a034101c1541400d00081e550b0744003e04d441042d121020341c0695030b689270084000c00500ca8240a1544082c07034a41e4850310b082800c100f4180c4074801400b4444080c1404078030303101403c827034074051840d40080100b45444032100e00b08440d42da01046808040e0182803d5900c051402c0100b2900019502c5500074461313038881103034410 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 597472158 1250 597470908 597470921
    0x70801030f1511090102011107020904030f0c0501020c0706080f0f0c030a0b0a121205120112060209060a180f0b070b04030c0c0b0d050f01061d01090f09050a1d10 71
    0x461030b681401c00304003410610700c996000c1000c0a103800f03075664020800a800d5481e485006481e0000c14402040580c4034040003070341c0b299051901c0b052081644500390341c507080041003d0003640c40880c0704044020001022800d684198464008581d00ca01d51030103034810480e49422010004800701d40790110503800303141c000c1105017000c5142d42c3c1c0034001c2071704990a584000600c51000c6001d00038440c502d03500200d0300902e0301d0114504600c4d031400e101561070610030300002100041c0300e5403d100d507903030540e504000d0043c03405648102d01403000b05802e490000c8018000040c800018413030400202110868840502040c108082c64a4060800c14020b00030390074070024491040010307411070b40301809481400e070141d4039251085010400c03510000c00361024141000010b101c100e40214080c0e03101c0001038104120b460108004840e00411940720031401c4400840201d44075040342c208a20501c10306404204451602e2081d102c0c0c2c02018a1b10079a50304188011491520075070010b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 597473408 1250 597472158 597472163
    0xc1c1b11130906060e0f01120302070905040303050603010c02240a020d060602060f15211f1d0d1b1113050915190c110d02010c17070801030f 62
    0x110011101001007407208441288a9015a50301d4007a40d040080c0f41c81904060407044095441d01d00d00030f0800f1100f008180241c000d01b030114115141014400c1008101614244206001030b04191078060042d02c0152000340c03280d400c0440b0740c91303180d20014510f050f00311360841d00e0705000381c0d07803482020905001d0202600c40b03800f004020021445070146800a000c40d5005103001e00c1c10030103480761714001401e245a001907041205203181c0d101c0d050050031040702a00c001b000503407100d01c03919050550050b9440c9070303500400c0c5200800e90b0390001d603412910340d103a0594891500303450b07074a4079001d00110340401c903844400081c41d9400340c03140300761038841d1201419140c200c50000783c0d0301c4006c2d1941a50642c0300c00030001368900c03d20415800e030205040300c0805080c0ba0000c00e03c40c030344074030802034040e42d1398401700c0c961807088002010548410055800e100e080f00002406020708491803c045600501000b11003622180071911840c3c241d500d01445908680d41c59981000c0d600c8213 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 597474658 1250 597473408 597473423
    0x71413050312030405070b03090309060c030c070e090f03041a0306011b050c040b0f0102100b0307030b0c0a091707050d0609020618120a0f0602030a1b03020c1c1b 71
    0x108040d10308020000c40020904861900c915240ca4010300e003d216401c8121a55410b00c144941c04d2740010650305a40340840e6070586600140308140e265000c0d03a4019040348c03242c050b00094042118a040307006030071034815117079107182c016030460341c9120703600c6040d079000703044070262446030a1030700507540000d01403600604c0303004920301040d040b10b643c150644d40c50700301c45202e12041c60507100d40d0f0818482650100c11f00c02403840003079212803030100e0001040e80c0341e0000c440c5903075040c00303a0070140d030780301c061000c290600d440090f0303464116401d83c001060300c0010105d1031001c1082c0680c8000c0300c0301c4c0240700075401c1809010741c04a402c00112100e40e103803411180140e03500809400c440c58809a0030900851190400c0704200300040126141e8000000c0b0b00c001ca2202c4100c14503140d0444c00161360f0303403101d40c126002011549480018900fa00300d90390300c0282e041d001004440020b808842c582200200ca5880070301c0301c002c4100c0400d1a410349428905661201460564080e00e10b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 597475908 1250 597474658 597474697
    0x2409051b0319061a04061202191d0402101b080d150603092d030e031005010305060a0b01080f040f03110115080f0a020d2d030c050607080714 62
    0x410b81d41958040c4411101151034000c00101c0030f10010b442d440005080b1018041c00c0e1034600440d6229007501c001134000d14501680d4179032401c10038812801800c0440c00c81100c10500588444450400d44080344103290110350404024414000c103030320500e00e500a03610390642039480400d607030702c68944076040f0790301d9040208007204c64540c0340000b840103407004140c10a151030319500c082704031300c42c20122a001c4200f468120342d502121407915585030a140314024066800240703025941001700801c40c0c00c01001100300034000c05d41a0203201400024849818100c0c01581c205800710740300705091039202c00150219800d190702c2540c440c020b090400011408200e45829510102d8401091180350740c01086001010088600d450109001034010000107500044548142030b01c00f410b1590b540e030001090290407480d00803011010582c0c455807030070074540034262000d8000c0c141d0341400707404001203506019500750340c440c01007075892002c03002d00d10b04030154a404c01b40818800d0841003e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 597477158 1250 597475908 597475933
    0x321030f0204151e0f0c0f080a020a02090a09020d0201050706090b1512011a0f180103030314160e0108090c0a080304080f03071113020906072409051b03 67
    0x8024009409640f01c0a100d1091150018000b0070404c0d511280c41c81507105041e03078950b0320036903880442c02545003620071000281069a100a44604054610302d000182071a120307030001102c00500380b0923140004c01d44d50320017005040f60998580a50011482c983d030b0303801523215400070502544510000580c0d460661900782c00e80500300c507154550008000103040603d130182043c81a000c0c3c04000703101d1101030720b006411004203018001e006081802ca07410490303131400001995282c08580d02d01c0f1a43e52410020041c2c4111200382d5000f8506001166000e900302d0900710007000d00c1c2e2500d820f03034880d03013004440c0d03000d0051651342c41d0f008040420b40d00c2e070f803069402001000c07103a0083da215070a1880303580c1040b458400b0b800d01c41e4001c22901c00000c403058032403064034408880c03050750109201c0071180a0301c80d594409900240001d40c2004010041109020b0030000c0b0614450703c0d21150507580403244000c0000d4140e41c441e0803440c203491900041240c5507500074060381c69803074255 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 597478408 1250 597477158 597477161
    0x90604110a02010c0e030708070506030403140a0f031a0f010c050f0109110a0503060402030a1202011d100e0118020d0203030706020f0c010b010807080106030513120302040807050402040321030f 85
    0x6905040050751030f00104c065980d4040d001402c0d441084001d040c5c00b0781f8100b100c47e034442c4680726076802407001100003428503000d050409455018090240c3d900c40701d00ca002061552511082c1000c6032900801c88201081440d103407002e050040e0411180400000040d21170180e0400c040b903540c4a48411400a241c0c28011100c0c80303441410318000c4221600c00b00b090a17009070308039501a510031410032015a400003040103401e904880300000080c1c40303501c102e01620b01c074060101d619816810400d02c01e2000108410135901e6102d00300301a000d8205503500361a40d41031441c9101d8107950f8103a000d80703040740e41e5031045440103044a1510520344e07916400e980064880c0c040c00d0101054882c03140e0001e02410440c03400918041c009880c001402800c103400c1030140000b007655420006880c82c95441d11021402c0e0004501040d002030b00c440200a50b000380104501030151070400151414079000342c400340c03903200f54074080600d00300726500c1c448011a0045010182c40e480301c3c804007030b1503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 597479658 1250 597478408 597478417
    0x809070312090e0105040504050a030c0302030903071203111b010311160b100605040b030712090c091d0604080d020a02030f04090b100c030f080c0405042a0f09030209060411 76
    0x441d02c03145000340c036280407120840f0301603101030b0240342401c040000141c00030944c14800b9616040c46c44500c181410b04a2440c0a00b0074070607003500c505500401e40d000000c0c0c80145441c441c0c0d55024452111601d0320351200104000c0c40804001c0c101d406d1810b41c000d4008090382c400f048215800c04409055881243c40c1155043c0c0e42c80320101c040c01a522424030f1000081c0100c0d0410900e05441c2046000346031000600100c1008424105030000d4816608054003050b000510274042d1611410010000d20710080708990b4a41034100d00d20441501241642c841c0d604034604504018952040c04083c1d44042040c104501041100101e070f00250303030281024050141000480e546408140600c2d400100300500600c4000c840c0f0400003640700c42d56403111410f81ca000712003901c408400c7c00301400745801c140d41c03060400904c00307800c90100c000f41e203101b4289070003034003000100d500c240d914a8141c484107000444028040c40507043c040307100e90300101d0140000036003510049424855030070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 597480908 1250 597479658 597479693
    0xc0a0e061212040503070f0b04030b0c04050303032707320307080d020105072109020f04020d022502031005100b07120201061413050c0d0c0822030e0108090703 70
    0x1000c03030f040c03204e0b090400116010b0440300c284540c40a0500d07403a484103000d18403000304000c00c00fa0000b50f5045202d0196001440050222600c130701301507049100b00a00152041d5400c45980501402c05100040010851711071140010014070208a19403058140c14880749814201c5203440c1c407544c801704003940050007030a010b0008400c2d5280c1c000d0079210041d20400c2000443c05036200f10502000d900940081400e1b13001400051505c0403a46014451041980c0580f004c1082c14150107142c008003000310502c400c01c50f40c002e8100840c00e05100080c4065015270111158008003045c55001c2a000040c1d01841c00169070342e40d687d10503642c0115400c41300030f02c0001c43c94802030707024000c41005e000f01d40017002464104101151580110b080c1e1085510303210000b00e0280c03c06401191005610900d0601c04444032010103401118180d07141440c6146d0a0200c58061404800020065500d9510300c50761b00c2002c401120300c5580505009418000d00c280080011427031105d41d100c402 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 597482014 1106 597480908 597480943
    0x5130b0d11030112061b2a02060a09080118020f010f030f111201120209041118100513090f08070c17010501170c0a0e0612 54
    0x1588507a0044400000070010410030001941e8240250040d04140024400b020300014110302040854001441d490303000c840442020b82d20003010b01e00c5043c409440d11345500004c0309a8020103081003c14a50314040085800a014a44000c000c02c840000b800d1200d401181140a01c0e15041d8100424030500c030902c0c40c026400b01e0054501c1d0241000b03012001d83e06d0088941c0706001d00c80181c0c1800c000090a050340c0d1340c4d182020f0b58041d00440060300c0c5c079558461803459001d82207508c0070b43d8842511341c004070466094403c0300701d10300512000d072524050181840701442c6011515080882520106551031408144a54000302e159607580450601c50312030352254100a601c102005030b18036100f041504018160740f0458228039510b41c04603c02540c43c1e516503841c81d04208803071400c11280c0d50205966a01c2080036000304400304048140b02c2c105071b046810b898044 = true := by decide +kernel

theorem cover : BRFrame.Cov 597302158 597482014 := by
  have h0 := BRFrame.cov_init 597302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 597302158 ≤ n) (h2 : n < 597482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
