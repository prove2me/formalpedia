-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0421
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:43:37.318278+00:00
-- url     : https://prove2.me/submissions/d66ccbef-9feb-4a6a-ab98-75c9703bfd30

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 75539570 ≤ n < 75719426 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 75540820 1250 75539570 75539593
    0x21903060f0e0d0908071509050a06030209010e0604060e0108090f0304080604140c0303030703050606090d050307030807020c0102070909210f080907060c02040c0c0b10060806090903070b130203 85
    0xb0701030121035641030b0b00403d440e1890302030080b0f84081c00d641c100401481c09600300700d403170b005c070103001c0c1004001d00c0360345c1400050a40c0c036500840c019080d05d64016840d106084005803071040f031990350380c5c0329034410310050103103590220002c030f0010802d207000ca00342d8860b40259400c5c2400e65041144501001401003000c280004031140aa441335840c1112511100202502c8041500816a25400410100c0d404034800c1c2c02071508610000c0880f0b141100b07410000e124550455003c0341c00f43c1012900310103240d00888150350098540c0080c104000311000000c0d107542150060f07583c0c0780c2c0d070340b10446c0503c00d01c1c031540d01454001c02038010000e255004003804004074000441700041e0ba40b0000b81000c900410f00f20115203d58030340118107415079003000094111800382000300003c0f54884e10128100d1030115000d5001103e65101d2141080c40007440070300024079007405800f628080c0078010070000300720307001e03641c00451004c040d450300700c05010301c80316441010b076051040481e03ca8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 75542070 1250 75540820 75540851
    0x421090501020f03071e11031c1d0310091a04031817060106030b0612040b060a0905010e060d050708060c190e010c060c120501150201050106080906010302190306 71
    0x242a940260201e441402104000c0d075542d12a05800030000c040000f0400d889080b03040100380c0d02c92240b12250030101200300440d01e410581075419400014880e6640c10700b0381c2180c4075260311034400103080400500c040100e580d40080d20355041341d4540e1000507006200b0b580d50840d052101e850502503c074200703414001e00f4110540001c04030390030b81000000c0c4c001086030820b42400d00d070801600282e844c200c0282c1c01800039040340c80e0071207410816681c0c1c1890b0714415034400d91141481440070700700b90043c80084400e64000410051800300140030007029411440c1d8400b40c100c40c141c0c00489180b511504000311a40702d2009482284280305480c070b00500a425020007180340480241c11000b0211403c40c00180510702203050781409101064564110301c0e0310168a0800c01d42895050058104660007640146810818520307486420355088c014580100003502e4150224140840c41c55203804040c40024801c0784c0b2684542494107403004d4600007180c2111040042006002c40700 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 75543320 1250 75542070 75542087
    0x604091509050d08150108061302030907030c050609011d2d012a030c050f030f070b010602210310090c02030d0c0f020a110d080a0203070b0606090d030302030421 71
    0x719280c2c010a81e10f40f440c24401c8031041c1c400d40c40e031030221040f007440c1801954603640140c00c581d000485440016032813042c5000039801500110b0042c19030900d5810b01d182107202c5600940e2080c08204044901680d002c004400c1c42801e0144110078840d03c0d1001618504003ca040b91340310011201080301403501c0e0940e082c0c1a030302078840c01c000d101c0804190744140b416000c2404a0301800302603d002c64800c50044100c18402c500700e905100002d86d920303295030001c914240121030005001020401c00d400d0320350041940e80001d01030300c0140b205400032039804146051400201000090551580002143c02000d841030100f0209003102e1009490360f21900d02e5110550a06000c410400d02c180c1c0100e52041c015400780a081e401036689428024460400031340c02811080d01c1c00118880300010310a1000c3c6400031a52070100e4a46801c0310b140042c9024401c04040c080e004844c5c80f410640701c1c0843e4580750045e540c0d502d9180140a003550011607004441c0e0450b050101c69030040c508 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 75544570 1250 75543320 75543323
    0x5010c18080307020a0303050901020a0c1205070902040b0f0f090907050c150906070f0e150316030b0102030d2301080102090a09050603030d09050a0b0c1201050d02090f0604091509 79
    0x31000c69515200440d0340e07880360f444002c0d009441842e0420101c0e2003000602080603051041d287c00c41c0c9252296407400c015a04003141e080da15844041c1005410043d440003803941400030760519180945c200000c6c01a441c1049030301e0000030740142090200400c41d5440070005103c00d803d0700303028000074040e403c9514100114403c8280c0301c041c010028032418440e9440c44000e0007280d9640d001142d560303000d40a00402e00411800041d095a50000c00010b242e80c50f1030100d0726031030001e1a000d0540068980241414a072418182e0f26903404000c59010400100300030440a18900c2e03810461401c3c143c8850848580d00004688000e040d002440b88041c111080441da03070300c0b580650221801a00c040c0c0e41a070080080403000c1c5025017003885118003400a541e050700346522204100c00085540d8600d40300c001485500c0303903d00c4044a8050f00c025290781f500440d00f81d0100d011020040c0c2604207906e000400614191356540221440980c4594100c6050f44803414220103461620130 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 75545820 1250 75544570 75544607
    0x2010b010e03011401060302090604030c030b060414010807060c0c05040f1d12031803040b13050916080a0b12010f020c1009080f0a03020d05042001050f04060e0a0305010c 75
    0x3030481c1039180500410300700d00488410384516910307100b004d400130b51040008580145003407000102042c03100002100540c003442c0c1807031076840c0c01c034100800c44800c1440e0009031905d03280140001c0500080354410b407500741c10b0a400105a60406800190440c0d000790b50090500c40840e00004290f040002d461030018588c0960f181c4605441d5124007030f116512101c1c078801d000094061a1524522102e0000744065a250580b1203051900540c0410b000d54050446081d007003000e41022400c4660014042c0710020701c40c114100010040d001c003800c100f04180d11144a01c2840d0f0301c4000030f40300c1d558250020807200d4680c070303550fa01075001300003042c3c5540160050103035100d00c0741c00703040b050a62120165141032003d48a251413900b2100e036000801d07900f8820b8070104003561040c4d40c0903600034141006000042c0c46690f405c3c415103003110341044414000910b48190b40c40903a0182d070464288151440040c0700840c25400080c4d00143c0b1035803c040c0341031211900500155a80907a000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 75547070 1250 75545820 75545837
    0x1e08070b01260106140f040908070b011d0c0307030509011d1506030712080a02010603021e03010b03010b0105030a1e02071209090204060909091a25110a1101020f010c02010b01 77
    0xb440c1c220b44480c880c022280c50111500500c0c3e02c2d2a04404001d50390007000020403100350703203d05000350005c4400b02d942201c003000500c6820842c101101064800f0788041e1700768034000c1240c084c0340c00060b14510074103499101103070403070301c0c01c0d00611014441c0028805100b5961070285a03212540070206031070790400030105106080c0400c00009a42c01d00d04003145112030307503641000503480305000390b0441d560342030040016031340c100d03465094420114508210600a2041600f15801840c4040c82a1314104030541da9903004029203501c40da04140014102c50740c4012500c280c520403030b1082c001e6200090050401402450141442c60b4964070160400e842c0c000c107004074401c90148101013600d000d420058401240c00c41d5031058030038207a0910b406d45034001d503013030a00280c50a01c40b441c11021102c0c41c5203516916001201040d160a0030149405082e150300d0f0060032178094141c0e07480001204482c0d001b0042c051118a00b2002001020007624000b402840303200c124500040318913 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 75548320 1250 75547070 75547139
    0xb091f05010503030f03190207080d110a09051309050604050a0b09030a0c230312092116081306080609060a08030306041a060f13080303041e08070b01 66
    0x80c41414140e4001400442ca80400b04083d6003054100800041c0c0903080701503c5c0c5000881400035005d4548a004010f4407103111404100c00d071160180e0281c548031040c84015405030b4800d10401c1101d0091b40c80f02c071700000e0a100b407400340a11a602408502c00c03582800700700880012305120442c002c09401490382c50301c161843d00d91103102c00f0500010400800c0350003003002c1c044941411036a2030036207000004c410842c3d50039900040c0302030180f070b25075004001050744107100340c160500840030913215610301c502c0c96104601800080e5028492940b0440d000c0110400480c0c440300340085408006136910078000788064003c0342d510340108d080002103030311402e000380041d058917001c038091811580d030344041c00001e04d00c030712410030011120040e510403605c494000b80014514003c80940e00e100d07203c04480345a10540c4826543d9104104002c049004102c0c81034148280c0102c60020f00c0b5181484071a50241c1c020181000c2604000050a0340d40540c00c100d03141c1c0545200004100c01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 75549570 1250 75548320 75548383
    0x60108060403080a0e0c090f0f0a0b06041403011104080601030303060b0703080106180f08010c14070203030f0d060320040c0e01080105010e0102070806091e0118080702030102070b09 80
    0x5450040110f440d1001040f0840500c2e003102c44e5072140c441c22903050b006d05000045594105454480101a01d1070506c0389604907003403941c0c0d00c0000e4000900c070000289010415501c100d1082511804640c0030f007480c5030b5400e40140290413804048252161b886c1c61415440c3e01c4c0a2001310040fa142c28400650070b841c5c0c40031303140f005406455030401ca0f8a440c1c020b5608441c80704010328650005100803903280c85001a54001c1d10401c800058414000d1034003505001c4d00440d100c59510003801300c000142e42c000201c3d80803c0000c0106d9807500e902588042c0900405e400c010303c62117100c000031103055814218281602c204440074060544800b030283da03820468081f05001641c020300520055026000704642c2001c10310480380c03c0e41d030b20a850782c1020b0082d1108841608111094940491001403207900804000001c008200d80b10040c40440d04403200028140307035011070f42e0310a40d0307030a5040e030301007035046a4900c1c110b1a01c0002076840d001c880140047c00450911212241c100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 75550820 1250 75549570 75549583
    0xf0c080f07080105120a0209070306150e09180a080f070201090b120402060c1f0608070506040e15060c06161209030206060d06061208030601021002090d02040b0102010e160305060108 80
    0xc98480701060313400e040501080301c020b84801c4010b8400c0c6165500140c540710680d5108000b603940000e140c0e800c2c81900c683d9008903c003058200580f4110300c101554a0940280d049000b00320304603a174003c1e603803800d0b0510038120b40c090301d031000100d1705040c1c0d0070204c4014035100e4802d982e5192420380342c2c030041459000f540070b4101022a09000034005040c40001801c031424520304030340411003c462040c000d5042901422810b80e1182c00402c20740c002000902e01901e0300301d07280c42c1001c0c02c16071070800703101001b800c040300002e0900c1c0003c029201c4004403a14070342104255091454000c0509428940e01c1e5147c00000c0c0c6200c980c0ca4000000381b05422059901d0f038080e200d69280c070b1041001c00280104141d43c400d594207030003c0c2c83d520040301440920310a4011586a240031000a820450513182a05246004004404150b998004013100e015070440d0001001005080101e00400c104d40e00242c062085640480012802e102c80c0001c8070310840c21a0303d103031b032070780c424644485 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 75552070 1250 75550820 75550831
    0x90e07080903091002102318060403080c040b04172a060904060f15030f06030b0c07060615020a060f020403080405060c030702040c050306030d02010606121d010f0c080f 74
    0x10403d001900700c0e4941429400c0500c0d0081c07040355040c0d50014042e004542040002d1603a403032070a090a2000c0c0100070146070f214000e9480459070300340110020741c80d0ba6000300014100031f0000000b801c01c0354660f0550300500800b170040d503160b5413960b0214040e4415108207044d90710466844001c1e403803c02000c20705090075254001301895010341440110b07000b44101560041e01e401000c5030b124011003810000b001c81403518400d00b11080406011202d20080408400307040040c00e0012a250035110b60300715800c64a0385a540c210b90070190000c000b20303000f1503a14541c1e5820102c40550000e8060391450042c0010001180c806079500100d01c1640320080461304240f004020078a0a440542482e080003400d40b4505041680000d0454500d400510041003000c0f0a000c050f05041088002c1200b41d80020840c003030030120054030994201418084241c0ca5a85103458030702402581118440040c0082c8019550283d080014220528454000680b0340001601820a0014160044 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 75553320 1250 75552070 75552073
    0x80105040b030c3f0106061403090d0507110409120909060f05060f0d18060b0402070302060105040209010215010806040605070513120204090f030c0b0105010e011d0a0e0106090e070809 81
    0x2440368400c0944c5007102450441944200344040032000c112848403040010007910002451078181007000e05100c1d00c40c0800074203461b061040200d51240001d185058020504090342c40d05a07600d030000500900c1d5010701e41090078411a4410413414512480d0844026210701c0840c980b610140c408486107442041d08011005a040180741084c01c000c1c0051300f0300401d01c52402c68a40c124405072100c01c0030f4500d0194507180f849050080c644508104518110350075407400440d071318001e55552041c0035492140b0340c00501100980e0003002402002070320b49410b4041c86da0358148a98551008542c20786150b82044005000a44078104550003401845040d20081d801c15000040ba1420040120b03081070342c5100d0400456107000c40c80392814800c1d034550400043c207103030442903400c060303000d5070500c803400e500441d0980e0480c40285c140704103044401400c00f80c110014081c903441c2d5001d00000f801d54000420800c3d80301c0b1140e419500020500700c52501d840341c0446400d4001c031503030a5507 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 75554570 1250 75553320 75553339
    0x100b0a02150403050906120601030f0c020615040e011d06070804020a12290907060813080306040b040c02030d05011e0b03041119051804020913050715080105040b030c 73
    0x411001500d0742c2c0c00c42c2c007900d4140d0820000c1070109040d07502ca000602c2c0d44140d000308022156270b150042c0b0072000e40d006018080c103009144041d54406000e0030801c1c1e03e4502d840c0e130322081c2e00c40303030301c050b201c2c0001071300a0005900c614580b48032020b00c101c400c51240540d80001e81441d01583c02039001c3e60303000d464869000e00d808483e04618818000c03c0301d104180b41444112103900c54035104c21604208a0903a613410300c102070516102e680c0c0d001000b4013a00e04200400140300360320541d5001d4000105580c0c985e10400010300038030f045184564024a40700414000c641d0000c0a4000b040d0a0030042050b0b0740c85100644451020400381040d03000c03500d00c280001910703580a540c0103072141d00c4181d005441e103030004440d00d400c401500d41ca03400c0c0c030100708018030380382d0400045082695000006410580c022031484c3c4001030000c1e504000c00481e80b01040b00c02c210000c020040c0900c1c0c4450120001c1d4000c00f126402e02c20a48118145043c007045454080746402a0311320040481c3d40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 75555820 1250 75554570 75554593
    0x60106120e100b031006030b0a0e07030605130c0f050609060a0e09010305030a02070b03010e0105012001090305070c05100c0204050601030603080309010603060e06150d1502070506100b0a02 83
    0x280002103031000240300c0e46500701420720300d00801c48802015400310001c41c1d00101c45040c18501810b1101d1074000609180c02000820a42048140c00c1803c2110100d000301c18040110701c1e05115500040c051840c181c00c201c1c3c0200350035007030b0074403c1c4583e4011901c203a44071000c0852640a004150b8406001c00c6180344d18a0301034008c101d10401400c0a240f0040c0040000e105e9040981c0300b03a400e07800c00070344654a00d03818040b440180c44100030b894215410010210362401c014029a4140410f90b95609440c4c07400d40005102c010740704000b800030f0700007483c0c001c000c1e4001d4201242c840e0040e81c40801c00d454481d2001000589030759071245104219020130014050242605040c180d4680011010410b504002c41c814038805001086640c41c0d4904201100e280101140c500d4000106101c0340a20f000070205800034116000310300590b0300e0524071070711003604004c1a6020710000d08441008030115400744035412403400040b409648604164041c4030b802e4902006820140801e603 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 75557070 1250 75555820 75555827
    0x1b120503040504020a110102030411010f020a211403100302031e060601030522050606030715080403050307030f0609090302060604023f0403091a070f032d09030b0c040305060106 78
    0x2101d95081c07078121b4860b54603200c1c1508a070300646040e6031622040b001d090749560090380c0385503101910320040c281611552948408806021a41051a02401cac030b02c16140d8480c0318074440311041840416900e0901c429980031019042c40203e001e4080c0d19601c54011071034285c00e628190191014285903552000110018200142200041020621f020260820403251400c40522800c02441d50b03040480401d4903002007640010001c8a40c003420034000d80e07100390540d4109038581030481d16615640d006501400700c06c43c1010740d03070b40b50150001e8481000d070044031500e03000b0303000c0d6030b001e485d40000c0c0010381c03060502c0700380560204420000e001c000c25280c1899450340062040220600d18152031403124262400c5d80010450307882400f180107c0c405038041162240305081c03424101c0e0317070364a0400e01c00305009000e100c0d4501d4580341050040031000380c0c040d20b400758802c0e0200443c0014000c0c29103030009464130304800000411018410003100c050342c0c1c009004142582c60160202c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 75558320 1250 75557070 75557077
    0x1905070908031602041b0c080708040305160303030e0708030906070302070306060b0c0f010b0d020f0103140703020301091410030807030917010605010305150108040314040b071b12050304050402 85
    0x18100891503000081801d024000f0b00f20034503080c220715204409500422060307a1004e8148910b001c0920b0b00c2080d4a44c011124011a641c407030000794441c0d07080c3c109038100d0301955002030024000d401c0d601c45030072800b6101c1d0040d00c2c82901c081010022580c02d00d651400700d805080920f600800081e5031918010000d040d40750304c40d104039000319031261303289000e1326041d9200900803000855400c2000740240302c1010440c04030f5000700300d902ea1079000600020000031000e40107210183ca1020164426044900c0f0311012f200031413518100058020b0095000b4403524003181d1038000066001150484500d0180142150b50200f580c215180c0601c96442400c08400f400480c030383c0025010311203083d9006031a0cd02e40001001d910f00700000d002d582000f071000894000d4012259126a0000546508a40c06107810700841002410300d003564440c1c0e800c010b0031001c0208070b413003c01070040800580f8040010309042d1045da00e0b410090600000c2d000217011b6001840144031508156002c1c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 75559570 1250 75558320 75558331
    0x714091f03110607081804060611030702041e02031602070602120f03150a090207050c092a0c010905100e03070302030f0a02010906090305031005010509030705130905010509061605031905 82
    0x1403520328641d444201c990300004291131550046082d091b070519003449a80e0042109040c10360045072840d8080b034580c0f141d201d00a101d5692203107908142c2c400076070060104407116031300710341d641001c10201d481c41c48204d000e00010301c0b410501180c400d10100d500c1c644803450441c0b0a040c00c8640c289151190001091a4900c040d03451111806503240289000140616080140e643c416801d00905215207030140500a820070f0040c45443c010047c201c1e482483e00d00c82c0042a50140802c00c1410721401184403419070a1102c01c0c0700344140411060141c2c02c90b88410030040340840c0102d0340700d0196003000740c0960018884170f501039001c4030081c0320804240c40000342c4400b00d0b80d200300032108100f10540c0010710200420403080c4559559802415003424660700b0881604000790f6a180c072402240e0285035030b050070071310b0b00390300d1b420814156600200a110500e070609074a0342d1f800007264041541c85000e48088083c03030281003101e001e80156100303602c1aa210303c3d649406000040c00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 75560820 1250 75559570 75559579
    0x3090a06030b1c150e0d0516140709020d051303050901080a0e06010b0c06091b0d0221010207020a0905040c060f120c02010b0a0902120109050c04080714091f0311 71
    0x1141034140c0c0e001202d000c11140702c2d12414000701c042000d03050803174010110315601c6a1041130200361840d009002c1d180f00c0000c400501c00d04c0d0700c1a2038495202c001c00307048100709200e0300310082040800d98001d0004080c841404220503902c1d802d42c000401c14003003020740810410040705e449940720306009030b4003a5207001e0126100501218031464600700745e00101b80207030045860040e128081c4030300d036040078130500100140e01d039102010982001014507a4402d1101008480464903030101c4001c1c6100c00e0802440a6000c40c880d45002c1d50014600300c0c480c200002000c01c800b600c510030a4020368000000d041902c1c203010056030805204001c0c542407181445c103403c00c81e04207004407800041c1a0303002144152141c0305000c01c41c002a0041240b0034014019400007452841e07001e41100c015210110300340d1501b0300c0350549489540c10071040ca0203800c0303000c200c1d5081100c50659540c01900c0001c4165140e03a1ba4003210008058140441c1d04901c1003040401c8150340b0030a600c030001007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 75562070 1250 75560820 75560839
    0x1103060922030804030f0309051e07090207050304050109060914100e0616120c02150a14040b1206060c0607030b0103110a0c020a050301050919030c170d050903090a06030b 75
    0x160010703910000c8034110000380d04a0100420076a10050045084140342402c2c00311110300c4d640c0d075840f50065151854880c402c1307000c581c501d103400c100c032100034100b03410119918500c130304241c1e03142d502c503008030703404a0401400000c9040c070172070f0400212146a54500007800740b0748200f001842c42041d42c002004015103a179041a59068003c00024004110343c100721000351504181941014240002303104614000d4000360b03c03284058210b2410a20016956420320310081c1c90380b49110078402421a0049004590715501c80000c0030144021040d811155854a0400100e0300c14580080c1098100c0b0010581c818025006206000c20505020030703400140c0e945902944c20960391600010b90840b010340550502407000c8000d800c06500a0140703240400ca01503031148040094400c01d0f0714074201e10181032180071440740780f950064081803c07022103107002c0c400784c015586426005117000080b8003402c000004846044a0251050f20024070308402a00140090007105070441043d1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 75563320 1250 75562070 75562111
    0x40f0804030605070c17210603011b180503031305040f09080309070311030f1507111e0c0a03020306010902160f0b0711010203010e010b0d0f05090309040f11030609 72
    0x90150038404c44480d55119100034540c10f114102e4211022400980002000440c01c0f92000380c0e4038a295181c60440307403d8071340f120f030301090050001e401580d2001699071400000d80fa40305101d80d40400400b1400c8204039225400c02d80c90b440341c4410060400e400090410940c1096046042130b41850303400098850501d8691600581c0100c91401503904850414002c2083d080807048010344103500800503a00d01081455889800c6802c1c1c0740303a0010280083c0fa014401e04030056654029826100f8184410701101c40c0b8081c4401600054092585003081d60b04140c0216000c03650000e0042c6020703468485840000d600c01410f030b44500c0b0101c0c0003000864181d59246400c2485a10114903131303e0488002840d0304a01e44100d400c0fa4010801002107400c203051142c15034040c0c1d5203056840250100c120000e006811800241c1402d0004000240c103010002c4c2a003168160b806200c0c0301e110384102022204041c0384c0c00002e45003440407480d54100074082903030101c542007110301039112a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 75564570 1250 75563320 75563333
    0x4061d040f020903070b030c03040f2f0f030a050a08160512040807051203070308060f091510230304110d05030d18080d090204060f0803091017040f080403 68
    0x810020703407440c9400049608440c02c003081402c0040003140340d03850841c00d06404144039440042c00181966500102420a0010240d180c84c48040390341c0c0300481080c840801c400d80842c5200c3c0003841210802c481258504022601224090b0b00601900418403965120b5810390403050840c10404030350300080d03000640c100000703ca4910000b42c0c40381c54510b8a28224504480c5810140c0544280f080c445406040001500d06041e410305221b00240d6440e00802c2410707101341041903120410310b0500060710b50100c0d4441c54400141e40c020104007030b0000560307000c203407041d80010b0184001200c2002d0a103070f0016540017032040c0840719410080b01d0020b104440004000e17074070754200099031900c028482c815a010f440802c5814500a502ea0301d5492840c018143c1140170f03592030b8030b0160219038855101801501c42240740240890b01c954080361340b60003400e8100e000320910f0b40c0030264113008486800d06141c01d0414000e05641d10795405454003440d54040340c41030403c0c480440000c68 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 75565820 1250 75564570 75564581
    0xb070f0b10260601050301060303090905060f13050907050603160c0809060301031208130b040201050d110d020a03050c0c2d030a080a0c110d1805130b090702070b04061d04 75
    0x22040700352016001c2d40307103914140343d01079025601c680e00d003030401c000198002c25101c0480ba68014005401d645a5000c1400310081c9820b49900201844410044510950155014102171422110200d8a94085c45468402541c0480030b81d0103481421001c0b9200d010b0507070109101c0d00d11241051250008519682c02c01e800c03c80301e00340d0b210030503040310713a2000c1f0b080d0380f02010300400c00b00b03070002d5103401d6a0004041c00103030400c100010450b0180c8503d410903501500c6100300b599551505002081c02500481c40550001c1d0034000803c2c501152030054135040a05000600050001030004800c0700040c07008902070b2072188005021802c40510241c1030920460300c5116480c40c24100c00012142100110014040c418641ca908608009511010109142803403411340010190030290300050354040c0380d001c40d100c400410880015040015242d405a52003150b0783ca41c1281a40c4950840c000c4039028101440201310082c0b0510b007962111342c00303969480d0034605180201d001c0d2030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 75567070 1250 75565820 75565859
    0xb030d02010e060702030717030705070c03050f010c050c030f09031c0f0806061c1d010f15080f030708090109120308061e06030604150e01030c050405010b070f0b10 72
    0x350350300c50100e02c81d03405000090f4403441c035101840c5485042d40e205240d501520f00d115215200200004410a02074411601590741151482c091507950340350040d44c48000b180000641e5081114101e02280244150380300d8447e040081c50501060440800054121101c0b07540d02d44961a04849107000b04212031900603010703543e423200c8800d0420081c01c071090142c002402060200300b0007680c6030950412002c02850704d180070400726482150f114420030106a8400c46500c5c0003800c503070303502c0381c0d0b8490340d407100c0f901c40241541544d03000d13841e440ba0001c05000c001500308120b20400a14200018080c50b10141004400380f9100c25104400203050700040740800e0a0724184403142c03034900800e00c00c20030150030541e0f05c0f003030340c1020502900001d03000c2c41c061916003101d51000d04080742c003440074054174001c00540d980d4905241048130494894030740901e281100100b04194000200c1d40f00039041102d0080c2c0340c55603500d0b120900e9000b868880307604c0400402081401012090841a8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 75568320 1250 75567070 75567073
    0x324090b090102070b0f040b0402012d05042301020d0806010309140105060f04050601091208120f041707110603041502030c070507050f18091204030c03030e040903050412020102010b030d02 83
    0x14034031385c589144d0090002c1c14030075141c031250041000050300603c0aa034030550a191150b0007035445003a00c0500c40c3d00c0e9046038100c000c48181d11f1501a4060003401c1141e907003440000032011203940b0710011103a1942c03c20b00503080a400154901c1c020200caa8001c41c040c580003509140d151211548190b0313064000c042a510345040c00000c0c03510405074581508211030400450070b10100282c4240000c1c4166420b111481340820309210400701642ca040c0d01050b020381003403400c02002101400d00f01c138203c1c0d06605071094640303225512015100000ea21a2800e641c0011160400100740c100034822241d5610340d9409450703034081070000d18003440701c0022540c0c6071207441c42c10500f00f220310741006002c1d00d0300000501d01951040c1144810f052024a50711150b2030300324119090064501a13550140c500040002c1081004c0d0500c40449000e55540180100440200001e5510745507018001860600082c0010620a490340492900c1400000f802c141c1007800319061840700190352015 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 75569570 1250 75568320 75568327
    0x1e0e0d03080f0f160c0203100903080702070902070302030d1a0d03020601140909071e0801090507051305090a020103150f120209011512090f0b0f0703060f0324090b090102 75
    0xca402d0b007065504030040800e4407803a441d1606002040d01114010f00003001042c018080540d1814084a0301003001c000f401c0c05200300608002d00003c00c160390310001441040c03400605043c041c030130703108076030780c10746c045c51030800750740a8040604600d4402c07041f20074005800c0d01c3d0654030320303000690f034601c69000b8100f0396240c200702c180506da840710624000c010030006c01070307429000319485040e0b64a0b100d048503152202e02c1525041822034002c003446600e05091201440000a034407011143c04589001003044e20b0740095054410603564001154000c0c480d2000540c001c0d00000c60840003050070083c026a148201c21075038a4507404800e02c0d07840840440158140000b48501403c061460550003001821004018956148000350641c2e0744a5024042084110a0700382490304401d101b84a803c0102e000d90001000f0356503800442d19000e80041e40012084410044941001043e0b13075a0702d00d001e0801030f003030700c11002070b0075640c1d0b4175034240c00140250041401500c01c00e00041e103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 75570820 1250 75569570 75569581
    0x3021509041e110403170708091005071110080f06031c05040302130203010506070f0f0b040308070801090b030c01050c030c0703050718050420010909020f1314011e0e0d0308 76
    0x80790038041c5403c2c40b440e4200800d101148030280341c0114041e12413002a907500130b80c180200c55000c0c00c8012a88807034008112407580d0750240190881c00d01461500004d48090401c010742c2c00340b940351000109a08900049590b0510a40568040300180981d00200c1c003886a60001c3c005d40c0e2100c8001c030780003203818015401d01c02d91240315140d4445086285504110000c1c1880c010414000c1c0302c1500000b10a0400680313100e00c918441e4040450806400c0c039107000350041a0031124400003444410000403122000e004004040d10f000d00a23205030180c0000450707072503015900d000043d102c20003103122240310400200d002940110064281c003414012a265a918501001a0543c2c10242400003107203240c2c00f0001c00300c04400540b104004001c006941c80c200e0784d0b01010215201043d01344003a480d2400414841100054072000540c03100001400001440480c03400500b0301d07106084086d40d05541c10448103002c0c2000c00c10340c0b019100040c0340840400c021400101d44005010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 75572070 1250 75570820 75570881
    0x901170601090905150408070209100612060b0a03020c010212040804051302090a061d220b0d0503070f030c0b010618080f0d0815040f090b010806100302150904 70
    0x3400b4295100060100704444d444442c0c0d80c4185d281d012480c4000784001c034040120700411251443c0d4003400c8400c040c60000c1003440688102d02ca03550104d0000500c17500c034440c4900c601c9007900c00f014000c070300f01700050b00110300a4202c2650095690341c2001060f0050404c80e840922070340c45002800c0e6958101004e2048000407031404000315801840102c074181d44110080d0140d5001e0720301064415000d20701e4155900565812a8002c1c44944000440d415000c034103080c498082001840b000340100e09002008081010151850300f05000c11000a0f49210721b80310082d000340382c48241440e00e0f40707620341c00314020781c4400041120b10120807403032415003c01c04024103000010340a0310480316001d07611802c0020f000010088084005424032603803d125107880781c0c01030020048003124499480c001d04040f82c1c00d0b5a0b100e1003100025040800080c62403042942c09158007415207142c1c01d1002206140c61700d684a448180304050094407a4418441d02d03036014849000794040b15542e40 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 75573320 1250 75572070 75572083
    0xf030405011112130213020a080a0e031e1602120606040609060815040311030d020c0f010c09090221150a0b03130308090c120303070f081504090f02090117 68
    0x212071500c050003004030f92040355900ca0742c070000140c0e005100b0352152002502c210a80e60705203011034804915448000e0744919580d1003144031240c01c00c108800c641c5880c0e079070301880400d0080c540541b1030b1460401101c0c0c0c042c0c000c404000c0c5012902110701e60004a500704101100702071648180100721003031a007401008010f1101d01010440d680c101791080e62600d81035102c140c0043e01c0c0b40045001c1500c80c4408044008031101078948940c801808400039510080e0401c0b41071007000130854441d4410301c5050344007200d64440c0107605191005d00c002942104940c050099201d42039805030503030032500e46109901074220042d014002c00e0400c8540207554010400100b002d008000c05c0c07200b07540501c0500d5415040450b255aa001c0c115032520030899000384e007005118a407a07008500010185000b48240d80300e0031641003844004a9846004070b88105c0305641c1e10203820480c0c202a80201030007400f9502d81e02c030002e80d81d008641100000e80c440070f9141d03514105506080003e00c1517 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 75574570 1250 75573320 75573341
    0x6060304020d0303020a0c05010507020304050301061a090d030903050d03050613060b0a0e190b0705100c0912020402090409082502030a060e030c0106030305040608090d08010b0307090b0f03040501 86
    0x10241141000e8000c00e07107103280d24100900b030650000b041070819016001c4d07400d078503903c40000d000314585620025240e401c14400c29000703600340320340414800c29041181142c440d0b050596410894500100076182c1051201a01800120314010000c10000e0041c4009101c442e00d020400e810302c5000d000580310094030101075a0310b0148280410900e64003219031804c49032815444403c500d41c0010083c000145004603020035004c0d00040403440030000d481e005000300141d504c14410b0300c00800648200d01103020004028400611002c0411418481c07060300140005007001001e2020508580304074070160b401400210714186180000900710810740502c82090100402c00e0340443d03a6039105a030010b16240d1100319154100400b00140e42c042e8450300b00034055207981e030070040c0c010341c02401144d0008412100050740e004000409400480030383c2d4590500743e1804c006208150400341840d81040151100010031070400b1024190003c40c05170019038904051520601b1143315525 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 75575820 1250 75574570 75574579
    0x11a010c02010903060e07180c08060108090613140f0106080f070b0d1a19030201020d0516110a051003060905010603051308090f0a03030e1302030114040906020c0a0f0b06 75
    0xe40310040c1d82c031003c0b60003203950000010865440841c800383c10803009070044c540100540d0f1708800013005c141c00403111300241c1d031070703003842c58a90300e0044071b0340346003100e404005600200208007104401071110840038050b494000584804001060401c1812408104d15a440f03035014001c00406110303811011103014000c040c9249040c42c40703407907400385108103271146658400599007006081c00e5520640002090300c121840c2400079812450300324002a801403140c2200480e480e4000c0c000c550400846111887c580340302503941000d200384407001a82c00043c65940001e46071903032800e402c005822610007085031420700c00120102c030f20581c1310100b05030400c814003001944e40724000745440d4005200aa41d031004074040344615100c00000ca40007440300700000140742c7e020344c01018282c0c0032181c18403024104050741040c0d020a008003c0e64840d04482280d03149010703072040380581d11602000d0304240010b0348031b5091034000402070310203800880400007040700c60b440f1164025000c85 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 75577070 1250 75575820 75575837
    0xd02210f07030c0f030911091e0a090305030a090302160b04080f0c0105120403170a0c030c0c020105090d02150304050f070609080606010813020901080f0f070302030a0f02060d020408011a01 83
    0x2d0020421901e9401020915a45078250401d119010381c8400300514007070180c2238181040707600c2c1c0c070b182841050740c628810110000309001c400f450103240350b51501651040e0654861503603200c001c1900302e00440641c0704201070201d204481d11250b0004244403881e240d1a00c3c50103446e10700b02000e0700f040d010b89400c0820359401503038101090300c038400903a882401c445d0359603240c142c0700c1411000191160360500e00c2044080041504288403070f5080740d4042c020000b8008041e02c100d00701520080c0455020b1080300c41500780503560050046c0000d144074011441c0c074441402680c0252800d4030150030031050301c248440f08104403001041c0924000c46080c1c54107a495480303d01c013034405410441c9032030101c0c90a26606a41400194006091002c0365942c1e03d4029510041c0c06040c0b031890250301c1d41c46a900e64045914011070350040c0151588600390358410700f05070000c00c01282d1168050016840c6089148041c201415010000003211448040004118034808192030b04014007003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 75578320 1250 75577070 75577091
    0x3050f0904062d0b0d050712020f0711060a08010e0a091406070801080604080409050c040801020d06080d110c04050612100b01020c060304200f130902040f0b06030403050d02210f0703 80
    0x242c1154611844c200d000038080d242c0110840723000c0d19000030202d10b00d001040e1096804080c1e03000f040783c14071800003540084401740500c034003401800c42c0788000c104a5801007060981c40f0f84c00d0344e849080d40c540000c18600f6640c03034008032900c030704103100ca540c0700d0020808250340103502580034105040081803940751aa503000103601c6903005200c07100e41c442c000706502d00c8690782554064072404000b55281c2c81e0000b01c00d030041c103480c4649189807180c90a582580c50140850225007001c43e005044010a401c0a010240030080c00f41178000003c8418440d00c42d0052190034030740400c240d408121800e803200020315007401074041500c90102041071000140d00c0700501d0202103910360b240ca08030520000000d010401004a031a0000b00c3d649005030440c03856400702c0e688500c00c88042104a00c20a105c0d011244651410fa0304481c0070008034006c41d016101501e40d404d803005000d40390829081d001041202181e520802140c051014407000302d05900c40190f000e1107e150401107034400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 75579570 1250 75578320 75578339
    0x30603020d11010309081908070f02030703030b03071d0403021203070507030806010903051b090109020f070b1b04090e060601030b10050a051207020d020d05070308010303050f0904062d 81
    0x441e5401004070711200b02c00740c00c90740280c001140c50380d005a0fa40d0b841e03030100c11074103ca41d024900014000b5840300000b880e0540126500c105140e1607034011414500690303820341c02011035600165041c46203500000c0c0303038884145042140007000403500040d09051502a15080d81c84110043c080024410801e00d9a400340c19640d510f50586041690764464000588070451982c02c050514098014016941c0650340c078900c1441c0002d0350310b520705a9a448004080b802507903010403000340304104504c01704590b15045a006525410310905031101c2c01c42d41400da5000c1e0b80246415030702c400c02d1520042e414010594072840c03e0030103000b480c46481c002544103180e003100c1c1c01480070106441d182d40c3d201c0d0068070820700042c141d050f024101010b01950304ca4503410594010310030701c8043c0720b20038403a00981d2440c90341520740213456425079905907440c0e00942a826141c04092000d1031441c1e54501582000303015840410650161000c0c021030740b038000c00e03009031780b0303000850b0b0401c80500c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 75580820 1250 75579570 75579589
    0x50102190b06040209010537020f2116050604060501090912120b03100510080a030f23070f1707030804020f040905070f15030527010e030403080301030b0703060302 72
    0x100301d800594410794040169514010180340320b8602c00e488072a032081d202c42a0391080288407602140c07210031500d1230708903611000d2042c640196000305042c00c45034000c2101458212280c041c609007850061034501512100343d00043d40d05910801c02d000501040d441142d002d8000b01c0d000f80141ea00945510000004a24140040020f2040c00a1100700b4541c000409405c0003401c1d1041031104130420000307003000707030b132050b010100e00c090000e821900080d000840e40d6040c0c0700c01c0e188820202c41518004184105951004400711052421074041c1005103a043e00c941c20180a091850901f40c905211080d0f00900c01c4c5c07010130000000ca034010115a50065040320407044e4034241c01c0129010304040440107000307100d240380110345120f022680a056030052641180c4c21205114210180c030390643c4c801d4050104403400c100d1403400003103031083c030b441781e4800441e4628602e50643d144d54032079441954407010100051041145000e502e0390440c050380b034140040c0781990002180b426 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 75582070 1250 75580820 75580831
    0x30906071e0e0d0230010b0d20010e0a03080a03111606020f0f130905100f06300e15040302070b130503010504081809040507120c05040c09050102190b 66
    0x40240e202902156680c41016041e40c01c811704041020400c1c01c00d00d0080303500010f00c04032a50904003014090704042d0507412842e9004070b03000701d40034014880340018003103201c1a241003140c00b5039200ca281d15190b02500003144143c0d21182e4607039003004000c0407580b84501191169104220304041050001078a80362030341c00210040c0d95066400008142e0300c510105880300c44070105810780340140c0c0704601c2c001c07155040b000380300c941d80c1d5685107040c50b895400340c18162280e010051041c944070741c030515440003004070303004003035101406043c110305100f8965582c0705456440c040c10390031090200312011011680d0346400c5060695000e51502490700a010070444c0120380700050a06070810b0f8002010050004c0100d414241040f80c4281e011111200105035521035107007980c01c0034942c180c032a0760020301034030100d800d0080507104480b0007103040d258070403400008203031a9240c0c8500c24810509407582c03405185400000b900700b07900c082050380095541c3c6050700100c0d000d605910b9004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 75583320 1250 75582070 75582079
    0x90412140409060b030403091a070321090b060a061d0111071805011409090c040b03150c07030212030c040b070611070303090c05030102090102030d0b010212030906071e0e 75
    0x220355129202019019590041d010182400000198884d8000c010741c040c038026030302e00010a4481322000c501d140340011500d4091820000280401d1081d80303180003c851142d031510341044c180e40c04030240d80700c2030f0042d030383d1880b08001d01a1a140880c940e200401d000d041200d81c55800000b0210800010760b60941840404c0410500e04003060014101034064441180038007a80d101d04040203240902540c3c090040d41c001d030344c84600c1c1118800784038603401e000800d006c0d1100d03000e000150081d004600e800d8440c440324680030303030000300005102d4440351030b245440f030306203050003890000c0b006c2e01d00360015030410500a181e142d80e821102610170001520355540f106103030043c0208100703103404550520120b1306200309581030700054500d6002d195034569090321202058200d10640c4200c50140c3e10800543c10200f0642e0050069444140140d03001020403000b000003582c421a4088541d811032400c1044083c0c100031207004602119910441303840c03890300081d10030303050303402860b105 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 75584570 1250 75583320 75583337
    0x3030a0902030705090405060709120b0a0c110304060305091504030206040b0603030d0606020c030d030b030d140c2b020601030209040305070c080d020a0c0815010b030408040905070801030203010b090412 89
    0x1507490402183c0001c18001e1302c603488078902414100e448000581d000000244a1180050408021082c3d40c80c4c00c2d8016071090642c0d1a001600002802e1280c064010703c42c080220840c074075030a01c05400105142c0c0c60204640c507150380c40d02c1c03d080b280707044030340090b004d141031101107980014060340c0203034415284078560325442c000910314001c103070b440c62010f030038000301082c2968080b8410200b0380060f0100e800d000500c1c0c60aa085c0ca8407035841540541c418030700c40480d64030440705140d04649407121986845e080300401800c0458a0702ca40c0e841e40303c0d108250f11400f0760400d1441c45524a4400b40c0034950450b80002da40d81d01c041c0010381005000304e03a030002d005000c110b890040041004446000c00300c8400039455004414040d600f5021014000070b011801142440740100c4100858403d40e003005400d04040d0006801500d29620521010503000954402c0390b01680b016121f1003095891031040509407540f005280c2d0080900c201804000342c4030354401d0030107000d40c0c20301808 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 75585820 1250 75584570 75584573
    0x2070b0c07120305090d1217160302090a0305030403081b0c0a06270e010603060b0c07030f03051903021206032a010c05030d090318080304030303051519060e0102010b0303030a09 78
    0x22a401750610482e0300c18011118081081600b2100d40419501d90b151000051200c820b0310710640c1c0101c2e00c3c3c3c00340c0321241702c1c06070106200764014490900010644000a80c4a4a0b40c6c1d15540240e0000c4594607000074440ea05070200b20a40300703c5099843c0104019000d03800418000e584610a0717806000500c41015a00e5552002c107041c401c0c80030152418aa980300b2110030103040a200d0783d030210f403904c0c00101c1e82d54a20300882e2004840d26004100340d520f1a941d50101c20701480090301040803e10610500940e0b085108072005255503000d40c40e1314821510182c0c02c00040c08042c86a8070540c2440c3c107490300084291341584c02c4000142030000114016647c450b00c04100400c58000040c0e00c84100d0420b9008000d228080da680030f10244410b4807404144001d4010740086620502041001034440d40102d81e200e10034186002400400340041411522084031040b500700e1703141c01c24000709911600b58030301e1410900c003c0c4140520900441c1c0c0301e00c00a0000120552203544000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 75587070 1250 75585820 75585827
    0x206030a0b0301140411040c0207050907030e030a0816031b080a0f090501150501171602100c120e0d09030b06150712080601141b01060b0c0a0302070b0c071203 70
    0x722055006002403145000610b101c1e07000d400100c0d400c4030b814800310009692410035120704c051900241e0010141d2605000801c102500c00804480400d038807036441181d42001400035080040c520b40329691141445000c1103404801c00b0b1488080504d4008001100039002d04031400141403410a0b0001b6120500b104001e420340b42128000075081c4090356040140541c44240071603019504103081f01e442d4001195050000b034070b1070110601c84c401044c4044903800584604c241c0354011201d003500c00d6025842940d5100221001098003601404014500390144c070080f06c15501c0504440380226001400c00b002070300005e0500c02e4a00001422601c8000c854030340400045813068645100d8a810031410840c154460700140c20340700891100d5004005180080c10343d401a00e04141e040e00f003800700c001c101d4181904a64171808006401c603502401010140711600c0070305584101800d007e481c04440c0d601a1114a00800090f14001004510007082d152444d104090702c24880c14101c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 75588320 1250 75587070 75587081
    0x30207090c020717030403030e0112060306091208100e070f1701030609020a090b030c01030e150103030207080c060906040504090203030d05090105070807020a020f2403150312040f030206030a 84
    0x494031503140000003094160001031000854005010141c41312121581a0b0b45134090b40c8002800b03e0800041e00d50780e980904070080401c00c0002001507415030340c0c0c88036020303035600325410b40e01c42140c280201d0200b940301d00031aa01581100c1041c00c03282c078010700f180e90148000d0065040203001185020211700c112001403611485110b0080156100d00f0410020410360300102d00c900303003035480040c00f82050b01441c549404010003600300e007084a001500502642d01d03a0b1185401050f02ba24100c2840544c3e0602a501a80c014007006062440f036a2404c9110029144100b6045c8080000c5580740011101540c1098801060207000b600c0030a10314000d0008941c401800d100402603090815030115202d1196503940e00c4490321001816620b801014038069085070807400c02c0905801c010501d0031041541d10000c4440100441224601d40c0040c0d0341d4a0040d04140c0c1050303041e180c100100d000d4200c0c414501c070b20382890715010805082039840028028400840000c1c40f103801c96101 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 75589570 1250 75588320 75588329
    0x80603150c0f0d0b10090b0a03020f041203110606040b0d020d080c03040303180b0a0e0904021507050102090a0e010e0103120e15030415060f050f03010905150702070504020a05030112030207 83
    0x51540f40c0b00c5415243d005000403d0955000e40c0c0703281c3c2c000c60341c68840c141c108125403a41c00c06614141d40e24800310069031006004048400c0100000604d01d1608000d404004e070095803400090040310508500f0008068101441141401c0c00301035213a9451000e400007917812140c00200c04024a014280d40c0520305990070f207030201080001c10b25400100d907907480510705e03001e08810307074450400340304900030100e00c0c600060303003e4030040c1c2034101500c0b0b01e50000d0009150003130403620000e4070551a8800d01049619035000b140c4003107a0308010500001070911040b11000c991305026107118000d03014071000d80440d0103417001d200040c1c0241019004024041d056641740444285071800642c0150390480f4800100000d07040c46400a2007000152440b90120303164a629100c2004198011701484136495561120540d00050f010050740603003030304044800b07220340b41500c400b9040000315401070380520b0041103154155a800011241525104a0b40c2003481d00242402c0707140c180c10350030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 75590820 1250 75589570 75589597
    0x80c060f0c0f061306140f010b07020f192303061306150b0a020c03060105031b04060b0d060e1b030711150c0c010b0102030708030109090f06020a080a0c080603150c 72
    0x41c02080d4610284c0040250f010303110500209100500d0340380c01e42000c891800109403400b00601804040400800d0320500041000c81c940c180000061400080c543c903801030081d10307090800c1607041100c605a441a00d108410341c1e0b0309001c02c0425120000204a14a22004004088204400d5500030840c3c084420480b01c816511541c4201c1954481350350761000d803141000c1da16a40c40c0010303003d0305946e800b40151880d4650444803001c0020704014141c0d0041e12020301041d100200800307060420380000d000304100d40360041d0020825005407030300301e0100008000100d5514a503048940110340c0740707040c1500380c119684490402c605001244480c034401810302078005103d4000e009900303209002080041c02d14030040e6500e00c140341c13008091190610042100d0556030381300c140000d001e02c800b00d07085040781d03864000700e03400303405510041b038610300c14060442c045204561440340682840c00440c100351001907a2101d03148050400b640b8540000b84012425205603103240c1745100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 75592070 1250 75590820 75590833
    0x4020f03120f0a1704120f200c09060303030106050304170912060403020606010905210a080a02010608070f03150905030d0204080109020310020301060807050702010e09010816080c060f0c0f 83
    0x290920030f40d00c030041040018941c8880c0f10014110280081d01a0780c1c446c202443e04004031030151100900c1c40103030014070208800703808107158803001104a0501c840060140040c490040141c12900500440d009030f000b44010b026058011040701d80090300310800d00031402040c00240c140d0310035481ea054028464050382400881d00084444c056446502641c0469490200441e5640716034412268030a100b00e208409070b400d428070b0507004400c80000c0d21141e500b252524219030b80074482801c0141c1d5a803108100c140820b004141c043c089404040790110301c0c544480d40588401c07040710303d80c07a5681c08820304020080044440003180004c0c01d54a8a40e5245114001c0001c402c05a020f4000d44001c0b0b0721800951080381d0603601700c0d031942455521041400c5403941c110314001c9050180c02031440c0159540d02d80664000c110b1000207144040c00c1141c02e141c9410a680500255400703a14904200c2c2d0380c15050301e1480b409903500d1a150440d40c10b0440c039002043c0d016400700d00881 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 75593320 1250 75592070 75592087
    0x60907060c11041d060f090d050d0b06030c0a02010c08060105070803100e090a030809010216121107090605040b010306030206090103020a1707020a02011d0a15030912030606021203010e04020f0312 86
    0x184c214612050000302603810b199100c0325003542014080782d40ca280b0360403c8844014181c0145c0103051800300034800090300c180b4080c0400c80c580d10555510100e4200490324005940c1d0900922019490910b007541550a000740003900034003a1990081014001100041001c5075584060004018503040080c003414040911a03c4581c4a50705400064200e80029400c540c14000c540304c1601e030380c09100010740720351180143c2c06010501c4d80c0c03c105540640c1400d521013008220040c0000110029895143c00d04100450305103441c0705061508040c0304001503a241800c0d502981001c0c200540e4400b4204012504150000d101e40708440c0301800b030100441c2c0c000342441c181d40c800c2c0c8488070305c2200144442010140b41c2c800540c0905560b00c10320000c450b114564500c0c181c02d05022409010a030344244450a10701180400640c0d10f000c02c11940381c9c100000c540d00000022214030715410704080d801c210382c000f8006809081410f9a1039010349081103083c0c00f000380c1da41030644a0003070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 75594570 1250 75593320 75593351
    0x825050409020d14070f03060e0c0f03100b0309011b0216030602030a0605030a060608150f0a0f14130215041412030f1215061216270905010602060907060c1104 70
    0x410702d40c10007e45400000308140c3d4031940b00c54019512020302074201520140f850059620051810042c8404004005004016000910300549100317001007100d4130007400d42c0c2040d42c004990390b0111340c00050341c072000c00030307520215040d02c3d000000940d43e03948409044001d00b005034000c680511608441400b482179540c0040c0076641107406131407518450360942284910107072080509104c0140218100c00010703030280b148a20900804551108004000d00d219603040301e40d03c2e40b8104808016046240108138500080301c0900103e06090611191403c5051051004ea00901180258101250081060f16041041140902c0d078840026940c91400e41082e682d010a2a21740340c0301480c140b038144c0544440504a42c046142561149403a080211480c00c018040c40694040b040210740072201c0c081309480f00311901d0b03070902d18011420088520581c0542c2c11908400b0500154200108401c0111822850030344540c1240f4106041c0002100d00f25941c46842c040110812140 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 75595820 1250 75594570 75594587
    0x3020f07030b040b060301060b040618051507020a230d1505090327060f070204110c01020c1002070b18030d1d160302010909022203030825050409020d1407 68
    0x1c9030301200f407140c0300d480c11b050980d5100e00424034004001d1105106580c4241d401c0401c9841a02106280da80c0d9040840c100d0b000150000302130a200240390b0040d424004e18900007816000d604607004203280084100c3d4408103422280708180c5441c01c1400e10100402c50850007020800c10411070911600c032503540e6100d0f0244d40d4a40d00441c203098110384529189620990026055a14042e0880d40120240e484480f0490b4021355844022106200d140080c002655144000582d00c0102007441c5107854649015803448a00400c241000158400d040a4100040600300c01614919a5045040d07004000105002c5480c000ca040120307014040000d800300306450584000c00c003c1c0041c000005464000a4046010b81d5010841c684080c0d00a0039003001440c1400f01d000c4046460900c22031040e442603002440e0303c024004c18810750700c810340b07002943c5107410300c0b03c1c401c1000c0601180558800c805055501080750003400b03241da0000c403440030202550810034642220007401110 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 75597070 1250 75595820 75595823
    0x21c030501170f060411211006120503090603130b1003030f1112030a020408150a06050303071a10150f0f110705060d0e2a0108010e040f03020f07030b04 67
    0x4018144111582c011400041c05a5000040c01d03607555142c81e1007401c01a0880d1907500102004060201d428407001c0c1e44c0b00012a1201810201043c01111415030340b8039000186517101c038401da00002807000044410465013514030306d44030b55400000381040c82070b140303014102c1031b280400c00080000111900050364800d850312503080851850490b0360714510100052660301903840c400f1056400d10180d41d100c104000003601d85500c03020351a041c8801e0620b40241000000309000c0104028003404001d03180c02e070019824080944c4821104000d5041d058080c40c003181c000c60082c0390000042e1000d00015000d00c0e140312245200100f0032050b2041406c002056808046a52445200456440e21080b03009105150400d420805164494541b400300d50b5030b00c2d00c100c00c2444e4103000d481601009003a160816441065507014403043c01e200d1603041141c00001031201140400007143c1158100321140050305c50b40c81c050340b03840103a030075203d0719115000001041000d03c960551240303 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 75598320 1250 75597070 75597089
    0x6030c09022d0702041d0a06060504051e010b130b040617070201060f1a040f060206011401020105010303210e03310503030a0c0309090203040f0209061e04090201021c030501 76
    0xc107201c0c0c10b481a40d407140381d0301c081c01010420000917140c9038000302d4000700720124128026440c000b4551901d0f030354501c102c40701522540e0401c1036107070a10480741c0c004004127600c09840d0a40c02001e0324260140a42030752260045000c0f0042050151070201424004d0421550303030b9180c040252030040782445070200081408005400b042c418054a011541031b410940b8a1905002012040740701042003c002805c043c080011840c140c1c044510080c06075030064203440d41800e28920707107041803040d5103056a040400400000754820240e213006281440c83c525913004400008005d00381c91aa002141c0c4008102c00300010700705040d0075140851020005541d040b415400c440d0303001f141c0300d11649604180000031034a0301800100104503c00d1429603041d40c3c49459580c120381013554244d900180141c0001c00b14180707090626046030003140c6000c0e80d2000e080416045038560400c440c09030745c0300c20100c1c04590082024840c1341800b0114054001c2214200500a003824810500d85 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 75599570 1250 75598320 75598357
    0x60906120b0a0b04210510200d0c080109061d04050102070f110f04090803010e060d0b01081c020102190509060d0f0506150412080307090308070515060a1d0a06030c0902 74
    0x2600140b003c17400e9107030352040117030003030b410180c03c040c2c010903c08480051000700c5000c890300f55030390034000b04034074050307004002114050281c000b0815001600809040d40ca041070138018503054690304841c5900b440103900181d0745c0e903c1c0180c00380c014000c0c020445440c64404800b04280d41c0c8003c038403417030305443d088001099802044141c0d642d2900103401e400b0200010b00c109290f0150341503000341c000c0c0c5101503201c2c83d50382d0707000e02ca0402da01c241c40640100340901400700030540300469240c0184000d41c280030380d51030794072013942401c0c961030244a40080c6011003500c555050b81c04101b00c400c82042410309401e8410040d1074100e561030b200d02044019111040c455005403000d440145004080902084ea01c01c0c0703e90f070026013004144031400c18000005400c04000b010300c03a2042002d04a0f442170030001e050f14400140c001807040c0749207031041c40504441b24050444c43d002011100d110b4595440c114001d109a403c007a10b2411a40004100781903035800403c03074140540141d500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 75600820 1250 75599570 75599609
    0x801050411090c040303230705060109060602010c031b0f120e01050415150306050a18030201020912010b03030d02030c0405030706170a090f0605041106131a04060906120b0a0b04 78
    0x100c4c800c82c040100800d10550100c90441403504079190321003400d1000074a011190b80700c0e5807520009030300034101c803600c601050090560a0080b103160341402d04081c0802d0f00c0d02c0102d80c0d00c14506805070b00400013001003110300644109560344000d507548104000b150303c40c00075240a040e04503425180d14506081c000700480706440307951100304039a80c040106a041d1b940306409480c0242c0810300541d160329900036104810707905041c40c40d1181e000142d43d2141d030018007001c1c040031448841c09901d045014100c8d42ca001c4111500703000315110042c0c0d00d42d030340c06100303145018980015030107101d80c28000c50040c0d004100c5951510b40c190000c0d126aa03400640410f0344c012107002400100c01c03126038000211035030442508103103d4240100440c1c3c0c03017400b0502907003040d001e904075903903000e00410804010461904203d5122440c0c24681810210b002d0030f885200d10418017040649490030b03c8058442c0d00401c40508003e0041900598600100d1040d030054085c00341c40b00c180f82c3c500384 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 75602070 1250 75600820 75600841
    0x4181407020d0e100203041e2111040504020105040b0a03060306140609010e33030604030e15121f0f03030804060f09050705060c03090603010305030432100504080105041109 76
    0x304841c4c02603009600d014200b5010551180e444409004200d070f250f4000300b907141000103404580382200701042201d82e01402c0000c508150a904140524035110600000d40da10404039010303101c01d110820303074820401c03008500030052640040c0c000307841c1a4040310341d8034464680501401d004c03a0300b0052a41c0b600304181a8410a0b030f441d2418003541d80104000700020440102094509010000da08402c03002183c20208100c0c0e0407800203885001981c170920302120301d0007031114112081800e01d9091b180ca280c1d41c41000d4000a2605601008004a5040c5064000242040001c000d400070341e40d180280010351f060342e0840d00c0c1420000310340070b620390611815102c44c0d00440104440b42c070f0001841740c0355001c0001c0c242c560200301300070100303511031a0007503000394404d40c02150340b1850700d404100b03024040e48108008194806075103000440d01d270404100c441d0100e80800f40e9001120040d01d030f07882190710021807135090404200601040c01c800c00130b4680181c4542000d0341c0c0d80c1c030b01c40 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 75603320 1250 75602070 75602089
    0x7020301060b03042d03080627060423011205010902060705010e06241e0d1a0a060b0315010c0609060504050115060203070803090307020a0e09010c050f04181407020d0e 74
    0xc0f0103280c6101c003c100803d100d114a44c1e042341010307001e6034206451a0750381701c4200c0352003601e034580a200810303c5607a04183c49802402000b0070a80e0f400110305c280154040300044c406c103001c64546103001313400c2c0002944299405035004100d90b94540341440d045010709950f0311000c40c540105000509100f0300c10040054800d8030606051440308003908008100b1464521035540d401e2501e41c55080352541d02c00003140b01c1c00740980b440b40000601c0710068609004000c0180799040100c20030490000105494001050708458000c2803a80c000480d051000000c01a05403402e001000e014400103a0105000754085c00003030003540404180f855114105106400040c3e108104500c080b884002c05075400060300d80135070745000340d079800095100d205600103c0d40e0100e28030522140c0c8000748101c100c41c0c400c50414a06050b40c0070309c090780b540140e11403011926840d4176603a0f0341d081158401c080e40106280d20307003041c2c1402c031070003035540b0b0701d010f051804a00545c5224a0620300b8030980d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 75604570 1250 75603320 75603383
    0x50f03040305060109060902120a0509010603052e0204060e150c030409050103050d080105012007080d020d0807140405120a210306050102030f0d180f050114060105070203060604020f07020301060b0304 88
    0x278100c03191510b004010050400404149481d56034a202000290b018482514484d0f44d4440d2814040444e1b640800007102c0b03070004221075881004200046038010341091007810045072800810000c13204400c5191040c010710407414040001c0100c0c0e030b07043c41e91003503050703c0c021001c0384e44a000c00c043c240d61024003070140c40c4c0410703681a180d01110300d50320745480011004209961640c4c1d50f6400701442c140a05a001015800101441040650008400da4040418035021044541d540c04141d05032243d80500c0d0300130074051032a040011303000c006004605501c03140c002c18500c80e00c0140740b00004100740e1080003a040220000f02d40d803000013540d000d8060503208510700028040d5120040000c910481e400d0200341c014003001c18180d03002d0044040c0500d0002c21881090041002190402021681807103403d1003801e000d1384001800301c4c0c1c0b0983c280d0b0012f0b590007070f094000c02c19000e0410025455070800c1004075020014402443c0128824000e800010000311000140300c40c48800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 75605820 1250 75604570 75604597
    0xc020102071518060e010c2607051b061e011512050601090b18030111030403020a030e0102070503010f0e070501170a0f020906030112020307080d0e0607050f03040305060109060902 79
    0x44900300089154441c0c2c0380110303c14040d5039180025901c0c1c6080c1c1e40d5541c84520280d641d104c884103107980100e000d070b02840041014046800d440380d41d54841306000340065080000118100030004980244641c0c4604504100c8281e0b250071608408084c00a00c0e2503c0000041e500004404016001d04e5003d150151542103031143c14510b07000c024040105060b040200d1340c100001c800700d020008000d4640b83c030404000001c5443c06050039141c403001aa040300c0020000c10010940c04034410255650629040c0c0e00790102a004078030300740340c64100380e038107500e00b04210f00c3c403d03107940c4100896400c02c2c007681c100341c1d030f140300564240031500c0e1240b01d480440b4000a42000055124442c464200a00141000d035100042031003500260040e84920300150740020552070700300305800c020300c2075900801c42e541c9801e100034044420307880094007170840800c00c6020400f0500c082d208102d080e0b800c0302e4403607649060055552200707114500440780b801e20007041c08140d5000712506450f0000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 75607070 1250 75605820 75605843
    0x30f150c021902120304050a0b12010501020a2a08030a02070911090a030206030705120c1b06040201050a03090f06090507170f0309010c03110d080601030b060309060c0306131503060c02010207 84
    0x20288041c015008504c10302c24001000003180980d112549540070f01b50b80900c82d5141c0600e101c0f50480c041042e0807180c10f56021000c44800144443c00b11151104040500c1c4c1d00b042c5c600302d8400550076103404c1007c1074000420912500e55000450204854549c007052000910f000c91444051081d0031007039030014504007050025003005002150020340b1031510f1443d007402e15503000000d02e803d8492440a10b070000300140480342641c108140d000d480406003100f81030660000c0c085104140c035030341c14552508250000d1102d074074070701081030f074010b41e0030305c012411842c21945845050054214044c5940b01d4080c40c0d11000074920004040071005500d0710b0406001590804903094084081107107800030700c0041c00003444204200c0045480300c0c0d456082490014069135646200207018010500800403202170014590f90015898032016690383c4403503000c0750303110602e550a4454281000c501c40c00b60301459a100c030490780649001c1000c00b440b15000c074280c0c8038911010344204070380b4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 75608320 1250 75607070 75607073
    0x807060504051f0506181b03070c020f040216110a03150902040e070f140609060a0f0905040e0604020904080909070e030c090108031e0d062d0602030d020a09030f150c0219 75
    0x6c0300c80d400100140d80142408038035255010560700441d48000001c44000c2240110700340300d403103400c440c80111030075401c241c0a001c02c1c0111501840015040042540c1540e0303540d10307000e140b1000355820100c000040c000100312640038015211003280194504901781400c01400300d82e01041d242d110511081c507500d007074075000c02034081c1000c1e250300c40802c000c1164165600802080414029120b6a080c400c0c080cbc2c020301035040607031084e4040c07402c01044035a1080b01040f01d50f4010760480304000f05454905050b81c46014100296030841860030901c458680c110701d480503c22012011a9045e230b100005000e1561401c0c4208001d41d403091108a0101c4011210446519000d518441c140410180d504c0140c0e8201e51200c0c0c0c07410300304010440050010501a125002911040329440745007840095492180800801005901161034084076104d00702d000015031700304081041d0b041160404481c84241e40e6901402103207409540c101d040e002203440007030741701d8189003031101200c103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 75609570 1250 75608320 75608359
    0x3010e0f04020301061503051f0605070803101a07050f1209120f0d090f14060702010807050c0d030e06070905010f051b0709020a021006030804120807060504051f0506 73
    0x9007080303925540303070711001c0342060029001c2010034000d990301280c9400d0005000c40801c52462030006460003a21040c00303000e0b004000c66602d9a4410300b611380c1c82c2c0c0ea50403030801003240d5422081d01001c00000100c0044800070140144a0049058400744204050035030ba442e14003042159a07420f09101c803207210319111f41c100c040a00c00301c09480211a49013042c41c14050401000c5000c42c07182441802700d05410046540a44100350301191142c0e140000100c6c0383c014290001c0c100310f4a0780024030b146200d801510703c49100f0204692580d8030050000d00a846814600c08440c840c5400081c0d4080c03090901b80101e07a010303110030b6581b045001080f95943e0044040740e18040c084194514903400421129004200d21000141c66050031000281407486903030703540b941c0c00c1c00c04000340085240d10040303034201c5c0c0e403801c02e1030f800ea40f00e450031400398040c00001502d480c0c07400c0304101c04d104011403103806409107124520202c94003c040303402140c40c00d807040c941064152261010b42c062 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 75610820 1250 75609570 75609601
    0x1006180518060f1803030f010e06010903060c0801061407020a050402030603010e1c0207150905091806090606010806040c0804060906020c1f05010f060806040903180b09100503010e 79
    0x7400080300001962003100516002050324540341400300c070410041c00b200070f80348004e41ea00c00d00f0701451450800103010b000086060103100d0a00c40c2100100e891a03000e0200c030310042d54800740a010f28903c062001e4803c560074468800481c0901d8a60100603400004480000d0b60003031451001d0780c2410140700003500000d10f000e425643e01c16003052800801c20071040a1043e1040b406560f203180c5030001d0a2a0f0b107688500d41382c016810418282903000f510400640c0d01c199443c101c2581c0780b0290030f051217645804194913004042c03e01640450114940c2d200d07034402e80343d80302c450300c44200f8401156541e80e0301c40d00140c08000480c001031415001202c03118003400015081c0b010032000b450510f600c80309091500d5000401c1810b81d844d0305e01441e40144003110101520614040c00540310043c020007680c4919990903002c01014003d8258240401401600d000f03a1601d5006502d003c1c2d04c850180b80c40340440e484100503151280049030f05846800c0c00c114440d072581144001c01c0309 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 75612070 1250 75610820 75610831
    0xa0c0219060f020706060510020c0303030f0c07020607080901030c0f050703052a100b0103150b1c020310082b11030f07201906050a0201060510020c0310061805 70
    0x50710b60044003120700550000e461018019000007511601d00020012240c0007840001d09642180c00300046503a8040281c0e80e0000c0c011001c80c4503a5070302003000a07588182440250301000104400c01480052809800c04110030f1300d04000421f0b604000b5200308070700350300c1359002500401028002a2107040640743d00c5c91a0b104640100c44d220716050704410030800b161000f070740300c05c01106181245ccc0c0a44000d00100782020450000c605050803011440d500443c00e44030b90010f000d0741400c1c0d140d400810340d0f844010045460b400d180b4190f0601890901c6010554403504502c49118400c03101d4001d4808440c032500c401404c9084800e460782120390102510742d0200b884880700c4140f0840c024012a80f00b074040c03c200c14a41c1003040040140e240002d4021081c0307500c294205840001041c0640c1c0c1c4904050b0f0700c2e079180460403405040e807504860b802100392402c40003d5600000c40c0d000030441202900e0040c4804070cc0c42e4100c401301c2c450109001035000d090100024140e02664021 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 75613320 1250 75612070 75612083
    0xa020a05010c0503041e0203060106030b061303030f0f0230071a0708010e06010e04050a09050712170a020309040f180b060a060f1706010306050d0b040b0a0c0219 71
    0x2040584405084615020003200402c0002040004111a036020b001e40c40da150142d0302c05d07200e50303500840c0d40c80005001e00c00a0585d034040002c815501c06065601c0c5040700c25030884102d88902e80103140505042240c40401e84402d00f86105d1800840e007450b104020a007094030700300340c00b24210071217118110740000c0d440b0304003c9080800d8504418200303405e0001580d504038109a032005003180c0b416800000c00800080a015490f1b90003c0114a828402c55011402d40c8640d401c802c018235020b840140507228071400055206601580300d04103c3c0149501e01c12001d50340d1903200d903840707a45020070050b041080213985034170f499403000c1c00701100e1800c002101640f00940c2c40240f541e1207004d4600ba4010800c11a40e4500003040700301901441c900b0208442e0a0b020260800609050b00b4101c01d0660700040c806034442d0b44440d00500e001089120b48007210700f041a0400d40c01c0d2400ea13070442840d000220100410300a88000c040140d00a103004c0700d80b000400100c103018102252031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 75614570 1250 75613320 75613333
    0x80d1503080c0102041401050c0615010905030f0a1101030507080403180308030f0907050604120f06020d11030403020f0c0f120f1002040801060e100510090503010c1d0d0b010b0a02 79
    0x460070103006000d210b04400c2c00169220b0920b10017003841041382c0205c504100d01003012902019010480c0e41e04014104c900818021500006850101094200a4051165036140c60482200049504a0b1409050741403403c525040c011000d03108220741880200d100c0c50007107800244218020700142c1032405850350f10701d40b650349600099100f41c41c5070300102c00804c180000300100b03109600080c48210b414a26041c540018070310000005c00002e0010034a8480036403d0124a4045541308403240d00c04018100b0b0780c02070050345800c161010780c014031a18108240748400050010119403001380141902c0841508000f0a80200483d2000d14010004001c500c4a4200003205100261350f90158030f40d82805060750071030300707194400107400c43c1a905010000303c906070309501340c2c1d03004e94400384c0c00d900b070203030907503e5106583c4410742641ca468404180342d80c3c080d03a45446403105035076102e41d0b14003210400001c40ea0051010b001c2140000c010400103100c00010140010240140c0c0c12 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 75615820 1250 75614570 75614573
    0x109060b04150c050a0303230405060c0a0c0b0106031d0a0b0f0406090210020d0215011206110708040b070b010b07031409010306030b0108011b0801030c030201030b0406120f021c080d1503 82
    0x1442c4405c0c10032008243c9800301060035054400088510f074800b81041c11243c9429201d055075060003410310f8400318000103050303640318426038600030610b0700500c6032442540d40b108000d00820541011b9070f0400074680303401d41700007030100d00b42c1e103180d4000d14a0381c01501c071041c54207038601e00a0070440d015a6614040d20060310b44251103008001d0a40140451008850307000e818460944038400c4006020001400300c2c0111001c0694825000741c000501d1181d41c0303100c69210710910310041d2044102060000c1e0310210000204079551107406c04150b9070f680e4402c264010f0040d4030000340820540003903524428a03200c0540040341052502190b8141d982d00d07140310010f401e070051002e44e516001c0c10b40c10070950b05400c1e400090585004459585180c5402d0942c884c1800020304160700c0d0116203880c0c2d03035950855000b03821300303080110104200f4a45110b218604202c2240074441c070100711a516010f0300c003c115504d81010095281c0212101c80c04001c0040c10001c14440c00c1d0740a0100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 75617070 1250 75615820 75615823
    0x30a11101101090303050108010e01411303020114010312030506030118060203040507060f0f05030a060906141002010c0e041e14010812090109030b06040902031b01080109060b04150c05 81
    0x19143d8000d440009480d414600864203403596901715948507810056220000c62460443c3c0d00c0c0d0b95111b024035241654404180320380c42c5141c4041c800211182003d12000441162885411034441e8000300600e00c00018802c94542c424400942040743d410300f028501c50281e00f00c1503010788000d00008181d40c6280e801603d00a0600054400c59400710070041044030801170f03500980392600381a90b0340b190300180181202d8003100c040b0700f00240400030569000882c2c002501404402c102803018980b80ca00d0340c5800d01c5642c48007885410700e015001a00c1d401031060480442d0305903a6151051182d0086c800509580d0a0b40042861195040c5503510014810308140f4010200301008ad545030202c0645481010410350004c1c2204000b414056a0015640d030202e035484800d14080c0e039580c2001600422050170080d4150007444403440070300d03440c9640400040d5098807800c2899032101420004c40d0010b000d51481c900b4200814015644c0c0444401c80e003940a14140328a100d9039a80e5a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 75618320 1250 75617070 75617081
    0xa12030e0c1201020405040f050c03061e0d03050d050f060603130c030f0c0302090108010b060d09020d0203070603051b04050a0302010507020a1208040f140d0b06190b04060e030a11101101 82
    0x40b80c090354003007401c0c02a0310702409101030280040c1d906016600b04100060461311001c0d201510420005c00000800c00205809510300b82005207100141c400c1401c0c0a042d90f80980301420f042e510300303000070712001441d41c41603002c6d5a014042c0c506580c0d4228122018407848034080c1d40c0b24010310b0001001884c204c4807802e02c103110310340560a1a01d036106000400206030018001d99040c855028103944440080c2c4400710701e00031000c1404e11007400410030702420a500650103010381807000c40c1240c1c00d50400390041940309409050305241000604950185001d001d500c4850344100308095032003a009405401e000070904031078181c2d1282054000d0010417006c940f03815010908110b8160001400c0b03004107503040021000c16040307000112041580c0c00d0003001e0041e0342c80031440030f40f140305206650240341c46004200369100d6031190001e0300244120000151001c06000c164100401d04013009540300680a194a0502c2c0401101a0580604c4400c200c01c505007100e503c042401030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 75619570 1250 75618320 75618349
    0x110f030c010c05070803040f021f020d18030201020a0f17040909030315030803061005040b16050601060f050d0b0319060f0c030203090a0303091703010602070608090a12030e0c 77
    0x440d40e0380345400c0e455080d01d070301c512103400380042445407402141084044030740c0030f40d001c1840c0340f6111040c070000e405204c1450138049ca10340c21042d2008902c0e0002490440c004094907076407031044180455443e041041e00000f40160015107420000441c00903014a0722803180602010940203443c020031300307400c5644074074101030319480507100b41601072180c2e80000b0214050070312070078111b84030b0140c948000b900860154042d0201d0400347c40c4602c0a90b4043d00119881964500b0b036180e2401c2d100c2000b020684081c010302c0000a4031074010a6035440035051a22628204100104404000c20100500d02e800d8010703a44d4000e40301c1203070159480e0b901c2c03203600b0004117a802880782008490002400f48c041c180304000740a80300030001034504003680e0601d0003080d07944540ca48580b2249246000c01c815880c0400081102d94001c122601981d0743c543d11203405507104901c8d00c1c0d643c0e40c040d4000e0140c0020380015654a48250403100c9401d6092045a000b44108004600140380c42d002 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 75620820 1250 75619570 75619573
    0x702040b12030403061103011a180406090e070504020a0f050315130f0c020c130b0301060f03060c0210110405010806180702070816031223040306021206040212010312110f 75
    0xc1c184100b010600c2945141140141b03542e04540c104020122550700803c0c00391074403980411b0700760303602c120340e0359140a44001034000e2140c80d5550840401078001c80303c0040c0075014110010915041501c07e41b00000480c1e5541004290300c5a8241e8683d800644103890080100d00c000440313850300c1d03c00e8116401d10150004502c85404c13958000c44950000394400c6400c40c283c003810503510f407030190740301c0b500902c0d000401d03000076000640181150381c0403081e080786005000042c0103056000e40c1d8040c036960240e8440440030b41d288000c940032880c4460051906200a20445d4032a00410b6072003840501050145292900081d034005030440380100160b11107041400303004c0702884194600314000030b8005c800ae0550b5101402c215650582404000058a80134159a00c0c0305a8050580d207081a003a591500c13400c240c4043d41c06840113407510540800171070242d0415100319418030749045c100200507401d44c1c0d034400c034820030082007408001e16008542c00d580c80620048030244002c0c3c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 75622070 1250 75620820 75620827
    0xc100c020d03060603052517100302121612080919090e03120a150506160507050f06070311250305070e0405070b0d0f05040803060a05060c10020702040b1203 69
    0x718000c042d40c40a8000000b05410b1106000240041e0045a10503c6030300c0300403c501d54440400f01d6581107075480840d0844c0b418024041c1018032101c00d00103aa000f03441030b02081610600040c1d681300516100c458501d00c2c15010402000016041e00042c1d1080428074640800d000c0002e800c02000d6031680c0680002001c1003007501d00520846040308050f402560510141c4003000f41d809070020012141075445902d494140c0e40c1c540c1b5008045c01e00280281d4541c403032529046402c141a40c07040303403503101d600c001203000d24120301c0c1c8803c4803800405080c41c00b807807035504a41e002d400e40c0c80c5554510408007054030413210b5491011034081d2441c0c0e8415030070b156040c214505120307548425252044031090102003200450000c0c142e91281e81c02c00d5a81b91510340040c020011003400d00103840c6450184010494040000c2d07004200855420141ca034460b070401220f13200d29500d13030005e0f07801b4400202d1301885a4000d4080d842c0001c100158110b500d0010804070402c0405908440c0c0002 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 75623320 1250 75622070 75622093
    0x3120f090c0a080a0605100e0907080d030603111e04060803070c09020307020a120e030d030c1e050a1404050301091a0705090d02060702031006081608120a03020c100c02 74
    0x300000c40c00c0d654202c404419461505200b50f41354518860042d080b291100c0004014010b0052420020000d0500c1c602d602e281040360715488040a0284280300c0c05030080c134510301446030044406684c3c00c0305171500c1c091026020001c49000d01040d1400c10244a62038143c55501c0317100300c074010300010700036680d610100d103098644405030f50084028a8414810f0140f495400070b4032107840c0c2d500c408040c0d4840000902510129125030f1859414030890540c440c030141d26800650034083c9907111161305991540020081802204a00300010003e10008052910411181410354008148c0780d10300754480380800d003034540740740040d507495201c03070218a0041c502001c02c55011859261550800c0c127010009440142c10050180c4650310124181d815907409202c03c00b41910a0081040069502d500030340c0c55220003030446c4203245001c1c038000b446003804100d01095031042c45196281684861096000390001d68608006200781054462009040d1185002d2845107070020024001c09 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 75624570 1250 75623320 75623323
    0x2010e010e07051c150903020f0a0f021806010c03030506060c03070602030f0c04080706031e0504060603020306060103141305011d06011404060503100e0115030b090706080603100b010203120f09 85
    0xc01c2c0c100000413a00001c44404182841c03d40098510072038400b19030b40f1000d0a0403440c00503550740007480c50040d8000e070130030481c2c2000905040d600c2610400d0a1051200394010140002c84615011400e40d5600d0400240b00c1d80c8000e5124030001c0003035060500f907034649441c2d5003002c0c400711150f03940082407000d24090f000c180d950000000b62110f18041c03c11600340c2d00c03880c2c244252010300d502c0b070081d12003000420b00031102c40000a5001c0049241c5414840040e01d011320050b406801248003285583d4403030b006007100c1e03051034805401ca50301d444034081e070042d203200000d4646540c4c03102401d0003417a1440c000c0c901e50b124803004118650403c1c0301c2c0030400d07000340881d9100307a203000d00c10030540e01c0200b4058428403075007000142081c601101c0d40c0c0505050900001c61000144021041254000c90180a082504100d03070301641c541805540d000300980d221a0315034000c00c2900c20a030b00321b0700030100403001841581e040142040310342c0702c000b10079212020441041c804008001c01d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 75625820 1250 75624570 75624589
    0x617100b030718020703050f0f030703060510022d0313060801090b130b0112020f0d0e060708040f050114010f030629060919060c03170717040302010e010e0705 70
    0x408a000d0721100307181c03c003c40c0c403460040e4050441283c010070440b05150180c415182c5817818070f50f03099a0b0726400c50b0b4800c915401101c0c0d440100b031600d04042410304208074203000240158004110515800c094982640d84490030101c0c24050710340c4030884c0450500140115105007c01c074410a81006e02c003074041e0005800c007031440351030495400000d0740c4800045d00181c043d1440001c0c10075010740101c2d55146102d525040081c000034501031603901c480000c080d52700c00c8080c02c02068121040d090744403041030325400d000411440110b000310704080c0c001000b852040000207103c48616111040006d000d9001048025803104104240300050207043e030f4800d560045114003071340c60502206150380091036940190703008100c480143c5c8070240303024010b00e40c84107403549030703580c1e01c10040107501241d404030001100c00c640030003201e000e03c0c1114000c115a48600c14034076039181c40c1600c1c2110042c8103a013159258140c50000f101c0030f1051500000c804030107400c0c0c844c20f02c81440881c3c2d8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 75627070 1250 75625820 75625841
    0x403061803081b0a0e06090301090c05030106120203070e0c0706151703070302060c18090406021305030f03040e07030204030f030903020a080304080c0618060f040312030501030f0f0501061710 84
    0x90200401010f100300da600320349007a807050500b000307169040c0011500f6401440105d0341c040d0f203041911000d1044001e000d00494104500038820b094458a6010800114000c02505a0b010440c00e0040b10303007200c0c0d8035501440c40340190303040032419280c0009840810140310100040010b050242c88442c03594402c1c4010640c005502c1c0c001283d400a50700c620081c02101c629402180c0500d0081c601160302c406200e0040002c181402c190915130001c1d44110310702c1e001e121030002c0015070313410045680700380070465001031824a80b410782d00d61554903006024408040d800c100100028804140b540b942c940255aa110b0781c900b9072061000071071b003907081275025034024081001104000205c0c002c0242003500c00545584600d200601e8640c1520041a805000461100d02c00342c21480940100d07401a004841c40403411030040c3d0480d0707428040940f41851011404011031074031103014020718426030002800700d0341c85540075404542c04002e1100c9401030304245c940700f00079002c1d400650 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 75628320 1250 75627070 75627091
    0x607030b010c02090402060409020a050c0601050a180515090106030c08060306010f03020f0d170310092c1e0a0201031d03070f05010b060d020a0210090b150402040306180308 76
    0x1490200028101c03010700d00b4000d11605000000030219150481920000e0403520700554075011480c3d00a00190002c003800381d541e2107020000121481c203c09040111400d9031992581c030000201090003030000109980c3c540784920380050780c60344401020310300130403c980e0002a0b00100d09402401d10300042d041078441c0d8090750042c400d420002c0307004401c0b60781c11070b06489445441c03c04100415650407001e411496800c000394a08801071008610600d04181041221601c1e8480350045901e0718604040d0b40100d0002800c00c0c41102c07010181d098202c3c0122900e22110b913012408000d83c1c403807100816000701c0011011035030140a21a07180a440e00440030403140c15601c4e45e60303405010b0015000303000e5003005009024081d84000381c9541c001c1c01943e0303112030303614100307000c0e61106960200512413041260080d130a244211a60720ba4407840b400c81d1a1688071080748400100580654059801c100010004602c1c1c400d07170041505003007003110029100d05004d008208000c099114a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 75629570 1250 75628320 75628331
    0x4050708010e070302070215041215050f010b09030c1201060614040b0a0c030512070206040b0702031303110f0a030c030c1a030a0504060914060103121119020612011403060703 77
    0x2e07000d4a090700342d0b0140a40c9001600d510550001541c080420801400030b103400142c0401c001c1d200081c2015440c5c01040304103d210661460034003100d400b00c40001440150f00014050320900f44000c0031390400c010200e13000b0140b07003400a42c4100411500a500d607540d0501040388941040c4c504240c40030400035241400d02e0f000c1c20400a20885036050100701c10342c00b641e030400d07009038152600100d60b16148607491408910103995203034280c90580b400044800000d040e20701c00011a200c003240d5950000320280b866a41c945208580c01c01c0320b030301480081c2c20f246540c03280070441008500440400114601e1810007035020b000b140c102c80102070001e01080c07030556170301003101d8000700030b0307280001d1607560780c2405801860300501c0204810b01d104118050320100140f0395050301c6c000c00152400c40342100c01074130500b1500001c4d101c05c1e005a140f03400d120340c80c01c004101d56800601003916054140c004445200c7d0300340c0018405c0c45420b80c02c8560780c00d0411000c0e50210190904105 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 75630820 1250 75629570 75629579
    0x7050102030405040b01090b030709061d010e0d020a1503021306050408030304030507050109020a030311070806160c05011418011103060a030204020901032007060b0f011403070c020a030b060405070801 88
    0x1264462800350f14000d5480d40040d201513441900c40000600c0f08100568a9003410540207141501521500d80058102e403032015601594010030410010305031a80e40620b810030702070128100043c001a80d01c2000303044002148031b01e20107041e002c1c1807551340040c2c1d509428030240c08285482d0b08000304100d0240070902c002e51000044035007143c1c26062241d1074100514003680580100c0900079004403954400200701a006440d222445210384107480105072038000c8039980700c2c030484022080c003200a1601c48454000c00128036040d0044002044000100f10600300410055801964018003c5000e6180700000e200e070104001a0124051541c01d10718001000c0b505d02d030001034403ca50000700b0009607030003a4840c102680c180040043d10388030103e254010303078200141c150350440c1081810303461884c0514050012010584516008022004606480360801480381c0b081c031980b20000005680d480b01c0c1440190321035003046d003451400800340000d503080540741d04240440c0d01e00600 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 75632070 1250 75630820 75630823
    0x10603090201170c0a050d0b190303110606010203090f01050c070803070c0602070501080601050f190305010f080105060616030c150903030e0a030c120c0f06050f0903121b0d1508010c0207050102 85
    0x1145c40e0443d282140d01e403840c4030720440c014030542c801d16174010185070b00c0340c8801503040756603800c42e07020380c5820204403200b04000b5240c00003214414010380041140da002840c20201405c039412061502d641041400c10310b140c0340018580141c038a5510110302c05041026004020018107442d1014010180c0340c070002818103034002d4a09414000d0104108420000c140f080c1c1e140e505a41005001c101e16250000d001400280115050944007103404034031104140981c0340100405403000d442c0641702800d02d03031158402c40d0100d0800103409144808141d0b454050703004100c0355803001480000614001d800c803249109000700d44d4000c00c0c044d5000c244c020043c5001d01e504034008241148010074110303035a25650310001c088240a51201041c0401a401180300e002041703440c01d0180c482c41d41d1035940b401652029801480c80c0b0300041c403800002805021401d0703824001074200141039040806940502001c031040030103009003001100c400f40140e412800301800900185414040000d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 75633320 1250 75632070 75632077
    0x90c09041805010e0f0607050a0c0b160201110a020316020a170c091302030d18081015120803220b04080306030c0a08100b130c0c060c1404141503010603090201170c 72
    0xa1f400c2c8a808600700c00e10a000b040d03d0b08a0a0f40500c445800c0d24190480712400026494040015031070f04a42c00e044500100803035071100f80c1c1d60019402c040241503080700040300e0382001c0b82c00110b60500058511404194100410101006450031601c00e80a0040a07c00101006002003240401001580340801e4102e9046134070319100c10070750740254410204005942c4000d85c60302c140490b05842401e1a480f861314045403107001101640c0c0c0d47d07009102e044a01101070803008082000c0381c41100813001d41c542c4107020726424600b0302e41c40c1d01d0300c000e241c0046800341e4a492000041001c02e02c0d09104032468142c08851440189060180540d0f503408030068200c4d80940e40c041c01c1055070f9400d003c0c005c00001c1d20505120507445c03242d00034140e459001040710441d0074201c256101034011f03400d03e45107040a002c40703820a464507524900300c980660160381c200c1c0b010446240d43e0300380000114040c152548000c141003015200041111440010314140d800c44e900030b01c444400c00c072045 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 75634570 1250 75633320 75633331
    0xf0a0e01050408040b0309073c050303040618080d08090f0105010e0604020d0e0d020102190503060102030d0f150305030306100302030c03040b061f030c030605040207020108010302090c09041805010e0f06 89
    0x242d5180d503038030b810316807410071960003086030b041d502845046666080d101c00940c4450251800c8602c032720b50b41d420100c0798814003500307a01d908144402c2c400f0522411580782840c0100444000c1c45654924441c1010110085d8100140c4858200010b4240800013010007451610080200350300d0202003039051403001d07141a01c11500014641403004039508800c0c15160703040d041e208151560400603000794000c05a010b0b002c80d8030f80b11640d019004e1003e90b481102d040e00910325040703240950000074402d0f40c60402041d40c0c1c82c4c20100e2501e5803c00c03030300e01443c0300c3c50003550b607030501c94104541c441d50300140c03000701401081045107109040007503036045540640c440109803603000000307440c000000c031010782445444502501040c0c1c10380005415000c81d8904102e0f0303e03180c3d0148001d03441620070181c0864507030343c010001814140200b0303074030103070000c1714500b0500d0500c002002e42e58240c1203017109010300b0305118280714003031040382010b8a108000f041c403030307991001311034981400408 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 75635820 1250 75634570 75634589
    0xc01020d1a220b060c1506010f0804060207061107060906050105040207110f0f03030f09010314091b010e0a030c050307090501120308130f06090b0708072003040302090f0a0e0105040804 81
    0xb10b0740d540c4410307420082603180010f050685842800380714941d1030711382c03640200c0c0d290481408034249501559010600520746d94403e050791f9201c0d204d000103075000322803c072119581e6415204010b1082c20141c03100511440001c00c56482c2030500e84e0680d20103800040c401c910400074140002c090881c0c01f03028150980702048100c1c0503c000440340340c8594a46a003600000402000c150117041c0101100342e42628108250a00e200d081462400c04030741156071503006000ea00c401c01e0000c0c2c01e50010090500d031406001c44203d001c15920100d0f40e100310380941030b8000038001481c01380004000b600303141c03000300080e40c13504010b40c800e100c1c601c20250900c01c07601d01086031200147c022448503904183c10f1901c02e03d01c0c0c50420018900c45006a40b01914200481c00e814480d0810502039211542c80f10480075550300601c012010780310001100740f200702b00000043c1c13601b046052081e4031588030300e0b40916000e0101c1302541c40083c1c100e0020b91410341084005015130050301c0a0303130740000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 75637070 1250 75635820 75635869
    0x290409060e01090311010c030209060a03020706061703071e02010203090603070302090a121509020609190806011d090336130b0f010e0307050607050709020c01020d1a 73
    0x90620040c003210750410842d5007401c21181c213041d08000f041c0046400d9034000c100e82c0f0290a0120200c1c0222414542d21902c03c000800d0050321030b4000c0c1035075038024440000e07455600c2002241c110740c2c002940302ca40c5c00124030b4400740800c1102c3c800122a0704890301800015550000b901e038800e0708010381c812000440480c1300c0764482c0e811ba5104101c09403600580a8460581c6012407102c0401100c25007800c800040740b01c403090040004041d8050311032401c085842c1c0030002220030031303901c8640302191820009005001000018001e15045210181406820450010142005184201c1540100010b0044025418201150b240c509002c0303c03421050166203200c040b208400d41d070b0702c07002d0620052050a525402074080d0307101107403e400f03503680480040d0b44c10800f85202d00d03810703004400c003001181895801044a80e2040055414242d201c06015049800c141041003183c0c0d40130503801503890b40340c070485851141e4612405c0032010050b0010300b1818445144650301c505d503a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 75638320 1250 75637070 75637073
    0x608040b1f0e04080910020102090a0b0c12071103010612030906030f0608010905060603061305030904020906091215010611060a09030e0607060f110f030c071b1503290409 75
    0x440312014002003814600507043c01e0400300001d4110601a522500001d0343d41502640140708451003404007070004004e83d4a041d00a50650b0000200440d00b40180b00e141c1d0f08140303540c0c005001c00386c03080f02d042130401e84c00c00134103084501503000701c10008850b000c5800071030342201011040380c4161902264a4214400d0203014080c194084410303582444070f603004002d0040b801d144966010b4040300c80a50b280400f00071700e8021288040e10940080007a0303e80c5061580041c42e40400240c10985440d558202048000b4018040310391942c2044110480c0c001d494415039005207420b1510305d1002100f15000b0b40c07541006051030f4001e5580b10104020540500340388860742c500103003010b48403403a50a100f0003500070862480410f40c904180310101c4913840c0150340f001c458942ca103d04542d540001084a035100b0001550814040744000b44d400d451451124064042d8020302043c040000002406840c00c1203c0c03242c012100c070030340005036a099405401608000c83d408280885036 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 75639570 1250 75638320 75638371
    0x18050303070236070309121b06020f2a010b0102010c0e010c0312110405011107060207030308100e01032a23150a030501080f06010b0a03051807060807090608040b 71
    0x40002c01c90060043c20304014155402d070b40f00c080c0041c0103000c0390b00006c000c000c080710300c800c032070103401c10226100c91030b840800c0281d400f50441c011500b90062600b00304561300704000d2840c0b1304044414900c440e0380459004280a040040d0000303000034042e1014550000e4200d4082110741810040381c0001c5806044c8504003642c1c01c0140c202c030800021041069500007944203001c2c0c98041090f00c040700c0c805c000e0001e4407108850142e4050f00c90b850540d0307800c42c1d1501c00503003034040100c80d107403011404041c185101802144039020850454103000c1c0039803404060100c013850b01403d0004c0c00c00c02101d4106014010f04503505154064034840ca00140c5580306404c0860340040010038102c4c1c545406500c014140d450200850f01004060080d9030368450f0302340102c2c5038025061001c801514081d0f04429003005000c00309101d07510801400f146070a1160b03004038005400b0f101070000c0c241d00b10307041704082c1c210341c90031115610789921440f45405010300361619a07048500410807100e42c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 75640820 1250 75639570 75639649
    0x12020d060f050604180b041721040c060c0b06151b06060a0f030314090d0206030405010b01140403031409060408070b0d1407020a060c030f020a180503030702 69
    0x34444010008480c0030840400240012504680114541103603d0420980ca0350301020701684035100c0c4103160b0740e560320700d2980c00340e10307850180c4480c0500c510070300c140040003403003c0100301c2480000c140c40c0c06d08120714404220390204d400d0001c1e9a03004800703d5480800254445000e640c4194a0712190422031441d1140419403404042041c218100c060404620340b0b00803103007103608502075900c407010107591403080c0c80002d001c15001c001440810301c00c44c000d4442180c004010410042103a008181e00da4400c8070221000d956070140c164886d078000c2c001e243c043d40900c209608140c21503401601103520101c00340e902001c0400d01310026654142241c0240054500340c8240c0d550341c8640c40d402d60042040e80b08524200045e070f580282207508200d204c0c0c0816402006001c0b0307261a40001804000405010552540c0b2111025115400103044a01165a860200f050a0010420031818540242c1c1c4250410803030313400582d44e510202c6404490740c448003030840b10090a001600e02 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 75642070 1250 75640820 75640823
    0x3070c03030c0219060605041113060c03090f060806030d0f02071404060f0305071406071101050a0c051c02071403030307051803010c03021c050105090a090602090d050106050a08030f0412020d 84
    0x1196524144c0070000c613500014112102920f003403088458030211b4a40380d020301da10f00680d20107010302c04c000c540d208502e0010001c1c0641030a04616480705046140c2c4807080e00010046803c8400384541801c040010000080c0d407460314031682048241c000b51100e0b81032055403a030400b840400350403507580c2d07840403000f0403840304009012540c1c0d141840e00d54845115041d4a07909a08140c0820308041d021155402d521400e292203c010030001510381e500214660030401460661500004508100b00a043d241c0076580304203c50211800900d0185150482c51215032800c046544946001058030340000071800d040c1e440f107110400541407401c0707003400c0c1c40e1b1560030035000404440c2c2580c02014400d41c4c0d080f440910300c05450080064910a100f6640c00200c21000075091100551082031403e204000241c60b192600c000a40689001c3c2030a8a40365513440c800c20040c682942401d00030101600031b582082480c0c0d035243c403240550b12032040203103100c070307007620465403040d8a140516 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 75643320 1250 75642070 75642103
    0xc02010e150603160812030702100608011d030c1203040201020a0c06080411030604120e0f1f1e05070609060204081e010b0109081f090510051005040203070c03030c02 73
    0x880c880c6101100005445480c081c2c084c44030703491050b62070045030100b600e100740b0060411414245100040d40d00061101c03046004818162014a80e540510320080000c00f0000c14503010414851404540c07500b40709105c0e034420000100550070105404540890840c2c0b0700380c49036910b000607401d1881141c03004201d40c40041c1c0c041109030b0040e400c90f010f107014a0385080b19991100602d955403405841c0178020541c0511040c0340640320f00b0719074235502070140c0070904060600c0041160700401c0340b50003030003044401d13891401543c414002064011401c10840c032410101c4030103440c0380b0034650058540e648840808003171216540445001f01144411284003844d8001c404000c03001c00c0098101c0340d402c101551900b580b1501002c030603102284044c040c6044494a00c0c2e80075908183c811050b251a002c20201060b020300004ea002142210040340e1031a104584510081594000511842c418014059107983c4040458980340d4142000260403802c054186d107481800c080c9641035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 75644570 1250 75643320 75643333
    0x301080f06010f0320010e0406090b0405070206061f0309170306031005010506090d05070302030307120306060f0c031d030303160318020906190b030a020301170a050601090c02010e 79
    0x4104001a8800c51158550a4880507601c03100402d2108145200203802200c550000350004403012101a188401c141407030804000f5030700208050fa58594000d00702141c0c1c41c02c054a06081c2400b130b05502c41400e1000e400140b9050303000a1031503800107500c3d05031500009000707075138502030b6002c3e01c449500b04024515031007503850000c1c5150305c00c0f15400c0c040d00641d81e0100c0540e0320781c0900c506940004100c40d003481201018840918000c8200752030341d00c03c1040020150700c05100808400d401510342d42c400d01507596001e410b0f22801d81c4101c04100f250114001d411794420540d0441c240c0c1850315007445c0e11b0401c3e2050440240354078940c2d15000c004140308841c8680341000c01c4991786602c090021054142a000d440324070b411001e900101c905001802c503140020302248030903c0b81e109001082d032601600d074010f42041382c616540c01d40c00001440114150000544941500c1c0c00800007010240e84d03840d198207040c880c001c3d1040c0c40b64000e02025000f0340003035090861a504035000f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 75645820 1250 75644570 75644579
    0xb04170c011401080c0306010609051018031218080a17070501110a02010c020606030a060b0607080406030b040e190602090111060f071e05040b0a031116060609090b010302100c0203030301 82
    0x40b01c81d000c0c400d9411610070090500100e040c007041e49412101d29840d02d403111352403d024081c113245080c440100300550030040e003100952074020305000d1030092400030444040241c0c0504100c04410340e0305100104080c5c02c1110160024551103403640c403c4c0010001c0703204142c034643e940110b1200802729420035400d11401032240014101b400f090754000c0c09a0208240282d840d00d41c20b841c5250141c000720052000301e031680e048084081406800e0914203d059100c152036904a07130054000a910340d02e1610340b034030f403601624803001c000320050145060340c0c2c452048114658003005110136004030781d00c1c038160300075045841c1608c1040261502e0f8900380c03d42142000f022079500010070500030554807500e00312034106c1c100d01581e4944c1d5140078244a500140e0303030091340a540c2023644410401c1807082a1401030a103800d21549551560a024903080c000e58059070402c9030f44a191180160115010140d141e0450b81c05803100300700c0e000307454000c0369007903140c0f5000303505844000300008 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 75647070 1250 75645820 75645851
    0x8180f06190e1e090402220605100302030108031c0b03010e0a021f020316050c060d09060516090509040203070b0a092904090c0306080d020c0405010509040b04170c01 73
    0x40000c0300310341d202c0c044450035904200050012442c00608004421488416814042116a0041c0c0014444400c96400d403a040f58540c9500146c0351441e501c400c0c0800581c14098070210060301079040560640d0b04041207150799020b141900750000340c00140380c0e8180d00131584400300703a04c4040d0003071010008d0701c002e40e0b6981102c40001ca028121004020340401d030056412141300c8155400385161024086a4900003020560300f43c805018101c104c21041c1e0b5140c2c01440465030415001c2040714003410690100c070002440300c7c07209040d50405040960744410080b0944504035040d00444c2c80d81d0020071701c1c05080303800100ca0910009003840030260407608000880312404840f114007401058000251034141c0e115030b0307040d001030006001c090001d400120101030280380001d1455568441e42d4030301f101c40260070000da04074041074107030743c01c160042501405040d280c0b200d55013016903600803411030060001d41603d00030b41124201c110540c04035410310240320000c1c010306000c1403015 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 75648320 1250 75647070 75647107
    0x606030207150b0d230724020d020c060c0c0604030f02100302090108040209060f030a0303060f05090103170a05040e1e010e240307030503030109020a03050601020a08180f06 76
    0x29280c60700202c2502c008042c09008a2610032000b400800c804141e6941e08035150085114040c50501e4401c00c40f00703c101d0802c05100140b084d8400505d6081d06101038100f124811000b1004642101410108103a00011041d00c01c28082e41e100e40e03240071301c0f0440c1e0300b49000c04a915600241c0000e0000c14401c0d810b400410090003141c0c64010400e0341c030002d4040b071183e05900b030701198094000070013600d000d03200c0340c2e4001c1c80900035001d220303000c000203811b1100440003140401e68442051201c240703002000e0015100580c0c8003500f950442d1645a41e800f80d200c0074082480000802c004403505c05d2042d1b070b0047c95914042d800e030381400080c42046008081c4a803402d2940980001960110075551900445440700c44041c00f003009081c00d08944107160040307405110f425030000004208000545c002d0511600068030381a01100090680344040d040c1c50440d840088600d01044258080306c0010181120b1902004961400f04140d1749107084842d610504c0030400c0807141e81c440100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 75649570 1250 75648320 75648323
    0x30f0d0e070501020a0b0606090402070602030f091b010503010e1015021f050103080d090804080a061b0206060102030307080a0b060a0305040c06110d08060d08040f030b010501022410030203010606030207 89
    0x1d981000e500d44004a0761071003010400380400a4610109000703003000030007402981e0001d0300151034840305448907010380e481940d505410810503410130164007805d020007542c92250380700e0500f900461100003072050106005101c00c80d00018042a21440c04140050007071804149050030455a444040e49418200c0d82c62449c0600110106c00441032501c109070599034000d02141c2043c8080b4501c070028000500100c0c0c944104000115408034104003248405100d0000810304030303644c84060108400314521881594411028400a0f03a0080180d903801f00f01450314413180d43d00d607900c5a01800d44144282e0700035000180b0420741039403580181e8405c80c041c007034032800c050b13542e6001ca41d1101959410320f00c0b034000e051010b21503880354403101e4011000800d201d0b40d00c0350940b0b0350040fa520540c8100d41c400007c400070010450b100000600610b000d001504401000c800c404000070b02c1c601e01c0114080d903413400601500200c400d58406980c02800800a2507103502c0061300943c0300500 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 75650820 1250 75649570 75649573
    0x3091507060c08060604061b020603011811030f19060e13030e01020705060901051305130204050a0905070c03110f0f010b030c0f0303070b04031209120e0f01021e030f0d0e 75
    0x20300c2c4669000380040d41c0035040c040d120324501850003008507002e0347c0c207018030007100203090b80e42c00159480f40301071406014000d00807000d02d81d99020950803a9030350940300140c40c1c03051081003e8034024002407a48a078003c4248401945442915401001d454110074281800c0743d0901100c000b10f212484c41c114420b803107401001c80c0d40d0005a0327480105c1d11400ba0700c00c10401048500b5403040010b000c00b48041b44a5106240c0c035200002c1e44403001003030a103d860790200d0100040e20b031185100c0000c3c407190b281000306043c4004014402c14800306c0203000d103c5400f244002e64902086a103003078565010a881000d0715030000c0d24041c01010b00b549100c0d01c81d0ad80213080c2d40c03a00341a0500959401001140303000799650b5002016030000b0f00a43c1480003824103010030b4421030103040ea403d88106480300d000311074100d01400094620388021b0080c006404454003598000444243d803500103804020303080c24cd620100e103544103041041000143c04519203049040c80c1c0c02c0080040704200 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 75652070 1250 75650820 75650831
    0x203090a060c050601180204080618010b010801060e09071b1104050106050c0304031203061706040302071202090402300c0a0e040b160207030f050c0a0504020301120809030309150706 80
    0x682251280700c1100040c0280d080580100000302013506c2c900f00c2d959003d0000f40c1407940d105815810408102c07494540080c03040e02c0f904042d9401e100b00741d01030384c09013403a917410b5040c2000100010190310316103010304404000b10301400d0164010700300c1c00340c40c02e4075285442d07102d00d41750003d0800356100b140a1410a400450254041d6080c0d0340310b0f0318504011400c242c0746441e42c000510b0b0010b02542031550399178000ca0b601015040a40f400215032009000c0340c101885c00a24140a550081201c0740010250f0310050340c8280b105504282c0465080c1c142085464101001c00c4810b40c6480407901d504c41c1c00300c90480f004c509409920821103121002c259102500803902c0d000b15002407031100c00340001511104a46242038404071a44101e07103040d40c403541c4807028000500030036622a8021040300c4186d10303160640b50040d003010340d0150704552501003254a0640180c2004018910102d240b03511620704000341c0351003e000030b19803110540d408940b001580c0c8040000e40740f641c14074 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 75653320 1250 75652070 75652079
    0x408070b01090219030b0f0a031406010b040303090501051c0203130506090307020108040f03050f0403150e0a11011b0f110907030e0615030109171306180b091f0203090a 74
    0x180f0036109078030507085030f04500140c0c101045000348100300285034007180701d044100003610340c2e0310f0782d0001c3c2d4455418178902e6101c8002d0b1906d0804168880b1800040c01c1005100103980406c02d0000c4070780a08245032135200c406403000c04c60003000c2c0c1c0d0342241131001c81040718030042040441401d5018409072401a1184140c2e29102d00ca05000680410b01810100e000142e4a02c00300e02804c0c040e00e80142003003000800c1c2d00c0c03140d20070703401964107185c0190410014030240c855000c0c0040d0480042055424a40d548a842c22560003c54107120208507080d2410790810780030000d20364401102c0c0c6090034641350040303401500e06200c600524140d00042c03c214064407903100286a2000240142d40d2414024084c081250326020b0f0595240d0090b82c1c002100f02750000703da090514a0f00d41c0764403085190001c0e40c0301c598032440800041558482d0200030030308041007501c19000c5400c0e9902c1d030040c0851100701c0542225003030881005054605140d000c00500b81c00f21086600c4403e196a4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 75654570 1250 75653320 75653339
    0xe0402030402091602030c0f010504030806012c0111030c030409060f0f150e04020c06040302060a06030804150915020a0b0109050601120c0e1908060a0c1b02010201060e0408070b01 79
    0x1110000e420030b00b00000318075250280b40c1c1404031a0a98070480c3d15006a8401480c04c0207484230300b807d1141c3d141ca003807008054000300e07d00c1d80f000d8203181c19002c40640c003ca580c1540c0c1e05902540c141d2243d074103002d40700d920a5802c54040141d00d42200d07031f6481c50349241c80d6a5441846101030b8289840b5002c20a00d416901034000c81d03404a4030621860f040c0718400e10740c81c1c0074107100c0051206984114586860358006440751071f140d14007a100b01e2030035050190920500400d5003006030718194060002030310303040a45059655901c00b41011094000094400410b9500550045040d45401c0c1d00202d03400107000d80e40c0351003920000480d907030741c140620680e4803e503907807400b150500e59001000091940308041905940c80c3c880c44101880c030208007012403a020000024041e2842882100c0c41000b0446e0400d410400c10098602c0004004004941d044034446040c010104503a043d60710035080107000e0700c582c000102250400f494202401d52021008a95088070031000240300c000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 75655820 1250 75654570 75654577
    0x10090f0522050c070b0103061d0c0d0b04170301030b0901060f0e070509040617011d0d020d08040c0b18011e0e0f0607080a030222060e041a120d0e0402 66
    0xc1c2044210110760040c1d00c0002501c00208401140d00c0b00f40191404643d560305228002d41c0035240006007036004d1000c48120713521a030880500d03a4003161680105485900c4007002042c0c000710110110385840c60110003034805102500800e04010001005010380540003d02034003e0300000c00c10650b03501d9039440169044c3c850060381c04000d000091049028100400c20100c00400001d042610381b1004015980002901007880e991003003038840c030401d24400100c00c104484014006181850360007595102031070303480c60411807064081802c0014a154640160048540b015210000c40ba80c46090f510711072101030026036001130490486070f840106201c01842c0b5076502c21803514030424424980c00d14191940c11443c1040305a011034401d1000c1c002803200350b5409a07458810829500b2202d941551071914002c0200042040d540c1152a1a10660003600c000c110714501d030482001c54140e1080850300071fa107580200d054080085140c001e0134101e510b81c004089511004d0104900 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 75657070 1250 75655820 75655849
    0x201050a03020d0209031005070210090f020d020613060c0b1312081b041202010315290705011803020106060306060509040207050f0a0b0f070507080901031a10090f05 73
    0x2681005845031041c401d4000345450451501d001d40340c10503090202e86405500d100910034141e5030414842e6540d4144200d40804176407160a0002110544803000040524013009100740c0280040000310340f106000d95034552450620b0301c10381569032901410516000c102100c0c04403d0500045400407035503240b02c1c00d15002000ca02c0c0c0800783e07401c00d032982800a0251014414903200c400280102d0f440104060100c81103060b6441800388000760a850040c55484c00c0c2100c61a03060040b80c00c00c0800749503c444a80c038030483c0c0a01050b0628591091030800f815650808140d4000706c41b803035400381d1000e0701c26402045482e50750030003241101c00074028030b0001003007000740304a50320300398000c2d1500382d0084007500e0b2921200101e1603c2d01c1021724084480d0041c6500700301031300300c0c00407e00b64004150b04000d480c03c0700b2582c03800c460748901082d403414540d42e810020400a8a00c1d10280b03100409031911201c03c000082c080c15003502c0e032080d200f80003041c440100f46070a0154900b840301c03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 75658320 1250 75657070 75657077
    0x1020414060c030a0c0809040c05180307060804120c0b130209071d130e010c020a030912020603010509090109021e04050a1505011d0301060605040302090f010b0f0c03091206010815040201 82
    0x50130100c112900e00c100c40042d80c4204061080c00d4260340d0780d00c40c0700320502d016105c055882c0c2c03507602c1031500d40c40320b9005580b21b600314070b10411000d5040b071310481e0f026910420b413040b00501c103e41980c100d0a580e8020380741a80c2078080120300d0451501c1d9502070790003241c00030026910102c00325440d0403145041172400c0d200c0c204c1ca244d142007800c401c10b1014150b0801144481480d84d42d2400c40b40030451080040c0c0c800d5800ca424142c105418002030504c24504c00c00c084e60b00d8010614602c010f204d200d00034540103001400410082d0f108180c000d50003002840c00800000ca8400101441014244154a030601003003802c0010f02c501102c3c44080c030103d140d080d2500c001518241c070000b0180710b02486444214200b9503003841540c000c0c101e9600d4094540b803d5005001d00208001c1c003020700010100010f1003200c4020041d5640110a132010b1965900018092420340c090744c1910745e0801543d400700e8040d038a000c200141030f510040c04a841c01e030b40030041103603c01419500079020 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 75659570 1250 75658320 75658327
    0x106080f060f0618091302010801090905030a110a0611301302031e0601090c030c020a080901030204090f02030105100903031403070e180702012924070501020414060c03 74
    0x20f06004001d0400c006081c0401074900242c0008035414003021a480c61030084500480d000315a08801381e41d0142820302c134104225885aa02c1503907038454407071403005118a01c481800c8007402007166a41159022006110f9001c1e4a00c0080098001a9020404081c0b140b00940c04681d20850070303031100441c40082e015901c414021160034504a03006030380500500b00d0081c405007040640005900003c00200219850141e140044a0380e011900c8201410008a03034205940041e08010345034002d140b1980c5c401c0200010b170024466a40700a100710b090078007200d90300400742c0c0030314100c80d41a602c071404000004001c86500f140c9000040101c1c0c0460b9034a90002e0011003d10b5000d6618100031070a44c180a00082c0d81c1c0700c031040d00c801500710003c2009050359080c000c60700d910140c00112002a1110007010300401d05064011740603156940c0c82040c04810701c0030a6040030301c1c01c01001e03580d40140c103165021703501c140034008644507a00d000c6201818540b044802c1c03881810040c504 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 75660820 1250 75659570 75659599
    0xf130b0103052d04060207050d0801050103110306030d0e01020102041a04180c0516020301060e010b0a0207080610060507050102090405040c14180a02071103010c0216050603040503040e090307060609050106080f06 93
    0x60b502c1c0508160340c5ca0b03509000f8400000d00401106414900313640300c0304040d43c0350500040640e84030140003010b80d031090007404115180054a40c0d08010a8249800c0541034100101c6c02800b880d070155562055034a8215070b8406580c000b081a10344580401c44e60344a01c05900c82550003030951500041c0d0200040d0b400228110742c5941c02c0343c4010004280259104210400c4020a030417401c190f4500090004955804000040c001c0c07800301d01034680361074400051111042c02e48501e50601100045040c00c01403707604491405000810802a5040900f0308581c008002d00400b01d11250547ca18141071402c04503444100c1f6070402d01c01c0c09682d800d00d0840194000190840d003c031460000c0c480c440d6028090741c0d8241c070307260340208102d2503010440c20030000303164007035800341c0410001c0c007000c140d020045030280c480c000340d0b4441d0380e1250120340d8034501c548076001d8011032030900c010601c0310310307908500c1c1203815550710780715140c4803403041100451042e03500c02d9200811060200 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 75662070 1250 75660820 75660901
    0x210705040e061f0b0d05061804020109090207031e0e0901060813060207060e07030b061017060f01091a040311010e0307060305090316050a020a080a0f110f130b010305 73
    0x1482c49003060f48546800d9941d0036444015005010100300d005c0d101c1e420092107040005800c1d040c0428132061003420300381600040c11143d01c5016803008140c00154003000d060280c0c41c0642c28418006c1c1c0340103c0320003403600420388d25441440c54840d88a03080001900d40c81094118026440007442022503801e46d540d00c80254802da400700d60550725101c600b0401c1c64288907082c010341c001c1c0300b0031559150490400600142e0f8051a005010b041d0b15011118041c05201da540014261503003408508941c4c0140d41281065118600500c504005a010400404017510031684206212000905800015204480840c8c14a0342681c40308900b0410340d4426000140c20405150941b40703415000e2607800c103030069902c000d43e4141c0c003980f0340038118241025500e009140c0800038084402044d95869100c102100303005d45030b00001c1c60082401c1c1d8401c9040d0003007200081003264a010168004400742100e41049130100786020000f41511001e15100e0210041811880341038405034440070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 75663320 1250 75662070 75662101
    0xf070c0309030b0907050103150311040b03150702010207020f0a082e0e150601090506040b0c1e061512070314010209041103011a0f0712020a02210705040e06 69
    0x19000c01c07951140000c045a00c04494500070503d0a010308422414180094241ca850024a000c02800082e0400104140e41c0b15030b1503401741207501049004008000034903084072402c44180c1600701c0018024510340550052800b60701c00d580055000000404010307a041040c8110420b0340c11650f40001d44d9100041010000c80a0840220102c035840fa0b00300120f42492a4811542d8401407022215000204c001c3c1d52200091820300f030045d040a02180340d500444c030400c00c240c01c022074401d42c800700034444080a0310040300043c40d5922040e410701d5a4079002c0e00e6004d00030010303251024260500280d00340d8809e42e071000030048d0070b1550340c1d4680b40e80c0c1c0c1410011019582405102c003140e13198061001420b440c049200d8482d41840084c500c9080c00b45a9101080704c200009803403c4501019030320b0b680d070000b44500b02014900401d1f400d10b0000078000703511001c1c014524401c0300c40045038010901c1d511045a5000e52120240811134850482d04640741e07010100140b9a0a0030540c170 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 75664570 1250 75663320 75663323
    0x80d021c050108160605090414010f030501051f0b0a020304230f03011109101412160206071b02040f060306020a0e03030304050c15120103060209010e030d08190603020d0804080f03030f070c 83
    0x103454846100309c1c003000c540c203800907541c080d100340081051220034000c2a4000d001032075400b1071100c62901d40a08030400d80b20740c14a00102181011071a030081c002c1d1801410610f800d407400e4105520f04102c48080d501010703214559042c04801e550405100f14600800b45078840d510b8000750008101c80a51111070003410042110300c0c3c18081c03001c140142c550b12114088000090500001c0c00040449031842502150300c458108800d0b035030300c000380b021310000206010700140e80f0380c00814050010440b08024003401e05000008201f0a036004111252030b550b0342070669420302081517181d01c400e4802415640c0440560f0320b451400044071007100d40c0749600c00746401000100540c80300c000f40c1c401d6684c1980420b218050356046031150740c03440000c8010300007808034042e01400b80c400c00b420003012441d810b0581c3c950746a45900100195400400945060f9414608100b45a0290280c1001e41c0100e00e04802e590300000140c070f000320202c00380ca0907140e0b200310088410b0f15800e01d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 75665820 1250 75664570 75664579
    0x9010b09040603060e0c01020d08040312050a020c0a0309060906030902180a0923070b04030807060b150c03040f170d0c0201030b0603070305090c030d0912080d021c05010816060509 79
    0x800000580244150280c1c40840c5d00034040040c0c060700064105070b00f000301d81041c400c00b01d081200086d400303240032100f405998000100b544801070ae41000b4000c59409103054850030782c069052540003603505003105c0560b039501d40d03c50303100c07001142980c1e000c0300000e402c00d48403c0d9500400140300e12095004c3c0d14001c0c0011b036003000da00d55910420a99070780704041d40403944003002c804410b01440d005400e800502610300751540daa580070341c1c41a4080505410754599000f0103640d500e001880c14060025001a00c0b5a0240c60944c3c407039000740300b0580c1d00e02c3c03500c2000036090312a03d4000ca001c04820301900c1d905074522000d561800f4240c0040341090382d9103c038182140d45240145000d5907440d43c0014951404031040d03460a1151484544240d010b600b00c80c18240c0e10005072800e0398440004050360b42c0300b916101005008110b10341c0c191a0000c034a1080d072911b4041358000102c1000810700044e41d907120940c5d03c600384e01c912002210fa200d5424488980034400030310f41140b000d030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 75667070 1250 75665820 75665831
    0x2190b090103091b0e010f0803070f080c160803040e0a0c21020909040c030201080a090b0a0b01020708010203010801020c070f03050601050402070f0b0c0c0111040806010302190902030c03190b09010b0904 89
    0x182c11041866583c0c00c114182e0391004018441c4080810b101d00248c01c007040158548030f20754807405294500c100d8002c1403c2400200c001d0b6603c41442156080c5480c04000e801640c0c0f542038454894200b4010b0b0182c81c581d0b00300080702e10105000f00300e00104141c54568961624103111384004080300783c103500e0641c080141107116216404010301c9a4060b441414a240c29032000504944001c2e0100614506002c0f4840104411060b6581c0000310034a0024a01450b540140d04000d0245d00907001544044000074130180190001d050b04070343c01065480d8187c65280e44100d0200714000500185d00440050019003401d500400e1003600a20750200e116903555209803441e14129004064110046a4881317141000d028000f84000c030a401c45003864145818150799480c14840079204080b0790000b1130034a07607003091110203003520900665591400614400c4694400e0340c0c2c2082d035038000c4030400b9001c2080d2103480c80c0e007400100b1250f09a460301c0c403590344540150101c4c0354865500e4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 75668320 1250 75667070 75667103
    0x906090921130605070c091802030105040606050102060106090e07050f0c100f06120206030609040303020f04060801060905011409010309051f06031a010503071203030906110702190b09010309 84
    0x5000d07190001d001500295503582004040c4030080c04580c0c050010321006000c034000040c03000e8103407402c0e00e0804900291448000501110500100c607010350994a46001d100600c40c60760030501c1520000e8003181c1081e41e90350012126078074540b058184061186020500300c910840042484115a101d0182811001c003142c0342829185194902c00c2991a41c10030803510b10742c0a81c80c020858151000e5aa071082d0300416207520004222a2180102000260415022f68150b41c1000925120b4680b01c649550001d814a0b01c28000c0c200032803113803640016198030602c0c42c06241580da001c610b0600c4103400040d00580750b40b400844181c0100380380000c1942300300680b610003034190480810982d2650400c1d105c0c1c16029451800c507255144010300c40c036100041d03000c007111246c01132203078189203e04084000f0600000c0003054a4244044a1801003610000d0300c5054002c4508a00c5010710103d440d036003111620a9105440080c0402c00c5203600940c4050300680c028035100702d41c03c000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 75669570 1250 75668320 75668353
    0x20a0602030a090803090a0b1c02030103150605030d0504140f090c1c0b06161502070b06100c02031207151103071101020f070f1401050c0c0d02070509060909 69
    0x1590052401a0700200c0c00008140e40702c040400100346520140d80390280403800b043d1911040c1c080c1e200990400101451000031000d41d107160403d04000131500c80d612403038903e1090024840a880890504001140705d00d00411554442c50395a21101e00d030620f00350320786213049a003a84036584030911250840e07031901c0391400c0c14450b51881c4d809660b00c901000c40d406403015041441e246107494041c01010a407140c0044426000501140c41401c0d03d075458602d22051702d80880783c09030b500110740e040c100700c008078905001e00d0702116070740d03040342131401c0860381840c2d20440654103a0002d203101c085014404c00400b80030307002e07409a120300d2416000c1542510b42150310210894070000c00c1110199020400b00d4100c0c4410009500c0c08170f0310890070010340143d50f0050700910800c401c042c100000141c081040c280d423000280803d1929152009141d08103a0003204a070140b010040f088038400304895042c0d94008081804a8540e0424002ca00720010b14107030252090400a00a40c0c09 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 75670820 1250 75669570 75669589
    0x5010303031b0f09140d02280f051503130f050d1b0b0106030507021617060907080c010323090105150f030618011805030406090609180905011b050301050f06031e070c02 74
    0x1a100d035625601c4403e85218100c5404c83e84407509c20b014200e0207100d950f41c1ca10480c081e41c1c40e5640815100d8540ca034601001c802c2241c00108041c4280411504001c0007207403103540340800362170350072045030719681450301810600001408201c0c10350040c04428020780c85a5008107482c811590031110a140c55904402d150300000484d8240b0210031031002e2042201c1540065504007508246142c00780c0103070f80d550025800d90505484482403420052900c90090b81e102e24090481014280030240d68001e04003520054070f15000d85003040301c40d0500100c80864030700081c00904465603640d5520540d5000071070900d007a55240c51218519056210460305800d00500145556a1821601808446080c1c0c006028042080070401944c516183c2c00d49510b624205c1c040b81c0b020851801600620070040e9080700803a000fa072640340944e11a000d1810ba802c2075800703500d940340003010003119001c2203407203184032510122241c44180007010056000b02844c24400300c20441c5a0006840c40b5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 75672070 1250 75670820 75670849
    0xe011103040f0807030b010b0a121e050a02120a021c0b060c030304080d050703060522151202010905040b06040513090501050f060415030323040905010303031b0f09140d02 75
    0x504c0030341d090092007000c1d5029401464202c00c07640c50450a500041c0ca10301d0a2031101d503507070b59540c10076102ea901d101c01d1301c8044204003600300714601d070940c0014002d40111149264502040c2c0002d211582540300301c03403d900301d44244c001a03041c48074000b0f02a0003c4545150810400d025040c25181d00700042c60185105103985070b211640488454111503005011104244c2800c40400c01c4d07444902c5414052528800c0c000ca82c0740d03000320580c024082d201300403a07801024180c000303049800f01c014107416a10036070303502560302e030345004200a03915034040017a48400c04200800c6075290540454135000030840c0d01160441050703c40c10308484084415070004214002001000d181c58800c90340000c200c85520b018003811514010126074552294a454008611005000c1080c100540c0c00074035910000703118039a180e1030b0007000740c00c5050100301030050b181002e800c0036000e1401003160394659914000a00e161002d010308400780c40d0345103070b0001520800e070409030310b454940c1103005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 75673320 1250 75672070 75672073
    0x30706020d020c250b0d090503160510051b07020f030d0906110f03030c07020a09050c070b090303041a060d0204110706110f0906070309050d1a0c0c12070501061215050105040902010e011103040f08 86
    0x1030040303080940c01c00c4008902a8640dd01d0601044498520b13814513441000b917413080076841b4200c6101250003014064a803a50610420426031030b140e40c040c500d40b050f101141d07107800c0d1541c40d00d020282c8d200101c086120b01030b0828400620900040d002038281c25000500e54049240d0301c038100d00403a4029100399000c20000191360040c02040d4602503081450f0500461461900d500c50480e2901d160614810700003158010411130380e210174542d0516a0000d2007080a5540b500300e40009038091a011a4181d0070850b032b03001180380200036135001e030079600600c6244c07108031410000e4503032000004809110130000701242035220340b002e130800c0520506008112540c02d0001040605004184402442d000c0000c00b0b01682c1c0882d409807040400501507448601c5898420f01401e40c135042000703185421030312807003072026004c101c017200c8400341d0701000681d0721340b010300003038a440f5903020340420301411865455501c0317201e10391400c030104001d486c1425120301e5058410401135000c91102d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 75674570 1250 75673320 75673357
    0x3030509120a0f0f0e0406060c1e12080402060f040e040311061902181008040b060a1a031009020a0e03061f0314030706020d020c250b0d090503 63
    0x100010050380d0302541c0601001e6092440b14400101120191650f41041048600001100c58042d40701900c80381e50051040c4105603c1e4207004080310241c520503585180c02400c502044940854140090b0b40c0210381000140c00c0c2d00000d90701900090700c200d80241d02089680b1502c2840d00241001d0041c40c007624601d401d01c0d0400034524050354a0020603030f00f0090601c0151011071b1103010218110f0103015032604804944d46000803c1c6284494200e00241d1005c0710440c0d0000500340320300d21a9500b42030300d441d40018086a000c03103010383c02d50a4510001c00119401d040c0c0a1030344415826003030b61400b1386403082e04050360094813400000c950003d08098240c5014458240e208084005000544c0b00104000c2d41414891001034400d0740c4803a150280b489090085560554004034195030300e4501d01c41103802580250a1200c1c18052106510b240302612590005207495001600220b182441ea09030b0040e0300004048041c0d0355900b2020000400c00c2c0050140158044c54000c80b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 75675820 1250 75674570 75674581
    0x90a021c14070e060d03051306050715020f0304030c0819050904060b120106050f04090510030c050906030604080306010201140405012307020d0c0609021903020f0402090a030605150904030305 84
    0x101110714100766020b400091050048031186140d00342c0c803c20884010391321103120304098640c1e118420403a0300444042002103103e54025004026852090142118003040c0c407400900302e00650701c00030810001040440d020a11031204640c482c0d00801200d4949180840889001c650300d80c1c03001c02242c00400c1c00e000d246010305c40c040c002c0496480561900261751440c01103100d050040e1000c0c0100401c15007071004c0701c1002d680107003090100030055414604682010349078203100850b1041c03043c110114040c100794215500500c0090001c0c100c9071101e9841140da40c00c0140094110f41d42c0b105000b0200c3d00c590241da008a010f5000011a0303a0307404422400b4120078488030715061492024072105990008070350620b004a407400120841c0306c2d19201001d03207819440a984903a28001100300301d1000d1001204692017102d1b0604003c40358000c2c0804e0b4003031100c0315644101084405c0010850308c1e041035900a90780c54507083c2c10101c000c0018085042501c0a4000950310800c019 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 75677070 1250 75675820 75675833
    0xc100b09060315010b07080c1204050f0f0603041112030a050c0d080402060301030b04061d010f050601020d05120a0b1005030a111c021803071d0112020d0b090a021c 72
    0x250070880590241c4454144100103511801061084566000d00045c100041c401d9a009864500005005440395506000d0120300310713801c00e00540d03110307003100100001d0a00d02044e010030362036800b1709202c1c11a503554440c0c030008104142240d4100c440c17940d83c0c1c00307014001d100402a85c0516240c40c0e450b404041100c030310300a0f110390510b05100d00c40c420711001da0345000580e81140d50101e03244445680c1c0b454410301801c0c600182d008030314080140d850011206400c084010601c1140801540c1e540000490342c4030040303a000e80109008002138001080e0039103030154004031402002c0342c01a940380100e020801c85d07014400000d2404001e0142c5100580240c11240c400080e0082c1006103441203030421400e0b001280014550000da141e18213050721809610510b00201524507403684c40d13004851100e840407003c3c1114044800110700c00f41c6102e07c01c119160013920071020004141d1b10010440405402c2485600c00e06003a000180e6401c103202a2040300382c010001c03c1c0400b0728100307 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 75678320 1250 75677070 75677089
    0x90b0f04031b050a0e041406040c060f0207260a0f0c211203022505030d060e0c07060b0a090f02271e0a0902030f10080a050a06020f0c100b 61
    0x4000e0182140030402544e0303100d100f220306583c0075506685032500c461909a03031003d00c401e1001c40d0307401850b041005001d44074a141e41211040d480d00300014076035903070481e1105090300441058081c42031903401c13030180001d0518150000301d0115904902961203020141e907004008441500720208184180b0b510b02c26a186880030400480030b11150030740d50a600840e1a110f107004050740410320004602010070f05420031480401c1040f540c0c8500c6c1441601d980c000e0580c18030704ca05011001908000860341644116181c00c005800e00d21180e448002400790081d1450b0320101304e03d00030440b08214411000e50300e26440c40141e41d0102607501103c01d500d42501c50010340030043c0042d180da00c800600311f81121440d80343c2110380d90800f0002c0c0c4110400c0d00207502c1c240c400700400c10740040045059016210074002c43c0d84240e0744080031075031940800030003402c82d00002440e60002d0040d40107000180e00d00700c1c1c00c03400e1000c1d2181c203c1c6411103003000921060b0f1a280101d01609000d1400b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 75679570 1250 75678320 75678353
    0x16060e0607080a0302131701090c060c0503030604020d02091002030a09060905210304090f051e0405070e1308070303021314061803010b060a0206041703041104020901090b0f0403 78
    0x1542050450380b140b00700d60050038034420a050300091418098441c049044003e4161b0f204646694000502407074020808020102c1e58841d0100c40030450710b000707410b00170a00e94840c00075441c2d0340d034040a00c0084d401c2001000d040e29001c0c41102a140e5907035900d0407403064161700442d11201100b400400c0c0654603440402030000d8100140060340b41c8403a110034841c3c3c00000300d610700315114021491803160383e0080030424034104d0502501c14151300543e009822043e00010000035031110400c43c001c0540703009040b42d01c001c104015200e03215080540c00352030161420740d0110507840740c030a10b0f0b004450440000303a00007940502c0980155581e005009004203805c0c1d003070040c001140d040c0c483e8450050810a40600e1008580d030250800010440c000e040a03844002c00d00002c0e54980c82038030211000417482d403400104400e03480590780b05603000b10391803107002152003d20000390b00907040181040300600010400304002e1008207200d0034040c40041c2c0d11031131400c24891001d100c50030b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 75680820 1250 75679570 75679579
    0x1d010501061806200601091508010605030a0b07030902090f1f050a050d050c040609140c0f1b0c04050403050307090603060e040803060a030f03020c01030c05030f1b0c16060e 76
    0x341808042c103021480064030030380e05080b42000e5041c0e0300800c52404602642d0f805108042c004075540c0b510b500070680c01f0b01099228201c06488203651820f88045000e0a03070541e019403e05804910f044c40d005400407128100014182a41e40201c3c04407034003100d10283c4005803805200d0500418452040782840e00c09aa0003200c2c140400240784e559140314061003802e403108400c0c00e215080c4032100c0385e0703400240204483d95480031100040c02a07030504050218903a400200e032001f00c14229040900b142001da850306105541d0144007817500c1c607200d02ca074859610007440300d440ba44651801a80a911a603480303107000780c002130100c690351704200700701410160100580300c0c3c148002a0001c1d8800643c82d242d503248000b142c0c02d10042e44c00682000c10070040501030580100d50b0544050302a641070100c941590f000790780d984070a5504a0035401b400300010303254814074544900841c3c034070010302e14040e01401100d00c0c24601c8440c040c3c01d035480300e40070003405400c894142d901070350544 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 75682070 1250 75680820 75680837
    0xc0c0601030f0c06031401170106090510050102010c05030106050405040207330e1f0c02030f180102061302130903030e010227120d05070519030804020111121b0705041d01050106 78
    0x501e241b15046040c42407281c200621001203043c400c084d048400648858002000705187c410a00c9468110074481c1c240035520303040710414054031610450341660100d440e9a0324242c03400080c04020360200509840b100c1c242e50600a0b4000700d210301103a00c60300c02e01801120444556450125880c42440d849240d000a81402004540c081d406881c550101c10005030703880c03404016800e41c459a07000c3d801170040098000301c040310b11441c002d90f4003000c0c0e007154140e554440403000640244100a13500c2902480202c115255607080150128440e180108803680341580203420380c2c000b80d02280c41d45400e111644214800607100751080d040072038041d0f401c14219500c80c0e8982001c1262642045000a0b04c2c1007072190400001c0c5130300002c6042ca18104009081c01401c4402c10341d403c030b00160707007404091201e0900140401c4d48009014900d403801c54407016488100c243c03007803c07407114014a440010140c2c2d6510a03803103409420038587c900614140d0145003110700c1600410705204c0c0c40d4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 75683320 1250 75682070 75682091
    0x626100501080c0402031803030906011701050613020a090306060f090e010203040b06010c21050408011802010e010315050d03030e0f0a11060c010207051c03060e0f0703050c0c0601030f0c0603 84
    0x182010650f501600e006a482c1c0f5600202a488180400c0b9070707116110000a00c840700100013840d604840c0400510f02030340c001481d0441c00c0c2d4405884030baa00c81d001c400c0c003200341e12150740104180c41d25400c0c030805117556a91004103588a82e07110159501c000201001204001c0c0551141c0c0590341c802185140341695821800740c03009002181042400382c405401c01c0507480104481003400340b000f02c002551044028901d901900411885500b409e00c1c0c41c240c3c004070075501014a0781615641d5103201d6400045000703051210030440b4030803a9a41c00940303901c560b400c08a485000e85d40201b00140103000e0f00e46043ca180042844c1640000300680110b61070200f42e04c5600300403a1645e555100e5403501b940680036035103000c0c105000740e402141020000c85541c1c85d00400740d4409003c4c0c00d50b1520703642c0c00440c007220f060b80260000400624041d03c29030080b5448030382a6201c074100b43c19901c5452506109030003c07101465994032003414449d000e180c1e1401840c0c0d0385818040014072 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 75684570 1250 75683320 75683323
    0x1b010603020904240218010306060c0510180f061a09010b040e061809070e070903050c0411070503030a06061d030a03120e0d180602070f03080a03062610050108 70
    0x10f00140100e945424845030742000d51a030001d11302d01c1e04100b0364541c001c5600d445501c8103c1c0030064080780c0b8180001604a0140032152101078003c0d0107880130b9601b50303803804080c1c0303080240c58041e070040004900000f2848050744503520b000d80e000190000d1a80103003006102907059003840350050b000100b05024042040b14150740c40c0d130403038103102d4982001107446100d0b06000d2918050401080040d903d20000b14402180c83d40040c429054403984001e55046100e07000241c42030300709100359038403800c098100b6840b018902d80e5061400304581c0b945400c5030030548182003126202c02080040a40c00404001680d46112400585070051800240d480c2c048180040a000710202c2d032140c52503503a07000090100307031a0103a5404c0250800000d1500100c0440a40e24203c5c0c01004a50288000354100035242c0d05400181e000b815038480007a190030010f03860042644480000c01e10040320f014591080320600110b0240d40070740100c144c1801c04180f0085511844c1c05c0041000400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 75685820 1250 75684570 75684589
    0x200d0b120a030c0501060b03130201030b0402250c031a0108011505010905041a0a060c1a040309031e0c1403010b090f010504020904020d0c020303040b090a03080105011419051b01060302 81
    0xc0c0b500b88800405214a0701e240900f1040c2d02c40c200301040802045040707404c8000650501c0d00c05da0302001001c2103801008102c1c000d40800c07200e41c08000303180700100207141184c0703800c0398081c81c0e441701201c1e0740381d031070f140c4842c802d00c40030380d0800e1610010400d0704424001d01d40010705004503000440e0505000800d142c0c410710816204a0701c0e0000c0144c0705940d640f2500010394040d107441c01c02902d402010788010b581040444083c0c0a03181c0d174002d05842107940c0c5005650680c1c030b40702100d140d51105040b041c0d058460b40001d540e00c10000d4001920000068010301d01e06500502200c0c020b070425086402020319035002e19450810028441150b0751002d054510480703005032075581e0103000c01c0c000c1c005d00b0705c9801954513020352080c0094000001e10f21a070710034082228a543e540f87c006031512030f000c400402040e2200c005100f998025148054038240d680751480c10328810030b000004580601c900794001c00c400040d1031018003844010700c400c20a22a000380038141c070755808101000c2c0c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 75687070 1250 75685820 75685823
    0x6060303030c09040207060e0d090603150b0c030f070f0b01080604050c0405091203040b0f0610050304020609040b04050f01080f150105040b0609090a0209100905061206010201200d0b120a 82
    0x500000f414401c070360301c5034184ca0000b0341000c000c114000c0c1075004d41c3e56a1080d4108c0501150b80f0300400241c4502c680190000710f1021500441c003a46081ea181d440c45e0441030940f5840d000c144080090030240074040c1000c240a9540c8800426103804c01e000b080b101a0000c1510350880010480407820000f0002ca004100761030000b00c1e80d44022449040900d15542411142c900100b400107100940001c940030b080240d800d10164ec440404000b1005840303101d480101e4401e000085c05898480041c01c40064094801300c0c1c0b4400490001c1c1c1202d40032103a003446c4035155401880003400c02c000304186407000300000c00c0c540c248100708010b4a941482030310700c52030701c800719010107071100c0081d180340c0b0101a120b02c03058109500c020010b50401480d05007e103406800043c069413007050040201c50000d03200a1a102244468040b4080700502c0c180c15076480d0942c1e29034408076031428120148095101d5a00d500e0061002400d0394016201288030780c96010b00a20314180108070f03140d0302c5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 75688320 1250 75687070 75687091
    0x60f0512060f0102100c052203020a09090f02040908071b081506040e01020a0f020c0a0308030403081b180405010509070906110f100c020d0c110d020f0402030718080606030303 77
    0x810b20600100d103000010012481c03083c0c24020b681a06a4221002d030203e032103003d40c02008a40340d032407100e0800300d59100195210345500c4c4100000000d40e40082e40c218065052000e1803a036540115058a02d0503004940e140c0000500505010040c1520b20311100d10521510800d4075003640141e0315145c80c10708181c4180c1c111301180d21580c655104400e040d086000a64030ba02003000c016041c6400f00d0500000350183c0d042c4503020786041c02d000000e803940001c040381940c640340c804580b0004000e2450b06039040001c58110464ac0d03c4014004680140c0500d484900e107000500041e1041030303101c1c60044080b0401d000c0916040710200040c0c443e030b4980081c0100050a2161078a1030042c00c01d00c047c09502d002d503003183c419030803003001a0019000c40b180204c5901003107902c074028810291a180d80e10380c080340d10703180800f0303440c401a000030b00c0000e110b440c03e80090101e0740107a80400106070b08101e0300810225440c1500d00402e081d9000c0c02040c0380c0b007400b00b52a032000401c0360070301 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 75689570 1250 75688320 75688339
    0x3090c010c0b1902160c06080a0204080601060309020f0316050111060f07030e190c090e0c010c03030e01060f0b04030209070507050c010c030c080d060e09120702040b0a05130501060f051206 83
    0x70303c240e0f410348855107032004000c402c00320541405c980b017103039078001c400c000b680d148000b5210740b55500071a411101020000c12240c1c0c64507504032700804000c4002c0741d100042d100ea0721000d6400700500303ca0107011420301c1080381e140400161190600244ca11100e402582c10400c0c0c01100980180e8019064107021483c401c013070341e9440c00d110054460224010b501c2c0e17100001e03c5030100300f0509031000c00c0300c00c001c1c40c1d000707015641c0d81f03811403011395000900c1e0b6040b500c0004d100342c002c07100c04480e550010401507107a9081c200080115000081182d00200f81002989000850150014040e0800034500940c54860585941d440c82c1441d05200001c4105000c1500c18488000c2c2140c0144d210b03070300c6458200201c805444c1038030654902810303180114680762400b2a0010300401ca44030400d2500499900b400007a180042c5140c1d0b004814030800607007a1a011120021407a840d8000207a541c1022405490710707805107200410443c0c1400b140e1b01030505c90903819040181203404206 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 75690820 1250 75689570 75689611
    0xe0d030c0b0f060f0a2301050f0a0c02040f0c050d1503020d0f11010e030a0212070506041e0608130f050a080f0403061a180a0f0207030503090c010c0b 66
    0x22109204a00200101c03004410026501c1030071103154001c003003c5900b414a140503030200004644607003e41840e507120320320400c00141d4940745144101006041480c00e184000c2c1542c146034029160703400c082020410118110328143c491404144041c46003002182c400b028000d045028203c6069680b56076040b21094036812040350328015503000b40021f4601c00f507880c08000000a103101109c4c55011104200b14035030049803400b200542c081d0040c0340502c159002c0010107004486100d80380e001c0c4000105d1291564801880684007140c00503090401c00c01815641b14200d40c450010400d40b60180040f8159030400e4890341504052180c5020a040c2050303420440c1d00440100042c10002d104511100d204020b401107902900e03003001204501c2d0b0b441d10407004495544c6030700c1000810107884041c4411841500700d00c1c040c00000c0e2003140f40c502c0204984c4080800d4000c01c030080704001c80c1480c10040758002880a1030314100090065542280000010b0211045c1d590003120500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 75692070 1250 75690820 75690827
    0xc09100e04080c1b090a050705180d060501030c0611030a0f030f180b15030a0209040318030b090106030b06030a050a020f04020918040507061d011407080a020106060305070f0e0d03 79
    0x316290444426a1560b031a075540c91013541061194490213059404002000704165100311403080915880341464400d080401954551403240c000e50300600d201d1899010413541e12945000e14802c2501510319400c014025200082c044800c0303e0039481002822001a40500245a9180a0b0601194848a204031030000e4a40d03035060368480007506401d0300a0284018002e40036001c58908080641c1049050640360511060701a400101100100d400284900007400f82c0b5041c000c20394040329243ea030b616105100949140d511691140004e1003807002c00b403031082d0001d108400604c03803164a551401c0d1911039017103020344950303051061b400003916160101d69103800000c094070b0060f100660160360321b40c4141d805032000d00c208080440e40c1030051040a9030604400c01550b0310303e410200440d010104076490b80124002800400d001452420180c998030354030303800100300a400c03c84003d08941b802001c070781c01c21074400c4200401580291103ca40382005583c8004a40350906059 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 75693320 1250 75692070 75692077
    0x721020604030b150a0506070209011703040e0108010207110f090406150503070f030506090303060604030f0804090203070809060c04050114090402091c1106190507150516020c09100e0408 82
    0x81c00c103e1400b03003044107507140d640d418000c0450841c0c400d0502038403a400e1114902800320000d4100300340100500805401c40c50100c1c169000c03e049074602500d0703e400c100404402c0e4403c03500e42c0c0d00400caa40403c410a00c403403d6107502900c000010b9450540011400c0c140640040c0809540344488014849890840b9010300360240480700c100c0d40d80c031020441c0c10300b0783c84140d03080d005200c00b00d42e80034004030480703000d030704c00800090038613095880b800c220200c40d903403c48003200c04010001e00c641142c00a03622400385611940c2441c40c040c103070b4905000f0001c06601d0380e40d10410090280da0b82001d2440300c1d00070f800455585a01500d40420024070440c10a66070000b0056044980707000d02c80d9050a4491003540601d603a100030a0600955019403050007000d10f001c100300c00143c40c8036a0242800d00d0041420f0380c4181e1044440f00c003120001e4507400756400080180c2040030350100241410b03c00283e4209800d460b01c2c00ca442c1029540f0b0045107180000003010405008245096 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 75694570 1250 75693320 75693323
    0xc02030106080d030510050102070303050a0c0203010f0e0105060111061501030e060103140f0706120903121b02071a030a0e03120f01060f020a030e040c11031902010e072102060403 79
    0xc10009854003603643d03844031524000c3c000241054006032150200c0b4400104464045c3c00401c5e10a056a4054401e0b070817410210080104055003007025a50034000d00103400b4044e900004c81c96003006040b801c1d00c20080841d414030800a004000280d00094002d6101e00b504e6030362681c20b051100128090f214078460b0203500e12400f0b0001c82480100500c500400300128100e481182c00c20300a40d440741501c0c1318400c00300d02512082c2888404d95000002c20b5032080c58a05030f0302c2c3ca024202411282684015105c26000c0c0b502440c0c41501000001d001d00709041c3c0005c40210640d030381d481240300040000329000c0e06e98007252050441001541d0001c000350041c070038545420518600041c400340314400016880900790380c481400411180085a01959030716600c41e84e8109200140c040b402080040060074150f8610800c4180064600300800c00d2030304002040c007880007402d480c110340110365180c010250810803a031039030421002c28038003600001c00c80c0340b4900002e07146000d158070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 75695820 1250 75694570 75694573
    0x1140904030839090f0915010c11031006030b0705120103121b05010c0e0603010503030307031104090c020a0b0604060e040b07030f02072a08030a050d0b0301090308190207150b010c0203 81
    0x20106407082d10707005040359181c21707a16a1141c1079000308100d00c22409072441b03040444111080075041d4402d1000b400da81e8052010100d80340360b0000842c1c07800e01c1900d00300000c40d0ba500c1c02401080b5841d113216400c9811494000c1c01c04d601c050010301d0140301840001c0141303c00342040c842c00750140400540007103001c1c81d00343d03444000b4141103000e4880b5030300074400522180c00300d2a5915285080d00c0c181e4078050300850030750f52003640603002486c9405101401c48014000050610154000d07440518002c1d8094103c8150626088a40c2c0700e000d00031603c520f00b41101401441c84001500c3c0d801a0070488403a0348d6120320209a0040010500030075205000103402820300110003940c2d00800c060240240200c0543e00054440c00500d003e10040b581007000032486442c0b00308083e003520103001400003074050b0844002402c603000c400c02103012813030b0042040010b90002d41302c4601ea48010701c0a41c07800c007555940c0c90608041101d0400c14598075046a000341e44078460f141c580c20380c00780 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 75697070 1250 75695820 75695911
    0x3030a110106080105150f15030a02070309050603220305040519060224010915080a06050106020d0c03021005070507050105180c04020702100f1202040e011409040308 73
    0x800180050844210340c6415070a110303001070100014441e15219a0001c00040b90b42c140c3c00d803c01000032960900d690f4800180c2c0244082c0240c04001907001e031200c8280144e80b2003952a0141c48110a070317100600c0b9180a0041260081403c0803000c400c05c40c2208600c5142401c0c607084e00c940c0202e070010782d00304036219000420416890b148000b41e40c4141c0849540c013200191a40c802d101c0f00526050f482940b80041104950766000071450020030880d0055060301d901049180000350041a2520fa40301d070010400d103074062006c281d15140324079002c070f00550a500d0180d502c100340d4080b0540c40350740e60005011315103c2d4090f02da40c41c1c0d201c80240603509003144000c0e04c004c8440440541801041e01040070391030603200300d44065a015016052610501d00b0503510044100000418840c0c40440744e112001389100520203443e040d07044002c0c95040c508d0284150051419a42c0a00c41000a00010a03044005075602940c0b030005d984041400e80e0200003030f20041d07409805480e02c0078 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 75698320 1250 75697070 75697087
    0x3090f0b0d05010e15040506031207080316050a09060810080a03081b0c07050405040318060801060f030606080f090111040602070e13020d0b0a0b15070c06080106022a0303 75
    0x80c000d041481404109111698841c0d120754402502030390354003030700588010740000a082c02c0d04080d038005001802d0320002400d0030b40c840c00c95800030000b115012000000c00c1101c00d00400d0144050005152a5060000c400c40240100101d401042d00784034504000840d112100c039240d00183c0468415101840018a00030303280c01c00586e040b1040703501e004560725505082d0700a540c0c620a5440060503014945004d200013081c02410960804c0040501c03003000201880000000f08034035135074245503601d08603008051030030b1130341ca0104240c01c000c2d00700002c81c0d000500d99044040c4039865801e50b01e403441c80c18010451500d04007242c07200072400203500c40d000f103000011142007480309038a503512405948681c2600e03e200a40c060b070f0000307078000410360301c90005030b002c00490800500350034610000782c0c007081c12081c01c0140000c0010303c0820080c18100000c01041142840c48407941001000386d02c2c2d03a962042c80e48641c801030400c1c80412601c21101039a40740140a482d07551030344 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 75699570 1250 75698320 75698339
    0x11011b030c0f0807120504060b0a030b010807090b0a050f0a0314030418060806040305030712050f1504050907171002030a090507060e0109060806130606031a030106080309090403090f 80
    0x201d8000303404200007600302c042e9a400346041c244200001da582c0301000042c080c000e03004010283c41038440c1560f030002c801d2251221000003001d140a40103024a079031400d030b501031a00c04160003001034541450100c3d9580c2d1076100186080d20340c00c880301014241080041040340503e580b0250101030454105c0c44004000320043c41680d81d003010b1114102c0400340b40304140d5160b0700c180903481d40144c000801091090000e10740016103481c06402503120340c0250f1040d41d006540c3c4000058512082c0320900592900c5c498050805071001e02c42e07890040000c603102c82c00f41c0720300c065140c411140d40c03036040802e04c5051112500c3c070208540780d0806d400100001c040307410084134180b040740000300707a10b40648054007010340305075203028441c0d08041c0110350144001c0d20060b0004a6030234041419040b81c040c80e406403910b075400081a07280200080e03210082020018000d0b4035005080c810004040f0031030b540018150749020441d250b130700d401c45009400f40c2c0400c02c2082d542d403010424140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 75700820 1250 75699570 75699581
    0x3010e01050a060f0e0c04061b08040f0608150d030f0e060304050d08061816050d09030221040b030417120103110a09020903030a030902030106050a0f0812090105070311011b03 77
    0x8004480d030790b44d251640a003420300c0f4000c0d125418820f02c184000c00005203e404188400c0d894280c00048200d81075441c2c4100c0e41081e040007850b650388400a211180d40084040d90244070045480c0300c00c524000480c4030010310f84005000c2045a11410030190700030700340e40d0b40d00080503040a61302d1500f410065120030040c1c04c454001034117039010408a00d0302c10900c0c0a24420b10828010a454000802c101c01813821000e906001c000d00100c900c080d2180704c0c0c00d0605000350003802c510052601070140ba00c00c004d10b0300108985c244414003061011078180da40c0294000c0323003000568104901d0201d07074064030700d03004880307641380001000700016614070724101c1006441c50f03603030940c80d81c009100b40c2c081e540c030b00d58042e0310a001d003440c00c9200f80c20018455001500000c3e8594803880860044000d80d08418a0140c9445c020001c0744001c03c10010010400c4140c5418000340000080003441443c00103005c0000340010710f21305807030a6001962040080540080c180f0090340050302811 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 75702070 1250 75700820 75700829
    0x521060102160b030123130c170406050613110d0504020a03050307080408060907030f02061c06060f090f03021503040c0f09050601030f150b0a14180306010b040612090203010e01050a06 81
    0x410149002d40b2401280c030820300c03904c0000700118107255881f07010070001c105041d0500c04018854101c45050100e07140020b00550051502140514141090002c40c01079a4400c241c42d901d4568000400d00c8120140c842c2800c041c40d000c18a900c0701d000042c5030300c40c00c1d00003a0090000142c0b1400300304440008000321260340d03098a040f0780e0740002030ba4642d001480b010340581180140b940040c5030403c000d04035000700c26107460108081100e40801c542e49500078201003000e11503030040c0c0c65000b81e00c0f0300040400c2441c004c0420300350350114000c014507958960000001001050410106450703900c0685020300b048003110f660b03034010310081e081c15100140464a402004100c052031170180161030f403000f5031000403c0c0d10b0130f15524800d40c8551100010407001c454074803801c0c980340300105607081c1c04400902c884000b010070141403c40603407003c1c1220408000030032850b07800c8408030942c0c400403880040c0c0c400306c07800404e01401c1080d00c500750a500e4034042020494a40d40040c0565 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 75703320 1250 75702070 75702089
    0x5100b10030203040203030406031e0606030506031e30070b420a03050a0b16110a030f05091816020a0201020c0f03010b060301030501050103050d0521060102160b0301 73
    0x100034a001a000c920094a01940680080000703000d80c82c02604011a4074001300300142d50b10542c0c1d80c1180c21a080c68208400098884c0700744041c52030304108241403e0341011110a40708015110301e5038400c000307110000c01440c0098014802c00105004680c00351810600d00c0c1c0e110340c14500718809034012107001400e1b4a0114041c1d0240030030910000404020f0851100041c0c0c210b4114012402030861195000710700031804800501d0500584042d90700c1207029507078a003040c0c81d01d42035000090f01d0410401200002034005a41c000840c01c9500c0d405051156000c680c080c0704541f18171034588001e0304050494041c00061140c1003aa070b2113401200c40c0c5824404040c14202d0700d1302c011143c040d006a002b80f440c90f0440c44c01d0f001c074a91086d002400003400a000c0c41c0455902c0d0400d9206490a0355520010000d100081c07000004aa24514001e0702e480c026541d214038003894500b01e0305e4071078621400140c00c0d90003085031078120744c3c0d08040800503555030a8041c1c0140c3c000d000b0b003240c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 75704570 1250 75703320 75703339
    0x60c070603061a0306220204091a030307050601140d0b0106050c0c01020309010507020906030304051c1208010302060a081b0c0c0f03060705030f0c07020d0303050708090d02032505100b 81
    0x109040040e080f0311050340f4520f0f01d00d0354407000c0801c401c0d007098442c0031810030000d00d4182140c82d078a2008000910f00090042603240303030303e44880001b00c1603940d001d000350000c10ad03500006502061540c1990f41041d0b101040d01d07031f0701011400301d07100880000c0c03030105600300100d440d9400c980a460712280c010300302d07043d00b4001401280c81c2d0064840080c04a41c0c103012842c014600000a641c0c01500601101d003044c1c0e44000003a00c600300003d503401030b01003210701c03c07062003030048a501601c0c850b42080031440d4950380c042001d502c03402060808001c41440440c20b146442c2c0300c04004c0c00300140b0b4094445441c2c10a01d61540e0b55010103e106100380840704440c2d0401041640c89a4056100e003819582caa8003031001440009008203d0000c1c204140f0005035142480c03480545d000b03a900050700e10f000b41019080c054044c007881e0950b0701024808000030340c00012107211036806450f200102601e00a0388612f4512000300801c07074050182d03a94002045035000716610101124071121 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 75705820 1250 75704570 75704579
    0x80a110c04110315030109050604111f05040b090301021306080108010606110c121207060204150c050604030f0e091608010b0309121e0c0d030b01050c1c050405060c07060306 76
    0x12119403150b8560b0415040c400203080300c40104440030740f20005000030800329043e030b5840c0c0c1820022142107405c0c00c408101201c0d9030809602d00d035031185c0c01c2d4040c0784114204c160060250b000d18419080012030004031010346460a4055034100032595501011090b200e0002402d800700901840000c2d40c03901304005181c51041041062100070440a802e00414030f4040c48640d507083c12180c001441381001c1200e00351801c0d001440110b02070364006844034140241811001c891b0440d0108020300c1e09080b001003080810601c0d00550b160400d12040701500310300380c9030901d901e01100d0348000c0603401c115428800607100d100d100c00c07541d6103105980c0c03130b400030b58030500082c2e803050110b600407619940000394690003440c0c1c902d00121906400c030300741c140c10402c51344680724004250700075151035800079815000380d2032064800d0130034904119014041c2c56585804204052001c40700104c0007440c64019001c80b40a0040070b408240d80d0841c0c000c8080d07482c4039620685002a280031000103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 75707070 1250 75705820 75705829
    0x4030318031b05031905040906061d13060b1210080d020d050309010b0a08010e010f2d0603050f0303040b0906010608010312121802011d0303030f040f080a110c 70
    0x80d080e5040d103903281180401d9038040c010820048085400748410002c41c002050322682d60905031840d5607950741c2d41c90a103458035080e070381e072036004409014101d800d00003800088428600481c4094030410010a0600401000380241d40d0054440c03550000d0f00c203c002c2e507105011032003125030101c80c3c004141d45540007565400080440780043c2c104009082210b48103200840c1c00c55220390010400401c00030004d031241400c1c2e07001e4000c0d41c1d9117034580309182e4400e00030025841310300760007000152003005407003206c400d85144925100045c80102c407040d50041d400701018542050484040061400c00f403603881c0d0050b102510b100f14079800007181d03840d00240e51810380d035890b582c69141c1d91070350b45c82040c940c803140041c8040c050800050480d0405911400d4100103005a080341e10034000e00016144003694408c000c82c20407200044203580d00c0003c11681c0214004040150a40e585c1c2403080c55014046030090030358000107040d0780569400300c0c01070300c942d00e0003041e02c001203850820803 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 75708320 1250 75707070 75707111
    0x405010b09120a03170c1e0d0e01060506160501060806010e060922030507020d14030a180f0501080405030d05040b04020a0608040506040b0709081c030e030c06010e04020d1505040303 80
    0x10f001031042c07174003204000341d241100c5401076109034000b400c010740c004980301e42105850b51159940c030301185c0030403040c80d54000e8000c4040b000d00204211810603010482c680f051252410016454113034860800c0310952020004122032001e0302c0c0656111548102030007804e0302e040d88207104010100e804a9030704104001d05500c0d03105d145175400840e50f000d40f800d0708041c1c002d0340d02401a090000106046508910b803604040300134581c0d8000180d809441034481007041d11303440c0805c09080c45180b00201e204401d842d02402e010590396101d10344180b0307500c14100c49071001d07420507003800100032424003a1406588200c07841d58040752a0701c0c0444a9810460300503280f41d11100c00304002c100307400300007500091549042e510568840118518043c144040000700c2000052940401d07035141c4542c5200086035405903160140765154255181c0e410701515144501550100d002c546d580e100500c0c4941d840304000070f00c080444070b8100107100844055000c241080c0f0001307854594003514 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 75709570 1250 75708320 75708323
    0x30b09010e01030f110d0302010518010c090e1f0b04050a06030506010c1704120c030c0b04060807030b0102010213080c130e0712020d06050f090d02010c0518010306050405010b09120a 80
    0x441c80e00d0b86580c40c0d0200c03c4020400c1035411040802008206469a40c0380891860082d0004201030414904c00d410043c0700184000d445d900d4201e0190520340d10000c10000c50b03008018103011900d407602d003541b5400507021075441c11142150005210100d00001e881254011217801c0d494980d9a0300c10b07001d48204a981074000381448040400044001903401c20000560403d10f00700b5071551980310304c1282c1100305582104101808108100c422480309001c0c1094141242c101460040c024101c40070140c000c400341529070300000c05591003541a00c0f4020b40c1700c40c01c50f54650703071a110503032641c03108807026000f1914806041c1a140360f600461480d0715030031000f80b19042c58002003032440980407070102e0384a0345410380d0b0400315445002e05805000380b000042840e080c0a030902e4545054035044109590409904400340340c0c0003000d50781c2d080d90b828203081051600c403004278020300b040c4e0411a441071500d030012400d0501c541c06007004000c291000400c1c818808045507491074907840 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 75710820 1250 75709570 75709589
    0x60b0403030c0606080d0c02030f010c050a0f0c0206070c17070305031c021e13060807090302041802090a0b032808070f120201270b01050108071701080d030b0901 71
    0x8104002446100c40c2e01c03689025100015400781c0701c1ca045030400351021100000076821000100541c9800d2200241e0031030098000c1001310705083c4058158003031600d03818140310283c1c1d00e038402d0038094001c44203034980c02046130b41d1351001860b00e002815000e00400c3d40a0f03155a008035801140001c003001942e40180c0110708142d080c07003158120407a0b803210f0a10068091001c2c0402035150700c645080300c4222456151111004450341c0c0740700b006036029400b0041e4141c01d100039503401c161004150b94055901103a0a820703d42206100107070000d0003500b0051610070444650500da1015413800c0c2c0032015107415040503209141080e10140c0c010304442411242c403030010300c2c420b0007030900900c54100155214815110304e0352800c00d000c80a0050b035110302441c01d40040c1034460141d404d4034500d9013a408080c90711103481b658414043e290612440740c5c04144c0700c0380034121901c010015203805484541e15280081d0b01e0740805401c040c0800e05002d4400c52600e00710381120f040c0c802c840b0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 75712070 1250 75710820 75710827
    0x71106040b0a1a0301020c07150518091e07020703031407050303150d0f0c030308070306080a0311120c0a0b0a0203040803070f03060302060d05060112050c0f091306030311060109060b 80
    0x240c00b0014043c0402890407500f034080d081807991030030b0010301802c5c00d07480007416060740381a2019080a424890072420004100b259096080c142050305d030825a060742c0900103641d85071b5130082500d4a02d907666141c0c4c18040101324901e42c0c0010100c003624072a581d4500d50070000d00e0852001c1c050550000c016030828800a564805003051071021400001c0100c0441e90390354451078541260004150780c403c050b040305000340740c1c2041034982c100036246010082d061400c1714042d00c91100f80c500500300000400e10b00c418240c02c0100004424035a014565160f00542e981540d403504200c00311008200c40000441d54912407080d00d01c91500100550715699409504441e1000f126502205152b41c0b040702201503210a0050062040600400540c82c1004030014008170300c00e49842c2c000d1803c2c0402c00c147c80c0725050542d14048100302c026500c95071342c240054420480d0082e400c0031035140c18000424568856500751002044100f95810307a600d598800054421601400c04011000c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 75713320 1250 75712070 75712081
    0x9130201050306030a020d0305040311060406120b180114030709111902030f03010f0503100903050a0e0402070605090a12030504050604020f0d05010f0209040606030b3006070305071106040b 83
    0x29002954060001130507500810301c1640050035018441100760000788002c5014000c02c80000081809140c080b981e443c00e0600e0250014a0180e02000c2c41400300d031940b0458465842c0c7c210b0395070340280003451020203580c4403001d41001c2d140051021348039100d040b8000400e0307080c0c0c0c407414160255030031001d458258641c50600700c20468140c0c0108501c01003008056210505000e540a021248410340043d85030004243c6007001000c410611180307044050390019401030119264408035003414072405400030b0014009014811024011509150030003661400101d60001828810b4070406411613504000f1001c41d002281c3c01001940018003103405840d14000c07a805d0450010501180c01d102591060709640e41d000c0d13128000c079004914210315103024001c03080170380464507041224040120004040312060001c501c0303000319801030006480404107025a0034900c46048603801d00781840002d00428045a241001134105009007c02c10030104034103015a401200d01c91540d242c9 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 75714570 1250 75713320 75713327
    0x1e0c05090d020f060403120309030305060102030903060a050c07020a15020105010b03091b040906020703080403020c010f051b070b0c03040e0c0a021f0e0d0c170f07110a1a03090c09130201 82
    0x143d0586640c409024400000061050803c01c120440b81d540d01084841f140d1a000d010f94074080c041c58150f41050042d01056100090183d078040316119021501d5128120b06103031510503a0b038003a4010790380410100300f811070801004140c0001c2d80c0200581d82e41c0d02c10080040c0400d40d45041742c1c0d00401d0a100c0ca001d0501190009200e005100065810055aa80040ba400010b00f2070206220504000901d80c0500000f48048420308107841d50031003804000b8030501c00c039034541400a4040c0041c4c1025002000110041d040542d2551340d07070403100c480300d030352a0003501c640405401c00c04005104c002513101a40c10380640b039002403000e64110000303a04940303010350f0440f210603134882400241800410218a14120170b0b214098404598144205c0655990f061038a246008022840c0d440356208212a080d42d0440d81810b21002c007500065a2a0b001c0d07800a10307400c0444074034050160011000310b015035200402c80d4106500c032014000090300032104210040605074240c03026500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 75715820 1250 75714570 75714589
    0x91009020105120a06180b040c0806060409050c0c0a0b010f050103060302180a0e0d0e12010207050a12020a0803010f05010f0c051e0c0603070c0b0703110301050d05010b041e0c05090d02 81
    0x84d004000b00300c407511741d000c00000762903941d080f2030395548528045449007080e2098913020b4156103440900c618066010440034801d5104129883e913880000038181e03c01541131311000218541903039141c01c11800c0c40c01c030b410300a000e900c0800c01c0041002500c0c0d0301a1017510201d81d8094040d03032441c007107200800304142c801044440d0198840718115403955040c003180c52104896129180e04100790000d116000f81c4001700031516a1041000201281000440d4117400d544400c010782e0a200000d0100d00344443c0c154020300d040e001000102701d0040c0340850b10240c800aa8515020a050710b04c11158000028005443da8104100340c080201d002900f803488440910f044900800420001c10b6050307000710b07070010001728082841020403001e030365003d40100c014901071010b078803200c8010240c0c0c80180b14592084640818200420400f0340051000b801c004201304224100f03024001d59051106040b80d44480c13502480007102d03801102a9040001c010704084640a0340e6801d01c03141c00d6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 75717070 1250 75715820 75715831
    0x70807030509100e01020c12161202031c0b010813200f09040606170304180506010c05190b0a14060d020d02030604030c060b27150607030809100902010512 68
    0x60a82402401e61850080c00390791348912000607540c0750a440098103000a114070b03521901d00070000005440d85034a4017022907a048603151001e800c0c624801d0b840e51045a10405840081600e1414a103c1681c003001c4400000c1e200c1008503558041c13020781c1d1070307080000100f622602c040d9540d03031805200380a0500c580c0181c0b0811307075983d07480300250f6140b43c1140d049400607150072043c4401c0044840c524880c01500d80110305003800d0519045800b094122580c2d44e05640d100041c00d2a8418062800c91359000401ea810782d9403d2a50f0310120b183d1440b0030b03a49040e030a4003040340000b40c1d100c0d04820b0004401c054a80c1e80f59801000207904c3c0104090f64010080125080542e40502015000d248603849400b40f410a52402c0c0041c0c404201c07145116070141d0300c08030034003075455104440100359400031544580d148018030256000b03c6203081d81080c40405c20004040d0030007072031800707012200c0c100c81d00061000c03d42c2003a503444450080c00248280001d41080b10b200b00050f8014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 75718320 1250 75717070 75717073
    0x10305041a04110d061a06040503030a1809020a030b011404061b0203070b03090a1e0f020402070501110406180801060803120a2409141515070203011505120303070807030509 76
    0x64821800058600b40d4a038401c1d1806550b428122051103506c1200034041201a5051401d0503c1c1000094907409004a04000c2c03080300b03070103592905100b144c030502420b4040d400f103444a9105800070700804891640f5030105503000381c0604110f5020701510112110b82d502c1581003894004460a41642640d04980502c0740c0040412404043e8000e54425510300d00103044094407070401c4200701d1720b5052050304d90759030210001d0126845848890040b41c0503507015035104041d00d03205004103500448485800004034010415075802001ea04040d2080e09aa50301280c85952040c00c8802c14030640d05194020010030009a180c404420384c48a603101000405880125440340c00b110b0010b040700c0041101c52080c00f1805031441012200d40013194007806a140404000c0f511b9040560528030076181c10709010000b100000455100c41e501a000380840034001d48003200105441c01043d00c00c40c000d40a40c1c00c003080000a903403194402e642c4040f0591240501038004040c058142040b9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 75719426 1106 75718320 75718343
    0x60228031a0d03021609050a0b060f0301030b041506080307140d021e01090611120702060408070f0f0212150105010f021b011701080109060b010305041a04 68
    0x9068042d280c0445140a81c10144e10f055941030500f94010b00740c1700b01181c9444540c0025000302d40c035010500c1140140b01c01c02649000307076508070380304007014401000801e03082c1d080b09420074002c035140c0d403141d55a01c03040e109882c020f810007503841e0300010b03000c0200102000d208443e0b0407020080c041d2603c6441c1c0081d110074600035400d0700c0c0010003280f4001040c003176000e18848c42d407126041052001806440000d90042d4920264010307410b000503032503500210b1a54801d40d03100003800d10b081050f03503804e2510071002005440c1008a4001040142c90b80d90203800c0000341c0304010146042c8070490303006030900581110b81000643c0300480b64858000804030103410701150390100554100c40104c03422034075005100c021031600720000403288019405034454902601050000d030070680c005409176241500c00401c0901c101ca41000040c082c400d801c3d801038490354100d02e2 = true := by decide +kernel

theorem cover : BRFrame.Cov 75539570 75719426 := by
  have h0 := BRFrame.cov_init 75539570
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75539570 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 75539570 ≤ n) (h2 : n < 75719426) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
