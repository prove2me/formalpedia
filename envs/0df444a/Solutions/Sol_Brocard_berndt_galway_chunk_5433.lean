-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5433
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:51:26.670762+00:00
-- url     : https://prove2.me/submissions/8810c61e-523a-43fc-8620-af5bfd922f94

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 976978417 ≤ n < 977158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 976979667 1250 976978417 976978421
    0x10b0a2106270e0c010503180708240609150a0503060a1d03041818020910030b0a20071a040804031205031e070e0d060f0f1e0207020117010603 63
    0x19442d2000b6514019003000b410070403c0311410340450400d900040c0e460f600310f40c450001141d203c0c1ca807508201d40c1d81451801140707081d80640003411f4560101c04141881044030401c0b01a4661451409025240480114107540405040400750807a0000c00c402141c0d1485802005020041d080303490b5864244520405000208003400c1d0364075840103550107100d4003100320b40c1501e170280c100c0c0800e9902900d181c0010404048035600310344480400c40d0050303543e00101402074010000c0d03041c2050860600080d09040605004120380c58103070411030003070041c00100450346c00d640301e00da1a19080d00740018030340240002d014007004c894040000b045005e42c09441580c0c0514812040c20180031410794040c44160381011071498140d1071003030b102c00e900800799488072603445c00c110108090004030381d084040110131543c664942d141200b08a0003841042e400b0f030350541080c00707030f00d200b528008982d0001c48140c0046540020740311040da4000c1608080240c1343d0081c0c50801d60b920440100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 976980917 1250 976979667 976979699
    0x110c15040203062d0a06170c04060b0708071e0b04030f08010f0515030a0b0303160b0c0708090409020d14030901084804060c110414011214010c0309140303010b0a2106 73
    0x9c0305518082010541d80d5105055905080d800204507260451030385402c14041d0039215200b005a08601001000401048002d4005e510940b5180d01d441e0081c40301900e0703844160440c0c1907043c400c407803c0050755620b40560b180d03003492042d0710360781e43ca0382807014001d00f4081007500d41511000886142040140b680c00d10150b0140d08000000d86422a004801340320710032000d40700c900e061021242d20b26050340b005250510080c601c0b1061400c560300c4480300c07800400d1000300d43c0c1020403911841d50f0800030042e07010340b1f02c1c0c8500810212450b040030310504898221340c05c2c403402071030f81e2000c0141d20000501105111030140c4e112640da0700010310030004810126850080c00410741d02d6807c0500507045401d610031048032641c2c0c20164024035400f1091000d45088502990056842e0070a01c00c0c1055a0550390300840c507400181844a040c03928030007694540d41c0704000400c14041c411050390140045403070414055110740721061541610308841e5160245044000581ea03200f800c0000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 976982167 1250 976980917 976980919
    0x60a2d09120c0e0106111209060417010b1306050a0b190c03110703151a011403130b01080607030605061804111903051807030f06110c15040203062d0a06170c 69
    0x3411f844014813004056002c1d400e0007680048060205001c5881426001048002c03403800004c2c200032210000340c501d80390007040180150b0303030310030500803030a05c0c0b00700c0b02c0a44072102049140c490260b0100d803103801c5096514040006140402c2d0405101d04443d800241c05102180c180b161031b400c110184008800100d0061442d000c112140c4540a8100d010341c402c05071214000b41302d5194206100d548001c0020206044031201d00002801203070f00c540c00b071b0100400400492030400b90180442d0080d800c107910801082c00800f01590140304980704200040d2400724800002407501141801900104980c50611130000d82c00ca65040c0e1149110780341d69100e041000c5801c544d00d544a410303d00002d8550b5145514010200d0320710707002001c200c1010907115250004072000d59080650384a04440c1103a000c509000a5260030041107030407101d412a07030700c807141e041d14003074200704081c890400780504c00000280d55140294030100c02080e0301e4840e0f22260460300f81d403580b0380070204231075 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 976983417 1250 976982167 976982173
    0x20a021c0203030a110409020f09040b0307050904060b0109030f060b0f0109080706051303120c0303150b03040f0302011b020705090c18120c060a2d09120c0e010611 72
    0x1000d400d14048454400d1100e650055850340d00c0b009005405800f103488020070b101800c02001510b14010b1000b0038400c40d01c6d21809490304d03d10010482074405205003540719500124060105980e42101c0359046641b01c2c00000e8900e22840059503c203105920140070302c0307501c2403100203100881d00814000141140c214a401c0c90000065602158074022003010781d01812091108a000784018174014180e00300564800750b8075a01c40265110b10904034000520b6442c0c09410150140181045540620175a040742801c1800b4a40a4000100050314a0b0850b00701501454000e40c40802002040e59403583c0541d841c540103583d81c103080c400c0c9030003610143c0000d402c256403801900d83c0d01c4401e90440c0103c022010401a40c44d003491404a01801240000b29044d60307060000d01c02c1800030385a400d4541c4040e6480b41d100b41d2600840c009450060b40300f01110f03980600300384281c0b60b000248202c540c0823800c1900441d01d80f038100355511002640045421500102c02900321007a240803 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 976984667 1250 976983417 976983433
    0x90309050918030306010c0501060b04030f05060112020310020904090b010915051c030c081b01061a0a0905100e0604180507090312350403031d030d05040809030f01020a02 75
    0x400215a0311040702e00010383c00a0002c1211036101e9081c010002e80144004100d00ea110140e41c80554000e60044038201448405c55080040a1201c1d03070041141800e07031100310340b00b81c01180d12080000701c03885c901079000428034002d6481d1b07404000d2540e044648201d070b0b980c40700c00e80b00c002c2c0514610400003030040368000815291640c0c00450030891010498405d511a64068030402c120710f0080b101c0c0082409150000440590060170740c071030031000410040c1c60304074180c140b02c084090801c24003108001e10fa02c00d6802c4034095040301c00555190f40b200418510885040001e5a800c5602090018001130b400e03c410703901c5034240080101c01c000700d8403103c0050f5440c4480b407000400180500c0440c068607800340540c80c0210a1500101410265000030144020a80c2c2c0a00d44e2100c2c58900340401d25505204078400001e01c10000c0c252406614000ba0380c0e401142d14016200c1d4540300001d00300034a5070709031503000001404032850300b401040c80c01d01035003203551601c00610507140 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 976985917 1250 976984667 976984681
    0x3240e1f0f0b060d0b010e1f030507050a0f12020903030f040906050103090c0e0619030b090601231309060504080a110c06090603040507051504030303200301210203010903090509 78
    0x2c03520651400040c46540360022100c48030000d042662203036410b000740e08240140a0319415002006840740030880da00341c102c0c4a1000c0c04440d009000907013003240a006000126270822581143c40215040010146901440400183c03140801564040c000030481111040100000e0015200ca0940500809480e20300440481d42c035440040d000c3c41100c2c60070000385020200075504008043c10103117480c07440710340c1c01102d1030150340304441405448081012034081881038502501404441c032404500300c12005113810f0850622610500d004148940c00710441e6001071102a40b205041c0001d10780f41c2458000398004001c7ca501064000f000c000300c1e12408168082c400f2001854141041e00e5241409020b40000f4421902440340034008036480e0f41701001b6203130001e10301c0c0009544904525005081e01c0f007000d2040b02c013401880034824602405001d4905442d10107900105050000d41211070014100130f0181d0036518011201d01030540c004a54000d40324151048546030312004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 976987167 1250 976985917 976985921
    0x11b020a03201f060b070c0323071e0306060803041712120601110a0c05100e030d0c020a0b04060c120206040b0106031805030c060906010e0103240e1f0f 67
    0x424506a81110000091141c99801c0c01c110510a107a0005051070711703002c1000701540300000c103503408914110200204125516904960007020961040a4480e0f005561351803030f15024000110829000f0384d8044070b074546008c00110f800407030902c0b03129680c50070641c403075000d4000c44804143c1c0e52419407241c0c5001900c120902c1d10012054984940802c0c2e02001500c0505074604000c40002a1055944108110110b2500070889004401d140104100c40d18103460121800d00440e03111001180e07402081000380029142802d9500c1c40982c40000e2800d046a00002c40c80500410003155603071b070142d440c814031440f64041d241d4003500f502040e60b5404080380c000300591207a41c018420340d842600304040004c402c0140340f2168505648441c11500002c8601c942d0360710860401100c9501001a1030041c42c0d1559010055410760f2640030807500200f0b13028008c0f40003882007a104502c40e03400201d494100206403190201d00c45514036140c0740d00718041000a013440003c418000b418 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 976988417 1250 976987167 976987217
    0x603070f0e07050c010c1d041103060d08070209040606050f0a0b18060d06060810120312050712051302031203090d0c050304050411030a050c0405061b011b020a03 71
    0x6050044403841d054401080050007820901004420b114070301c121402400b910140e601d160300c503500036541005a41c1c11082103188180e116509020799940c00110f110105e0ba0010f101b079508880e1761416040105040c454040002d4100506004210500000e544441c0554504443e18a40342c00c004040015441ba01d001c1e08040c3c0364200708020000c09803024407180690090042400c28108404d8001101c010b980400302150550b01000320000c1140424400740002500c01004000c3c9506d00501c0f021040074402d203c540c2c2e8001040ca02d0b130180c0e1519100c259940300501c900d181c650500f003644046075204a000b88100500c0c055142e4004003624400d0358400001c0c000e02c40781000440d01e0070320b110f1041d030741c9010420011520b500c56008813103850910100b0941c1d6400d02090749821540d0080281080050a200502140d980c0d00308071a041c1030f2060240490590b543c0103d80181510071022603406000d01c07240d02d02580100e040ca05240c0a51980d4100d0303000860311680404807 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 976989667 1250 976988417 976988429
    0x40b04022b060806040209060f0d0803010b0a0908030a0516030c050d0f0219020906061b10060305070603090f03030e100509010f060e010806010509420607021f0302070218010509060307 81
    0x1f4800180396050001c0d030084000300040804003000c0840d19146441d80c401e8000391b10403000090446000c5401c9081e1b0030007004180b001f1441d0082c01c14008001d4040c114208000c58031121404061620030202d0b0318845070040300740e0f860b1400e541070142c0b0683d40c6d1980d05025001b0703030140908084050120302c1c0c00680140040360b6507510402046480e91141c0640710f030120506518050041c010000c03420040c5004100040032402c40c00d0480c6025611f0780003e04050800d006100040e440381c00004903164141800714613140c0d04003045050010440024a05a1621080042c0b40c841500f00f00c2d44001d054008009c038a4407508040c840017001d02948070103512100c01045107060440e56264000b100c6584e400c01a15000c003816225241c0c440f07180c14443c1460441107405101c6400d990358000120349481c51301b201c0e80c0c0070418000d420741c0c205a02020348144699468002e8040350750340ca5008103412000d03c1c040740000e101c030b9428064907025003603e5000901d01e0500090250a030b0364 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 976990917 1250 976989667 976989679
    0x30a050f0610080603120c06060319052509090b010614041a030915130606060306061b0203030d0216060b04020f0d090204110c0307060f020a0e040b04022b0608060402 73
    0x240c4002e081d1404000a003050780c062040500d15980c0202500c0540b080384c022902a00290410310101031415640c3e0618402c03002199242800290340080c0e00140d5900c00e41c0780b000305803108a107003218854164843c04490741080804020803100c040704074103a404a03202c0320b44000380502d000031240074a000b07a1000c10303402119800b07441d11a070042d640c41040d1f40d080310180002141c0320788028030183d40d019a1310703002c02c01100800c2424020b1001801c520324080000500e056002044906640403140088041450703103001c0d518240100d030946e41c085071081d075a42948018001d5080013481055130403602d00b01c0d1800b400c1c60240225004140280301050604600d002c2030300040403481c0041386c0c411f035600d82041c0860440006802d0440c1e200300030b0354031000c0e681400e40a0b6054828030713110042c03041112400f0140c00c046800d405010030b0b6070000f5440708841c040f4000348074005d4112120251440b05039031a040d195885e07580440300c0700f000d1180d40c1e6290101940e80c0810741d0001c0d4005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 976992167 1250 976990917 976990939
    0x30f24010309020a05041401170d080402060a0903061a03010b03061e10180f0b011718030c010203010b210123030316050601150801120605101703030a050f06 69
    0x507110341c1012000c640004d1030109200c1c2c0e41d1001404540704e4841d0740e03150190f4900104002c2c6c01d00c8210700000b5000700e02805490320303400030041034181c0c0200024410030b0086484001548140912000345501c420b003008504204282482002941c1c0107481c401d42c01e2820314442d03410007040305130042030764003005440c0010b11452280420b10080040792040c9140038000340f060300300031408041c02d00c1080f00141450059084c00252401d090b0030078107115480d0895004000307002c3e1216032200b810840031281d001081c1205096125280c1c10307030fa8541c000300004c9085640c04004061070107451f80c6c510b402810f50803a10280100901c115171010080b50b40303210075024801c41603080500024252850004019208085558030300425175880d4040320040c440c25401740e44c211041c20f5a800d180120358900851044030488410004200716201c4021641e40d500e6081204007901031452000e203054807005280341d5036002101c4050307203242002c000c6400d1844202929000702d202415441d40f40e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 976993417 1250 976992167 976992169
    0xa1709011d0115120515040b07080109140601050a031d0d2a060207020a080a060b10021203131a010605030712110a03090c05060d05060405011d07031817030f24 70
    0x843c03210081078445e801462501242d09002107040d5200358442c020324002c5080841005006a00503008256058504030307032001c8a108001c002030b4829424a44940d940303050744000c078041d0000c0700c80300c00000001414005004401300d0000b042e010f240d50350b03400741c20202c000081e0b0400303041c01e00261088840c1da00c00211b40a60014400c0c2400903044502040d50307078043c80e2070401c15901c16540c0c640d42c1c10024003545030158140000c1e20a030310040030314156070300c40707030841d8030028080340e400c495180100400c200700102d1741078450034142e4500d41c00e5a91103034013030030661048600000052000b9200d8003210303d00c0c8198011100f49900a0f4104440840268001c0140040540711050030203000100c66032030340002e0031024800c3d2004101401d120043c0010b64006807c051001141071f060230325007249022110354444668500800d40601c603070880d0420741003143d409400155001c1404104802e804000c5000e01c00341c444400c00e664880d00b1501c100d080c0002c040442450040d081d40319 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 976994667 1250 976993417 976993439
    0xb061c08030903130b03071e091e0b03010611070501020a03270f0602030a17040305161707080325140f0c03131503110706020a1709011d0115 62
    0x440000c08080fa4075041d08180e1107254044030781c0c010030038618000204108903a101c0c612094102d103c0102d4a00c40c3c03510440504204041c0c000c4a8120400760082c01c10503481907900002004d550708400d03903d50b100c3c8001420101c0307105120b110b91168880000c2c00e940f0000e00d410312513404d076448098101c2d0180440c002c0700303104401806010f00c401004140c228010301d24100511542e00107650f00c64035014040c141e4280c030600e444000210340100310100c0c0d01701e0308550781030144036030a80503502685040901c7c81e07030142c0f4000c400078001c510b120401045400540c014400d1120881d0720740c1c0c0003100c050018803000007840004400d80590b40f150312035540500703485c039448444a424001e03180041d503c0c540000d00c0c0111820a8003904006e440b44d005200107280c0c05610b4240605442d0580c2d402451207194801403800340d0000e0800c00c0c2502c20400c50500d032504110030304860929901c0d55028104042809a04415030b01c00c0d0307912072405206484424420307a5000401c02d29001703000079 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 976995917 1250 976994667 976994671
    0x506060f031005010f05120304050a09020f1c0f0e030a020d0f110625021c1b02060c07031217040b090f03070303052d04020906011e020a0b061c0803 65
    0x7405110390112200c0e0400140185406051005000c04036030f4030b0131003004041c614040000a20360000c000c140900d4445883e00b8003070700c5e038242c0d000da61020b0031260340000348201020780084900400280040d18440e40200c1316260317160b0030034030400c507402e107007036071280701c0c0f8540000941c2c003d130f140c000b484d402122100200c15003410b041c2007a00607190a45d051090850704000680e0030b10102e005c1584211000c494080307491310040c0040c2d0740161355004c010318013030070a00030300c2440c6140072035149000f00e445101a41c09052140c989960340400ba5603030b003030f45c0000c64070008a449a501c1941c42000a141540d050030340082164031203855550f82c0650180c80c01040380140c0e001f00038088410030081030060300c80e5400048a02c0c0241900c880c0300c01d1000d650455011a081c43c2000d1003514101ea80c010350101c4500e6616200c3d440181d82d0a0222542d6030884540c10b108500301e01c0d00801c4c810451070094192080c00c1d660042040740c648038105040690790800710010340890300d20300181da = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 976997167 1250 976995917 976995919
    0xe060a0c1704080105041b0b03010303080c19110d02011104050409060f0504031d01080105010c030f020703140f0c240c03091f11060114040f1e020909130506060f 71
    0x8000c001c116000992640309800844580e03445200740f00800090000400746695004e80400800d4140500352100b48410f04c0040d040010b1100421004100e8400b09d0b000348110423000410b1103030700c4e8800b03840e10281502ca04018001c2005402440d80180112418020b86000c0f5914260410080000a090001056903060f507652410060070f10584555402540a622500e0b41c55a2240001c88003800a44032a8100048007004003c2c590300807000d0f0307201035814180f002c80d0958a00c4101c0c5084107540c00a010b1500f15011401c1c0710b5408108448800d4085040e0f47d0040d030707104d0030b10020702180010098807041c200d0340d010f01005500094081030b5000000d5910707001000c1c00103441d03c0c500711815018071410940030f4114640011032075071900e1440c1d01a00e038642c50201050031816010590394007490322901c4030b4031041ca65911601c110560074104001400750061500029004162407900031204071010070460744000800c00d19095005000b441c0c255202028000d01c441d40448031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 976998417 1250 976997167 976997183
    0x90c03050109030504050a091103070507050a02090708220804033f110a33060312090609080d0f03020c0316110f090c07080705070b0304120e060a0c 65
    0x480019000c1c050b41c61000d01035a02da54856041c0010441c08403144e900488050b450440c0d001250b035510000c0e25441009400c000761505030504107607080407050000254001744030810400100d8102d42c4450007064110042c1940b03c5d00b141c66016040400c58025002c428184010000100401c05407070608801c00100d40c1c4125a0103181869280c66409110403085e51100340606143d0100400c80040001402000b4802d010748980000d08150304c0d000c40a0b510209020f80d000c12111002440c2600680c0104038244da20b00b811071101c01100003010014100100004100303105094030320548a0200c06052140440c440c140d4140c081c0420030300505d0f800340036038480884240047c1070719400548000c040d078001c0d4a010107000130740350482032081d0003420001e903107501c1e008200b40d03112000480700b0303666001c0c5041801d5540241d4000614500c2030314408184400741d180030f0f5026902c140007110705102d003d0003d84554000000183c3c10810074014490b4481c400c8a03d540e041c1d00846003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 976999667 1250 976998417 976998419
    0x1805190b0d1103150f0105071509080c241501050a030f09021819180609050c1c1511090108040204090c080a0b0112020a1e0f03111e0112090c 62
    0x1540e00d0540007104c0c5880b142a070003844030400d040c1400c0c035040010091900c549803c40568580c0c4c40a40c80010140c4c09075640c12035002000510380171907165811020459011070302000094001c008010b0710080c40d59498404140c030907000c2d070060090a1303416124107041100c0b005040300284807244801a0007602c880c00c0d00090303114203000e502c0e41081403003000e01a2402101c0700303651200b008020f0900c507152080d0000c1d0111100300c81144a0b52102010071951814140309146c01250b9410941c840380c0035031750708400720150401c4907044c0c3c405c0e442d0505004a0304600000c89030241d101c1020f0702010400c02e407080d031103054510361042c402800002c41c1c00c6a601c62441c5000550460a074071351017420411b0502181c007101600412404005900c80807803030340415034072034003481800109010504c48044d04010410581c016040c101c41d031070076213a40c0707081c2810003400040106016a140d016407011280c1c102441c00140f41c0d041c1c54920404000c041c4d048010584600190303100484034030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 977000917 1250 976999667 976999691
    0x3010308091314190e07030203070501120f060b040e0702010e060f040f140102090f0316030224181e030a1403070c0e1602191707121805190b0d 63
    0x85001d8401d18078400421258050001304907480780f02e030380c0220f038003092081005a80004145007503500a01e411400c000c085002c00c006000a1400c50030003034140500803d40d90240009481180c940054102107078a880c801642203413800480262960800c1c0c001691000310282d007550014804c1100c40b0941c2d109844000b910702043c40f900c0b0303441c2d4001880241c90b10389090001e070380400c01c401034030450170141040e45005401d840001c4c0100b0807126916036084807025098040c283c2d55070543d6880309800070201030f041e03101d5a110f109910180f41c0380d03005c004080700e41603005400380c010f0407006d00030344442900c1a40f080c0c080b14107200806c05000020606020303c0024026032610790310904180c114010709027500416501103500403410250010100420044210b17040844000c1121a40512a205200e00d00010b0404151710342c02040107980925401050710075001c100c42c03015110002c01c58202c0780c142000000240141d070900503034490f000141002c420f80c1e20006800c0c10303261 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 977002167 1250 977000917 977000951
    0xb090c090f1c11220902120d0c060c030b0a03050106030620120c160b1e160c0c090911040b040b03120906040e1303032d0c030902190807050303030103080913 69
    0x507108941154035421503000718204644031102101125014090303500000c0c20041261941e00c100ac0d00258940c1c422140b506d019a0044130f02d91b001401401e0320980364140b0b1230181c084c030f101c100c0c0d060303161000041d0700c01d03900703404501c5100111800c145010303e07502d0303103034807062001d44440c1c0090010009850308403102c02281141a100b05200c0100e0315052004a280325440581d042c5000c10300d1003003121100703007580d0310080b0200300e040c00b6062103590300308410b44001581260420520705081801417014841035041c4440d0125400d1120b51030300010702090f11000203100360140c1c064100d801100028001600d040100031f0070840c10540d1300e0100900d00c040c143e0310100e12100c2d1b40310314014198940696606200da0929034000aa070140210070344400701d000a10700740d583e40802da940c45100c0e410580103d80c00902e552004074201e0071000f2641d5051242c007140d407144040016442c140403003903030304803908040e1142c186061b4005201c203c0c440c0c0c0000100707041c4d4036036030300411103058 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 977003417 1250 977002167 977002219
    0x2e0504030e0415030c08121b1005340e061c020d090b150108060607050a120f021905030306040510150503060906011b150b090c090f1c11 60
    0x80780f400000140b450400c0000341e01d094001800d07e800c0402c1c103894000302c1c0b80840d001d00390b00340f1110700b41c200d104140b00e007003040d40e0313201030021070400007403001d214001419051640070741c80c40c40c122003003c0d08541c001e43c440801c4800124540625129451501c00060700109900602d02401400302c43e18410890b0b000c0c0081c0000c0d1a81c0c0c0042405100080c14620341c000a4005024519000100040c00c45d03d07008014503c2860001003e40c1000300901091646650012003888a50681c002c0540420401e09913540140b10b903400120541e060140d034106200e410401030752440d01c0301424000a460000e004400745020f850700003504042004101d40311400c10741d035940d100d09001781009030111028103007604118841e0080c0d4800210403880305c40c0554403401c0c07284c604200740c2c02100031380403030780401da8495280c108201309043c9140c0103145509003290340302c0c000342c3c55000f0015001900421b00504151000b11400043c80da40405140d0100040401040d507400c000c68400f11400c0c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 977004667 1250 977003417 977003441
    0x7060509100b0d031e0c240c050408060a020d241e03110f010509031614040e06072f060a050f010b0f0a020309101805060c03071509232e0504030e04 65
    0x3036001c7d100d94500040c800c00800b0109498894a05403a0110301607503058090056010707140c0c0040d840401c170302d05602624500709280c05185010b0940000f200d41000c15100d08400000c20523440700b007101c050624803081c0d82e4400b912481d181c21207800e100020340702c0170440d418042d08224600b6a590304201d10440da20382d42070200c0046040c110910500d03613800306a40d000d030f4103000d807140d150364006c54055408145840c1030340c0010300e080d00d012101c90903800b042c0080c0c510304410004141d004941180f1844a550090000b901c80132178010744003500b4450800030301014442e40d20180e00366070090104480c544112410b01843c0f4000070b03101b0081c40d10360008510b0f03814031152428004004040100700c1164958100108421210b8482c0f0460034000c10400711000c054541c0c510540c001c0a4441e00102903da016104000e10300d0550005210700d030040c443c6e0003086221220155420020344c00c41095031400b20509203906000d00800750003201480b80c07001d2461025129403040001000d2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 977005917 1250 977004667 977004713
    0x908030106020c060f0d0b041401060f020f0606030a080a170c07020415080601060c0804030b01060203030f0f011d0405010b092401090e130807060509100b0d031e0c 72
    0x450101d01078540b10000619070302681050140c412000007560980f40c1360001c0003070100c0c0000f01c0c1400600145a40c443e092041c181017030020400310703448811080c00703030481d408456940e110381d0174055a411085078450351642c040400d0b10001038204015002d05a01c6081500000c0000300ca0110302d0301003100c108001c0000410300034203515050240c500028040380c100320b041800e00c2041038681605000d24000d000c2c064001c3c0007040b8019048400030354014104822558460100949170390050702d0401d0000c00d0480440d0105800b049030710304031080402d041d541040c5003420149410b00090058415559800e800c481548540007414803980300001a00c2604d81d480c4003500080540c220324504004019605114807000061129007003030300c04038242240c2c0c0c80c615154600344250000149200d0401d000d101800b103002403142c2081040d41c0044c404807004105028051a10041c050b00241c1034005030180041c4016014000041c0c0307151603260054151140c40f03d00300c0080d14808604 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 977007167 1250 977005917 977005919
    0x12030a081009020309060601081b1206040617151801051e0907050f0f0609061b100b090414160b0310060309050a030509012a050f0303073009080301 65
    0x20222841c800c040c1610400071415420003a10140d61020001c12883c1481002400301c0d00c4840600d03103a1403401641410140c3d160080d4030342d9291107209680b41d500603410305030082202590b1048480032210b07407000400422012070409614240064000300e401120800ca000d00007000707020781031084940d07254014000b410240c13403051400000f050003006411024050100d59a5250850019841161a003100e40e440c17800003905803181c4140c0701e47c070001c009007038043c40b00411102d440381c1503e2004e03200083e42e154001010f540040881d540d2080c0361100140001d429400110301c071b42500411140075900b59008600a440590041c5899034800300801a09203144a40724000d08640d1030f0500200d00196603166440b801c192000b410300402048000d0306900c242030300901d00c0482000002c200400540004400c002c100c0140e8072800360418030240c8130f00000880340203284680ea201d0500c003012350100d004810003200c0954503c0149020300d0002c2040c00b601c0402d50244540310f0380c0c0c0d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 977008417 1250 977007167 977007181
    0x90a0806040201183c2705131e060e100509010c0203070f21050d0e0129030a020d03020d180b07030503060301091202011a12030a0e12030a08 62
    0x300003102c4d907001030211240f00611055910241c0c0150ba80c0800c103400308996504480b65500c15000120407070045021000040c400d100ca00d91000391158040340044c0308080c07842140c05581d81100c80d1009100800400701c0001e10705012851201e000810100b840c1c0c0455840006843d822081507016a2226000d800062040e20501d0341042d03d000080102950690002c1c2d1240501034000d030102c1019040c010a20800c09a4a680f020f2281070341c6020003000940500a5007210001d0390645242c04680811500705101d4480f0f481d070f11030f024001466200c1035101d074030100c030b10600e03405000c5e0700460001a01c4008482014a110342c0244c10b6458803844000d003200c03418070f00c6612514007035108102d414980320031601140e4161078041d50700d81e41c0f4001300f400b60188140050215126480c1309a5160381984080154050b02101581000c40d0604001108071040c0e080c54aa4008000d40100203000b11050140d4110107040c4950301e1208801c0760303003180c210502ca0301c08100300c80300300415 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 977009667 1250 977008417 977008427
    0x10513090209011101020315040b06040e25030b0a050f01051204060209031606050306060a0306050d05010509060a0605370b090a0e0f0412020c101e02010207051f02090a0806040201 79
    0x201344608021411403420342800b4840758428070304140900d5031112800e0680e1a0a412100504442039800500c0e0520070484042d0100200c1c14141d1601445090a07509200b0f010b010035448000b00304505a9040c0410003c00a00742c0c007195041c043c080001d540100b07813888001e48614014407005840d10304100915062092902030030300e01103c0000d007849481e400000340c9400c030321b054a00d030b03444c1e00265009900900280c0c1205070702001c000c1641080100541020f44500d2440080d1040c0b030302c91700c40050a6604074010a68002e881e40101002d0400f107101c8507000868410b01d107002c400302c050040020310095000505520000658113405e801d00d110352000400e6040c80140d40d41c40c00544d070150490001d03000500b9517a00780340d50f413800ca108020b00b48001c0f10003072103515029101000602026103094280403002c484a607000c1c1010300601c2503d450035004009804030201800717000c050040d2440d800b80055a080c4246282615507810700301c060a8010300401c00c50034180000740c6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 977010917 1250 977009667 977009687
    0x10f091503020d0c0f14070203070f0e0712150b03090c06190206162709110c0715140c1c03020a2c06090102190b01181a010e01051309020901 62
    0x30034041011845c40c95580e110340700e00f6201000c04000d82c0c9a0044e840081e0501145a04c012411030b20500089072600194025501880b501d8a600c5900d520012071b15055a50040308010b0903e40a1000c2103200e0405004543c44803030710080e10055505500090710581040b15542c2502c4140000007506603010072445820590704e4499031040840900010030700c45556445005444015502c034400e14a51005107024043c0c0312414030001c1c1250401000c20740000801c1703900d51089590000307408901c0000c4584086007540c807481d000000300781806041d0300000c90b140f40c0340301d60f03004207007407c1c42e40c228400d6a48440c1d5001d41c0d02d1240e180e00410000b480181c48408400107140901a011901c0510b1030300710081d1080c2e81c96814510040c3e00f4100d00c03c20711400059904c0004040045481b02941070f0b8071018081c4080940300310883c400c881c016100016622414403e03404e90b58041c1d8130010070000c051404514040880d65105107224056200742c02161b00410004aa5a00840502 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 977012167 1250 977010917 977010941
    0x807050c12120a140c070311071e0e0f06131e0b0f0103140601050327101116060c140d0603031b0b01140a080d0f030c0c08030a051e04030c0615080606010f091503020d 73
    0xe003e0411454580c0760400c0a03140d984614669452200c6e400d0160f0046c020308d00b2511442400858100052405443904a521921034100d03400d182e1400c0d0b00074491060061210555090703280d60304001590340390b0001e880141e05122990540340220a2540b4040000030050043d05e0448824542c0d03000380c0780d00401402002c002442444204096601d0010f400b0350060310225264680081c151696003003228600036030440040c40da508414250040003c60340304c0d47d540c08800000040d0326948511000b0010100c0941c0d0b0010000b4202c0c603040e000070503000520b006215070740d82e00d9035840c14101d68410404a0002100d056035650035100709040300080e030604116443c40356456080300d210041100d503c05a0791030204015000f0070041c920103104d01e0b01101294289401c0141500000007412110f0900381020020940c1c05603c040045401d0303200101603d8462100540d09019546890810071811031000103040100300307414a00d00e00140c90050740c6140510404003a1840c00c4000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 977013417 1250 977012167 977012189
    0xb0406060305030c0109110a0605370c0b0c03010e1503030d180212030f0403061104120f0c061d100e062b06060504060807050c12120a140c070311071e 66
    0x4c100258103c0e00f16441c886000980031114178bd0f81d14044420b240b100d0000b00301541c1e8240d424a00c541013200031242c540a98a0103945a9606e01c0100c55032209000e002c010070312000124044458501000c01030002c0101905d05240030325080c5411280200010391440c2c500b640e2a600394180b4614400c040310846020758235101903080c0910491040d480010401607803950340005001e4142e0a4601800503d1040e5160303807101d05100d01c0c00440c00710244d500d1a851003001803064000c0d00e0b01d80713440c49042c4400d60244009420000d00511030140c440a2181840c034150855450304001c1c10f034890b05102e110100000000301d480184a408110b2104501e040414050b690300841628200e81701384c9410309041d9520300040320503000d0b0700402e0405204000b030758000711058001070024444a0800c1011540d01c4000344030544a4180403900c0d00c1e800c00009c1000c40640c4002004224000c0c01c20000100001d1540b0346019042c2d0302120030911008d2072418903501c801c031001b008005d41c443da = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 977014667 1250 977013417 977013419
    0x70f170f19091a0904062c0906130602030403020a0b181b0918030c0601060504090b040b01140a090803030405060f0603060f070818061519030f0b0406060305030c0109110a 75
    0x611910200002e4943d02d1160001c58604c2060f0b0b40c9401c0303e0080d0150f5070b01030600301401074103a0080e9071000e00265454020200040d106a40018103900c0384244a00610101d045a180c00380254006032040e011800343c10200400f081032400201d000701000b101c5400304c410182005821719000302200705121200a410001c20f68403144016001044114071403510260346644520314403444090158901480b400001c20b180c00001170802c0740d07602e1005008680381e41d002c1200310348070804264003080c0c400b001d15074440c95070f1002e003c9024043c00c02800641d11014030b50700d9504122000c691980c4843d04100102440900c101e40121040c3c0c0141980d082580c516244038000030305400c104800000065200074403010031282c0c0c151080c0a8585d80e04000c0c8420100d940302d500214001c07003001030f0245003110702100c0303d012203800c80400480c016290791071403807100e4058404c0e540e442c2c449d00b000c000703e0403e100820600055100010740c81c031301450a03030004035516411510070040010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 977015917 1250 977014667 977014679
    0x40e19051b070b090109020d0f0b06090106051c02040b070c03150e0706110c0a06110f2107060207140d0e0604060807030b010201061a040e011a070f170f1909 69
    0x1c29222500e0744185070032183d54450042a006000411020b5481211900a2001d000c0c0d026141060a0300038042d40c0b55590b07400c001e002d5044000c0c0f1903a0005541040700c014081c204611820700a030f940e0002624090303840034000742640040c4029501c02424034000c108101001c1030004905031031150a005000541c0c0d001034944032980300d54000e00c45002c0d0060402a01406042040d85004009407071042d00d4007030007820322400a00c0d0303c009106e000c0d8110300100f00052894105d441c0302540443c3d10210341301c00c21a9030410b40c2c04440841d002d00500d00003d080001082c030b84540c5000400c200b1080200080030b28a074003600c240105001c01091180d2540f2041903503100c03242c2d081c08540300c45c0100040b4010708050b400400e002402c0c100a1240038400f8005100320351103191075110503604c41142e15100c000f183c40d0207582c80310804c291030001d005000c0c0c48103048c0c010300140880311552000000e9681c04160521010100014000c4040300382051880c038222030b910b804410b01d17003060 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 977017167 1250 977015917 977015971
    0x40f02150d06082b0e06071101020c041509090203031315120c0f21050412031a0a03030f020a0c0b0a1d03060601110703080d0510060c050a02060f040e1905 68
    0x702e060031030100d4907004044c40b1805080c62036a404800303010035546403800c0c240003a24030040e160080c01802926000d00051805019113031741d64001e003aa03003507080d14001c0408000e111141d0200d130140000d20841c8070790444403c100300180760460158200030700300c00740108086a2140c600c80d940d46844444000c4550214404070241c00174284091a103901064115610820150308460141400100401c02524030200c003100a040e031424040082c1091100000111104e0102c1e04103025010801c0400d00c507200c2c6443c9041d150040d038490041d5a00c0309140680e058001d202120300014044400580c0a034980b0448014442d080b5802c1c2c40f82c00010340c80d064003402a03030421098542484c26410140304000082d0b0f030010b44607035245104c04441016103801c071182c2d1040d86040200203090740c020454240781a0303100f80609004040c55003040a984c00c000c09030001140103010115100321078078000d074003c4c03003000c501c0c4074402140000001a240002c00511000f1010059909840100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 977018417 1250 977017167 977017213
    0x91401060602011103090601030b0601090305160f0501091a1e040303020708060a0c02060a0f0204120606050f030609030406080c040306060b030a0c02010b0a0902071407030c030b0601050405130203040f02150d0608 93
    0x12252b80011038031801c0040302c400c030071504040d2032400b410800143d4601c0d001140001c581c100400c0d546d40541c1c403401552070000740d03c2a240088030220042c0b4144460310010916107500e41003030300031903c00411005031130700075400440150344944420311812900b000026403003480f000c0e042c0002c80000780e00940f110300180859200c00c1e1541c22007070781d844568047d03a014104202074201b00e200117085c0140948030b6817091500500c1c0440081d00a0b08022422520580c0020020352500d841d041c0c08030307281c440082c40340900c2074007484044000f035900d0180070020310288001b42d40f24180381055000f11148543c401040d0380c50414128a99140c0c800d04408a44191800589407105030a110383c811426030510b115078010010302000f000303007400c801802daa00885450a241d95044e0054030244118083c00b540304074480f5144641e51a15001035620500c24801681441415400f080c80501e2041c1d1820f11a84080b40c8000c81420034890700c0001d089400c02090300108001c402901c030308030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 977019667 1250 977018417 977018423
    0x2906100c23031c1b0503010b1c020423090402010206011e030b0a0c11030c030d09060e2a0406030f020105030912040b090a0602011e0f09140106060201110309060103 72
    0x89880090040000740c03406100c160801540c0d610700b802d154904003209180401408a8688400d0300070800000781040440c8001d520303181c0c0355908011801589401010390410005402c004550b0044c4003030015100070031056001c00340c2914278040a42d160380200c0d9016010350510400c01002d42e900045a504580305400188500381c204c000d502502c0304503400140040c3c0c003010a02c08224a142d10040c509601c60f40d480921420420040b03407244154010300d109603206001d920300010440e400000020311411001035212908516079080c250200840301c0280101c410059820819030340c40310b404841203404005660440d507800c00d82214240004e4100b01004c00001c5400c00100b01c1da15283d1003c84142e52150364072480400503900076403e0a000d43c144400019000d4014050052a4810031800561101040da1700000030000c1070200c0c507400b5141c004c24030108035150802136035421014004141039003000d40c06829105140204020100100100021044041303642070540303034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 977020917 1250 977019667 977019683
    0x50906091801020706180506010b12071d100e1507032a0f08190503090624100c02090105030a0203060a0b0a0314060403110d0203120406092906100c 65
    0x403107100054028064080000c3c15985000c1c0f45011688010403032191241c4180202c519607030b00c0c0c603480701540c0207501c1c0541c410b40b05003011948044c02603200c1801c07000341c0f540c21465580400c0000b44414103904141c2d012503000640340d04c072400c140300341c00c0344c0d108602032040c90300c0000c1c8d030300400802d410244403980c00407405146094940501c01c00100a4000840714600b1250342007a8941d0740c400c540307500038110020001c8840a002d101981e00c80c0c1806006404141d9441c403074265507005100d598041640e064200e40a50351f2400d842c002d40741a156200c24100d000751050200e15035068101d82e12a030300c00e2000f800141d4000500d03a03401003654501280085140d400b00e40094003503040284986c0100c008044000b03000a0803e10540c0603907519004505509212a22030040350607190050308100480500b07160801200c3d6002445001c0000c1c90301b240e600d4800b0380801041c91900140094000c80e80d11f40030468407644c0111003100e100211000c41c02001d000d8a01c00000180801 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 977022167 1250 977020917 977020951
    0xf18011404080a0618080c2404030e010e011707090305070e04110d0c0806160f0822110604080f0f010213050906040209040f05091203040c03230a030302120105090609 73
    0x30032048440701c96591b004108079100e041e00308280d40c13130349001c58030060076070501e020402149840c2009140110342640390148284001c0740119000d01862001e50b0500c4180c001841c07201c40c201603440c0c455551a079820b60224191715019042030615405401c41c0034600050102090908100301a911000c4480064080c9649412260f04000e9406030400d80070303410070850000281d90801d10014296603540650348141d0406440301c450583d940c00010144140144e6031140f18080c0c8201540a40c0444109001510010320315030b02c81d40006910f0742242c040924410820411001072941c1d140c000d43c1030420311601c400c07020040d449524070440c0003d02062141c2c43e10360464500c7c05002e00203021895404803414090201a1200000c520440035904e50400b078540076a8003503648100c3c2003041c9861506d600b45c4460042841501c0e00c0501c03951151411401c2041c0c1403014441c0e1030140c1c440030314540c01c01c421203050307002c2400707208800200145a81c6181c10140d03c42450a5082094 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 977023417 1250 977022167 977022191
    0x60509030f01050a050a140714090d061b02070b1e070201140a0c0b18060c2101151e0203090907030b060c0f0c1210050c0f18011404080a06 61
    0x10007011503401c1e54604010f0004800c003d82000e0710603003520344103101e001000d10740c5040182044407084001034034030890b001c4026408008050a503002051800a689542c40f411300722030040e1160281007103203441d62548140c040c01b61000401c1a540001e0a0081080489144681480040c808598001032210031a0f00404030340700250140d43c103442c3c031225031220240c0305400c0258107459006000b40001c1c1c08028400e000504d0340c0d19a409888182c85030000d503000ca0300102ca10341c0a031041c0101d0354901c0703c00d25207580d000380300803181c401c900a0030b01c40c094060121581c0158a0700241003682a019400000b00c0b241c0282c2030700d14040765555440308078014490000c0d004d60100c0009204181e5400000c0d40c444841c0f100b0b01503602a00f008820010001d11101e10300005070405401c0071081d0340c165000c60b85c014140c502c450703d0a10082a07048455100f4020420041032241c400c0302156401810803460f200d08042240c9003904016100740e480d490090010440b648401558048d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 977024667 1250 977023417 977023423
    0xa030c051501091a060a0c03032003070507030306050306010e0c0703030e120d05092103130609060c0206060a081b060d060b25321518060405060106050903 68
    0x140c2844088501d00d540c544984202074000c503103a0350000d80e081041102d03503181c000101c9078010420303152400a00b80e1030b902500503280a28070500050340c07080e08040e20b560900e0040d41b06500a6031210356901c040c0c03501504841407030300303d07070f02a600220062140c0d401000079550840d0510100c55110001c51030200d0240c0685042c1c12218000c2d42007505070104041c001d46030303003142b05006019540d1f898100c0395640c4000d035a0b200aa405c0c400c00004020380d0b0034002c3d40c111000040c0c210b10640140c8606007510150b020444000356160f1400010503414030010340c0041c401c4810840940c58402144c2c1d0302c1d018150034100042c4505c54a401640d6400115080070f901d00a06101d0181d4071111009c1d941c00400203c00000002c3c0b44c585400c1b842804054001a80030604032124000340c4182c4004500d80d2001c038503da070500f10041000c00d02005080b501c5c06403815458014500341d10740859403d440201010517600c001c060100003440130800d1410342d102441c0131a110300c11600000e113 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 977025917 1250 977024667 977024683
    0x60a0b060c0a050601090c030e070302010509060c01020a090f06051c0b010e120105070225140a12051e0309061b0c060c010605010905010e0f0d0212030f1909080a030c05 74
    0x3070724801d064400d002c0080208007541282c0a0f82010481070000d82c40c03e07429130b190040110004d80103035a06000541c0103d014103000e24018019a0a06912810150072640010190000310300c81000c104041030344e03d0155406070010b4a0050f0a05d4800010140300180b48461015015103902d2541d05503481081c0035030082800810034024001510021070080409890303035401401003844007034903212011000070441844000c1e142e802454101034507070040381c504616034030580000d40080c110b941c003895172030b420340500058030102481a4000c684d8000380c048083c016041404a081c80750f41c3c001c02e81d040d0741074017903610b004985003000ca01c1c01c100159904070b0b03106001240102c900c00b415070040041da8400e803188501151039200543d10081203414250340480309200e4110142080d4003000d591610203003481c1d9a40c1c494447c003500b55004640c09070030442c00418004898410102d115040d6034543c1813130411a400c10208903110036041da40a0103004611903075104000007080064 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 977027167 1250 977025917 977025937
    0x1150b0403051b03030904052203030b100212040905040501110a320f09150c150c0403210e100f0201050141030a03030b180f310c030b0c070302060a0b06 67
    0x610909d04a00d4003600420585503254060144002481001800000c401607528410400907040c18036000e2840e000d0302d0002c1040707500d5521400c001d0540380546015101d05400e50303c42e1400c1c0150b0401c90001c500441d01e001c803151300004074854405820b0000c072134a2400c0c1000385903032520000049060171165801c4c4107205800018610300a403400314007014041c000d42184507a50b01c580c44515920f00403800003403c00c0301076525114007031881d5082010156800c0c01e0840700822054000b4950203444262040484c0303001010164207542032103114054030701e04210305800452a851803141103d80b0449200013902c0c1d4442c5104851302c00302401c017126000307003110070420951600070064241081d03540d00030066802b101c031441368020350440c40382ca08040d42c02116501c0740751075507003914081a44040d203282c038610036114821580e21200d24900407803400103030314694030300ba034100341001700300c1c4050341802d003c5040002c0d8085245034000309900300c0851404145000078105210392043c2c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 977028417 1250 977027167 977027221
    0xf07230a26010512030f0a032a0f0e031c0e0102030d020d0218030114040b10090905070e0115050f090a17010903020d0509010c02060c01150b0403051b0303090405 71
    0x2020034030140100301d810390300c0c1500c0007130800940da481c2e25501c1c0500c40b41940d80301c500f484020304c03079032003507101403000905601e103109104550002030107850002c0c1031500014015510075070566820a101d2f24480340245c0040c60b009002e07501e900341e5401e203110703030004000300c0b8001c1024a0f84200180c60504803600d004551b12000d68401e10029400500c0c000a0764080d084200c8683c501845900c080d889102043c3c10160740d0ac1da10840400f80041100d80800511078020414049510502120b00d21800c0100a06402c6c00030040d0440c5050b0301810042c442e0480d85e8034440d0b0300a094030410401800040d842d03198280c0010000040381e0002c210708441009455a1074405401c540011401380e02034030280351640b030046541c0c1c400c0d40c1c10140400c140318030310401410100000e2a40d005540000141104103403038400120040c0ea1100f11070782c80104007803050001c184132245251407010601c80c514000403010940360301034004228403c59445000030510b07a000d03200c0342142d0703110581c5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 977029667 1250 977028417 977028467
    0x605030607020c13110d0e12070506040b013f1403070303290f06090d03020f0705271e0108031216080f070203090907080f07230a 57
    0x259180c410095540c4074210241e01d0f48441c401504c82c001c0c56001e0317181040c0c50143c3c074002200250100321a40d0645210b01e41c0741106200f4a4030180c454640304401a0140f07007840d0400280361001a04840800030b01b02d01c411000c080305282221030340b41c5c520030321131030b0902c15608104000c1e0b000d40054000c0c0f031300c40b01d100c6403204040000d200c92352007910100002140e03144c518114107080d80e5900190030b800c68201ca150b1408010800001d40024000b82c6055000360100300084500b640403405070380400c075100e80d444810f00c501700c05400141d40c6d0702c0d060800b03418007500e5120598842281c0c401c00d880442d090320074121030052500c18210100701c1e0384d60744480c016600e07886400881c112280b0751001c111200e046000c0c01010350710f10f41e10003803551942082c00401c0d0101500c0303002944401c2241a80c140c6070690068070607003003500d491080e4500001d0503030940000134480d5042110700d10f0f68003500d910741360103004107041c000c0180b922000140c2c0252959000851014a0160800340e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 977030917 1250 977029667 977029681
    0xb10030206070f0501200a050c03070c080601030c08060903070605040809100503010515070506040b060a03050a0308190c0c08093015040f11060d050f04060b01170a0c0306050306 78
    0x107180303143c5902c03e20003003140c2d0407000300400c451808a403500c11003043c01c0001e041500d12480281804440301000c0e249407030441d80d0f0f44914091280d1102181340c2000004000303105a41385940024480d000243c0b0072031409810b403945910441100130400c682e220003250a00540d070050711390106010380140d505e140c400030f014089800900c0b4140c80f4030a448903131311752032a601081d10344099001d0020501a00c407a035445015407001441142c000c8400c2c0000004280d0401111032101d000382c4500340c0900b00000005140d80320914055041030904032500d82c1140c0c45040c044d41c00f908112031640b83e008000c0000d01c542980c901c21034050f071018024845110740c2c080c2002c600304800c0c00301c40d4550803178080c105907524111005061000441e04850100d803900c4004503040500404a51074031007441018003c540741540c40c240121188002c20003000751a1044544803802400c100341e0000b8440510cc1401078010521030040d51101e0201e900a03010340c00120181400409031060b07850000c1c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 977032167 1250 977030917 977030933
    0x50c19020405010524091c0303061d011d040201112a01020a05100e010b06040905040b0906220606030218070315151b15020c0115050105070b1003020607 67
    0x5826481140781c000002464030b0035a50482256a15841d01d03d6041040f5aa01e100f642100303682d41e80107074140484004c820520481010041e100b42c9001400500340038100050300c41d44484900b181008000503c0b01050100b9044076900040003044490340e182d10040fa2072880412000c107042c41004503005203480d0100381c5801e0b4004201e940d00e0041460401240e0342d010705071020f030440c1c000581803440b40c2030742c1d0000700341200183c2c00401c0030180e9001240440d07010758410310b000c580d0759042c0310802c030100d8180c542065040703005001c0c03801c0003560280c0000d10254010881d4804e2b2159030704004082e00420002c580090008110000c0710442c54960701088031440700080c03800c890100480304400d0184240c2d01208402c4101c1c81c003003c01624104250030840c01b03903c1d05508074400041511004001102d640d0310056140d440b0400d4840c00c0d10240307085101906203842c0140517030f0741c1c0081521212508101446211340f190420301c54800c01507000030750444c1002800c2401d1007010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 977033417 1250 977032167 977032213
    0x21c081803010b0612010608180d0807081302100f0909050a060e090303070906110102070b16030e070806061c06050a14130f170909010f03030e24030403050c 69
    0x580083c4030b02c83c605000c10495201d2120540f2010303045100622000344519036080e4080d654241e04003401c4e42200c111403509010301c681c8000900c110b0704001c411039011001c1901326100c1c0300701300300c8202554009142c0d00e0000015004001c0300e039030710b07980a038030401040001f0b001c078010800a50410000381d1014004a0060110322000000071400f05035002040341e00c0340c10542c1d1040081810b15800700c50204185544e51903c0d90280481c1300800e101d0140c0c140035a038038030428541c007180e403100135040d105040b40700030030381d04030903c02c00ca40d0b103011030300c0380d8021011036002c010703038090a1a011010885400c00343c030a51030300b01040b030032032001d03400715840b801041041201035449081d1440074042c41003004140f000c000c192240059008442c0d41000c00c80300000c503081880c001c0201c0c01c20b6009901c003400c03c0c604070404005064000c120020722031000e03540c2c55150f14140d00c039100c03a20000880c203241da901c0000014145807103501650341011461080d50313403216115a15040384a00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 977034667 1250 977033417 977033419
    0x212090616050f01051e0105042c0105090c0604180b0d0525050406030519021c030503101e0303120f060b0903101a06130e07050705070f12021c0818 65
    0x11380004100100080005940443c141074800c6c3c20503030a21003448041d0015038071341e03200c01c459800211400915400850002c41803800001800c1c0307860a4024500b1100800d0b0b140928410001809428005c03009411780011600b0003040c840c85080100e042d100614101825074000c0c8000f900e40d83c11594049140105a1140700081503164000c0100312101e5110007005c0380c0c0650049205841c030700b241400d54078002401ea0b0014600007503034000b50100d101c41200044c400000704005013840d4824107001e410719141e00b0702030303a824889440c003240303c600002d8140013949260007150040f07a00031702003101220702c041c08011755640f050300c40340d040074840c00d2182c007423075201d28004d080030b10500080c4814034a103210807034004000c0c0500c03540034007030300c948030121050080751094038283c056000300180d80c0c4144c0c2d10003080c1001c07070401041d500071000b01480d1100800c00e060501115504598040b2041c0c03420b00c0c1da4003043d542c2040c4595000b02100004500340188828030001d0649102e4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 977035917 1250 977034667 977034671
    0x60c180503010c1e090b031302150a02120c07080106060309031d0f0103020c0c030106080d021506030a12020118051b0603010513020304020a0801150501030b010804030212090616050f01 81
    0x103100c008050a0324400c80d43c020020b4400c00b8200f0030603200d1520542c8049650402141103600c5620108543d03000321108903000e10105203440850074001240d02c3c2011066402c1401c0c4020300e04001d4070342040b580c40300c583c40d001080744580c4401c14020a001071044034020071180303030b840a0103406000707413020690200340085000b401c003400c1c0c01c103600707031861000b012000360403900320054009401800d09480c2c44d2048034500741031130302c003403064030042c11440c001040d0381212110000c4c940503050a40c0b440f00400d48040c4a00d60701e0004154085650142444400d0b840d0080100d006050f444001c1ca07400176101d139041e00b030200120b200103414003c0d0401d00c0000b07030b80d041400520301c800e10845070450b910404021041c60607074091500300348000c11854030b103503036010401d003525421200d141022804400420a40d80c03d442034499800003170800e50030610317142c0c8002e0b460b41ca8003404000c6c118000204014031356558402c860040759200c2001c0070582c501c0c103195580c2c03e012075120b10258 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 977037167 1250 977035917 977035919
    0x5040f03080108060f161b0b04020a0512070515072003010c0f12090503070f110906010804020f040e12040902040305120c031b03040b0c0d0f08220807060c18 69
    0x200f010032000e1003000400e03851450f40e15131940e8a20145840351915040100d00c4140b9000480018a083c1c82c203401030b03901d20150b05050041060b420001d60040384604040000003020810108200c0225401103030f0210540c84009100b0b9114031542e43d006005100c014507204504070030643d401000c260070790003002440c7da214000d0710865510384c4441d012682d8070320f0b0350001101d543c025048407071089017545d06184080d81d50810014904a040300c103912108030300c0aa505041c0d041c0e0713910480c24038001000303080c9500840c6c140000810018025030f107518a02201c01300400010a8815042c0719a0340ea0303603a15000b0f04000d41060104852500030440412036a03541c0740155006904401e014614200348060701c0414142c41519902103030000307000c0002e40c55149406001000840c0000d000e045400a5001740415a080c08180a0040c00010310010315000c02c0030055a0121041048400b825400d10100500038181c000f081107040c0405001e82c6a404006110381a4100b03091843c22 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 977038417 1250 977037167 977037179
    0xe1612030c020a03122a0206130e0708011403010b0d030c111e120a11061b06040c0602100917070804050d05070302031e03030f0a0b1e03120705060f041505040f030801 73
    0x14000f006186040c2c0640e1b0a9034054540314008100a55160b145d00d102c1c1545c40400000d03025040b5050404103134100010400003090ba0060842c81030118001c21403103510f600001d00c085c440a0015003000940103d1a0412030b03041a03074152008001c0c81c030340d40c2b400c400030702c8084128000b110f03d00078007504958041c03808000544030003640d800018002034070200f000340085604040b45000010034040d0b465048400203021940c05607000301d941210080c20800042d00d400d10308014a04000d203051000d80100340e46150001900180c01c0e0050f60300d03892030824800c40d000d16044558018051600d0310204000010b051003100d20980c26507204120251400c0d800401c8680e5040f402d4004000181c1059050158907500100d40040050000c14400202c0c1e0303019040c0c1c0701001401813054801d8900d180401c1244046d101004c00b640c6030618640d0354641318600600b821303880e0584c3c00042400c0150900e860043c07800004020015840d0a060284480c844139100742d000c00c82000c004152 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 977039667 1250 977038417 977038457
    0x13050339030d060b0405063403170c1303060e0123250806060a090b07031809060605040b070c1701060e0c19080702030f04080c040e1612030c020a0312 66
    0x12160010047c80c28004c1078945140406050b0b2483c81344a5101840140e46071454104550f80500030343d80c804500a880343e00ca51190320141007501c14100500c038190301f54200c84903c0e81603c0c1c0c40040415080c2c01440000d0142515480c20503800310100002040c1c4040251042d204400d0003402e86484004034110b134040c070b03150b24042d00c001014140040c115043c0341000300f995012900d41200d009075118410002a0008442200003c1c000b032101211310500710f00030f102902d00c007601007020f80d18051024103d417044d48116158600007180382002e110800ca00d11009014000d140801c01049011040c024035150096100041d911301c00700c2c42990f9014161440341e110740641660f202d2039030f2020358004000a0500b0f0840c0b20400c8000c4000600d035000e030004051120040a20104035410030050315404482c4d42c420754400030440d001920340140240c00c40d25004c09601000b0103c1c103040350045250301d000780d040002c0d41000030405c0b9001024002408699a03150030903903a030003190305 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 977040917 1250 977039667 977039669
    0x100f03030206010608040203070e0109020c1606020304030b25020a150506010e061b0d111902030604140a06021912110d180b100e13050339030d060b04 66
    0x801030b070162005014960240500c150443c0c001070858504a075100700c14500ca01c02600903807840c035004641e840101b0010010314580340000d8440058050034064025500d0040d840b010303124030f40d2a004940114030a0045101d44848070303011051a01e08800c010b59545180b280490359100141c2020751010100d11030ba50085105075140c00360241c094003000005c0d0482850044450700009140115003030800c0494103070b0049445148805171151445410300d5900e681c001c07444400070001c44016038010640540c01640030703401c400311001484c400c0340740502e1000c0c0282102d10000c2c1441c02d40000c01d100b0840e40a2503500c040a5100c1c40d01c6c07240658204034202c919009090001c00040c024903040804e1403060038100750082080c1d40c40701803250302c0070b540304280e040720610706004244400113055444020020861100015a0b40302592407052524088110308888244142071400c0c001e48400c100385610000314410400303241c95202c1e40300004440990f80390201c009801d00006007a14 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 977042167 1250 977040917 977040923
    0x209010b0406110601120f0201020f010f0b12070806061009080f0303150d0201020c010e04090c0905040c061806180e0a1d0a0201090b0f0c06090309090a0621021512100f03 75
    0x410b000742c440c2c7d10b100b104403910001324151300880c031010302801c00074421000c04036551000403405c1c00c0b0540a00030303603200c015001c10280c0c01002c003d210070240010344e03d41240c0240c980502d00c2400c0704048450100d04e40090100b40603030702210503d50000400b0f140200c10b02c0e03441d503000281200c01c000040c0407418000340035030044268981c01d58025102046500d1000c3e1001c1100340460382ca10301c12402c10b40018424540d9181400300380419996810701030402801d2011814110313a49152298416101d00020058040c0012030304010a00000c4001c220f0b180300c65105083c80074080014240c8070320100b25078154031040941c0d0010009440030403d4040e1640c0c0003090411a045280d5444481840150741c005c00a24025030b000b040140c0c41030703a038080559280c00d004400c01001c04400341c0030240d15070520344240b00b40707140e0040b04404000014100310b4921640c4c404144503900c402d98581c12900046450100384600c612561702c585400c0002c070313100d035450782034190503003045003c05 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 977043417 1250 977042167 977042189
    0x1401030203060a090507270b060f030412020a020d0302010c030c020706120515100804030e06070804060c02010c0507062d0e150408030703032c0607050f070209010b0406110601 77
    0x814001d50013580007501d41030207001510700c410703190248810505001c40d9074501884218050202110040c4a216007038442210194540741070445002e825000150018121320426020bc40040340200101d40700b05134007510b001c0528a923401c01034020304682c0c2d11701000c203080c8101401d442d03201003140000d45c1e80d0780c3c54ac0001c0e81802003100c001003800500d0560140121b01c500841c40e0703540c1c0e0501009200e595500c10385071a007031400030000c440307a0040c03d00801c0c00780034a10010f000e802c00d40303055501c24900414090307901d0004a48400240c100074115004040c004201c007544400e42c0303100c00300140c994003e8080c0914980b0f141041100b01e00001a07840d0000210518040640c5000d8a611741c610034140390f1100092806c641c056101140400e81d1035854041030b0884000012038102103a030110500e61501081f00d4603040700402e07407020080005132104007098002ccc240d940b00c0760040c00701c200742d40e1510300c1d11100380e20030f002e1a40850000000f00b8580b03000080c01d90305a880312648 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 977044667 1250 977043417 977043421
    0xc2a0c0f1d0919050a0c030615060305040201090b0a03150e1803030f1302130501060918200d0f020f0306010201290d060e060910060602011517030405130e01140103020306 75
    0x45402c41843c0030000c540038014550044041643c010750640654012600002e00300541105443d040e0032a6002d003041c1800c2508200141c1c1c2c2040148044a40100d800c5a862824440c228018002000596402007050801044a00781200302511494101c038031200c0d03800005200355540c0c0411107168074001580c000091403158107040445450348060b061011240100d00c01205843d4240c02000004441d440100030070f400144213000021a6091704004001c4000c501451071000c40e00360401c1840001000c1c003407041103078030081c0c2140d0804002c644804001035000d189910680b5524010341c00c2c031642c82e0b04100c01046000074000180e070040c1144000c4804d10000c0780390008255030060751240104000b04052004606c01c807110400307400e05d02c81410340034081325100e4000008682c5060380d01081c0c2d018060035042507503019080300d0751940f081d10f6000d00d140300d2030b009a0340040003074a000031820280c1e0000011101100008d102100740000d200800c10310074400030b5415449600 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 977045917 1250 977044667 977044693
    0x1101020d150b2a01020910020a020f06030606120c0f070309031b0815070219121815120b2728020a02160f030203100c2a0c0f1d09 57
    0x104141c400000c0700c3c000b42c14040034000190034a0040c00100307015070802c5003402c08601d041806079444140c102c0712141103080c04008614135005083d614801d4085440c04a900c019546060343c4110b140081029912009460000d10444031480704540d10349000e28001102e40810342c0400c1612480700c0104100486680980c031002c8010740b009040d0b019804018080307106003098140e690340030f030200f5046147c01c0d0030010440362144646061204607402c0034842031170700229041080c005442c2c1803150b0220f201561004020203140198003000041d03041ca801ca4642c4416140085220410f8440ba680c80b400181c0d0175044191003134007994030f50403800e0b100509601900040380c0700d00c129132800326030071030135442c0018035005001d8504641e4001c03c02c500d800c2025940014480b90b041c0000743c012070001c0d00ba4003034042c074008e4521803101580c90032001d00b100018000c0d081200c01e4002a40c490303444c070042515000d841c09c00c080590211040000760511103002d2144100103007030240b0050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 977047167 1250 977045917 977045977
    0x60703020c0d06091a091b032a04020d2708041a0712110d03020c060408090d1b052b110a0f030b100e0c12071101020d150b 54
    0x2030b40c101c400b41d076101c0f250000325600d600000d07816030000200c0c580302d041020229152241c03013090014240c2c494190050181c030041303001c400f01c2c080344003880480701d01200342078030b00e911401009030401e10206140120348642d4001d001111203150941021010003880d510b4590211003018040e14410002001060030700c010001c4151403101815040400c16034801207540d0f524071803035000555840048007080402d0041442d0380c0300740e09046241184803111103032210002440903101c0200440c030b000013030f01d03240c03160a40954802d140c0458203200814400290400740510360190fa200d410de1420210408803c082001850703014100380368003990303641025028030302119044510070500080b41240380302d4000107544604c0d0158894a00f40e46074001c03425159000c2d01c1c02110315000d1202c4414a001101c1545080051842003a51110000d40305940d00180d2280c1540c0700207002400410281c0c09124061012504106241c0da030340003865445c001c0f2940d02040085103038910301c44407a11 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 977048417 1250 977047167 977047189
    0x6020f1c140a020a0618050709021e0a0206090706080c1b0106120b0618010e0112060209090403020309040609020307271214010507080c160c05130204060e060703020c 73
    0x3450210201c001c00100c00c1d005802c10b50900700580d100c150761104201c001d00407808180001045442c60070841d4a41c03551300d0120348950030400e170b80061031900c0403500c3c01c200c18003090601d801907610f0a40381c0700255170f240201d030380103244e0080003c04203401e881504518041e020101c2c17040c0c01c10110f086514081000101c0c48415503596540c0004c0340e2582540481040c0d01400b0044494036054060003000781140008801c1d8042e0300005200503800c0300801340c1580e048840709001c3c0e120515141d002480303901201948070181d10200030803d60300200a01041e0402d840a0208135540c00b0080300380d001c1600d6540c089000d607059030001e8104001800e6010392841011001701d660b0b8011050104100101640c0b01d034090788c070b407402e543d10900405421405e02d2810042030b00d800041d206581c0500e01c0c0403c0010b411461481c02d10004070704080161030f00a00000fa40e2091041800c0250301910a82000c00c4510281d4040c0d072030008291100b4a82580240181084400400284041c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 977049667 1250 977048417 977048473
    0xc0a05040527010b0909090c0901061b051e010b040b0a060e03010912050307020d090b0405060306031609020309150408040501030207210306030c080c010c020f060d141006020f 77
    0x900c0205008040d9001a00780c000e04c6030402e49039550350002c044c0700000e00b006140b50b6540d0b001c00c1c20f0203015125000e085044452500c1c004501400701040036002103440c0e1005403092060b941c041c01041842c941c0081c1800640008114419a0005100c103548011030010361081180e5010440140524030b05100814014000103003a0480d0380e03802c1036a0f40d2b10082c50000b540c044104860140c04100c18619117802d130804616140c94a0503046840c840c50180b203001c1c02021002c15640e450800c00010600700300d050485d0020b8444880c80020340003221800150700c85c8180c4c0003031301e4111103095405241c100001034603060170000194040c5d4403928048a03201c00c41041580b03c0d6069038880c004000c00740e903020820520314101804948130303036003081c000d540000851086503a0001103070b01c4090b070306941e07a04828980d8800170b401c034004d96913080c0040c1e08140d02031000314010b00d820b038032620f003e041341c141356505e41c0404ca81c0d46070b1002407008203620001009416102450b049540d10134 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 977050917 1250 977049667 977049709
    0x609150301090209150a050108220f061b0305060d02061e04120309060206010b2a070b04320328120c11120a020d020301062c0c0a050405 60
    0xe02c0d43c08100990310840d4030801007503a0b5401c607112864042c60600c0200f07400d1804250038181180c07000410750a903400b4810200c800e43c40201006850704c80034007841c4c0c02420411070a51201c0d0b03008403201c0e01120000001e85020006043c0c1c0c070300008024009500075040ca41850498201c52260034000c00e0440714154082c000080c4c0c5903469805a60010701c20755454002c40e20b0410084d151010681004010317020a004120300c2c007204465208621211000300c00b00703461803401090a010f22600151104100007401142d41141c11a83c0a40d03da20458031a1906c0322000210310300d440c060740d440d5896004010340000807904001c030841c4407158804035800da442c2d555030780094140d602e11a0030220350200b10f48010f101102902d80b091500644400d01c400307498042d03968640d01c80a10080c81100c500c4400000c4d501e0962094015011143e008460900a105420038105031080445806d4a4280c0090501242d5205a03082c11002e9210f041c00d0034188000c1148200030b50b5841c0c18002 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 977052167 1250 977050917 977050931
    0x6150e0d0506090703030f020105040308040209100e0a0204050f0402040b070209102c07020d140a110d0e1504030c030f060906050a020c010b0612010e0712020c07050f090609150301 79
    0xd4020712441d80164541001072844c1482e41c40c0207000700e01400c0000c401c0d039250404000c0441d0700501c0306948503604552071b0000355502c2444500002c00ea070042c0c000d845d411010003d62a07071070b40c014010350700200c407049c000e8107410741004168400c0340130b040410f1b4014000c17480107003016138030150411110b0036280503007910744007064000c1c001d08420345003100d070541c09101414448080160490b0b400e00c0945128540e60780098507524411000c407003415400280841c4c45440f506400011410010950701c41e49a0300c48000d01c407106511082e44200f0400445011003c03240c0111000c481d0310402c2d0169140c0340d92901095141106c000341c1360692604061400581140704e40c3c0d108141d042801030300d8126075076009085a00d00c02119010303100c20008000030302d801041d41070465400b013862030115038401e403045541168013014800b134103002044900c03140901068580c16075000740c42030b80704401c824003040030400b0203031081e60b009244080469042d1805c02caa4018604002d0000f140407 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 977053417 1250 977052167 977052173
    0x7110109230316060b010809030901230c070b03042a0506210406150812030406390e04090807020409030e0a080304090b0d020310051e0901020a021006150e0d 69
    0x10000250f04135000c0343c1d05c400640c070035a04000a1904030340690001e504102c0c440c40040c1000301240314104241c604143c03003202e245401403c58070321400103019250003a0341c59031100c41300d400581d030840d103440c0460b1007100700100022039142c1401504040260452820042c400b81d0b60142060b1030148901e4040050750f1151076039100d008502c41c0d140061070a2404559102c0c402c0a504600c4031904030520b10605800da90003031320b42054110800044602c0355510640b9100c0511000c44989600715068500381002034400c82c80030f403003948903240d60b44000030803c0100d4403544001004000d06000d04005802d06a001c061428400d0a00500480c0e03120001790000d403560303008202580c00001d091000242d28001c2c2e4401c140e09643c0740310443c0e900da00003a110081241d440c3d122903621800181d00c000c8000244010281324140c0c0c0005003002d4810034080d40c014620500580f24040b807100009201e48994030494222000908582062540403116481003100071a4401c0c079820460000c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 977054667 1250 977053417 977053447
    0x603210d021902070503060601020a06050619030506150a0609090e0c302803050906070804170a240b040c03020a23180118030b071101092303 62
    0x1040c03444000707082c02ca08075004000d15281c050b0b00418080d81010f0184100c690b000101004410340c0584003103115610140030624010445400c40000d01c89030400006000c4045800360040d04051584620740400805220f00c4003490301c550740c0020000341c02001412311580c0030000c82144038042d02c2d020f5401200084090f00c10000c0f42c031210441d0755440202e01100b654200c104c15411014100d00b2002c1401d80700b90b000140d00079000c5480601c008c40400d40710700200c1d2402100180741c03a41307034021801d009000790800e00611300c00010040b101e03148054000f549845441c0c0c4039080511000301950280c5851340004000030245448401d207002d56595400b80c4201d8a02c580d8005807200303450071009041445401814403c40c0031401d803800000b4090045440b14003011401d003400e80500c000482d2800502c08420f8000310b81c0303040101c204030100710303a580141e010344d4441034401c10525001c2d003201d94000d0004c114040e01d190f0b800c110403001c1c5251aa0030341090a0705d04000100f00d030144 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 977055917 1250 977054667 977054677
    0x902130515010210060e0103030e060412060203061c020d03180302030609150f0108070311130203180d05280905181009023a0f091a0603210d02 63
    0x107030108200381c04141959041000d00345600e40c0800034042e4610303107885a5280401800050b04000150440d0105a1219401c032001054404401240640e1300c1c20f200d8020340040d202c65205601c03040e842c0100140c009840248103400400304003100d201513a00340d41c19100038010742c0f60440e86420000c09640c0600803075200d008000040c0c0f002500d0005800702403000203151400c00340301540140030000d0001540c100f81c170751100c0c1c00f035404c81c11035000500d00c8030034400d0901043d00001c00c004071100a0707612124100390702c1c1d007115000250b460701680e19028004d246403608145100501803210703803030409845c1c4e05141c10720361185615040480e420440811009116000b400184801c511083c0091001820768a00c01c40c01e000d405692042994203d20500c180c0103030024001190b00145884a4901c0c2d601860402101449170b030180c0151460080070b846008107030b01c500d00a2030350303030b0b100512914008018100703030078582d60320740620b9000c41401317000c80a05000000e14070403144003c2c9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 977057167 1250 977055917 977055931
    0x402040b1804060f090b1603020d05010303051e0414090c0405030d0c0b060d4206050a1e0605030703021c050f2a0a02030c060f06011805010e0409021305 67
    0x1c245003604104050701c00c1c00b54540c0d8591700e401d804001042403107841d00d4000c0124402554402110035086010b0700810522101081c5070000010801d50010024407102c01000c0001143e0300c0001522011400340d44102d819100d00f251402c5110324100c1e032010b83c003c0040981900b80313610354004c6860109000702d41004a0324150350b01060101c1c00100981c40a411924414041d07034550b41c0e00603140034010b1549060800000400b61044450080381c0c040b4082d10680d1601c1104104000103004240305041c0910102c00300404d1505802d044007920482c0e82c0d01940300c0038a015011521b135840200014201a404d000a0521520712400280e02c07a50809003c5098203000207440501c19000d0018076844c080014103901c90b40300c0b411601d80f8070002c1013505407108d880c060b040e400c5224100c2200e01c00d016041c1008075501c0301c1d2100a000302030a07078540d60304415031250307480d440301c103801813a0114191865031541480c0a40100d210144058201e81ca402000f030b65584c2a55400d44010b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 977058417 1250 977057167 977057209
    0x9030c0905100806070e0103020304050c1f11061b090a0b040803040e0603010207021e0a1d0a18080706150e0406050a150f0b070609050f0304080d0f020607080402040b 73
    0x30004640c210b00d9800083c040d01d1015050702c1c282080007411a200f10008141031580100028040c06030074404400c03020005082690642c2c4d442495114601480710043c0c0490300c2468458103100c00041e181e440703640e0040940035041800319009416420004030035038046524500130130030070082000742004021420095842c1c074141040703411014802007100740681c1c41400742da00580d49204403044070310341400341210801e801c2e1020404810141d08038003650f02500e0929650000c550311800d10500740c1140030440c803000c20203030500169104034040c05041c030600084022a0303503030344505210070b840240341d4015aa144a8444449421582507d0f81d950340c908002c140d049a001300c601f0b90f5020308403420002d043c01e4550600548074050b11050a00104180e0200007155100c0030384290014100e41e082482009810390380d5205000d000ca444c0980c0700e40088050080700c1003440003036950041d01c0f8540d2513050880715003100030002c0e070788a9200c05c1d270070449460724503010801c8a00f400e52 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 977059667 1250 977058417 977058421
    0x21050706050c03060f2e0c1b080d030c090906030503070308180d08130602070507032609040c0c080d060618030b06011b05010c08070305100501020601120309030c0905 73
    0x110302121402800c00030070000401c108441566481882d130280103044a403109981c00300320400ca000c4034900b012035088425440400d03c1c09806c0b0420380c20040c41049201c0b2039040c0000e0b51544442d003032241160550020301c00401c103d00941107524800420300e400342c8496650401c03c02030342c96680c000c0e0399940000408006040d481241d0a90054504000d13061500503a40300f035035212070890841d0104141e04020136011841c03282850708003900500199140c2805003400758403680244000c5400a03050f0424a100b0055001d554035403280325007a5a0901e086801401b001c0c02800c900c000422045503101070004d036030384021f4040120350b0103002a8550030104007806d0300156001c40003195515480030000140550001c2d5171092081c030b0011039250a00030440c4904101c800024015401c0903040c000569101100c00d220f0109603a09202948840030003507202c0800c0d024540c0107800c83e02c01440400400d00200100601c42d14112400603501d0b02c071811901e003582c108041e500d8503141 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 977060917 1250 977059667 977059673
    0x5100c0516151e1d030a080c010c02060a0b09010e0702031905030712090c09022503030203070806011803030e0d0503030924220f02122b080112210507 66
    0x314440c0800d141d008411048910160160400040340c9203001c2c141c07040e01840d21151000d0005400260b4051f14840c2c6440204054a0181c0241e00856005225141c0010040301c818020b94040c0d00026002503c243d08100313101c0200c100041a182c152310042109296101562815003010700055803942e8503800c114400912041140c80c86000b00381c05c1000e80800b14200c18805403c031281160b0059580071a521100c00e2945c0b071403204140440070004000506406400841c80340c112961143e1031507403450010b640c03c045083c508100401e000e4014000640201c24550a00800404c01581075203213070f0760513113140d008079000300003904800d070203042d4a00050f07814a0720100c100d105c0707142480d100010341c1c81051f030320403050300e004070a443c400244070011060070021500078042481d800205c0d01003a07654140c00580b244140e00100171104130302da806600e0101c1069990710030300c0a910708991807020091070303041521710984145440706940c107000c0e48a480c21005440302615842d080c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 977062167 1250 977060917 977060927
    0x20090f0601110307020603010e070c05100603020117010806190f02161e210504030c030605061e010507030e12011b0306090b090a0911210f0705100c051615 68
    0x858210300e0f600911115005a56503030540303064070344040303c0304441d584c0e103a011640c080d0700200250050140807202007510041c1e0b003051069a00031b881e0143c0d120001c141e401c10b80320007413040d410b450f000140496182112401c44140990001c180450781d280b110150200b00e81c800f040061508103a11a41d0301000103400300380d14a817005030000301031041243c4035a4140450441c40f0441c40303241c254030414480c091030a580c007842c1c101840c84180380e168500750000b0842902c16502c10704800c00406224075294041106d1498180c0d2a9401c004623a501580c42d904d41c5540e00c1d5015210200110b146d0340300340325074030015141e0340785100c26245451000d0308030740706500b002d00b0b0740e414081c1500003030716486001d54105a007a5000a070880f40350503c050748075038880189910200f071184404038448140e030450040c034410401d440c040c40c01c01c030409a40e43c3c410710406801c40300d40342c5145e11107030141301044061802442551003441c840c1160310544115a0003140205c8480201c00c0040d603840 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 977063417 1250 977062167 977062187
    0x309090b03370c1d0c0c1c1107060f020c030703050c13390216050105090409061a0a061110020708040911281202030703020d060801020406020f030a090320090f0601 72
    0x2405c40c3ca840e028001140b1174a95590703c054a04000132a0500c0a2803440f98030b0541d606a509001e03030364815201d40c0c000b030400410010b610010320602d5084506480e0100f5a80110307603100000b020007130021010700401d80d41001c0e6252038550b45805103503901826240188104904d0503940c44090011201e140070103524410300b604540c001603000703980c2c08444a0748401e0b01d10034245a034070f40300683c00160142c0301c080c1d4002c0c0032606100c40002000041204da00001c0803c0301c0310500c02d6146d900c01c030f9001c01c445084e40e40c2c0740d20001035032200c841e247d030003004564010401e852070161101044019290050702c031500040e030015940954559581001c0f0465070400d044041e9040403000042501c2d0f0000641c88440ea80040420460350003a0704485903c0140e080510116030b4034074002c0d000390018440e0001600a001c0322000c8404044200c525148513900c45d0300a142c11626203801291200000381030302404c030019807d041c0e44904000e0f01c12306880c5405203862425200043c401018 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 977064667 1250 977063417 977063431
    0x110a03030e0c04150303180b0d0f0b03030d0606122a09050d050c0103050109090b07030e0f120318060c07031103040b180f010206130f06090209040309090b03370c1d 72
    0x41100f00344070104100c4100e9400c0d27610010042510807101e502200240444000c0650510001648135031540158028400301c0d002d9032103035000014007036400c00c20740390b4814600700087e4400000c001b40d0b885011140f2900116480d00900c150b4840012902c03090661a00b651203920040c1d030140290b80c1401a14054036009409000202003559031083d03401d4050520003c0c5501e540c22501300301020000b41d80c0412541c41100c100080220300040940d00030751f114074080032146100030718084001006809000903000b44c5180140946046448c0b41c044452512030f40020000003131901250300c060000f40690100120707031206041e0410125803911412a410741d0481d82c1000801c0003454504070000350041034042541100745081c000501c0301701c00082d442038501c000d020a25a00000820540d600d50790108000403c0c20105035480344452000e1204968a0401c00c02901e11b404034000343c7c003031104420000034107a50b980d0001c80c90903081100f41c04020001c0503042c9074404080d68108070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 977065917 1250 977064667 977064707
    0x120705040f0b0a0509010e04140717060301090c120c08070b0301150206010312030207050c0402070f0308011205030901050a03020d06032103091110021c020706090501110a03030e0c04150303 83
    0x40c10f0b00a4070a0058a4038913050000c8516003061540b150340210b625414400d400c0308542c5020a0040c0c0508000c244aa5483c0d6035240081c8681c101445600d107860740189000d16a82e00d02503030038140c00c03031141c011900c01c02c010074000b440640c20440d41e009004501480e68413981800c01194440784149811411035110900400100c0d82440c2c00d601d80c040d0320315003d0780c1d80b112410154600030700201e4494000e40300092103418000750700010140d0714802d030b50702a42c6907a152402c41c0141044c0201400c01d81003000300440c1980140d000b131500a809060250601010f100300b90100c0c0c070903034020381e180c11550f040400849804070304134030f0094560500b007143c2c010a8840c0320500d03c500c000d25004142c94002e0340d0029001f000720321a201441d0016100003140200000c4d00d07141948202d0000c035886500205039980107505810506242074000d094040054404802608552880541d41d0140d08207580e182d07111405110804010040540b40d494510314008000c6001c0719a003000d154 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 977067167 1250 977065917 977065927
    0x2060f13200a050a140103060e071209022b06150b0319141311010c0201021c111002130501111c020118060b18100e0c120705040f0b 58
    0x2440c9090520020486944010324401040c000c154080a030303402c00c503401169200c0c000350310001c1030144081c42d0070a1f1ba06205840e80c80110b849a0001684c0500200e201e0048100e80a401c541c03050310814001040b04401025090200c01151001118800748030700600845d028050345009840303891940c2016812440d280428808090201810442c001e2407404194580311025030414201449140d00c000360a00300b65900c1d016481200e40c0884400000640505003513018000c0440402c2d010380103051910b00c44041d00c0500104081000300b4040d81c140449076030442086480d5004024000041e0740702421800100d0400752540300904000d6126542c1003840310224420525414014140fa4503000d104002da01501401403000110380d45401e440c1c0501010b41c01039800014155104004689032010000341814120307611002d80544400810001a80c500115404105c2482c1c060401218060707004a031402070710328000043d40032034240320910301008001c0050009940c614603003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 977068417 1250 977067167 977067173
    0x320d0c06081509011d2a070c090204030803151306120303050a0501080a1b050d0f02040b04050c1c020405090f040515010f030b07030e010e011a1c060b030a0503030702060f13 76
    0x4a58620310f25030801c00200c04505020000030709020440c046d03a03221040300110115107806508181130540c2d400c201c085000504181600c2100e040d1781d00543d0403890b540d101d0031400c54849040582d940c1201d00c45031580d9042d0703c1441044007a00306076000106007520f03800c000781602c030050240d5450602d03001c01000f81020002ea61317100640d1200e0f20980e038001c3e442c0350a1840c00d65901c41500840341c071030a001080243c8002c001d1461080714204854464102441b0440d9070890700400da2642c100010080140107030507081002208140140c607140e1680049003d04070706a40100420349544207100400000f07020030b20017404103c5070b207040c640c9468460701802116200260a0700368907008204401e129801400351207040b04000d000501c0003801c814001c01200c281621981c1d89400b280100c0d16144104140c400380700c81d6904410085515080c008100b2580801d41c140b00e031110700000a42d0900c007640c801d03009900a80789a2500c2000c0e1404a00e00a000c3c1c0c1481ca40c0320034904c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 977069667 1250 977068417 977068439
    0x715080a09020f030601082413020f01050c01050709260604030e030f0106140a0b07031b0f020d050d021c0e060c071a030f0106140307080c13080304050a320d0c0608150901 75
    0x30440e01126002f0f441034951006803070701e02c07401ca041455542484e0401411a8004084400310342c00e4901c03801502c5083c40c0d02c0001e8201c020380300d900310380240000c107000ca841020f2204240c003004080e100c4156480400e5421518280c2c4105408940794401002030718118581000400b610741c0030618101c0560341c0140003c801192070f040d03081c0c0c44100756040c0000b10302c440d0710300c9502822000d9002b00f9810015960070809106200520481d51340c0d0001005007014402483e8868a640d491000e070714040041c1c3d5000212407003240e03c103130710300041c003008020400d4a06400034103c3d15520304003010085d5030003405801050600064032034048008400700b0403298851071500d0700007a83d072079a0b0080b445078032900388001c0700904900b0700414949004401481256000c88218401e6691a811402d503202803003e100010300e99544601881c00401c0c2500c08811001414180c0c1c4041c0c0d075441401440300740d084000010004070401400308096a602100000101c0d4030280315031528000e84c41d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 977070917 1250 977069667 977069701
    0x90c0f090a0203090a0212100501050a150c050f011b0f0801030305040e062107050102010e070509040b090106050d03032903030f0901020a05010c110715080a09020f0306010824 77
    0x240c10b0307400000240da6040c24020000d410f81d0081060790143c0404c01c4450b81c50502c0003212400d60300d0407000185a103000a031207000c40311103903101000c03111020390659180c01c00303000c00e68042c000c00406400075242031040024807071191085158640301b191008090443e0146601d00f840f081d40b0060001c80c0d049400d450440d24041440e040b541c1d24000480c0d500407001c00c1d0f0024a001445402108090200d924000d441007a4002c004100114500340c0d9541c200c1d110301c40c2c10003403000124012515100007158003018440c0042003003139485020441040103000c091380069601c041005907401401d002000c0e29001442d224808a0058002612031241c0806041100c00002c2d113044035034020700150701e01c503400c400200a88892190094883c06501031581c0440c01490404510720700c520004a9010045541c3d0b03801554426042400400c95030406991003217002250302e0480c0d0b81002500e000c0c14820020700300b540c601c000081042d07100808c204c0a55441d030001c01140305980c04a4031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 977072167 1250 977070917 977070931
    0xc0f060909052a07051608010f06051806011407050304030c06030e12090301090b130501050106020f1c050f130905130b06040c03090b040b07020d1b1203020f040e090c0f09 75
    0x1c500100654510203d4030802000905900500030681e04402c03484402c40308441488000340820100e2a01c4a0100c810b10701500e5800301c505401720904403c4400c2480c0e0103081810039805018100800081c59003007400d0440709640002014810084082c0342000205200e04003808880500d80895480384580d00203002c0c4480c0108404c000c59409401c00104180c00418280e00c500300311620541c03004000200303403030a608010001400910010720303c0207854103c0094004214490a40b101100d00380f0441410080709100caa4881c5401000625060f8000415820914900501802030344c500a0000c419420803164400c003140c83c0c0c0401e00e43c04401243d00145000c4110026402440c2842c0b020386020362200c1000300b0090307400c41e901c0c0182102e4088410510180c40120707105207100c5640b140d00308826640740001350b00043d5000c00820281005810600603014285a031307045030784044004102304e01480070045041c0300180104c00c0c1034840c030300c59020182c089146154090800307 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 977073417 1250 977072167 977072221
    0x61202090901181b060509010816120f0c03060f0b04170709020c15010b031e1504020a091404020322081608040504150509130f0c0f06090905 62
    0x19900c590a42c0114030f03a07039068065001c004107a042040c4c1074901011500810040000c0c007068941c001c0042d04e03500003050b581c242e000e0b41c072600380d40d4034618402c50034424040d54001c015040c03078460241840c10721620000150304940c0070001802d40d805035020fa0032030135101c1c5013800103400b424100c0741510260051440c0c40c103030b0030020a242c25102d50110698038800f140b940f9000c0004900c8442d0b21007408400c400590b00c50940061a00c016141c59022085d80240f1150060042c1c0b101603100b4018081c540005010078042002e071ba11215030b440004410741010b101c4c41da9210581195000b0698003141140740030a281d441e440440900c1226038200c040e035260802982100b00d85800c2001e440140001e50310b45012159a0018000d00d44540d081480c0450035540001004080792030080140040341c50700101080d90301201c60341910a25440d100490204540d034042000420100c29107440091030b14500801040f038a40002d8146802e01c014861400c00301e90105066402031040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 977074667 1250 977073417 977073421
    0x60406290630040506091b010207090e0307060f0209130b0a12020d15060e01061e0f0c0c0b0304020301140405061f090c0309020406060318060209150f130906120209 72
    0x21407524450907032040010090b440200010004040b51850003000f4510032542005012822000c0c000ca00360440342c0141e001c0c0808000c1e01c01d041d08541c1c018900e08081c0e0b4545400d0b9120702056a0946d034642d0900740d000500c8611038141054034000000344024108020006c000c00115210060b22581920406080301d0780d042d1350328420b607020300690004400441103440c0c07406001800b801d20a03040d003000140c0001039a039000da8541c4020301200d5034134420101c0b905200369869200d09405504024070520804009545d2543d09009070840708811500c03071a15104141c00e480000001034180785940d010b000002d4400241203070000b8851105025542909000d0050401039920a07400d2600b059418092a5010f07405104110b009640902020ba25410282c0640d01d095000d00b408856410700300003c119103501825042038001e020500d0740d44007040c0c80c05a41c010400901c513800001503641c0006200c050f56000401d991013090195618040c00c1e0003c80444c10800b0740550400c40c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 977075917 1250 977074667 977074717
    0x170702070605090409050c12012a050a1d06040602010e0705040603120806030a1217090609100e01090602040b28080103080702190f0503012007030c03030605030604062906 75
    0x1c250f01c0d10340223004038610510034914035001c2c0884c00b21082224903440a0110014211008841d0488464071003a2038024142c0381122110251001c2d002c18000ca00310040444d511000148001d041c02c1d40080707045481c0c0a8503e0800c1c0080d884648540d2038003000704005400d222045540040f0307414a24007a40e220804a420041005001030120346042c445c0c0126640102280959004400c030488266480303c440b940d442406a1740010198800b84100c0c1d414612500414034100d6440004039104006588a805a8006401a85100002203040039840e8031401002c0c0c429400710061f001c0810008501078a242c6060101400d980c03400104c000c01c0d9158603814402442180a140040d00c7e55103000c6444d21045015142c07003542040e0303004510041d950b82c4401016039545c8080e00e07241d0580d8048c0d60051180c1e800300d0901d0749421002610340d4092001520450103680041882144400080204000c40c80005410700c40500000910780b40c420940340110440783c000c8801c900004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 977077167 1250 977075917 977075923
    0x32402040306180b0603010b1c05070812040812120a230c1c020403021e12071e1d0129070602070c380f0a17070207060509040905 57
    0x14101800407410941c030307281060900f0004140d441e010300301000007030f100c10b801c060036108a400850360010500c0d04031642d1505040e00c4065481c40f510842e6a882d039a0a821424010022554000018081400c100c110f80030b100c09001814407008407441c01c400150309150440c0302030204c01f00e2540c0d41c103880f82c1000411040100c20400061031140b03c0c501034809501d81e030701c06000d191031503110642c5440041c2082c020f80d01620f40c003d040c42c003801c0c1c81c0f030550202c4d560340c120100c2c1d000513a1401c604c109101405a00301501501d1f00d94030507282d0300000b40c0c4501d2904d912031031498001d020403034030200c41314900d00cac10740c1c3c1800a10b05034041303031a03540741d0002107400700340c0c0502d07a0001d482810040c959000703161017031140c1507022015641d1903811410105020030148000c01c5100440007400000c11000a014002d850b018200f404846511000341c01c0240c640010600c100c00f0280e500b4000c04000f98030003035a2004000c50390815400810f50700480105d1801107888000d8801044414 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 977078417 1250 977077167 977077169
    0x120215040c03114204050d02150f030106230406120c05090604060c0b0a0213090905031306020d08010828080d0c23090120070302090a020a0201060504020403240204 72
    0x4420030244d9010f4075800c40729445401d2500d907040e80c1100381d0405804c0e40030310070745084510090110804080580038000140620500c02044540400c4040d0031000c03880095030103003d89644608030324020302522002e6a03082848044282d9007400204080e6500c0203040a03a8480200041a06101d0500c2035500b4051a2102d60344484042030120741264409441034140b400340954011b280c9900411908034410340a0361240900caa480a110981072504031a0242c0c0c410422207240c6201158090700c42d164a400800042e0070002500142551041d88039000d00000409484240c804c00000044040c0001c1481541c0c1d0140c3c1c3d01209000214040ea00e046075001c03410311180320039810081c25075038000d058811043e0b0100ea12506840e40364152201e10354181c552180700c114080005aa428440c15019100d106210000c4016221030000301c2c02070f100140050b072914181c601c06800e40c2c10750b8111034003070791040c413040020401c0380c1c032038804500140c01000303040042c02c4260006032090f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 977079667 1250 977078417 977078449
    0x81b012a1703010b090913050a2303070c031a150d02030304031a040c1202030615030a150b0f04050925080609100f0510030605061804120215040c0311 66
    0x4000001c0032500b13100204840c0f501100c04141c559201864811b540f614007030040c0540c1e100c3c208420000d440c08048840654000c0d00546030407419603d1146107600c142e4089030b1041c407611040003003040d00c050f0b184280300c400d0011185e615005c409903002c400800c20f5544203110424152083d91014000c503000f0310340044c08150b407000c441969000780310040d40c00320b40c0b0700c224160000350760114004170100d49500402402d00f603201c45050455900728608610340c18056030150702c0028020030031110389a40070440109607030800b8000c00800341204420316001c0d41c2048208101d0b4007000c100c07903400502401c0052072280c0503d41210b40c051907074100c03d00c0c9110b00c1082c4641c10000164807510080c10079410b00000f41c851030081d080d81c000780d03440415815440014000540c2540080b07a1044001d0414200d0b48582140b0709a900d500351400d660020f420030400d18141d505000c0d8006484403202c9409140c1080e9894174001d040600c001740001200040c400110b9840032242c02010308 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 977080917 1250 977079667 977079713
    0x51513020904051003030813051002090604090911010908070b0415020a17090a0906080a030c03030209100908010507020f030a050915030c03070306090e100f110301081b012a 76
    0x540700c0c4104813445124001070b80854542000076059200c2e49045c40f40407684040580315004000040ca8042e4101303048403540310b03a040c0000b041141c01407051144490103444942041c1d8106000941144260340281c14190800c1200344240004101200c044511500c442c03103980005400c2241403000a800051a14940c244d004d002d6980071409403030788410480e00c40702113940d2081c800341200c40c1c602c070f95400c0f40c104225070b4000c60701801c5035400240c041d040141c5480e401d64001400800203200041c041201039506002c0520248503603540804580000c05040c0500c90406a50b8001c040702c010400000184c00a0103032130b108100803002601181c850b8503030a14207440f0035150021521400004c0c034100300011000014011403d113116000c1c042c0103120000b400340c0e0098800000e0301d44005c0e44403005200840c5900d0000d50003012203c0280181031958a1420740090359022502d040114480c0d1040c4450f02c400d00420300e0000360000c0c03a80c20034082c6000300b440456103202d800304103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 977082167 1250 977080917 977080921
    0x13050303042711041203020c0301051303050a120612030905060a02070b0c010b0a0b191d27010b04050306010e040b0a09050a060e07080c01022d0a050f030a0f0305151302090405 77
    0x41428821310940c5d8402d4003074890014500301814201e40045505444000e404154140803a01460050181d5445450464542104184d1001c12707518140c0c88041028603545140040c940c1c132034180f40c06800200c0380c03146440113040c4000c0d500c1030f1138018200303200c0c2c0010703441c1e072144c40960000c11000d0000e040d1541480d50b80c7c2000d071468201c1d103024a010340b51103d00003038141c0314491000c640080c1c03002211604c0e4032102448005000c0b43c1107142c48081c13010901481c2ca0301503d16070700030090040c10303c2e580c0d4100403e03d07041c0794044c0d020f140d1401c0380b28140b00016600c0440342c0d034459210700c1d0006042030075042c09481c11030440c1d03000e400185440e013181d40500021a0fa0000c1d58064002c0b50007003d02c60004a0380c8180e10a210300354442c4441259082407500424205420414012151000751070340360300c0e040070380503a410310b0789500004004400b1070b040000f014155105080400081c941207011340543c005241c250340c8100041700f2590300300a0f00750b069802c0b41001070010003440c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 977083417 1250 977082167 977082179
    0x61906081803070308070305180109050601030c06050a02190809090f060406080c213a03020702180730110306241e1305030304271104 59
    0x1180207498400701c00012403064281480300008071024964981d840710751690342c480c0101c00411001d81400110105c00401d5400800300340074550310710b8000c01c007802e03840d455890410181d1455501140034031009010b060b00b10398000c14100302000c0c2141c07030035131003402d64a080c800d10f2280c8a02c00794469005024032103054405114548200000e64040040355123440015a96800581e2015804810000803007402075a0003a00c0411902c81400c82d01281020f0b00907869042500d44080041c02c00b486100d4a9036a058000e419021441d060440ca0440d450300441c043c8a5a4003644120800c0e1801041d001446086990007503054503180c0c050a40190a0003614200340b1840d07180300350308195400010520390001c8134042e01e0001c0010324025250a104a840c0071038000740c00c50307144184520079440c003c40c649a0015904801007543c0c800d0281c4202006107103d411a030b00a41c810f000c140019070a009120422680b00200c8015200f6206600006005d6518845080c080045000210 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 977084667 1250 977083417 977083427
    0x5010602010b210307020d020d08070308070f0e060307051b0609010e21040512030408030f0304020301051305060718090e011e090f140f2b08011d061906 67
    0x30b0380100316400350320051034214812a11607241040401504100b0002005103080729014003540e1000d05480c2e181c0100f03803101680c64020900980111384103104102c0d1241c1c2c0b1a19900c900241824140c105007400000702c1c0d01408020918030a0020000d030004800200d0304018010003001e4080315030030701c2c0964020740a0400b92036850040d126420007066075000c1c0002d60826540801090350515107080200000c80700024458407150004020205d0314200500003064414050501155641024414142100c4000388101006074005980d0400102d001c548160000100d2810319620400320304104128501948040c1d949403800d20f03502145c090640100c550122100c1e500403a0001d411446025510042ca0050242c1131741d024401c00207005402c0f0601500302c4800300c5504d89a038640c441d1030903011150120401400c1c19a0050107104910318201224040c40e00c23076020352400060311000b000f840039084000700ea2100091050301d41c2688468220300094540030b5041e510303074010b05 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 977085917 1250 977084667 977084681
    0x2031e041b03051038060f070b061c0308040209100b030f100807030c1a0409021201091d0c040507210b01082220030f010b10081e060d060501060201 65
    0x1045070305041d11004000c4103a08a00e00c080701c030256800401c80d07810351710001031150183e465404002480300b60034260400d03000e404001e204407828820f5040075170401100303202c43c80441094205503050000003940c0200d40603001030b4181d03106980c6848480700f00d4011000c0f0b40082040714008010330101c0000110018000c1100d500921185625408495258011400090541d0035003000800c885541802e40350007003028130610b0ba0a140d00c41d40301106983c800000240c406100000500001c044d030710821500d1150031001480112843d4a40364454120030703441841283d540c80001c4481d40a40c01485c1e80002d42d2410031407031084500102e0003080482c006500040e4000e00043d030310700059106480c40c0120304d40c5000e1084003540c5020954803d00d05181203a00d030b2100d0f10485880070030003101079500140010414074448818000c80380c08114882c5c0c100003140c81440b224070801c488440d4026011001c5030800c2d5201d101160b14041903040041c0b03039a00c0d0900010780c01d0b1381035100748 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 977087167 1250 977085917 977085943
    0x302210c0d21020c0109270c0302070302010b030309010918060801090b3c070221071104060b04051e10030e061003030e120a0210030204031502031e041b0305 69
    0x30310040b5149004036911443c40c20343e1804070f40294424400309007000500c0c03040801d5242003191b81058070342d14070300351607900c8900300100ea00407403880300305a02070103500070a110030340081d4200418200020207411440c4980c0300e02552000401d8103001e055002180038050349802400305c086070785010380c0e0f0078030101c03440e1103501504503056915010700c1c0103085d00e00d103102c1e080515100e00940c950189103406011101540b081c40142c20240c0960703011140103c08541a5076103d034260f0808119400314070341d42c240300b85e00d480b40612600000c0c5058806a031002d942e0070030b22425098102101c903184494540d402410301c4c0080e035035568107810850081c58070303d0942c0c20315102c1507940d0641c41380e1404001d0100e209562005100c0c10728881e5510a81c0340e0008482001c040358001c40d041c800300e80c0441c00040e400213018018045c0e2104038480b400000e41c0118a146071011030501c007014844800196810704202107424002104150207030055148024200b142e13a91500b150381d414048010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 977088417 1250 977087167 977087213
    0xe120a05030f010e01060206180c120106090b060717071506120c080a0201320711030c120a03050d1407020a05010c0914090a020c0304060906031103010302210c0d 71
    0x101d05098244130803412121660002c1403940c555405000d0406081640b40c0c4041c403030442191300c260350300c00312050030003525000000c6403402e162812060780d00c1c0031003540c000c89042144c031001810012007501c4802405d89416100c041903d0640710740d010109640548a04101e004078440e0100381d901040d0a200b21120001555903030540c58444400c600702a0200f1390401c00903001c5607107081c0c0c0c01c90140c3c0200341a2080802c60041903440d8000d000180c4002080310341000741410204420741030104201c1d81c1e101c43d520748504007503440d00e08010040820202260614400007180c00001016219076190702ca1458a040300030340d0b0301c03504502074901e5801c1185060107140903442010907244031406404100c200f90341817007100c003c007900340b1015640c2007014007959202031000d4000b41c4040e9442040d41442c010300241a40e58070304001c488208100b00400c0140c1d87c41804001e04803452941010400e007100c46942400000700e03606400406412684080040f052000d81500c880904c02d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 977089667 1250 977088417 977088419
    0x15110615030601050f130906020d0e100501060e090a0b061614010b01050c15090a050d1e0503010f050108100e010605041706060a03030c060b0d0f02010816080105040e120a05030f01 79
    0x41045c0100c0d03110459070401c000401d25841c0f8100342d000f03d920540100e0b00986415140d4080d0b1045900748a20322040e82c0100d100c0d500d18880d07501595005000c98509080a02c0c070b600d00143c24400054518251a940c503805051107480d402c05952844001e030111100000300b600f0008186042d20050341440d501c0e141007980c40b0b60098064031050fa08000040c02e045102103095040e07481c014001c10754074840d0400140c00100c1c10011400c1015440e0b03121240083c0200352074001346400700c18013050140030702c01400708000f511426002c491702440c041f107694444011000e190505500001800c41103800003203465504400108100c1e44c0d6051880d405403c007040c45501c0b90000e0707c00d981d01c4414080108003081c890181e904405000e200c00142415410300040e9141900e0390084489000400d140c105560304628032070380c0b0000401110307811b440100e80041078030005010343d0780300366038a0000c9112403c040060380800506003141507545d8843c040301605540084840000c21008100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 977090917 1250 977089667 977089669
    0x90803030c0a1e1b0303091e02090f04032f07030c05010f022103041b03110f04020702011e020304180b040b010c052d15041401151511061503060105 65
    0x64403854400c0903980c1d42c06104a80441e00e0320341590413015002c0540705c420440100d40a4111516040010110f1000503c02031043c425011401082007007100142c000308008240c00c61240c0c5100600b600740304241840c00d4141361114040c80300c010183c0d00ca030f0705d008000c0040c103081e044251035098891880820842000702d1b9580444800c20f11203003a13540c1c141178001c080c0400717150000d01c1011003002180d076200074080d0034680c83d4000d81c0c0b10840c4101d0190242007541542d071221405403401d502d007030301c20303000078103600060606141008914a07200f1103052080c405e940142801e0402c042c0314103000c9440101a0007514404c910661402d91840c84940c05040c4541c803041d8000e0151032851126480303101510090406204d03204503800d21031800034000e0028131444840a01144070074205420640d01e4a4500000b080303042e0301d003007004045010b49000e01c2c011a2002182030800100b11802101c13201e0b10792030301170142e10680b0188044d240400c0040c4031880d00603400c603041683e03100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 977092167 1250 977090917 977090957
    0x50405010b0708070b0a0917070204050a061202010e130c08040b0604060609060e0f06030106020312060303040f05120f010c0c05160605182b05070f081903090803030c0a 74
    0x140c0007030400f0b50401282c0700145544110030350100896200247d00e2087d034948095034020703100307002120b0310005164021031034107114003034208100c104100800b5090140c0a080240c0d10a4064180300441c5e01d40041551214129070b481d8130107a105200028040c103014104000688044800b410744d8400620070b0f05123032180200b02c0b206035407502610351134903006039030301c110812856412065000d66074050b0303164440114020300165005550b10406080010500c600280890307110f60010402008124454450501030f00c4040b280140043c000c08601d514007805004009000d50901c0c844001036a0030196180a03030f4040d600b0b80d6140b00e1074080d0100901c1583c02042e0108805014141c0885649621900c1504000d020f11407260340d0394025501d80900000c0d00035a1915681c048403c08c5014840300008007907125007072a01c1c82c1000743c2181c4a603040240314403400e0030301d60314009151103500150028070711907040d01d50301d0404048100705a400360b000d5401040e0781c2c5107039060f218411 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 977093417 1250 977092167 977092177
    0x60806090304210501050f01090e070e1605190c151808030405030c070806101719210e01200a03081b04080705011407030e09070512070801050405010b 66
    0x40340145140c00c0c2410011109110494030402d4402140c0d200100024004d200c0c29010350781da550800d0300340d0314210162003661008003d03081e05030002101000092070818080390001d8062048481c00b10320840c04407002d01881445120103140c0100014030203820411f00c8103d1400346070f058442500703030240081079941c05242c078140460100d050700c0109401001542d089031062096074034200900c0005490004680c000d401c454004006018054400300000001000d1040d01ca5840d1000c02d100d8a45500c82c2085c00c0c40a030a001440000f045080c3c0380c2d11011814600d41504c1803480c070403006043d05200325805000c1643c402102803241685c041ca0500d4a2102004101480b95598111803810005d4803103450200780d808424061707009440035101800c0d1150040c44c03900c3c5458001400300c15103589641813081d0820201012a40c004c050800f051025685c0c10f1490b207544604882c24403603030350341c0d4240e80d04038030a211a40e81d20000d198100d0304211740901c116603c4a01501e42c40c803030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 977094667 1250 977093417 977093431
    0x40b130c06050703050c150106080703090b0c16051203061305151e040915060f0506041205070312050705060105041806091b0f0e07030504030e01121e02040306060806 73
    0x3503460100311280c8078800402c00144a40740c40750030302c002c0040051030710030542c0b100021034130020018440341d40c0c843c00032a40310383c0518042c0f00c5441aa01e07519074607070018180c0c03104034500285c009503100404200e50001e41d40401117500f501a49810701c00aa041911124480c1c604401c0c0003c00c02818012680618098914410322207820700400160181e00810401c04500050b80840c0703a0b0703903038410000b0144c00340b504819003586502040c41215550b1304440d42d061110282032149403200416627080d44c000d000000700040031402c0039454514150f00040890010780326100074140d1003806841150721520480e280c2e6620f0300308100590303410214a850383d58180c45c141d03000c00e005070086240070340074100380f420b011072102d1031031031400c0c0700c1e0000820030668807800c004442204d03070826844040381c43c4c10415802c0955005002151403c42d041c10410801c03038022030104a50300a01d140802e40810040408017168400083d41142c1f005841841c6086d000050100d000700c2c01500c01e440d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 977095917 1250 977094667 977094683
    0x605030906070c0b0f0402010c0c0609030314070b0403050f0c0304061215061d0d05070e0610030608100f0b040f0c02011a0609040c0c08120411031609022d03040b13 72
    0x14941904980c05e4030010403d81c10041d03e40380c80c0d0041414405524050440f03599004205c9003907007070242201020550180b00b07202d04101d0600805d15007181c00790465454138007156100c0191b0424442c5000307000c010380842c0000100081d070103411400c4044078207440007040c0a880d140100a18406081c1d2180780082400010417140007000c88c800020380074401080c1c004070b008661110f80c40c0201035040742c1940d00c150002d000c0d49140c03000550b1400c441a16041c8845c40c200501d25442d4030140024454280d21101c5c0c81440c200c85030825048008007400401c00103054081d14401b0382810101d0318090b5181241040c0145006100c4d40b8030700c00c2c082c01d118501210303001440001d004100b400d9040004080b4010006285003004040c1030513280e8042c039581c2018144018a140d084008900c254807060380100301c17040c01c000b900200e074100400161030380808a00414821040b0011319032002da0303802c005c080e484170b09010710300640c000c2c2d10104140c0e9850303e500d074458103240c4000d05405 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 977097167 1250 977095917 977095921
    0x10051804020c0f070e15060a0f0804060b190509150303030402061b070f0906090e0d030506031920060703090e10050d0b090d021204030f020a0503070605030906070c0b 73
    0xc1000d80007425040e5824080740c3d428656024894240070b025044204104064420710048452400d48143e04500480b40745e4070b4545150009401260b8031208501800501c00000702804100d5100007543d450284c1100a00c4180b140d0110303020781540078161180081202042803031584010f03503608420060010b6246071101c1d02040300303030303000180c101b0b0815154582c5281070f10000c3c019600201030300030050744083e06013100202500c059400070790889141a21010002d0000901b9403801c0a0724100015943c0350382c00400d0038104007803c407000807598641c0d944100046118032501003054200a80840e45401041120754031403600050001000c01e0414016a16407aa050350407000c80741d2245900c07030747c50003c80c0e07103807407034000c01e8075440845010000c405105024141d4205924400307007035070b0f06100c61485828000c5010180c201d81800422900310b4807521503003009480e004046901c583d95800f4003d03c0d40c1e0045a0650603809080081134405006010000966604c007004020036 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 977098417 1250 977097167 977097169
    0x4060c02120c0d0f0615170c01031503030804141b01080112050a0311100501120204050a1e02090a12050a02011706091b090d0c1505070803060d0203100e0c100518 71
    0x31405101055030080c0d551481050b410112040d008020514105080c1c059400041c032181412405c912027818541000c0d007164a0004158000b81130300e505003010a41c81d299424981174149203ca24800c55114800c819002105465200c1d42040001d90b00c448290307885030b6030701c03403c080e04500041441d0321a141400c002405030240344922031000044071600b80d095000720090b950281e00903c0180d0548292006504060045940c071442251060000c901040c0a010001c400c00d1440380502c1d50101e0701507125560500c01d40010241e20007250700040c081d061203074403080100030890121b00d10f94044054072051039995440303200001c2c905c1c0360079514032014503d2802001801060310100b04846001b6980d1400030214a2f8012458002e4a0f03081130200c00e070b0301034200201403d00c00c09001084c0002c0040341104d0b40182e0541c1d10a1841c3c0c0d991010030720b440a00d000382241c2c04e05018120b2048140041c5444a050046032000c2e00c079480a8425503540c8030f4509100046c2104844880e45 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 977099667 1250 977098417 977098433
    0x503010f123906090f06020f0a021e09040b010e0f070e011b02030a050105041428051906020d0c0509010206041115120603070603020405010507060b0103020d0204060c02120c0d 77
    0x4060320000c00140c500804644442e1200c543c1d0011000305107418403c1c0803494031500300d100500107500081a550388020541c075a2903000000c024030481841b040c7d803001d140c400340742c5d40080c3d0010f0800d200a040600c1d220b100140240114500d4000020014205050b6000031034003e207035648074184000590001102c40d0303146025008480701c0518107100068500f004407143c031034007400002074a428249030081c1f40e41c048103001b804c1688182110b041d80385c514003c28400f804843d007000c18492051a007141441c1c2910400030705601c0f80507110342032103141d8009002c8400001000c00c180d040c03400007a5043e004a01c04a03005034044c60010b00040c10b50181c00c00502402040d600341070301d8500710034496500c008001c0b180000d07818203201007030604100c0c800240105050a604207801d2400090160140d00320140c06c00c0c2c0c907003620740942e900a504840d0305030000802995201d8445401904013a4900c2d0100c0c091640032000100c010741c049001d0f0b0070502c0051481c641d8070703055111104 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 977100917 1250 977099667 977099723
    0x1b13090203071706070914030322050402040f08010606020601060c0222020d0903110c09160903080a050a020c22020c0f060f060a171e010209040c0503010f12 69
    0x6058802c00d200421078404003028915080c0010300242660324014400a041c030b0101c0d030000d40800304200380402155400300a030b45000e803072554044081d55111081c85d900000540c8610741042c400500440c440304030712008020f903401e00c40244080390b601d00023265551004d114407400550b181d5402001481c010030814490072451901a45a000c00d8404001301e034172001c556980c4c1503544085000309900a041000294200005010720b0600d043c080f54110000401048002c8040c00d04041c0076801000d440001d0354026079400c1d01c1d40d4051340301500740e0b44021400c0d80940f00d0446040719a03e44428a100320245104408035040c00421078003019401c24001240940181141e800619100f0403140d0b12031103651200000742e0410740d041c000c0b04201a0043c10244500031140b02c4055800181c03800320b148031044080c6944c4c405510280240103118003141d03c0307800c140e045c01529910402850589942d0001c091032290399500d41c4078180201e00000303000001800c003800002c402807907001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 977102167 1250 977100917 977100919
    0x70e150a02030c1209032b0c1e0c090609050601120c050f0f030709120b04120c02041a040522110109031a0103031202040303081f090c0206091b130902 66
    0x2c0c18035003400700b8581084e034030300301c0e1602c1c00801280c0c1001514007003214a02c0c0a038800360400510001552501450060142c04000c0c4500d94940c0401c00c9860b0100d0500d648690100307003035841091800100181c0305118a03040242401400b2510451a2098500400c0140c56200040c0c1c1005150005003801401309014800c0034482584020894001007140c050201c0c1d41c0c0d80e0b6071808810243c15038540780c00c0501c4414998114100040503100c41c0c2d0303000360300003040700c0405030081821180d030810120001d4010f030400740100700c01800c494407040038140880e0f00b400b442d40d81d01d6816030121421480c1e0800300c03c00254000100d064090854031000c010300d44040c0841c0c490300da00c030100c1035080a80c040c4800c024010001e03d54401011545d54035240019454240345031001014903102900716072448c0c0e00110425060038140843c9401454183c5061080d20031805003e5103a04084407000c0c128082d2103d50302c4110019403200000744802020003690740c111082400041415220403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 977103417 1250 977102167 977102173
    0x1409120f010221160c06021c09060c02010b01050a0903062403081804140103060f0e0f0a0b0a0c23041e09142719120206070e150a02 58
    0x1580402080c00100802803030601801000c200d0148040f00401c4001d1604607441d519076100c00c0300c1079000740c00b04074a40e0007040158070f40100d20720704071224000451402c10180f80a95040400220317400500c002c150301c0d0000c203c1c0c1da051200648551040302182c10001f00c4120062000a0742d5510802e8440400400740340301e005015411440c268050300141c4130340001041d0700902d40f01c22040c81002d04004c1e070f014040c03041c21306492840030806002c02005151149050034019210358068420088458220307100150704d40300d41a1541c00101d015129109060002084000980900d403a1070803103076110311400824a1150b914124401d03c041d081507410440000ca044050740491b140809010411400910381070711082241c25015038040d1162500c000c126110b02400c0c2003500c483c100c594014000d03440242c0d800d082034004810002403855001e03003842408890303032201000c42000e808507419034403081816220401503050203903001440715828120f6540c204003428507800e00d4011 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 977104667 1250 977103417 977103433
    0xc0302030303040f0b071119150504060606030f0b0f10020f0f030d051e19020d0f14062409040207081605010b1804170f0406110d140912 60
    0x103401d41d0b109540503544803040040c0902404002c001940c1c020015080c400144000711b40000d8a0b04044080900710210a0804800303004410f103103800c072005000b00411031740c40d01d80303400d00040006000b50b1000070f29101420450f000b0703e1180041e0490010300e0069100c00c044104428030443c282280d0840c000da0092109403881007222100301044c04010795124604801c402d4126100100103a03d03100e6171442144403280c0141c441a00000b85034030800b980c2c4c0d0f501072260040e102c1c151103d02242d160214507001048640e10102c81100301c00090b0401e81c6845040000010f00b8111a189010a90101402c0c0e00240030041c244040e02a001505045054035241c4c10745e044203c8002511002620550800100b0f10440307040100840e40c000445c590a60300342000b041c0108000c000e0b203401001c11404074032141c150340000c07008010095440b51a40802032402d101c0a80030481880760302d8070721041c1030059a50303500c1c10481000700d44c1003160400c2080640044c5002008050141c521 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 977105917 1250 977104667 977104669
    0x90e130803040605061807050a020115060818010e0304060309020f1503132301090515190b0d061127090f0402040f060605091203030c03061314100302030d020a0503160c0302 76
    0x1124030310482e900d2316003644030a400680a8203440c40c2c901a81a4000f9008003400300300d0308180300344d80103420908035202214030482c00500410b1b500c80041d000384004500024541d5040e045085114825601020b41101e40340034807080c583c0ca903c03081c007110070520000303081d0f9030341070f003004031840c059850203480c246800c4540e400801c1e01d58a060361039446417600018460304111010418038046810411440c21a030481040b01003610b07071003007844d100d14015002ea80d800c6c881840464101d0020402d030303450400c1400380d96000b540c9840c0f0405404041e4680381c8011140d000941001038056009075840c070420341c0750080020000c0340e2040e0f40361702c481d0310314845118450103006039464150703440c0c541d94104480001e82035144991a441001003000000417001a0703500a002941d12803013451441d441b54010f0190081103038905121041006071050f05601410120ba00076400d41707d0646940e40e0407038030b0700d03240f03cbd0107403030341c0c0c01008010506400d80210540c214060009091810344980c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 977107167 1250 977105917 977105959
    0xd0c0503071a070f0e010518030a05161a16060b01031b02010203061e030d1b050d091d07092321010e0d0801060305041a07090e13080304060506 63
    0x2072010b107800e50301c0d0041100b0141c2140ca8070380c01c201d0505161806804040000b4414401d4a060390904612503100603032645040111405003988101950b000c60389455500d0501c03c0e040c407038901107186c4180c0c80310746040318004031515490590840c034600440c940b80c401c00f1f0504002c0580c10140e41c1c4040b4130f0b201c01c083e010700341148001d5001590364101b400c2000039900c5424464071007840d4544100c0d18640e400109445500340b503080c85c105005841554017810100003001502600804240c82d9115901041c00003d4078414400c0380c1003d00340c80c1d50790390600c40450304d0801140c0304120500085000c01c603600250700003116140f143e800c19002203201440c05080985031010080ad02d000b00500030f00a0030302480900340180540521544001c3c500403045c4100d1041c16500d00101c2d0910102c50000801880e42c0c9403d20b90508064030300500710fa8491007401705d1881d400c1c0c04902c090394900d09241440d030304030304041d046864036103a500051401030006079024039000124560803100c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 977108417 1250 977107167 977107193
    0x130e180d03061505090303090409030c0c06020c1003020408101505041406040b0909100b0a05120d2706390c060207050d0b090c090907170f0d0c050307 66
    0x39640c00b00e0403520788441c0700b4000034a09040010302c0400e121a441c2c07910000191800040100c50219202040c0d082c1640c2c0318000000191000e920302e603011484540000d41c099070f44c9801d03215001007119812040302280641c1c01601482c0d0405403061030070101d150003110082208550051503c0d40d02d000040880742d002c040260316007240c504102c0980340c517100d040c1c2042015181d5480514144540b00d13119003043c2250050789603501191100c80d200c00e020a405400f001d001801180c601a0b2015694820703080c0e244001201080100c00244251100c0b40000148510014a641c1070280580315480e08600c003c50a26540300740c080032640400b80c52074000350805a864808030325003006100d410442c0c00070780542d404030008001030b403690756000b90f480c2d03049108a80283c440c0799049080c03864519120703038007003885824032100c00da0220740e10040b81d514035914001c4810740403036151110155541c041c6c03240c014800302c8038098081c4139080e100030301c1841030f40e20340303082070340c0f001e1104900e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 977109667 1250 977108417 977108443
    0x80f03070819022b11150c070611040314101b0f1202030a0207050f1218060c0f0c041a1c1403040602010c090b070b1801112d130e18 58
    0x82c0802d0050060704402c0e0400440305c2c0e000600745900d562030b607aa440b41d0000d05418000d480005201c0b041c0901503120050a4034588241c0d59140d80e28201200c2c00c5006001c886814059010120f45000d424487c51142070703854150032020408000054030011035010280302404083c019086d42d400c040d200852103440c0c401030041c3c48401c18107003e4a02400101640d5095000c04105080751418505550304528406602e0303040030450f0000c40c50301c0c01884469096803043e10368009503030001040303074007881c801500d0401208401d500c090400c00c0c00c25a2190b000203050460801c201c0900240c020a1030103004401c0240344416040c91856010b90b10600050f55203604514200da0710184100c004e00c3d6170364160b4100b180949a2480d061805050000b441000e1040e032800c4900c01e4025070b6880c0031810a1300d03101c00c200c408800300b0502101c1101d0001441c4036020b10410301d240d0544a60019403101803081c0d0381003c0060300603050107007000c00c485101e21030104410400300418540300d02 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 977110917 1250 977109667 977109733
    0xe151306060905010503091c09080d0327030c0f03021507080f0c090619090803070b011502060403080a02071b18050a06290d15080f0307081902 63
    0x12a115004080c082590083c3c1e04029041052112038600010b02d0500300c90310700c0c02c0004030102c2d880203403001314196220000381e01400d28001c03490b0360550300c56100965008200706843c85411006013010f4001080180070500c00880c980110f0941400e1a00c03440c4280104e449000a284541c16036040441d400303000107000504000300c4d02400354060340c01000610340c243c01d040c03808001507a50302480c8039041100002e0f03440b03441c0c514800e0796210004c0844c1c006807a550441c070b040010385458240600e0110840040c00240c4051001485500c1550580d0304c151090301c031030702c0380d8020b075029100503101044400006841404c078411054002c0c469408130399280b070400c01d15482039880c01000d41a070382d80b80441c200301540d0607849450300da0581c40003241009050040e1310703140d4012420441c1c80503140114050000000b0700008056500c02c03c2151a9a09580c0d15035549104402c0020056174042c0505100c0a018410b0580e005146005030b64580c0214075800c11030b41011581106141 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 977112167 1250 977110917 977110919
    0x3110108070e0303040b0d06034b1e0b0c07051903050f03041104020a270b0906070c0e0c21040c0b09060903010c020d14040b1e04090c02060a0c05130e151306 69
    0x2e4480400100c140074158a1200000311500010090b00005802070010b501400b0302015900e070041c0bd2118181e8845521400c9003403410f02e444881e00038040851390f601c10021052048014480303058031031685991010316084061086202a03080030b40b040301c4240403080c002c2c0742c1e035545001400f501b01c0e0a81e2444841c5095044200800c554000985142d03480c1d81130502c1a1004002104d100130342c180c03440c964400b1b203803910300603c109581c8a0b207140610030041c00031408080c030080c000103101d14050202400340d02c190004424055800500d0010300d004100015240c60011b4404120014030071400d0411301c2d00840d003543c003600704910041e0401d000000d0001d03002240408490866001281014240b2508005610074004001d03096002c4107041c01198502604440141030660703000d1100800100c00650368800582c0c159400c181001c0e0a000b00c540b00758141d403c844002618044028602030214880840c080c0c42005000818589040da64a8409190600482c818800a1310b1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 977113417 1250 977112167 977112233
    0xc02130c02102417031e0703080c0a2a061802030706030b01081503010e030a0302040608070c110108060301060506070c080c0910032004050103110108070e0303040b0d0603 75
    0x4854142510003500c060000812140f50300d074185a054a01e00c1039102c44004e82c5440765803031030091a0380410b00500000a030342c0c4e595561006820001d00c2034484c1c00c021740b21700c09090114040d1007503a0001841601c0804400350242c4244150702c0d0780441422400c000c962a1903058441c41e001c80c401c0444120941c0c82181810400c541c01031840b0f207007c224200221000810101c8080d01100504a0120034680540c0e070079400328007400b15000840381d0300c200e180400f0703019401c5807281c0800720701e007040001c40f1a401540d4a44c0141d90000c524002d00c52544015180b032400580401d4140d036075640d001ca00c0b40c90380340003418454001d0035101400381c9028110391500c4941c10002d4000d00085081c408030800302c000080a07a5400f403070070408402000b0200c403010880c2c01002c0c1c2e11501300800041131050b881603e00e5480820b0344c424801341d13648130060300e20030b8040e4682501a4401c000030003020b801040a00080b4880c3d4101240441d92911a0651004450300030b00c20000214050300c41 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 977114667 1250 977113417 977113421
    0x403020709021305010c02041418060a050f0c0706061502010614030a02090121050118050c010809030f28020708150f070302181f0908060c0306010c02130c0210 70
    0x1801c22200c194548040e10000080c160082d110700303030510441d584020b046650320f030400903424080400711070302ca203060100c8084051090007801034030b02400c0085a400b01403030250a1140315250360700445a01c420086651a0340880800d4074096600c420100701e15150044210803c042540082038060610302440c021048031048903210303900c03040340400140c0320719030002d0450b00000c146580c40c02860101d641c4000d40c10303100070046c0d40f03800d00b81180d0694101e05201614042d400b121441c20380c2c2e20055450540c241d4040260368018030640c1c41c1118458000c1150140d40180c14031740317803440d8035075503c080c58440342c600140e004408103001701c101c1002524461001c16500134094209604140c4081c00013074001e408050300010001074046001d950040c00d01006803114003c28803031b860401c1c94180e0504d946000565040001601290024006008004800c9003524680f140801500c5001e2006001c80e00400004c0010010740c4041c454080310040b581c0240000c19000d10030101 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 977115917 1250 977114667 977114669
    0xf0e09091c030e06070c0201090f1211010c051209040e0f0a051203010609060302031521010e010e1506011701031b1a220807080714040219210f0504030207 68
    0x815161018050b01c146000541c00e4103c5c01c181081e4580852a000484032501b01750807110301120028070005400413403c19491450340114000800d45503540300444511902100261403544003000d01406204c010004020717983c00103000046101d235030007101d41004d10782c0705286126002000c1c5070041c1301d02804071805e03105450440c50301c0c66042c040d001c0c240700341a001f074030201580800001c1c000d500700c0e087d031100c00314000e09030126040a042c510700d1501c40607103615095400c00c18902c1040c84140100498061150042c01041101e421201c030003000041c070381d504000202c4403544200440b40c650038040d5005150405ea0380f0b07034191407000c003400d540e8444804801038007282c0d8a01d44250051f070700e0180f501c2c48039818140c0c0c0030102d8106c607040782d0000562800345c9140050405000110a400c48804c0d01182d4041c2c0c9100c800c0200f207000c0d04802c0c0031915132049162011a1042440d21100040c0a40d448054a40e540e1842e00722910341c44008032240c0d03103005000a250301004010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 977117167 1250 977115917 977115973
    0x1006030506100f03020901090213050d060c030b030706050904110d140915010506030c1c06080a0201030510080d0807020f0d0924090b0703051e090a140607030f0e0909 73
    0x1c220f0914550100f101c503041407217003e407455804200e050121a910303001000400004100c05075801c558144007008188602d606d4002c04c4c40c0800042950a021804000310717642a140e050a2413440300a000240200506440c0072030070400c503095408185124800003000130307481d80c50342c1d480c06511540c0340010407100120101d00e5540108807542d2a50106c0780c1c0800c003041c02540341c019024800c850400301e2400301202c0f0381040d0003c1481000000d03552003142c000d80e01800181c031812800344655409016a00d43c54000e01c1420000314058a51035401902d00c1c4101c4018a1100034103a0806001c0c0740351340009601c4000130000500c066001c2014191107440325200d84250380e10140a9200500c01d0590304d070303c04a60f0380185400b41d0305440c840c070601c0b4000c0c4280482e000e46902c04c0d90041e10818800d5a0702c18022078141d4a00c11084500034001d400b0a103400240c3e14141d130074060302e0685404000c0700ba1501c04079074980d031a01500235042c0500800c8014490440344441121441c200 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 977118417 1250 977117167 977117189
    0x50d060f02030c130b180f0d0210110106170d0507051002030a090605060f031c17040c06110f0604201003090b060d0f0b041a07050405031b21100603050610 68
    0x26050148200744d80d2000d0030421039483c1d0071f03250088003103820f6010345a0013940c00000603000e100c1c030641000c80707031000d1000b50000b007199985035501c1224000040f1105800e40d40310521108086000b50024400d00d80100112001000d03004c01840580e031048480010030b9448280a4040100d18010305822480442d0b52000d0b200103040400d40d590600d10302d400102d1489682c064a40b4013803501d0094a03854043c62650520b042c0c200f004800c050352103520b0008800091412070402e003c10114000c108407170180c8010707202d40c1c8480c40400d0710409248150724070514524070036900e0580350050000c2c81d41300442c9107150307400d090b0405a402008a40504608034031100000c1811141c0f07585c241e801102c00344140c9560030880022041e000c496400d01d4501424404c0c2144c00c08003800c03c0790720407012103007600c0405d11103c81c0c4900b064006900110791203a0b10280d43082940034403480082c800d0840d00500314420305041034a400394001c1d100c9170007950610480d5410316525202401030030b035035 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 977119667 1250 977118417 977118427
    0x5120c0c060c0315091b070605100e040f201e0102100614040504060f05010f290301050108090c04020a0903020a0911030f090106091407030f050709050d060f02030c130b 74
    0x101602c86507008030140720310b41c4130317001454040c01000400014043c110101d520385000c0d1518900411080d50f40241c44681114000340d003031103603070840344600d620142c4031505802580c0c481030b0703806902d00c4040300c0e60303c600084406a01e801d01020503101021015600510318240060300304801c1c00140103480d81090010700070034850703101174190f0b140180d60001d1a5038540c10001e005014100c280c0c000d0a061900000722b5485090300c4806880d07150380c1d1008081c1078010b900d100c0301020310503842c000703c0c18001040158000c0d02481e40c0440c0c2032042d2214820940700041c201e900c001c1d14040810b420407414015420403c036000d01600440c501000060101c40e0554050f02005240081a03005a000104200000c0d0448001450103107130038071600c40075140403140c0e280111031600c00686050400c1e0301c801ca01c4e02505004812030b858143d802d81c01d08091087c0c015601109440303139511511040100d280c90300c002e500c901d04007010340e6251051540181d1100c4940e030b10003004001c080c00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 977120917 1250 977119667 977119681
    0x1701050630011e0f0b2407060b130902091e060904020d05010c2f0601090902060d05040c15030912111615032904021c0c0f020c0a08120a05120c0c060c03 67
    0x24511a078070b2010b81c06c9444060a103041c00143c250042070300c0e0012741e151801d510488031a0843e8048503c212510803217580e4540c41500908108554005c00b51010004070f0018204244601e0b0080d0010304171501001850300d40b02c3c00d4400b550308100c000b80c941d03402041e2209025003040c0400c0d05140840305480d0500c1c00160382d2f074106000d00341c1c0450780e03540301100710b5a6140c21103071010200f4209000b240b51a0400740f482040da841441001ca0742100841d0185200744030381c0d40b040d6400200e00c18099400345044540501051200c5204c2c855040302c1c116810100824a0040c0f1000b01c110904224000c0b005041d118080340407220341026a1a03400c000d00722108a0f144170708180da00503200d00c43c41d000000703003c0d040e441c1050301620340034016407e80d905c80640c5003c0c060a808903042600d440301805038201c0d10b4801d480d80c50300110094806074185200a0901c0556460300c181489070b036072080d0030080760a403118941010f0014806034881c0e07050003000c1e401900c10408506600c0c2001c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 977122167 1250 977120917 977120959
    0x3060f1208090303090a0e01030b010905040213110f1201080f0601180908040e01060c0b092e0b09070c03110c06070615030602041701050630011e0f0b 66
    0x30000d062100118040c1c00d940c8003001603502d035800013820030f80c0c620b80c1c95021a032901c10a00040e40c03e4110300c80007080940d001d00920740a40d034041c040040031000c1d040c0a6000b4000c040100c0040c440c10045461000000c2c03002c0c2c10f451011101c40341540d40f40280007442e082e04a40da810f450b400141c010014003506040100311150416404284d40c0f240c0d140c405103d100740d8010500c0025160004560103600425840c003280c4140da41d8040e603111810029a600252030f0490380e20036a5a04468032a480d40c0c00da05007170300d44070101040d01456200006d441210403200800020103240303200050643c0940c070040040310b00d40140021024040100754284a81c0038054202903c843c0048518195074103940021508518119110364540803001c0b004400307194460900c0d0308000100e0010b190100d183c0c015408070001d9011303072840d1820040c000301420444050366541ea1070f40045a1a451211450044080c4000240034401c000b0300504076041c0c007445078001c0e86003980102e0003071345c00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 977123417 1250 977122167 977122199
    0x604031e090503030304030305010503060a150515040515030915010e010b031e070f0905060309060424020c030a09061707051b0307050d0305060618040203070e0d1203060f 75
    0x1404060100c54000c41034844007034a6000e180c1510000003004140340e03040d4011410b8400843c1650116195405038800340e40b604e8944c1c03a41a03502d000d00b00018039110350032000460100441d2030504d9a01c4000a41c1800340454070032500c4000020080f03c2c00007801003980c241612803000d40c295061801182c07020710140110745542d000007021505200710503038480d03102100502100101d14221100804100f0742d003c2c500d011600540000c61a0701e456401c0d64850407035540100800d1703079903032500c11040242c207811400084050744041030307140c0e0600041081060700c0340190341d030300311040300104145103961055082100a01400301c070b8010607d0348d65007220f11880e0545d2110440070b11441c0c41b0941c1e040100c024400003c5000800c43c005c076560001a180f62400c00042e0782d004140a01c2c0c1c071502071210307000072812802c62103619043e4099a08440d881c038103802030781d145c2008075860552000040d2a8010701c0642ea04004c1e5050190b503000c1c00e01d003a0f405449902c0c0100c080f20300070030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 977124667 1250 977123417 977123447
    0x15041206020318011517071410111203040c2103030903090f06090305070e0108100236030c011110020904180f03090b040b0f0901230417060403 63
    0x1c0030800b00d8800f2030101c10881d035030b00003c002854001c400603143c2c525620034401c00200d45040c07880c030000041604d00c01c980400e0007501c0c44d0080e01040024402064503000305000d01148940800d003020014080d8604030513282da5a607007040d00317080c005240d03d03502c5006032396082040340c0d0b100c96040f00e06001da01e5050601052003003c0e840c0c15562500c1681042c6081c42c1d4070f110004e9840d50040d0110126030090081d21240c5031224144c01c2c1281c1e00f40242010360344a8008130f00b40c183c0960082c00203040320400803203c283c00b0509180f03140042d000040c446400c0360200344035803405001800400c0b509007041422604460143c5848040300e1110000040d400705070031407603858540000c1172030ba034280186841240341d403400c580310000c0280c0c1580000c840c20004038486044000b00c9080ea001e0724401d5050621107609443c1d00d40c44841c83d1030400c80c895006081980700302e814244811007c0240d0754540d42060a03a08611300001e40c6648264441303014000402c2d04204200c8a805d1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 977125917 1250 977124667 977124671
    0x90603020c0705360a051012230111041a0414100302121815070801051306091404290c030702010f0e01060501030e030906030a020703020304210b0105010206191a15070215041206 78
    0xc6001047c03a01d5400c800c1c3c2800e00c55081c2a28510300341c03010030060041d5015448071202c100c378042d0a17500a4082c5014007255000d81e0a01c61140d850b285090303280122641c82e0151900c2c03110b030201038640c44207541d16001d07040c1500070b42c1c0c90706405120703980110041d0b140d644020714200200410900d018400d540c055003030f42212404841740c83d080032015015100c4180902e919480d00c20b01014421076054504203081c0300141154a40c00244191407024422688583d464003001c01e0b5003640003800007030966580f20203000302d894140c0642e1403070701c4600d00005407880c03400001500b65810f4044207017880d001000200829500e00e403cad240c00c1005e00c0401600c813015403030706030304d0741c480c0342c10400070316000c510380a01c089010b070b054000c8a0710861404815907a29070040e40d0354030003a103100100540c0800180314405d400d50140b2000c4120013001d0102c8602c0b0b001141d480c03401603d02e1030403903100280740340560601e16010840701c0034032043c0398a01450904003680d80d030b600203c000c051503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 977127167 1250 977125917 977125943
    0x60e03011517071d0106200604060203060609100e0a0f0602191e0819050307080403270620030301030f060209011808030307090603020c0705360a051012 67
    0xd4100b01c12406880c2042c4c0d10388403e130400300841001c40c02442250001454511000c100d502e009902c100012001c04c000c0485032680e545020103500000e00b9180c00c41c0092104407813070f81da10301d0601580c010310344071024044641c2d028801c00c3c07815500584103003103c0d11810410300f0340c001038a94100850850000940d16240307001c0c1480d4080000700001c41c00342c084807078107100f002d1000303010000c0c50701c24420101d0403482050720203002c1100d628022480440020300401d00603040c04100400d40740350b00344006010100300ca0000d019400680009078030410820356200b040802c00d00002d1707440000e50540d851984c03480d0110034241002080980c01040d1703104a640541e03140c0f110500104e0103100b0103500d4004c0749a89400458220300043c40c0400e0004015000c1c1c030850300d8500e9008060200b060805003072043c0c51101c401170201003040311107002003003801c44c10202e41180c1e10b0702070010241803139091441521006011480c91150300d080c02c1101d07400600f014503030f155010041e05400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 977128417 1250 977127167 977127209
    0x90f12010f050f15150702010c140607050a020105060306130f0311010c030f0f05010506220911190504080a030e030a050f1018020a171f06060e030115 66
    0x1414408540d405440d05020503c00024640404144540e11280c50810f21070342070030801a01702c0a0b0598a5402c1c00700b0015030025500c1203003d54041802107003401c0f0030b90341c640010707440c00b602211040002040450f01c0c4c0740c096420b0207080e4010f10304500420352814000342444400b600d044004207a444060740250825004a150802c12541c580c000c01191503034002c06005001d4408a42d0440351070719001204201040c41114143c51010345402d04203001d520103594004100c2d04104800407410303a001a800802c0c0c0038041340224101ba01c5500c0c2c4000d9480301c002c816881c99520305000e000c0c4014400160002243c240361074040c46e0818405c10903001103810328900140203007860180a030032102101d000564818112044101008510a44d0892704540240e1600c006d610402120041000100c1c2000c03850b54a011642950010303110030711020f480a1801980f803650a8039820308004054100511142400e016002400310102ca800d1000703000105000c0c01c0300d510304601600c461 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 977129667 1250 977128417 977128421
    0xf05010c0309170304031419061104030c0f170601080607182411030403050c15041706160314070c03050d0e030c250303030f090b150f0303090f1201 65
    0x10114441900f103540c4454681c240c407075001d0302003520003410482c074640d084040022a1071101c1001c07034000c1200344156403244054507010342424840301c024800440450f42c0c48004d807006001c2001c0c000111880c04000030800d205099000010f0740217603004101030b10004c02e1030396211030f4506d800c5412041a07510020700c0300355600541c002c0a0002072421071200c80b44d1900503040e400e13031035500f00d11119148440c1e5030f210364000141107411003024150107061080d00181c5080c10f00c0c1c0281c0c2007541711145490410b03000c241d0422180d00160030b1140c03102e84c4400500010340140380a2201e001402da80e030028050140c508420400c0004d10700c802c0c58403c07811b54011038181c04041c4120803200c51450340c0c0780c0001082c072401d4051150543d0690180303060b0107000311516408980b000c3d286881c150001c0545104041e2683e4850101c000040d0340ca4a20350710503224064120142504041400725003c15a070a06000c0d900400c464074603652101c910342c1e41d410341160404822500c0700c0200340 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 977130917 1250 977129667 977129669
    0xc1302130b0f1812072c0709061704030507081b030307020c030105130c180b040f020307030c0822150207060903080901090c0e0721050a06050a0f05010c0309 69
    0x41d245404038440101203000401880301c2030314440300c14000148001080311007401070480d104103904c580b008001030280b200c01c96210418044500200040c0e0072044440404110707940c00c000ba00c4030400b8021907411541941c0040c1285480c44514501594007031b29501c6140d401030301d100e40214685c20b01d580b41d0540b4103032441c0560141e98076801c02e580042e50358104196803921039401c02001404084000c07a9142c00b4942040044100703900d000d400481c01d25180b080301041e2900e4481520f0b903500c85015209041d002c203200183e0324a4505802000c480046210f581041060002d000a03440c899049040b40d2410450842c45034800b0b20384061441e14113407110312128000b060600500c4155072010220314000c3d11106010f075500384004c0c2c00c80381c40c1c00004080a55450f0240249102d00700c215900140324144800c068a80d88807640d1107102c1d1138500a40382d5115010010300202a0048400801080d00e034195000c0c02d00030b01328142c084c10b00a40741080312541c0b003001810300c5420014 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 977132167 1250 977130917 977130929
    0x60f0b0d03110c040504110906030a1b0f05102c09090304031101050c1902060702030609011a0d0f020603060a0b120601031107030206150109170f0f0c130213 69
    0x1140c000c0d01441d0280c0b040e40d080c00c904107240541e104140c058101400f4081c840c59000600500400b01481041402e60001e00007030f40510540440b500051041c0c01c9452400c110340c81c01030b00852906118440101d45a0445070140c216500480a00c9411080301800c9040015040b10950007a002d00d00244150511440c0d104011105100c0050004002082980c2c061a040e0400314070302001500c05200e0f42d03020350001c1e400f038940c12044644c00c080340c0300154802031200f4a03240340c2e42c000900d061420307180b440307039030755079544110180c005110078120101e030956a1040045294445034141d45040d031002c3d006206c0040058010f1740c030304903900060300c80c0f001c006460710800b980d000c0c010481120454082841e000070080e5110a481c1075070312030b682c1035000b0101545d4103102005541c2c0c9209205050240030728012a000d000c100b0801c03443d6000000401c0040101114185080310030804074110381c011042d101080d03152080460b81e60912a40f01581d500c1e100580300540701182d0303000d1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 977133417 1250 977132167 977132179
    0xc070b21072d0e0d060e210f070f210e010e1e04060504060305030a080c1c0b1503160e040213050d240204031104140601030903020a050a29010f03060f0b 67
    0x140d0400c21246d004080d000092070480701800c00c0060407030041a0407902c0003c048100748241c42c1c3e80031980c001081071500c5286141c00d0f4036019600c0e20036802800240c248000b054012692805a0159000e00380702001d02e020141c035441d1380d0228840309480c0141c0c0000d941150001c000580300e40d000100180b0001e00b04005080d1790b404c02036100d8000d10207410005540030302140842341c09000f5152500d603520101003001416441c40c800811100301c0d4260410002034884a401c03003480c0146120700103003d250043d0144440c0014420340c003556141d84610302c10302c50f820382c00003030301600c1068030816180340e901c3c99002e051521498400c2c0c184205804601d800c81c0c410a0f0558026000f240e114081d0403901e80828030030441910190040b040720340038608005125503220b40c000060041c000d005541001085403500b6040102200381652844007001001d41035074a26440b410005010a01280e00e6505200005420303002c140f01c09005103440d224408105146a4482990b9030001400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 977134667 1250 977133417 977133439
    0x103152a0c05120a0f0509030309010c050a0f0b0603010e030c0a110a0312030b0f0132040902180312030103030c080a051911121e0c070b21072d0e 64
    0x703c4815038845030040e400981c1143c4010300315401202035400c0c000b0010007850030b000d1800e00440c7c0005c001c0d0026038580c40740780354010111304241c40031100e890144111000f1880e20314241800e48420b16041d02c0320f503004003c2ca106c4083c000c10814210350b44002c04040c01402240042c035540c4160300050100c41005000342000c60f055404046c4040302a146030300042502c000560b8801c041e09409880b96601c50303a40700803095648084800402400c0b00e8a050503111900305040341c1050105402d044001d0549607258a0104030030410a04003243c860b00c0c9d503043d80e40c014044405524024509000410400803d5010b10151307524520455484c0020b43c000610003032125003800b2802e06107000d8a01000142c840c008119546c141c50300d4555441d0005044108410382d220060403a014016040045000f020500050031145c4c81600074100e4050b40041c00302c05444e0241609007800340504112809205003d882c80300244200a0108040c4c0400c400703982941c1740203903581e80000078040d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 977135917 1250 977134667 977134693
    0x2120a020907050405010e0907021c031104031103060109050408040e040602211006080108070e060a090c080411062505010e1906050108030f19050f04030305030103152a0c05 76
    0x8040e04c100e581c240c0c1c89203085000b400074403400d10700135616100140c006044030031620b000e071450b00c0034502c0d09240000350445044c108150981213a002294140000b0001c1020351508008103801751801201c00c01c0701e0300f85540c5a030b44512507072003695075141500000406100c1280e058404040b010940603040c0304100024843d20300c41101c0402c507140f0508000b2400e11300c2520103c3c1a03138070714030081c0052810b14241903603400d0b000307003080ea101107980300109040380c2030f0042d0800200d1030345900c02076003414030b44141d1204d002945a0300996092045482250314850303440302e041c0d030b1540140d120b1061070903c50f0241c400c1c6603201d28148181031402401040149000002034014201000542d80b124001ca4507440ba01e2000b4141d843c0a100440400c03610030000c03032042c241418a9860030102d01c2ea2107413141c000e81d005a01043c0003100400c103010f8100d4000600e8000070408009286640d0006907010008051680402c1350808000301001e00411041440c0c0d03402c031007201d00d00d03d0881 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 977137167 1250 977135917 977135927
    0x905090d08070216142103180609100e0a0815012714010510020a0b0408090a0315020d1404120e030c0301050f1501090f0905151e1017010302120a020907 67
    0x80d218050010440c1c14503003240039640c0c103090181c6ca82d0140d0700e00396a900d991444015200d4000f544818104203c418603981e41034070045003a0903458010140704403108004c0c1c04042030b03100141e01c0d0401c14480f0700c804003800d8041e064481044400300c070701e00c24048007110440a45116600c00b4a880100311002c0b0700d5402e110b04a0300121005014006800f1080342c503280705081c002c10741c1c2d101102240000704d038003015007030804020b082c400b4407982d00d881c0d004260101580c421b0886600162800c5000854042e000c0c0f43d04900d10707041881d080c903a4441c00ca06002e0002c0e1010000c103c0500740140e5824003040d4698203008000344018105010100046442504c02c00c075800401d112042d40c5500602c0900c048800688196040c28a0030f06d0105c0649001003888684401e00540b901080d9900444400041c1039407007d600d03e41049030510075039203640c800c913500340075070603a14044510b118020701d8152641035548200700b10140c103075617140507907403d00290710000320070410000da5441 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 977138417 1250 977137167 977137199
    0x181a010504061a09060304030203070f12020d08041a060f10170105100c03270602060405070f080304030f2d110d02010503040f030908030c1005010905090d08070216 72
    0x12102009042e6a0750103483c00d00203140d00d45504a038041c4843d04691808001031a0b10074003c0c01924680b8006c0d545e41015003841303080446612480d082c0029400f80c0c10032114040c0c070709504000305a03040c1910f602141e500706119085600c00741000041c0c190311a00c680040103d00034148643e05012f880c030240c1144042609001d0810080c000050149400021906648030540f220210b841c69618203c0d1000407401101c035441ea01100e40071107004407498660004c03d555400360810342064034042d030801ea1150300c01c0719010280d803014032103900044112000c0700d910240c032080705000e900d0b103c1c00140345031000842050081e4080c10920420b4140b050041d481010202003c000b584104030840d0701803000039002038030900009000602d4901e001d01840e0003401c0c010841030344d0b020018a903601c02c42004541e074103d03010001500c1524051580907018406080c40203103004031919030340b6141c800400c020480190b0125031514002c0c000c2d808c4241c218000701d80140d40b5481c0c001a0080c0d1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 977139667 1250 977138417 977138419
    0x10020a120e03040b041221210c0906050c1204080a120201090503070803060d170a03060f03020f0d080f0c0a020a230f011202030a0605010e100909181a0105 68
    0x701641801d007241d000c411142902c130003145040c20142000c01c03208580140210071542c40c2c242c3d0798048a181040d4098614041e160b80d150412402d15440c1c100d10075500e90500c1900e1401c0c0b40c2c8070000581c110945e0400c0c2c5015290946d15804038054261030010804517240040c040040c0c0401d00c041b02007050f810301d501810b0305a1a52269503400c0b800c03102d4441e0080c11a41040c00000d0002c2d40c890000c6402c008020310541c4a8007140d1907130700a0402808141c4511038000848000d039941500450009183c003027403a034103003840c43d00403485142070164424441c120100030401080803550540e00f1408030221031503181c081d01c00c48641c0d11101790070140e10440900078000340c02e5482c1146500b04100742c0c00040320000b805014000e03008030030194241806205015a8582c1000c0e20156100385520480032484130f2500c000034104000620605008a070310041801805030449203480483e0003a000018540480d942130f00c540c0203804900500003101041c00005c035a24420843c1e0580344 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 977140917 1250 977139667 977139671
    0x209040f20040b0301180914011a0406180f061703091e011b06180c03060f0c0c030f020a0c0b03040b0a051302040e010f060f080114060d0209070210020a12 68
    0x20034200c50700d000340107910441c8035040d003c10041c89284140b04d51760045841e01040450100c20316035400c0d166450920902c0c0395699240c5074026011082200124281e0b01560204032041c240000d4003081c501d01d180b40c0c42040c7e140c02d2844030b4840325a0242008000e04007005440802043c0750545075030141a0310751246c40b42508a1401c0c1c80381e0700020b490040c058541c082c400844100c07410720142c91740e80580310b003982c64400032064150390202880f40391041141c2c907069030451900d1b108840204010781c1181e4501140d50886c0303500548407040d8250507050181150f144000d0403440e0074100e8500400010101800254250318400690f010324400c0c01581216070b2040100400c40d10125130324007401155250450160500b43d00038500742c03940b9000400c1503440808002e0540301d0950200030404070385201049004028807039041e000f8a1084016a6401c0c02c0c0005260844901c902910607035641e801319120700d00130000080b001060b90025500c40c40c80c2c0c2c001521001c0b01c2000410018 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 977142167 1250 977140917 977140961
    0x418021c0e0f0606041802010f030e1e0f060f01030b0414100b01020c19090f0b060f04081c051206010c0b04030504080f06010b0406051e27060711130209040f 69
    0x305d05406218005012880c0b1198452040d800459946a4613540881030640d98803035a8101030092100b0401000c400c07441c4588034102d076045d145002c1d4654245807990300300f0410f11008010340e01c03035541143c3d0891111780c182d407078134240000310450b540e42e071451a01c07031508028a03690301c503000001405001d8082d6101c42c03100c4021300c80501440008030001b1b140c400010700641e5144e611401200034810030020b684c80295020a12651184c02840300c4000b022608000d004003c0120300030121446240e11a40b2172901c401600758003a060030084c82803000c80000f0242c0c1d21601500e0b40303c0341c00500c810715a01305420060001ea0090065203840c0c050a898079444090014215040358001e5000610745450202c08580036000a01c040c0d0801c4103080da000300c0c0d054a00082c01c02d0440380b180198144068000c1e07400c80c000880405070260724103010800100d003080582102c4000d0984038403402c0da810200300d1009204850b90b5940c05850082c44d0b034000c00c0554881e084107480301081082507 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 977143417 1250 977142167 977142169
    0x7030b09060402210102120907090c090e0103060f09320304060215060409050618071a090909010b040207140c01210c050417210418021c0e0f0606 64
    0x144011100650407410196451107285240c1030988054084c007400141010804290003003513a2060300e008400e644540d07420b111041c943c0c4190030084140b4182050350030700d840410141018140300140085a03201c0074001c031030104e60002d02045602441e95400d014043d01c0009a00d20103500940c4402003189101c150f8440005c12101600d0b4a50010000c40d070301030607195040c1c00c0003064942c20607296418031340003c004002c2e441c0078205425a0b48082d04644080ba8a44009036000020b6032482500300c1c0700d10444001100d10018080d19103040f29a03820000ea8050008156440c0e0418400101e00080c00309a044441150742120156521b6041c440011240c224900c00445013001130715445111168069020220030b40f010b080540c03c02da96403411250340c80300c101040046d608800d000c139403c000d030595403101900041203210308150502c441d04041c9400f81014004a80c3d000540186010b011b2030b403500d948906140600400d80780c461940d46524841c5c5104850303214000c041095 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 977144667 1250 977143417 977143423
    0xa0213050109080a0605100b03340e0d1b080307140c0105040b031e0a05011409010305060a150306110c06010e040f020112020d0504060501180218010f050f030907030b09 74
    0x403101d6210043c10020f03ca0703112000245800b5041c101c1d1f041c4010030001d0300088080285204a415404070b1100100209a9415003102909001781c01d142032154244580c2d00100401c44250090304d0ba8010b04940e440d150f95420f4107611222142e00440c3c6000501880010040034401e21405080328403006840c08a03a403000288540c0f40031400500090003e48a940f010b154002c212a885030b0f441e000051070380c5039286040e90325855850c1c440340103000003207240031003001981b0180e848040d03561458403900c1d00d50002030000c0700d2071521201c0b011a040f000507181006181c000008010070000207842030740c41d0384043d074840c5543c054a4000610201e00d000083c0c46144c019400800c41039041c0d00464807000100c1d481004181d0034001c401e40750403603100d25072040348181c1c8005a03650402c1c00c188a09120300681c40c0015004101d25007210340c00d0180505404403c0c2081c0c00d1442034240c0c16202802004041c11021744007004000640d0320000b0280206d0b4040e42041081da2190007045403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 977145917 1250 977144667 977144669
    0x180619060b03010e220602040905040b13021003020a09050612040b010e040f0f0201091d0615090303040311060f13090b0409081e0408010603030c150902100e0d0b0a0213050109 77
    0x10007201c4420024017604a07001c4c1d100090310b1a604070550414096507080c080f03800c190440c1c0310107981d54040100f0420951000c9402440342d0103010b1824000e680040d402d91070500f106001c260300814410a124014040d806c040c0c00700600345601c942e0341181682d030020044400380d031080703001310000405100c000022030041c0c0e00804040030040c1c164403688940c41418404904102d40c8080002d2440c0b9004164003d1800c0007626200300d007802020030921107058010140c10b41010070008144d680e00004540440307500104c000102815a00014242d000303d004034128600c0000f03a01268903180d11624096036030741c5208202c120890000d220840d200b90388003c03c501402c020451039a19a101d850b2000c0f0038010446280c0f5444d07900c00b82c04c1d2009a4812408a141501d4000c20042e07070320b91034001d0b2418007004211010f01900000d901d048a10104024031201200300745144d11407071018980181c11141001c0c690400c886040004c2d03001c40d0103a000c200e03001c070001c91030750700c101c0b0b1081c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 977147167 1250 977145917 977145929
    0x80a0209070809071a040905090114060303040522180302030a110309060708031003061e1a1f020a05030a111005090318010507060906060501080a0c0215180619060b0301 74
    0x4c074481c181505080c9089001c200480b00410038000050794540d07a0040034814040f0780c2c00414038070a1035848244048025000034440d41003072000344401d0322a806040059040011080c0b681034591403041c00806403a100a0740c1038540ba40356405250b00003008003c0406a03544402542c108007901c20385a0142090896124a007005084045001d450180d600941208007071000503603241e60344012590703018285080c40d1510901101c1d00c02e600d10805110040e8074403950078520b415000510f40d40004458403112400d4108a40b0481d4404c005508003a94488201c0f40e44201e0300300013030101051400d80c00031380c1c40741000d05100ea41d15070180900450074000114103207480c55901c0072045914044003410014103000c058003160b8640105103d440c050140056628107000004100030001080b940c43c080c1820103e4810a034001003440d01034401c0040208292200c402403d85c4c0000014404070610501d400c0c040400d8040241101e48a04118200170700c0b41d542c0030b002a2400240700788 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 977148417 1250 977147167 977147173
    0x4080d0c0b04061a13060f091a0103020705160b03011a07110108190f1a1503040807020402041d01091b080f041406100305010f1109010e030c0a080a0209070809 70
    0x20400040c41500142c04c19582d803450880031401d003030702240e5030705e0614419510041d118881000301071141400c120141c1180e1000740091140040e0824244811440c0141056070004030700003803201c1032182c1c1d220040b1504c1018041569917070501d0301500b080c0510640052100607500e42c2004660440b5049503212080c9482d08211100554081000628040094403046214691190340c0d01c00c1e010910380701d10000602070243c9141c00d400f205036141c058010b071a20380f450091007403c8419a5480b580c444084c540d02c00a502c0400d019000d9644080701c0700c001c108504000d0710007203444a0603202d000c4e90402044000310614030801052000300800b00e1b00081c0441e668181c4014101da20a0040c210811002d298042040c6000e4040343c5108004065980c02c0c07041240038001c00c9041050201c00b41320200c2a000c10704414890300d141a4103004602540c40d074141c0702030000040c0c006004040410443c1e5500c10035480e00c0144004074842d07200c60000908490140341d0483c0610140001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 977149667 1250 977148417 977148421
    0x2060c1b04180f12141b060a06031e08160c150f0801030b07051b0c010212030610120908070f030e010203040e070302090a05090c0d0e07060c1704050405012403140703021b07090204080d0c0b 83
    0x2faa564441c01420181c8080404212009100010141a90484d8070075000c3c0d100c101d1410f1843c40ca480c1030414010704203c1328040e0f0804040c1e001c1500e60650f5080b840d45206030304c4d07424040d111885517440701804641e003001d01c02c50807080070425800310b1b402038099405d41c540c6401144e58074070003210711aa2103480d000200c1622407241c0e060300074601d0705600004e240d4603035850700200c5810040b000c41e4408a480d803204200356022072908034515080c0021800c10f424035a00b080e0446008140d40700305a07010a0804840d610710030702e50010640684450b4590030100084801381e40310841c0007010900b4209403190389100080c81004641c01c0c0d6807400d9542040e0342e50001c98030010000b40704801014440418265540d1090782d00038aa848803864a10001004041050302402c4030102890302d0705a4401c211241c00e2050b550244081c500165242036004c03245600c0050785400c1c1106110345000402d446445500820581c1c1c1c0c500d080b40c01d0b800c88040e003107614110b4120018040345920300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 977150917 1250 977149667 977149703
    0x408010518190501090c140111030306090115170906093a090e160806090907051212040902090a05100f0c02060c1b04180f12141b060a0603 61
    0x1d800b409003407041c00081802070003a01d644441b503015030402d02c6114020181d441482d0380188100c0100101c0c2340c043c6003541340201c001b902590341445090307074003141d10b0400020b8501c1f40d640703501a80200800c5000c0d50a0240c482590340e04126480e801c42e226909810a42c15003000c505a00c02c4119490318900c000030314041034800c100c0c041ca007011320001c100d000c5403500d110307c4064840c144007113030307070880c00b840140c0107003445c101903d090302480c540b40a02c51520303408100c0304140c0c1c205642801c0d50842440380185000518090f402d00b002010901240e0610700d07400420080d4011520b0140160f1035504110210328802c240c0781c0403030f24403115400454000c1846007100b84c0014501c0c3e00304410100b00505001d280000c1d00710544541e00c01200c00e00d03192040c40d140712044641a05102c030075503503c0c8501105514007400c0d8610103a0742014451141c1e25510040103100d03491a04c903204045038503030418609900f10910301a90700050103104551080d0750417680c00c190700d0300c0507402c150 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 977152167 1250 977150917 977150953
    0xc020604031416031202070911030601030e1c1106070323150402070303052a0a050c07081906110310030206130e012306030108060708070c0c0b0408010518 68
    0x80e40102e20380118000501d2101d00c1c00c210b8002540502c03035820b03500b0320b4904000e04180c030680010342e0281c580311500510345688000d481d13005000f070800040d603c4285590a207072040300700031120901c0d01480345400d00ca80c0000c0950002010b002103540c0794590700401d400361940380c42c01c04504450b500850900342c454401142d04440300a14071210380740e02e070001c00d090340d0026505401207500c42c02806100a99400382e0110301582c41a10074203a4106006c140e840e1050582d004108800810340c800390306400d101c2c8a0042c005242100e00b4004000070140b46107140710740642c1c20500e8078900b00f0f24040b400046131b11034043d1041c804000c6082d982040000d412031030680c0d8604c001c002000ca00c22100450072070281101d80d811103d1080f840164500350a20702607480d005a10610040204650001714150024140d040c100300a5503100d000700c412180011025000711030381000014084000b00080050710541402031101e5a520082c3d282041c040c103c01500035807141c041294245508 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 977153417 1250 977152167 977152193
    0x90b0f010512181005060306150105041203090f0305060628052e0e1c0b0604050415091109090f070e18060115020c090103030503040b061c0606030b06010c02060403 72
    0x1600e0b1801e800103c421000e0b00d4014a0000002000d0303956043c000e003440c04000f129070289605c100207060b03d0310000002e100d4060340c8550548089041044000c050041c48920050608c1c2600500d07103580d40c1c10041e0340d941d020794075540684841e4144220360044050410403440c1416883c8041a00c1c0006008201c1160001000c0b244e00664440c08014000c1c0e1048000015655501e02d9240d101c4082014443da0f800ca50845400751803006000103040c00f00ea03e5001008440009582d03495041c00704510b2008882c5a603c185803106c42010804040043d51140b5410786868003982e64504680b580d98400b180c044901ea03200e110704012410031340201d1030b0711204a401c00c03040c40d550442e1aa00d00442a0001c81304500c01c44440780095604220305090800120348480311303545161030280203880007600181c440700a807030000d030751502d680340c000e000c20902201030340c80c4020303d081c03180003805503000c12522080780f5004140c49604c1900324a814540040101785840e1555070340304541d00ca5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 977154667 1250 977153417 977153431
    0x7090209060c01151a3603010c0c050c04091104090609050304031a010b040302030303060d030201020c12040e07020c0d030e1807050909010f1d06030c091602010506060415050a020c09090106090b0f010512 89
    0x4206c0ea03941c1d058400b03024040a91a00e5124140c680c002842d1a0703007081d04d038698035409103150601c04004604000c0c0e90411801d81561700154045103400d0020140a5008000e0841c2c0300c0010004200074804003c1c0c2d800c52500804c05030f2603600d52a104049209610000c0c0d0b060f881400890918508140000e2440b80301c0d0000500c3c28580c18207a40c02d000c0b1440c04801203002c045801c014800105070301c0c2c0c0e4404468070141807903d40b040b00241c0c59540156000d803c0002801900b081c9444201a2004d0554142c2e085100d41c80d2510004080c0c1d4003100480e402200e40100000e0103c80c0c48402c18255080b40500391403019424010320b403000402040944c3c144501d00d148011520707500140c3d805044d81c0715014449410b01c4101a09483d0090301240c015081000100302030460003850b0801c41050380b0701250384500c440c2049207000c00c81c010b0168013242a0341407000d01c500c1503210004489008074117200c1c2480b86800c00002c84000c000080c04200100f10400c0500c08402c0c00310740c0312036 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 977155917 1250 977154667 977154757
    0x1303150603061a1207050907080a022820060601110106051002060f130302121c060f0503011a0a0e07140c010c110a020307090209060c01151a 62
    0x80d50b03440b2801641e80c501c01a06042100045030045802c22009040070a06070300300a00e80c141c07a003004544240d600070182420045000d001c202c0a8a56404a0700d00441403902a0720500340c40c3c03d00500180c52012050100f02282160508805c1f5080c25604040b40c1c1c0000e00800d0765964010340c0c00551250000c1c0c083d559a00300455141c0c0d40d0b08c14000b000c038880d401880079150045c4010100c20000c0c01c04040301c06a04d84a0700000d0b03000506c1c4030743d40105910390342c07100e01c0403410544002100d80c444201509042c80450003000744180c01d01101c43c1280240580c044202001007106010303402c80da002015600305100c1008a920907942013a01c0d4a4054030011096420038625048504140079a94540c0004501c20384e110704940b40c561a20006043d40c03011587c00a81c0d5102c003442241c92050700410404e41a030b0382e02068030f1919403010000d0020305200039400c1d21410040c0a041105400c0a02549560a0f40001d60f2441440403050b58054a8114032050311607007641420750b5025 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 977157167 1250 977155917 977155919
    0xe04020403050303010305061b0f0414040b0d2105180d02030c061305030606010f170a0e030d1d0307030f0e0f060d021902030c0316050304170706120213031506 70
    0x550100010760086006001230911804c000f845442c1518861f40805001c00081c803248400e00175000845044480200c580d40c0c0e8003103130700046000350241e00901580995031128400a0183d080f032802a40c00008a10f1441c12a0030901621180070702d074000d8180c2c960240c0804900d0620030051482c40c0e000030200d4204c1c2007018000380c0c0641c04000d41f00c0b0000002d4108001c1805c0410001c1e07046802428034140c189101c0314001c1109005045102505201002180c10b100455000a4988041606480da076959801c41307600541106141880070942401402d640e000b404010f8a01880c1d143ea1445003580302010125460081e07040750350350105902006552996561000b400581340980c40940c42c1d0200c0494216540c01c19105101550020050315150030390200484101e1000125805903a1550381821490360040750842801c900810f0113038070350400002400380484455a0341c040700900648440001d9000d54072070411114800d15043c0f0000f00503030b0f035103540340c030395000000340301 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 977158273 1106 977157167 977157173
    0x10501060806190906140a05100806310621170f0913050f09120a0f020f16050406171506060d06140a08011b0e04020403 53
    0x42e5a0030300240f5034a100981c008001e40701014042140b15190b07120710f03100422078600c1c6881036860a000144d9031400c00071200780700d145a625051035895801c2440f100c00c00558549020050854400c40d8140d904607070060340304c1c4000c0001c01c0b4146080c0c4505205118124281300782030300407441c80b010810102e500b0604050307010a840c0c0d10049006c0003500c0b4001c4184035a40480c0e00f2040001800c082e4000c45d0240c50b10b21581200c1c0e85849100b287d441840708152890400240140942c46001e0704d1195000200b034019505240300c1e48400900740a040e40c0d0301d40a0f00c124841c11311070380c102441010007410301c00800e03a103030040c9229156500c0e083c2c60070010200501800003003403602c4203c26107801c2404910180b01d210740303030504442d40340800306030a8051240e64000141c800c0c0b050140b14a00759014144000501300c1a100325018401c3c07060b0140c005800f00000800 = true := by decide +kernel

theorem cover : BRFrame.Cov 976978417 977158273 := by
  have h0 := BRFrame.cov_init 976978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 976978417 ≤ n) (h2 : n < 977158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
