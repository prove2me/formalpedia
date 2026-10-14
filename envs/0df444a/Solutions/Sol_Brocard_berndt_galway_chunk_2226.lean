-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2226
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:03:26.076474+00:00
-- url     : https://prove2.me/submissions/944ce519-a873-4671-ae9a-2618c4683004

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 400179856 ≤ n < 400359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 400181106 1250 400179856 400179859
    0x1f090c1503110a180f05030d0c080f0a1d12030304060c02010f1a040605040501061b06021b03040f084905040f051804020105030a0912030c020607030e060a1505 70
    0x2d00d0302200360b000002c0b003040782100c1c07100e8441140d6800840081e04481e106c0d41d90540c101c01000540765100c2d007280c4c501e45100d41d40181c100721a0008088160b00044038200105003105c11a04904505113180789404000f121908004000d0a0302d0545a004c00f500081000f5220b08400a00134001c0d040304281c040f2081c020005190003400342e10b50803d091010500880c54030a02146d281000e01420f030590f80d485e00c1d95080d081d521007540012903808641590f44507400c0c8a6001c004e1301003111080c0f80d4041000954450b0b00b8241d0130107000ba000d911005d043c1c4d1004248484074420b0452206071b1269401090010866200c00080c0d13581e02000e55410a02088070840300180e00000541309488050201030002600c030810f0105015492840400c100c801000090043d032041004640c00f0788600030100daa10071964a9051341d503c81a10076010a45807481440070a5040000b540d116125103030500001c040968420f40307411015059201c29031326241d402c1c892041c40010407004010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 400182356 1250 400181106 400181141
    0x10c03110d0e180906241005040315020301211a0c0d06060c080f030c0d020301030501020d0b0117070e0303070c08010203090712050c1905040c021f090c1503 69
    0x12010402000c501502101d1482041c3c920644a450703000200d03040d00c603254a00081420380c0b00d104044c0c1007609040c201080c8403428001c83c0f811074403000e02141d0b045803944ca88170f13100da040d407400d114407540c03455401c0074848c81400100180820701140f090b180c1480c01c0401c130340d4400340c03c0c14004104e90340f83c1c4d001e021200d081800380040c0000020310300041c0040c800c10078240c880740100d50702c0340d10000150402106003c81d0b0000451040115000003400c135085150405170361004051780c20981c02921240d46c08140780140508900074801d03103640034038140410741d0310180c84040c542c601074081000c001c40c0d01d8a0010a0b10700700304507001a5008a0280035141d07488140c01d01070351046a5414007801501800907011090b151210031060f032110182c01c40007021014015281d03a025049041e4a54840001131542c84e64802c0c0c2540e66002e5014000b168021001050240e100e420b0f078a2a036450070089101203003080c1d442e4400d66040c00010f0300390140b0303080300f20041c1c1142c06140c1d02c200c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 400183606 1250 400182356 400182373
    0x1a04090f0302010f0c050d0c1e020d1205040f060e030d14161815020a230706080c040905060303090301060821070b151f0504062003040302010c0311 65
    0x2194030400365605110303600a1082c4240c1d102c55006641000c8a802d011440038040511000074231f40207601340500d41d14008080032001908034802140304c15201026801036149245603c1d4040c56420208a0443d01841581440e03075444c4220a507606d00501010703680c85001c0301c00d18041c0111502c035210042c05200c0120b0200480c0c20010f01950442c4000742d4984c0c440003101d004501c0030203803100d00602c10301c0c1607180c501c10169140c69410140d046000d59100e060000328040b10052521840d584c0450007031040944c4146001ea8a40010f424801201c0401c40409841000c0b41c0950307a07004030214258880001007481c5004d400c0d1280c0d0316508044010546440014030030500d0390b48084220040381c601701c0c45030514852030f40c0c00790840e4880b00000d6241071905000c0480b1000291585803007044510483c00c201014000040018900003410011194004142443c8100c3d8842503260300c020390b00c105e56a8032407440001d05201c400a20301c424580510380d07440d128611300b41501c1030340 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 400184856 1250 400183606 400183613
    0xa0b0f150d0608010e060f1008030d061d0c180d1a1b0c1c0e030a0305030901110c0d030902011404030b1e060306180a0602040e1e040809041a0409 64
    0x40e001400e4462030766203040c0001070149414099031700c1e06091038025000940320004041420840101404203c080d95000016541c034100000c0030141c0b0640c03000107460f0304210b8009590f0b0728902c40940110720640900c0004181c0c08100c0c1d16104100d82d907450011300d4400840c001950030b500150546002d00f20001d480e07500406180c1c0700b01600300d241070a01d55840c2ca42c211718000ca42c0030a02c1a4002084440314030b00c0120046d9010510342000920301c8040c000192034201103550440000e04c3c040b007403100b6a4001d01030f0500c882c0080714020b04100d03010340080e40d285a034281c8141055150300940040da405942d003a001000303040b5410780da540e1a4100000707410740c02d0355080d070044007092100801441d0490520302610b8000d0140145071558480b1103010720340214010300303500660340c96034002001072005100500e601e00c030f00c0780d907460306905080c1801d604402c80000c0c0a0070b50100030014cc000411181126011140020301002020520309229403401d40217410524245010092 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 400186106 1250 400184856 400184899
    0xc0b0f150d0510050903040f1e21050f0f0615010e0a030b070906090e190e1e0708030307050d0203100f0909060e03090616080d0501060504091b05030a0b0f 68
    0x4800410b9062100d80c945c840001d42c4d0384110303c25103206880340441401480d007465821803040d04400090340e501074846121300d1076000c4000023841900202c0e0184003c101e024400310140e010544050310005820140c40360b280e010040c2700c5051804400302000640c0c2c0a660b01107c11100034051400c02900c0e442c0003840004245e641e80e0104120000000301c10348250410b100365504941111380d651110381345c00c03d00d0582d4034070201d42c45480f00002a80d094081242c483c0407860001c04001c0c080c3d1a400850070003203140c00600c000d810810401c00b00c150040d0840b076000c5a182d200503a00d541d4000300b4920590103400900e0010f000c00302c0041e585441d900318080c183c2c0070b401c0401c03442c2e514031a140c0e528440c0c80ca459403c25005d0110714840004041421341490048003a14a03001085440b00110340d800d07005907000c5440850b050000b0f58141c0708040641004405110046030b000314080e20038000203203049001c94407428202c0302611940051501d02c600a0701c01d03083c0348405065842c2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 400187356 1250 400186106 400186123
    0xa09050a1a0901021c090609060f02040f0b0c03031f030605040602032d0106180e010305070e0c07030806060c0a20270403110307080f0d0605010c0b0f150d05 69
    0x1a0044160301042c4025418400c03038006640340521100c0c0c031003100e21a503011346603900e0f0503140e50713a507003030824082203041c022220641c0c001c200c01a900d9051003218092505541c000721100802804880d421007000802c8907045040290301040c05040381c038003412881d030310381c000814560034103003440204031164014601072036a0030990b401c034009104034800d1806076461105000b901140040000c540a203c4400905280180e9448500d4461458001030003083e0300032200366001201c02c0010780020221160070402c2e202c40d45161070055100100061000f48c4280d01c1901d00040d68036040008000d803001c090784c008204080d0303040d00d828644280f12840c0c000d6014a5010785020f609242412051a030203803c1d5901403890344481e242141c6411007542d80010501c8100b00c0030010071201800b03840341c01400b42c510b030f5549800d56180d50540c1e0450348842d0500060206110000b1149440c2c0f9a1001480119010b00d9981134042030281c80120b51454100c014042441c0500801165504 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 400188606 1250 400187356 400187393
    0xe06040b07110703110301090602130e01050a0f030b06010302090423060a062001021c0b0109090c170426070219180207020a0504061415160206030a09050a 68
    0x4440d035075008000e55400c109660301600607000441e051000450126501e6030701d00e0042c000081020300740c0c5d180c4003240c0c40b585103030185240341c0b4420050041c0c074004540c05003000751002501d0358038240300200030100d58000184452450750020320164401e0781a82c0c0381c0c00c0000c10611000074412000840325046642e0210030321555030005510f800d100400070121403143d0b44003480012040c0350040f4001100c80c50300010754007040014a007400014074010a810550800100c12907003400244c1540c08940c002e06109003481c1d40c00350150b030082d0840f1503403500000b00c01c082e6640ea14000a02d10300e4040c0303031581440c20710507003410409018007a101c8a442514400000301e0b2a1503180c00512451080791202c0e9070703e1240c0020240c094001d0808144040c15804100703031100001000d076550f941041030031118441c5001c00a01c0c0c4200d011140901d9840c1c01864025100c50f080d01024031a9406400741200001089880c80035600562000f9041015a010002e5500c1c0c8891032225049691 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 400189856 1250 400188606 400188623
    0x1201090f0f05090a0201030b03070b040e01091b140a03140109020c0c0d021f1106130302100b010813110a080d09060801050112050c1303110a08010605060301270e0604 73
    0x1d41011410301c1840d00401c0104000d0600c83e89a500440141842e1000e154040c0100300d40001c4007610351000c0e001900000c4070b021040d43c1045070000c100d90502d002c005c102e043c0d020b503245095420010b55010030701203150081d500d03031201806501030102d580035088680d8071080006100d220f998003400c80241c4142c180d40b60980b1140c1044840a0030505c065407001e41030142c5980c1451508040d000c103d15800e2940c0d424a0001106c1d05080041700c410064003000c1b02040101a410b005084407044280d02c01c2008420540000f051080010585500550f52000403018030250265940103a20014a0108690b440f206c140b41c880c488060301c100420405a0302043c0a4003030350005d4160307601a518907048090509100025000140070070500500401c544001c0c500d00b2070b0b28102450148404d56078011280d401d0003441c482c5680101666450008103101d03544d00c48044904481c28001e0702c94000d445440350122602c84500c22207002071070000100c107034140225209110364040c2c0c951 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 400191106 1250 400189856 400189871
    0xb040b010e0306420f030303190e030705030712090b0c0606041104030f11010206090c010c020f27100b09010c021002070b0f0705060112020d03050a03021201090f 71
    0x5580800d120381c07403954960444000141c505410102000321076150b582103009011030701c0c3e40034286001078031010301507140c4080c00070140d007404007540885101c1507004529501d81a201d1041103046806004181d80d101c820400e034a0078100140e4964036089025255906034a1618036030303188640080c480421100030000410100202c02d885680ca03006016003526907580003004007c05091016011110341030002101040070150b6040f42180304440716514000e44100181ca04080100f00d01d445034800300790405aa640700c194503089640c10b03200c41282072454000103c0c40f04940391144500c500703074520081d01c000038004082c09032081001d200045074489001c01c8052003004112800b2a00369026200141843d203c18010410144141c4006680f030307015600b4107a028003169007203044041405410310200388140d0380100001d00303070041c0307a00c1154041848107401c40f0010301032100214800c0811402901101da00d9403405a0b84011503850b400b2110041c001902c0e850151840d0415 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 400192356 1250 400191106 400191109
    0x91305070b040e060f031908070f15051503010e1509010204031208150301051003140705030105010603090b0603070608040f060608071d07020111030112020a0b070f030206070e0a030b0a0e100b040b 86
    0x1032084541d42a20644840402c031f40d00d50412a9100140848409504138004400709020040b1841c000e010b11101050030308140c1d0340b0610324038041550a10903458115030241c848030004405103031802d44c1202350f8165031403102c4580203000b540c1c40902001104a84c0624495001100600c1920000240b01c80c1420020616003211401c881c081c00e034040c1c0c00018804074060301c802c84910307100c400807200d000ba1580046802e6070800e13448540403940b608245002c1003403042c0c20710742c8101d00360014044180b8008004045100141021b0031820170307001c142d400c8c04100d81083d005030090108a4031080d80d9518080888442400200c1550395070501184491744180038104491084000c514250307401d01c442e5028503050910b027240d11500301c40c40000c84410300c50140900300d0052080407002c000c10f050180c00d05200030400d0b81040310790001044150780d01043c41d010341c5c2d003140d08550b079a90b400000074002d242686401c4140d2090035540c2c001016207400c005103c10b0142d03000d00000301d4000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 400193606 1250 400192356 400192363
    0x80607080a0e0606060d020c0f03040504200a0f090e09070501030c030c09030206090307180509010e0a0302060a0b15070f0c080f0705091b0309071401080402091305070b040e060f03 79
    0x80409050f030000c0c00850294541000589140f48001e9001482c03c00150703061880d1500480f06c4100075040803808010501d03151003810310a02040410440d09a099480203115120ba820440d00b44108403005000301071160301001d014080c014005603250400b000b405543d01100d00c0b0740ca002a05020802c0f40782d80c400d005840c240d03002c940700c4000950a503030030440d1917008580710a8141c40b4405002441c0c2001180c031407002c40c1d0f604800641418aa070034603080d1180f8000566180e407058401034000b942c001110382d40182940c1001402168640000301c8443c4420f03159103400c08040740c01c030140720075540e0030300c149442103403441c2446503a0190503841da1056030240400303030401142085039041540125900010320001c42c4010f00f140041503085810a66a440c2c150748a05070900c250021011500c1183da13003428031b080301d8582070740083c100c0c9200404541149002300005801c1007001c00c4003401a180c101081c036251501c070740384540810700460380140b14210440304a0081d08011 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 400194856 1250 400193606 400193621
    0x105010f0c24230f0705190e04020c030d0524010807030b03120a020d17070912060b060708071a040c05062118060f010e040b190c0e030d1706010e19080607080a 70
    0x5400c1c00c0c5114040300002e40323200e840c071443d40c0e8000781c080000910040c0d00b40002d2001a01c480c00c00205410304c00d1900784000003980140a075001000045005a03810100741c1e68401c45500e40407541034031800219080604200c04c0d6580c00740c0102d051a040741d008030b007201ea0350807580d44160310043c03807013075101401c42d0a448181c046989030360b05000e10034200c03402c840003500408000c038502900c080800c480e0350040005503a12540401c1c1c032802c0205030228010700c0ba07031504440407503040c15140c54040e00c21510501c0d100d001c00203072000650001c01c0750340500d10040030380c44409180a416801360001c01c0c00c029a4a40101300c0015034014603485041d060303c440e5048903640d50f55583e211082164045c2041d04890308144481010503403d01516a80080766664050041140b0382410b00e03103c0101030585c20b201007040d01011441d00301a02640c00b420903c0d1100b1100c5030900031907401d00d020110300512081c44074012900010004010307004000d541c0d5614004da880550000858046 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 400196106 1250 400194856 400194877
    0x60b121003120518150301060f030203010b0a1d030607200109050607030b0a08030c07091107211202030109060e0c031303082d0105010f0c24230f0705 66
    0x402c4010aa282c0c41800030340740710100c000103982e58841c030a000801d92081038100303184c000c030004010320003294410081410079185042c29411541400c084c5443e502035101d0720410400b6111902d14909698a0004508000503054880740d0504c4003004041e20800030f400b584880e150980e02e40103480500c90a0380ca1070b004000f40900e03807610f60f82200580714845180d0b40c4020400c4001c950f04c1010310060901b09036850040c5125443e0482c41c105480962030502c4000000344682404103910800d100413440c10100212000b60320b20782c0c04d9407020050003040d0f260074070100001c5107070140d590011040d5034038000011010b60394007000d1202480704071030756a4030610341496103001a01500c86150801101d07500b105140d8013441241240035462010b036800f200c6000010801e550f00150084d030300702d500c4e24120008640c1503c503082c40b00d007001c0c40700c4c0e02001c3c6080e0310700302d8400d03e41c4446c03541d4201c02039641c40003480c90350004c00c828050722102454141000410907070b90186088520310300c1d5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 400197356 1250 400196106 400196123
    0x2030405060f0f0a08041a01150305040519051b0a0b0f0706091202010203070315050a26010e03070302121303082a1b09010806010b03040510060b121003 67
    0x4003420300403190081d81c69035441042c20f000e0315006001c500c0203401d8400e1140c1c0d9414080c81c0c54203019141229030102464900e1442c0011f02c0400800300b040c92601e0198140416240c541e07260a40c5001400402c10180c41d01406490082003004140e401111030103400900c980c00d102000c2002c02965031094500d454020081d0311070100188001d0b105480c0501e4001440e60030356110980c0a904424040300103075030000c208645140c0604c00d40684050310f154002e0001e0400012445031445400756403034040500d10341114104080c90f980f01884280c00082c0b1265010700c0c80540c0c2e1760021203040340580604560701e040e0030000300540d0100140000c88101c0d0034515160881c0c554080030000f0602c1024002007030302e1207110107034061074032098001080412240b0340002c3c920300d5480010f5104001802c01045076880000344181529003000d002990313500c2d42e203400e03032500054826100c0314a04003000001d0000041018040c0b4880d00c444070300c1e40385c1d600c895803000d56106000c02400b880 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 400198606 1250 400197356 400197359
    0xe010b1312050a050105071e03050103050d3c1d0a170109021e03010b06070b010302040b030304080d0f0305060d0f08090d14100c171f0905071d03070501020304 70
    0x182980d40c400320703041c000c0b0300381e45110480391221402d4070000c5036503101050904403120100010b816010441c07903030601c0c08003c00d504503950301c1d0b00d42558980d41e8040001e4105001180391424107082c1d42c3c0d40704d100c100c51180c1c03072840824402d141c54001d0300010480c4594080f42804012080c3c1b600400020200c0722070504000354032644840111034030f0341300c0d966a074034070303005171240040d03822148000c0b000d4071281c130011000c150a40d003008035000e00407803083c041c0c0340010b840807000505607a41201c0120740c1c002d00c032001c039145001d43e5215403003902c43e0f5400000d03802c0e00002121811a078940c2c09001e00d07519170301800078184580c0c0000708010104058038000c10150000b0f011440d4004207804640c401130b88415140d0300c1070024091464014504850a11048c1c0c4601e0544845134200a2440a880410380302c078510020100103a59002005c8400c10a910038403078005010101d0040059040c00d10000f066400c40818000020310b99000b010303c1c51800240407000c40700143d001310701d0b05 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 400199856 1250 400198606 400198619
    0xa18110406080d170705220911071e03031e0f06150c120e030f1c0306030803190b0603160207050102011505061c06150311030606070b040c03020a0602070e010b13 71
    0x242c0c4000c0002c0200320003032114070b12501d01e00e00c54144c0c000b406d911f0b15185608044600046176841000c0c440000c0d0f040242c2c400180171500710052078914880907861300886420300340c02400d29421810324000705244001c443c112a0b0b407181512146240041100d1525090050390000042d10078a000c107403240c029400241c41040e04200c842d941d8900720b10414180f9008c2407401c1e08155080030036421a50440c800402e8650f141c2d100e0400f02d1070140051407954603500d1891201408100d01e460b450305082203818081e41189403203003400360a0b2503491510075520000702c00f00c034601d01c005000340740000035990f10500503400007424190f941e510a51034034040060981c0320023010301218990880720304203040f0700e200d414001d12603040d14012004001b0340040c00c07a42a604840036940d4140103101da50703182c5c103061700c605139441462070490307882c1e60403c05102c5982d0350009500c0380160101240c4154040f5510b001c42d002c9140680e010398882c1080011070180040030101c0508041040046 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 400201106 1250 400199856 400199897
    0x2c0c0316031e02220b061c110f0708130308040e180f0721120e0a06090806070e060d09080408100501030b04020f0a15020d2a020402030a18110406080d 66
    0x2d00c2c51010001071902094004103400383c00070301030720000141021f68940140f4190007040341c201d03020300c401850000c10004042903401004000350003590042121180e4410a0030f1103405143c0180801c1d4440c4e90300c004460351100c08440c01050318600fa9655840014002000002e00c0c0488010b0843c650500300302c0440704007214030300418012038586660225070703040240305038455941c0e60082e46040141c24410103141580c0003001300010038504212040b000303e0074a03008205031030640000d0311402d001544a0069042c068582858003812901b04168600103100300c0d0340e0745065400c010341e030418542c1250024400684021081d10001c0d0061800301d0b0b03031485d4000014050240251150481505001c66902d408091b91140441a469942100000089046035646c0b0300005110300c0c210221031040c003170001d0150341c001c00829003090342600076041070020190500c85c00c1b2080d041031b6003d10000d100640c0154548a0003041d25070303012844058440994445181a01503a04c00291 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 400202356 1250 400201106 400201159
    0x1020115090506041107320607030c030618060303030f02130506030925030203060105220504080f1c0e0715081504110c0706032c0c0316031e02 63
    0x1400707540c41c01200b01c004405170182c031806024010380800c0641d901440d2509141c01c0349081044003a442d4080b840b00c0300007880650181d44c03440c3c082035182e401d0105030003901c201e03004064603070354000c0e05c0c41116040e80d2040084a029036001e015480002101c40c04a01c950035803802c03c010001e10170300181c00c0c0003001b0368000480004803403042962200a4080c2054181080040b00d00c28004200358941000f445000d002e04591030b04000b00f82002d0043d80a052158001c43e19480c0d200040a02001c07400384c172803035420141a2555480c4540324594003070f00c1c442000d41c03242e15104070180503c03000034480c0150b034101541c24400b0138100740c06884c04407008003241314505000388002e02030344541c014080c1052000e0501526100c446083c0750400b00d05410900406250049440c1c0d5a01018202010142115506440303d120562031909103011050883c0d0075100700103035841c000b9003c501d8081203e008054544e0741040760868040b4220362200042d6000d07044d040091480d90583d04d002d117 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 400203606 1250 400202356 400202359
    0x203060a0311061303050703051203070e010f0903050607021614010212071106120103200901061404090e03071a0c09040f090203100203070f0c0503041710060f1401020115090506 78
    0xe0608041d04c50307104001529410403101034000c0702c010400c004041091080120382e80044c281145051040100b00c1c8442c0d104490400452100c002d907a54090214a0040e503081030030303103129192034140655140e2509100d8070055448103070010310324007210200250018160f01510100400d51a56180754002540a550711844a89400000c1d51128010040104070744940c240035032440c00e0696050140301020140f60010481b0311029940388043c050540704c1d1400c241421003128642c5403501e003d81c0e04080051031422100c0544090004054102c081c0304103403020310a0498a00200c215509480c03a40c4501400c0c01342ca8814a081d82000341c460310701c1800002d00800940000f8502582107441540c076035400824412407990118101c3c0c04030b881814841905209950340c981c0e00c2c8114414011503840751514482c801c0c1040c0202003042060400612a4035120840500c1c04901d51246d004a401c061502902d954018029000c91215070885540c5030707840d181d500b201800c1c0040925 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 400204856 1250 400203606 400203619
    0x71107081c05130e0402040b1f08150910030b0618060f01110105150a050f060d0509030423030d08010e0a0902031002070605010510090503060c280201050405100203060a0311 76
    0x2d0485240c0440e00c3e0700200410308000303000e03090600511003202e0400159074000c21401500070308803004111030807046003940ca8041000e075500e4031122414001e0020155205e4040c07018007980207808290001603a024070081031458890380d01b08185140ca015609041607000e000180304e901d070944402ca242034041c113142008101c162005400c40300704503469a081c142420030307482c013420074226181c041d10090f2a40700c6500c3d040700010310179000d9034045c9051151100001406468107000f80c60040100d401041c129030350b404100594520442000c502034401d0185100e0024401d035402c0c2c6c100d804141d80d20b041900c40710460301c060210710805a0305441600e40b0182070b919544001c1c17481038026400010194101010440515115003040041180006050210340d0f4082039541d0022044000a6038682118088501050411002040300c4440d2110b01601c65019048280b240f03202c0c80980e0024203a6113a100c040780816200283c00802d4104c090002880c2e0080c0304200700c4004145 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 400206106 1250 400204856 400204867
    0x6040507020f0a06091b0602031803030903030403082809081c0807180f06030609060915230406091409060103211707023f03040305190206071107081c05 67
    0x301d07901c1b8041d90300440043e0b00c001a2600b5003006c40c80c1074901b06400718051031070b00120a0000303580e40680c0c0000b40460400240d101070058821121000e00b120315196110498170008000c6d12855842c81684058021007646031f81032550850ba000390401c40741c80341b8144c1d4a44100403601d01050281c0142c1e02400114080741c3c000c000c1c00c0000c014026582c0104149051002c0d079001d9503c9640400c0216003040082500c011500c0c814200359914202c42c402c0d4040700400e084050010062202d40107441c100012841d00007540051140c02481c10b21114075071103000c134036651400d0034440a001c4855800a1000c1c2d8a1817015100a01c052807510100300100340b045031004c0303081a245400545d01085248104201c414000340e501e4198440340d14120040ca88070122130841d03030f00c025031303c3c020020000e0105030092041d50b84a07201500d401590b0780c032104000e03541708019601e02001c288212455000b43d0310010348003081c3c6103d013024015018014002d4060b910310a481c47e828014103206 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 400207356 1250 400206106 400206143
    0x3040807060b130c090b04031e02063c0a0207050103050c04031e0501050c030c070312182a05060d150509090102040e01050a1d0403031d030306040507020f0a0609 71
    0x50103c05a041500084603c0700da0005419850320f907004070900c000a10082012461a4500405041d1180d4656000100c1840002c0c590720529220700108a0170a001c8520b05d024010084500c0d0081e480740324215000b402c080d2168060700c0b030114010380c4102070910081d4071035001640c00548440a5505054a0b41d0710043c0505e8070061030310f4000740d54145101808800d003d40c3c2d8004010500340340c42e50401e42d804251034850b209001d0b041c48142d000301c801c0383c4890381c8104910070303c449411155440c50704e8072440c80640819601030f0302030411407000a05680000310760461300d000700814540380742c40c900a0080c190104c031840d281da40a400006458483e40b0040b4800d0815000060381e550030105800780c00d0f01c0680115014400c0794030240041484200c2040c03606140e90b0007000340c0d90301d5103021800340c410100031010ba00c80c081c0c8010900c00e0004050360281c00d08880511250f0fa42d46403c03a901c103a40707407029a8070b03808044070501180c4075034004907125000340d119210440c0a0030303 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 400208606 1250 400207356 400207369
    0x2092b0210091701141003031b0201020a0b2d06010504090b0607060903050c100b010909051f06090303020c030a021813020405070e040506190618081e0d0c020603040807060b 76
    0x1a0b1200e4036512070345034502c0050b012400075805041085086c0c50070342141c0303004004800b28501d90840c5100314000005580c02009903c5005601c40b4900070b0354940303c1c1d640000c5640c0412108003100711005481084980100034521800040c0d40d1507043c14541880c0e42d002c0c12080c008660031060411103080401c0082c044d80f1010740c06511003a58a882005090340741c40d0300d03895400085440c020500b034450380d00c515594111080d082000c241ca445e0a03604098403043c2450a030030106071301d84009902c540050440c42240c0c040d40a45a602d4404010b068541c603d20724002c0d070001c107130101d050400f09028032030340d0054440d40c40f00f0a800095808541110b07800c0d10150085142810248102d10b018040d40f40c1c464025a41c0c0701e0000a16800080c0c1400760b805800180018280350f412008021040c81e4014030b040c008503031100042c815102182d11031884100664012003440c02c4038503000d40380c1040100d501409851559031141c80b152102d0b08220005c40d407454a542c0c100300c0320b95885 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 400209856 1250 400208606 400208639
    0x32a010f06050a0806010e15010201020d1b02010c03110403080705070b030403030605040e1b0f150d09030e0d050c060306041e050a1b020c040c020a1502092b021009 72
    0x4005001c0381040e00b0403a0b02d4400354846a8241e00220061000e200549070041d040160103d280d4160a00600181e001e0b015010816030113034a0914041da01c0d092880345500010001d8000b04a03402103100104d0035a007280645d018407050402c41040000c5071304000b800c0f42402501912070040d2160480e451543c800e8034203600107038480b101440a40b6080c0b080080c40101c03880101080520204e29a010f11080e40c5d480f80316202c0d058035540c654407078040c80600d45690070002681d880000143d2401030030720394415000074402281c40318850604a82c41c00140e90040300402d0035050302c00800c45c541d800105007580140d21038198800d101d401090729480ca44060b0b1000c50b861800c040307120100c40805038202c45001168961014258001c58050709490007036401040000c001d00e0b0903071a1411404006140d403070f100d230381c0c01c01815030342e80a00ba0064084410140903051b00c00c80c1032517048503080307a0424180032042c1a00524154414080900c00f0b403c00c1e0100c80e940d60320089100080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 400211106 1250 400209856 400209881
    0x302011e060906150813112116030803040b040c090507020a030e010801180203100b0318010b150315030f03040902040e0c030405062208161203050405032a01 69
    0x50307039424000910340b40118400707092000000d4010140b500f03802000428041c1a24080c0c00600c030003401031002c210102c01c4640000ba001c8844000840e085403440715524070800c0040c02294400d048240e0fa80c4424001c0b00e410591003411610b4a4844c0c4401502c0503104840020003100c00048200b1140074951160341c0c2383e0094600c24030241000ba0001c1e405031100750411540c03400600001c54408000c07080c001c0e005100584995500003a09010090754124014600c0c0110812841001c000b03011091070a0b2a4001d00c2154100030500100620b504482d06100c4014000100741d01c1c1c04030f5103104103490050480d900d0001c5130300c03600e04540c055000303e900c2580004047c4083c80364425120b401407074010354985945021b840701078075100c001d00600400104501000480e501c40d807211990141c10281c410b5440350300d034030101c03418000f2802c00c560017020341c00e680b20b8141c003902c00c03640f045400c8000780d443d00542e02503580190310340030007502016880c20081c8201d04400d03c06c8031003e144 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 400212356 1250 400211106 400211111
    0x70b010b0901021b011b26042105120304110a091b020a0503040e04081b0a03031b1d01090909060203060f1203040902030c0c0312040213060608130302011e 68
    0x41c00002400e0407212011100c09030180300300c1d07800590744120310303000c00c030705503480020007200514042403c3d0144580364a4040c1800c03104c402070750800340060044440c001814450250018148040410744100c0a026a04601440c80307010705070f04004c6620602c25a08101c0c54811480090744010050b086550715a41d296038900c00d03001c108101410400c1180001c05004142e59507060b40c0f440b40d40644108900564082010803020760107661140414508030f17224113480c7c0180c20f41e0b500302501e082d0002800d11211354500041070f41c5000b002d030041e50790100c000c58183c0d142035203802d1811000e0704010141000064102d40ca01c40d48582c24880c020140c0e0382c0c10030208001c20b140d6440740b1180b00f0041045440d1080000108035011600480c40240c2c03030707643d08440e10b556409400303050f450324000010700c10144a5444c030074620892088460104d030301c03001900300044541c1400b584021515900c007181d44810b2001610328000d100344000304400c9140392452000c0303585500355403000c68 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 400213606 1250 400212356 400212367
    0xb030a0e060915040210020127020310020906070b06030c03030a0207050405060604050904120302040f080a0c060e03070302120c0a0e090d0203270a08030c07031e170a05070b010b 78
    0x340300340000c58000034a00000c0c0011a03155100030b0f04071501800083c410b4003100e114406e0a8000e40081c0501800c0d072101c204071058002c03010801200310403080b842801500c9604400c800d45100303903855010b015000c0e5007003545584d90303125889006862250f00d40300b1440751030040d0750204001c2111000076030250040c40d1800c01800103940003c0c080e80c0c4992414442844640c0380c000c52a580076801c51075001007211104010ba000b031045402001c40800b0748900421100800141111924407c1e07404040f900d5a43c00e048802500d400380c2150b064011600c01c0026103002c0e240c164140fa01401a54640702540300012007103004c6901100711100204101b181c274103070621400c4402d5141f40080e614200c111440303075900c46420000b1418000f00e9081e00b08044c0c0300c00f00300001800c0300008807992040c25100c0195a00361520040310f40400c520404074119145101d51110076a1000d4028030303102c4980ca039000190005410603003002414806040403551881c0788070300a10b841c8884039031b140c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 400214856 1250 400213606 400213631
    0xf0f0f170a0207150c0804120c0f030504170703020102071e0e150a150525050708011b02030408030406051605070b03040312200d060e010b040501030c021b190b030a 72
    0x2d41600301402c0c1000c0c5000c0d000e105e901d80180e8002e0f8000da001004000c00c041103d0b082d0343c030801c8035501070000009a00100c04142c2c00900800075140380045c400e14141c40740e01c00740d556241c42d002c002d00603000500c1c20804503183c02c13402c5054100e15481501859107500384174010741000c817008603104822011903440c0f81001c409650240042c0140a040c1270001d0030042d000c1e10031164003d410801550101c0c4aa0364100741041803140d00c14203941095944012041c0a130040e02a01e4400b074050000000c8414000003c8404880e1284065400c26141030301c02d4400340c00c241081c102c071078040401440040c105104090103000480d18281d03e07410300d8203005000140f12000c1104051900014150820f4210608038240c883d0416055841d1110700c40d860290000380e101d64000b11450300081100c40e2042d000c0e000b95002030764208000f08540401b20380d00e01060050514200710081201d0070742c01c0c03030808283c804030301d017240c5403001d6980e03010420746510031a10303c007070b042c0d0310786980460713 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 400216106 1250 400214856 400214873
    0x50607080d060e0403140915030f01030204112703030f0a02150609270c040e010605030c0d1212060b0d0f050a0b060a0e040e0601080610060f0f0f170a0207 68
    0x3503c1140725840c960b1500b981c0161510302610440b003a2103001040315030302e5680b65000c04003a41203802c040d945030b0820381d02d0042c95442c2030108030311035820529601044500c0303400365840d242e06152460590700000718105607050480308205d8244c0000c01030000c00c0ca10403070041800d201c2c10f5005000c0d0880706c0081c6204042d001e07000a1088103c0c0c2c05000d00c3c4521030070b110b4070654481110348503c001c1c05581da85082c1c101c3c88101e4005040c0b807400e280880341035100004640058095400c0d041d100c808000c260740d00c1d0b0000503c2110200c0100418902c202c05c00c1d01c000c400c80c00300044580d100c544521381904040704172200c0f1504c46060000d88c3c5500e000c0d0a030840c8070702c0d03028840f1100343d400107006800740411400400208540b19003051f40c0b20341014442c031400e030042d10110b586030f11440b910344000f02e82d440e1903901161400034015100e141500909910360790b0f00c40001c14066412986800700300d4141c820000c0c9a085610000015007605000322540320005a0341c200510300a2003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 400217356 1250 400216106 400216109
    0x120901180305160f0f030c05040b04060306050108010642050708030c030711070b04090f020d050405070501180503150601022406031b0307092003072109150e07050607080d06 76
    0x801c071400006c20000b095200404250b5200703d401080500b81d07040800c00425040c1c1c8042e107040d0810000090703005065021400781c829509500749517072100e0324042508129904050100a4603c1c06118045980c032103038446104545001480c0000030b0b1151042e0360400d9070209803030074000090141d807a8006021070600d00c501005807003058508a041e40e074600035407080c1c000940d212101a071a14a0b264100c0f04892820f407010007882c2001d051050351541d43d0f001c0c05001c1040c01c0f01c0342540310030200401c0d044860040003454a0710181e240880c02c031001410803819803080204926901c60503428092134070b0040200706100385846010989094241e0104442ca50b0380e030000a00c20f6100803510506440300101c1c0070a185a905584084503102c50300240c50034100070052100c11a403101d0a06a008200810000b202c0709420310a01143c0b98064002c2c28508400400182c400454001b980c00c039540400b43c4a1040c1d5900204a4942c8505400c0f40d610340700044244080c0f0b4039108020 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 400218606 1250 400217356 400217369
    0x151203070813120b010303050f0f0f040e07050708041818060c09060c0b0c0a020a021206071202120604150504060e09010e2d0309270108120901180305160f 68
    0x1400c0500350300c0b80c4904084c1800080d040001c0022402c0c1241003100417030798081c1c00051541d0342c0740e501c0320786400300390003d000b5500d054194001190810b403046054844240e000700c0350610346494140c0145003000d200418081254843c80011510751160490029140c000d00c2c01084030140c81c3c000424641850b0810300500c110b0b2524074005c211a44845640714500e41d82040ea18218450700ba844c0804100c070095008044144034011100d011502c43c0c0650815242c1ca0500d0b01c0180364141a40142d07008140143c101030009415851300e500320803a24204601e10f10901e98944c1d0110341602c5c2c1c00c0c1c10414101c04500180120300c0c000744601032422421030003401c00301e001208000501c240d400c400d920303100d400180f15854500240101e41e00d0b03039001030502c540b5119540703181401c0307a00d002d000510f9071684000010743c0350020408948010018071000d14008401e001514801c0014000d4648840100400700020707604210199071103002140840450b45400000034050442ea000013 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 400219856 1250 400218606 400218629
    0x90606041107030e0f0303030c040f05030a03080412110304120b0f070e0d031e0c210206010b0c0a33090203060123040c03020c010b01021203151203070813 68
    0x20604a800e402e640701d156151502c03101a01180b000649901a20310305140d15010010501984106c040010012182c603040c820000c0ca941e401015120740b140d000107004504400d0000300022011005000710700001c0c10140e43c00004500b400745590860740001d0600d00144d003a20040c001d00c00052544a04500c0068003d803411200c014200c094602d0309034081c034583c1030294109800b90700309011070300060390b41da4005000c1d50300062810602c00404c0d540c1c520301c560a2404d090750124049644000ca0b0010700c09a481c203829110141d000141125050040969034000120040540150000e81c0c0e0a03103c5006d4010b0351814249104902c040307541c45c035083d00400140c4003c2110b03811551180001d40a48070f1100300d03100004054041c040e4820325000c2206a01ca40541c01360100031100c20080000e078507401e005903942e0f1000884500d9180081c8000340f420b184020b18550b0840c0045c04600211103251000d038030350f8000d420200c461000200e181d03480c034604260880010200c501c3c01 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 400221106 1250 400219856 400219871
    0x5010c120b0f1c1703130b0603030304111201090219090605060406020604031b0203011508060705040b030114010314070c1104052403010b061201090b0603160c0c03060204030b09060604 81
    0x20740e90400e030741603003e405100349440c5040c04411a0f19a1058241034901c03a601c0c501015065407400740301c24202c41d00203a4001007201820700005581c8510741c4010700484801ca18401c0121018090000007029900d810144005031580485140100178903404004024182145041501c0b000d40240f0f01070701040c00304109650b40040c00c9070704507401d424003190034030044c1d00355103941c50004030294166081119180c4c14114140c150b030300301c410b0139003540d001d0b0316141c43c00c8506d0300c100c2c4a1160700e03503001c0c001400070102020032024200014140001ea100d0b174111003103007035042101d4000100d2550080c04041c41651101c84101c020100c4041095141c04440030342c0c510700e0942c90100c4d154040305010f219072425404041c000000404283d00d44031080301c004101c0d80d0034050301c509d42d800d01010010505090003541d000300b80310305100f40e07032082a40b001c0703914151400e030a40314411403c40010100d0200d00c001c101540c011503882641c0d20f80f0541c454901031018008134003941c0303040030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 400222356 1250 400221106 400221109
    0x1a070314010905061309031d040e0705060c07081609141006030b4507020d111c030207050c010906050412210507140601050102030d021605010c120b0f 66
    0xc078152074010400150340d444100101304110400c401e89a29289424000000d041c1c111a03141c0c0c0101e1a114403210070002081031000343c9100706800000d6070700000302440a45440380c007500141703416a0440f440d003542e4400d200d2a103d920861045018004c007020300000406000b162043d4208840c00909400c1a5039022100724103441010201961a140d40c0d40b59070b50790031200c20b48041403608202c0018039042d0070f10001ca1030302a2044407019104140c041e144a1001d50f0311801d17450f0007500402c4000740041e03c3d902c1501000c42da840c01006000c0c43d402e060a0b80c1e15484821070b580060f141e441d2071403d2482c20749006e06042c180040d02100304101039106007241c090380d040e141c111507844020b2800b000c010406225040c0884244807141f1601ca50008c0504002c1e402450400b852814100f1542c0d1514028041c89006070020010240100d000b81c005180004951205010403070700d507214142119a526140c00001d64800149444080703940030310041130004030780a0144440304070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 400223606 1250 400222356 400222391
    0x120109030e0607030509031209180c07020405040201121b08012102010e040f110c061015051303020d0b090105010b04061b05071a07051b060d0915091a0703 68
    0x510942c0701d0b100004000382058481c000762203e4841c090110f900c0c0a00c000c80102c0a42c00018801c3d01543d0101c1401010309510342400380035501880d051850f2480a4007404041c040080c0280d051010742c80c0003600c440302500c01c2d02c19004040b840580381040300c0100070034000040e4050790301c078090701080810300c0400f1940ca000131a130908003400480705400c0450007030402c0d10b521000c56450595000f54005600f40103083d00c1180d00c01ba00d10340e68400c16000300d9204507004501545074800e090010880c040c00087c1003030032030800c80d42d00407030b80e070b0f400038400801e901030440760001c22005000b0340c4070003401418098007030040c11a0800b030a0040003400f60140b0729000700e90141044040042c80410b01c0000f028011001b000e265881025084041592002c141142e15100701280c01c413001e490b07202c8000f84a070000b011142741259030040c0f20040c114a20003540e0141d182c0c1611800c18a07c0d10400600302d02c1a0100600c280b9a0b1041004200000389000103250a08100c80c20f01030104 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 400224856 1250 400223606 400223627
    0x4050d09060f08070909110304050705010908100504060906020d020702090106080106020309040207081209030c12090a090e3c0a1713270b041506051e03011412010903 73
    0x14070f000707121036035840801c03105600503501000f04146022480e104008842c00150300c80ca018000b210300c80341d50380b0011502000705201d400d80b03035027041c0c0c103503150703421150400c0780c100d4014980802c003002e90f42c0b02c030b0080341e20025540ca0b6a5900003a500114202900a2401020b040c140200c0c0e175032505001035201e114421781c003071090350300082c040f04018920056400f80c803621080124a0303d044401b40d43c4d80e03401403003100e403035120305407000c0780c4005c14008071a02c18102a20440b0490301d030a0018002d4504181c6059080c056002100ca480000002d03000c007544c041410070041e04505001000300c1000100140c1c0c5c01c2d049003002601144e244105140d1110080201903030b5200c860400c0091040e1507000300d007000319040070030288072007164240b030062a041541004010841000c1008035100e4102480e0000e001d0b081c02c000d1140a44042d05c018108003404110600b1100c580070680d6000760800440b0106450703001065040c20141c00320300340182e00c02004150642e032000790070031860 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 400226106 1250 400224856 400224887
    0x601032904092603091002090604331d030601050d020d0302070b03090102030f1303020d0f050d0f0e1e0c1c05100509010b0609090a020306041104030b04050d0906 71
    0x6802ea49010891a00b10b807a42d080c180a800342d26684000c01e40d02c0b040d900c01c0c1ca855030349201d28481d40101441900c00c90301d4102c4c0041c0310038901450001040314401c10400480c544000d00c40c2481d11011410207070349140300c3c1580d914a1540314103821503400c101c00380c0010f030203a0300841c0140b10b140c071a00e8100503401c2e0102d5500c03840c182c0c00e1408900c0e060041c0c010820804012060280b80b0405401940c06096503e9036603005586544101ca891100d120014006900115200356010f0060300c0300100703901d403403405914108500344170105171100003030b220392425902c00d1007002d169010f00c1a5802540c00402d18030410804540302030341c400022846610410040c4107200c40a40642c0070f0030502c55018040d140091039000008000746012908040c0c5542805201d41c19480c1c11030440d0801440180000b001d501c03041b004000070b4100901c10343c1c00503a84d25103450301c0c942c601c3c09080110300c5100051814078007460101c0c24400035036400010f20411301c200780401a00320603201c40c140c24 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 400227356 1250 400226106 400226111
    0x3120302131404270c06081501080901020405061303061109130c09050d030201051821161b03030e04270611041203080c03042609040c05030601032904 66
    0x38070000080003440c00d14480c0c1a45030100b6000a400250301c0705804c80540a0b07104c1c1044e01e41c0e140340c1951502401c4500002c41e400c40c5410130041c1d80107a4065800c60415000181401d44510105205038050003c0c40200d9444a80420811881d4040c540340340440f11a441d0030100b2980c00320341c0c0c440c600315458640f0341e110320558140f503225940104c0180710040c40310148002906001e4003c201c00d60310303224007030380c45911944c012134005400e400d01d02800003d000000c1c03010001107450380040c00305409510721100390340d000c42d68840d201425210b001500000b00340ca54a400750400402500c118043e50403c549003180c00390548406502c803103e0882c04402c0b80491818400070152192008901d042c0071402142840b2035941081c2c81c07034800c0e11540311686070b0044103030720344c002101c00400005001c8032440040300b4224a007506108201046401c02e11500001800d072101c3c50060700000c0c4c004010040507607498000c0301d0030000c1c3c0c00000c80b1400e010039004504000e40316081c2c0d00458 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 400228606 1250 400227356 400227389
    0x80105012d0509220b0c0304050d030915020a170c0c0615030312041b1e0b180f12101e090c0306110c1b09090f060106140c0f01060312030213 62
    0x10420721800810590000045c4518030f4070354110407071600203503403d80d0544184e405802000f801391203501c800ca40c01c120402c001200601950000e940403080301c1013000343d6480e05070390509044148900400041c0300302500c94041070310491500f00024070516103c044402c51501c180c40100c211800340b4844803004080340e403981845880460320283c460030760b011040c80020034100ba1038060120000042030340391542c0d91020a40624001c011500c0007005103900c00c0556890007143d80030314240040c142c61a03040000103541e00b01002c2d8050a00d005480311000c442e03000b0507a00910003d0b000c00c1003000041129102c0c0c200c3c0080701d000c02846036907142d820900708403408040e1400110b0341000c8422010620002d044545030421116009101030340c0442c070808c2000c2000b86031183d030a801041b29a05c0e05400b00c940110860b030001e0000020055078400281c00d0000c00d81c400152070010035107524510b01082c161038041142000c040c414440700104c401131540300401c45205000090403207 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 400229856 1250 400228606 400228651
    0x40303031505030d02010e061006140d090b040503130b04030b15031606020703050c1203180607120c0210050c030418152603030c03010303080907080105012d0509 71
    0x429541d000b696041c800c40c104a40403640c1500000468658401910714540f100019030703601c03641d940240000715119445000c400c1209401070132085410a4000c900e004040d01d9404003080140c4051718260000248031041e100d5203000c00d00100240603c0601d0b00b0f01d1034440798170482001e0020341d0030b207001842508a40e46e0403c040780406035500e60070442c0e40e03500d00e001b950300c402a1004442c2d030b0065844026552130211258030050314005c0c0a10314006143c145210703140d0b8240c0380315520180c00d02181c0302096100d104d544119596840d42c00c5c0642c4540100303e001c45881ca8890100041040074614a0101109507812180d1880441e00741040b101e55000c054802c00c0e0040c400d40985150012318110103a214048a0404600e011000880723100c000d0384038407045940c00e426001c00c000420009100d00d0b019540302c241d45090f29801d940b200c82490a4900c282e1041004036900742d001c00d00704000090954440e45a41c0c0280c11851902c00450300d140760003003190060415010880014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 400231106 1250 400229856 400229891
    0x415201203160e032505060a090b070f320d320a030b10030b0f010c1b08010b01020f0c030c012d021006050402070b06062a01090203061b04030303 64
    0x1070400040945d040321510b003010f1408507090710f100c01ea001c00502000502414400c044840c11542a650821101c1c14250707a0300041d4808803040300c0d13004960442c00d003c136000e0201110401e42c180d1444202601d60540c0c13a40007903460350792440380e400542444041c2a0040d040d0b029000314210107001941d07240d44c20b81d074040349440e52030b0346880001401c440e0590340759110100060f0220b034124540d10382020202d0031200c070320819541203000000b02100039802503ca84c07008034410020304482030202208041010160781c06101140c2d156a0850303415030701131046000d1740480000400c01080a0000030356140c1c9201c1c03046041c00000c0070344004540c0e80b000c0007440700350001c41030a01c0d0321030302e0f42c001e40d80c402d020401c0300a54508030300450b45213800d008842040d500100081c02c00e80b510420040294005050b60010401d014005580b250303a07900290880c0000000000e03a413140c80c010305040500c0109a601f00c15400c001100040c0901002d403003e8980503c1d0019036820f609210380e04 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 400232356 1250 400231106 400231127
    0x120201061a070308010803030702061506040b07060e1002130e04030203070209070806130618110405040e10050a0501030b04060b060904110c0d05030907030204090206041520120316 79
    0x22401c9008064030721004075540200540d0b84a81c0d92000d4903a6210001500ca0200780c424100581111002c20522500031013040c5031000b000303154a180c0303a9110051591039110030001c554250311050703028a0301000340301c182907080300f1020561a02d0006080c0002d103600c14021840d5031042c400114081c51302c00c1040ea440d480d0b01504043c0d00341089e5002070460101120824800e1103002c1c1c41e404100c609019a8048070b11806242400d041d1010180c0d01030203000c024500c00a006200000f169982ca005256001c45d4010280130303525011060682981c40085c000c62030103041100420004290b00b945650243c4c01010010b1402c2c080d000050711442510b004d2039000d4103017100000c017518084003e280c240041c03812200071024007842600c0c1800304464000c02c5411420040016003000e800280e4018401000705103415141d042509008401145050004150400000020400d018103001c4041d116006258000003c04000f48500c00200781100300202480c1e20f13a0450f02803a40c1e4036 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 400233606 1250 400232356 400232369
    0x7240519111c06121a01060f0801030f150f02120901060501020c010813240f0b03060c130305010204060503040318050d030e0d1208060406140a05040e070806091c08100312020106 78
    0xc07200d04c41804c0c92803100000c900d0b40060112400f000080513409805100785003145625034415682c6035803151070351082200c0c410348007485298560411021644503a907020701d07802c100161110100712060407013200003004141c40384c0c5849001e00c034582e00015108103644007480d244008ac0d81d00700b2240d4403e4126000107145e0803090540c00d044081e24032070358082a82d00c0c2000c00140500c0c0290344280c4041e00740f0355400d43c200c034011410004086000f003a5804406041041040d601c0c0c0d85c25007240c0c002d502c0701c1c0c0002c00c040140420141d0108900c0d00300c1d0301c42031142c410241010300250f21014200345c0101802103e0142da40d071500d60f107c0390800140c010a1100800d10007890183c11600100c490074411b41c5014004229044401e9500c4100c007001b0b00550515401d28091100400a00d000c019051290140c0064560800c0103240e1050005001812007030340c0b0204800c4208804005940601c0760100402c4020340c41002100b0440c1e0704040c4405c064200d0306030a0b40140300750303080395 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 400234856 1250 400233606 400233629
    0x41e0e0a0c0e06120f1c030b0904030e03030705060103050d11060702030a03091e06200f030a090206160c031506120201030908040b0406050304051204081207240519111c06 75
    0x8001c0b45d0310214510301000707505000140d900d042d10008504039151400c9581d4403001160200d40030070300c41c904c41701c0c55601c060110380c075084a5444242ca810400d0b0b00031140d80d4802c940d17040701c6560142006c038100c541c40f0001d0451f030401a5000e07491b80140b80d104400c2560351a400401d1128000e00b003a8015010828040d0501980c2800c0000d800301045030001d0100c803550a022812821040350740303480d0950b06044c1141c4400d0800400341c5400d620590384040c0600244c410581c0703a2110201451003a0201c017403a900c0c8d40f03040c0a0418241d83c80c01d01c5189032810070403200b9143e58400d00c502c1c0d42441c00151100c02d40ca0800054051600440100fa1000c40e01003612074104004600950081040741c0085040d000040c070103100e14003035001c81d50003604a15503000c0a0b00c014003002032007900014100d441464014070892a0203980d069010340f600140304583c1800341301d018140d04c280d40c1c00d000c00c2d04e42c01080041c6100d00c1034030440d41251310460b1400c6281540c000c030050300071036048 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 400236106 1250 400234856 400234873
    0x7020d0501020c1e12130504050106170606161e1509020a0e04110607060b04020a0f030507030903080c070606050a03050a0c090204030b010b070302010209041e0e0a0c0e0612 76
    0x10303030003034010749443c0b000707840350881509900000d001103100404030f4200a141c0190110340e01c8201d904846000110000c00c810007141c45d81c2c0300c0c00341c0c0c4c1c080d00403503641445801d600d8903203800a020180030300340212000c01ca00303148516404003034281c440d006181207460b682950340301d40c043c14040c10091320001c0d00808880364031382560000000c040c002c68840d074000f900d503016a502c00f501034400804221082081403240d09004c800380c0407560007401c0000300360444d5070204041e684a04601c03400641039003050707100e0719010b2192a030020042c2c9010071036064944d801402040001d0704c00d014400010488000b04040750f0082800b80c07001804260b100c654903c1d00c9030341c50500520803039140003038840c04141745043d80b01707841c2141c0d002401e80b10305900c0c0204084881c4c1c0109015011950204007422050725240240c405800402441c02c5041000200d06004c031410601c01003440d03004510305002040c0b62414403002c0e90100300d0780360060f0f120303030000801c001001e01e403c00031030141015 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 400237356 1250 400236106 400236113
    0xf181b030b01121514090f120406030b0a090c0c021807090608060f0d0b010905160e130605060a0801030c09020c0c04020a0318060207030f080c0703080c160c090f0c080f04030507020d 80
    0x17080c000d13140d20342207a60915024045c45d4450300180c0024690040600081065511940101d040d101e4044c03d01204151581c1091054404000c01180880c0b030102858007141842d80c2c440306604520205020305e0304200b9001040c0140c1d605c580b000708521140824110768450010740a000002003c007850313203120381b504081c4043e00b445502d003110329050020b41c00852200c108440e001c03241d5903400c80030380ca507420003800b48281c03510215403650303a610115a035111300c4010100750080e40c482441c80d602d10300c0d200127900341d660048048140140005207628000180800d82c0140840740980c642c0302e40d49040300100050001c0000111030300900780d0034041a036006240c2e06010307541c0c1c024959000c0c41c042c0d0742404180c0e019a07180d9010000d04010911545415030000d0300140450301c1c00000403404c61141c4c91030b120607141144001410070801c0f1340c5200e60788000100100502410660305009004510000c00910b15042000b0000c3d0415108100b00e8030340035070040c98500300507610305 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 400238606 1250 400237356 400237391
    0x110406020105090d030204060801170304170f0d050f0a0309061401120605060f1c06060f060e0a080a02090c3414120a050d0f181b030b011215 62
    0x43d07904496000d0412100780907846402107509a88140e181c103076880e4a481c6035014008844240c40c82540014440803449440f0290403a170403410781001041c00c0114540da0509124010b40c402081c40810807a505400014005456162019060000e440c10b518200320f80501450300e28044400d400c00000700d04440504002c0503d207000d50030400469071408180408107544801040d4080d000701e4620420004100f101c100030740c0300d51404a44d007541e03540c068116021a40008003c0b4619003c030700788030b0030b000001c2401804400020003462550f5000b04511510203042d55644080c0018091608040c86c2080c50159a0800c520700b2f052600c0582c4514103048010101c4800714111000c90000b50002942e00b51130344450340c004e240c41e0f8802001c3e51150f010768001c51030142c8071030500c1801811445908120a04000744004064007441c1070849000c1004818040c1408a074040c0007051551078a135045d1380d450701740a401f01d401410400b480c01c419506183d030050401c0f014445801c080b1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 400239856 1250 400238606 400238611
    0x1050109150f0302060d021b06040b0601030e160b0c19060207021804020f04020307030902090a020c0f1b0105070f0f0f020102010b0f090a09020f1f080c2b110406020105 74
    0x4052280840d51240c0c1c88140c40c02ea10b03c00070754042400c3c010f070394803090b01d80d0007010302c0c10140e4100b0307100d141d0280c2107038241003040700c050701c0c81d43d414402c0041d2543c060144040000480b006000405101040d00401007128041e44883b881d012a90721140b51040116162009038a41c0c0a00086054500704020b540302260072402051141031018880c03545404007805681d0040080035624a000d0502c0000d40004011034101600c0300d50190141e15290038440c002e41c02000c000d170ba140c1d03224214505e05000040d10001e20b90201124811014440f555800c0813682481d209683ea003940c2000d05038405040000f90003429806860030030400f8a048644205100380c000f441019541e600700040d03004201c01003500301c04040006a9042c600743d018104541c4014003100200d1040d82c0402c1718841d003542c2000b2030310304c4541c0d00c2d1000e40e00841d4080d407008054030f04074603210a015000800400044959501e5021000f00c0c5000300e440c0d802a4214100c81e90310640c580399500c50003800390609 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 400241106 1250 400239856 400239881
    0x10c020a1701150e16050304020f040506032107050712030f0f1404060e030f06010f03020910030f0c031b050105120a0f020c07050f0f030304051c0f03081806010812070206090301050109 81
    0x201c1d1110302d03d0150007030364800d0327400404555840c2c42d09400d10016010090a00341e05008405400d0188111403115503151060140703190b40b202d1851401d28944000707908000d503966039500d18803000039442031b4101840c06040c9016030b902c0345c50520075a201a8103200ba05070303055001c603000c24440c0c1d02c080320380c8038040102c0440e41203110390107601d61985828011140400302180040c400340c00c2c02c185041e000a00c0a200200391640c9840e5180855051001200c00d220407034020001c3c0451341e041e0200e03103c0801d520808591400340081c00511600842d401c913503e0b0f0000140c4400710703d0307000450380c000c0b0b000103650714151100d0603034a40c0e0381801707464840c4986000d566007908124a44030b440c1c0401400075880c06041c40100302c0d00400760000441c2030315250307200d0000103041e01c5050b00307201d1198030341d02c40500740481c6618480864203440c4009500c003070010442c00c0c10014141c00801c1c40050019940d03041400070072043d100310307a8a5a0950b00b04800000c070200c00d90300c11802e4524 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 400242356 1250 400241106 400241131
    0xc01090236010501120903140a050301030c0902040503030d0c11060408040603060e01031109092a010f080915060a050a080c030c030a0321090605070c02030c010c020a1701150e 77
    0x1200c000710081c54100780241070000344103246102292100340d01842c0d055000e030408a500031518080384005503c4488080002100880104104101c145880b8094940a00103604103814540401e54a004000f05841082e403500400e04110b406070340781042200f403a909a51141c03510b400c00a680e83d000c3d2066000083c40c1800014008050710030440c181c03075010784071082d503990140c1003042804024007a107050340540460002c1c1d11032803000540c0c22000b1503103400400b9200000242c400708444e0b03180404d02c03c00004000b06030304042a5001d450040341012915510340001044914078640c0000f500601ea0304004101a9000030744102c0000046044500c416070307080c1459256682200c000300820302210802120f200c1c41c04500c609401c075004000740d120701d251150401d8803016078103100481d204299040960409006000d08803900b801c00c0b1381e4040300c9a000c24103031002c0d4420324501c10f0680c0250b0442403401e4110451803404120b1141c05292511415060300e2800c5d214201600c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 400243606 1250 400242356 400242439
    0x20606040614061b0d2a020603060415050310060503070b0c0318040915020d0605150d02090d0b070807020f010603030e012d0905010e0f0d080c010902 66
    0x3510740a00300039918071200c2082603180040a009080d0400c0140703010f48403c2a404030902c070400c001d1030204086590350318203c605100c042e04401c0110100c0c1050710a404480030303026864010403039030811703000d5400141e070b01c1300b180c0c0c1c0150741e03a01e942003994503014403091000c3c2150140c00000a40e03c0031410740d4502983d0344078404043c0304110606561341c1017840035404c3c4030140314070303c003642d42c000d003011030b026031a50741d650501e9107211508090250302096800504a107407140304083d100c16200032101844135100c9a03114029010041001c540000381d071030240d180c4600c40740e41140d01c50203803516405c209002404d00f51088920b0001446011140030b80150140100c0d000c0702d4041d141c0503410907060703004460140030003100c6684104030030307150f8290006a440062070046a541c411200b142060300041c505201c0310212840713203056401458940c1d84100c00c805009a00111056403403408044160141c0b01011005c0d5200c01102c0e1150a4200c03890381d0602d0000d0150740c010350b00d1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 400244856 1250 400243606 400243609
    0x90503010501061725080405010b0d120f09050307050402090d020d080304021f0e1c1211010b0301020408100b21031c14040b10030b0c0408010c0c082a010903020a03020606 75
    0x819002d003038940d0300045c140c100a1805001c0107a0010f000e64004070702a91040301185e000c01e80d19034121a920b40c0c00100700c044682c00445810752480f14a4503112030361030302000a655403130a018183c81f0b198006401505595118141c81a0030340c0a4100039416030715081c0041240c10881d03051f8002c1d8402d040c1509000c03140c02c60052444501e884154481c44030105002c0c0d00000d43c4a0304101c0c288980d80e0b02c0118900210b881820005503461030312034540520f2050940b40500d9149009070700600050110080100c1c01029610a01500150a1804070000390354603200400384103409181518695002402000400512441c49071035600311810f018100308a032002c220a00700203111030081000102901d8030b854011407040e4104040d603442c5c2c1c135108881e000c1540c911256503000901007020b80020b0007034002c442142e08181002c0c2e03000f40c503080c141d48602541031042440d42c2e1002001c60445070b02500106400400802101010f8600655600503400341640035105107000540c40303 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 400246106 1250 400244856 400244881
    0xc01030b0102030f070f030507020616030e0a08060c09060403020a061d09041208040809040e011406060705030307050a0c240501050303090d061104120f030f0201021204030f0905030105010617 84
    0x4a403502d0030741301d03d00100e941b01c00d6883c0b04014011010804200400300150303980c40c020f400c2480352f925018122000300e141c040e2100340c100120320300804034038a017000a00d0300400d2483d84003001c100b81540e60300c481400140148115000254840311402e0b02040c0142d120750000c10040c1070310b004011410b00d000c00c00424031411a001411100c44180080c411482200902d070010310400245050031200d500245c1034906103104810182e41d202c203d81c9820846040c0300b50000c000743c8001d0710301011034903a6501c0e031100074221000c2c031200154203a289407050460105c15904980303515004803100c0c040c044901003401945603218202000811245004002c5808440000301640c80210041d500c0f44050710031001c50f8001c091080c000000c821442c46079510300188242d0110502071414a8003504040e4040034510447e071061203000d07d10b0b03080c1110160001d0700f50408000c6172040e403404480054098006a82550030300c0b000154803a0060b91920b0000b054245400060792000710b103401 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 400247356 1250 400246106 400246117
    0x140127060c0201090f06241d0f0c1e040509010914060a080304061d0406031208070201050708150d1a070f0c080d02031e130c0e061f021006080c01030b010203 69
    0x60100070320680000a074096020304030210360140034400c038920322813584005807c03a52052464000000c4039840c00042043c0159103d1720b005400c06490401560740c40340c0e07010300c6d07900e584c034180c001e200102008022801e960041c500202403111542e100c5c2c280d000602101c03c850701c0e12442c04c03000f08980d0b103410400c01c0e003656020001141018a810000c813805940f03500c0865100328540106407090302d881c0968000746000d80c003284403821000c4001800c4c60402802c81046924003000d014540d5030100c3c1982d080034249900c0304101c2400c0f40000ca0078031111f100100302c0c24000750140c0100c1c4c00c13145040c0c440c1b002071701c075200070910011040e90341c00364605000303001220800c20081c5042c10fa13409180c100742018511b5883ea8401071034414403500c00d072607400710014080813032410090514120f801030900c440c90360030b0342c0c2056408241e052019030720b01d156049020303800d483c0f054401c01110303200d6480c0080601505075540000f41d1600c1d1107c00a50009003403c0074140c03994000001ca42 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 400248606 1250 400247356 400247363
    0x3010b1e0d0606030b060a0212090406180c020606060c0c13021b0c150a140705030708070302010218040c0c02010807020f16030c090203090307080c03070b180c030118140127060c020109 81
    0x8852700340180090355035220020440c0e00513900c01d008280d0a41d000b4411140e40039000300003ca1400c03040000c0e180c85001403505200c0ca204119640c0c002c10302003030015400c14159107501d64814111980b43c007a000f402600c4824018641100c410f864000581c980e030080c0a8039034102041d40410401542e00c0b41c0440c580105855507e000c200f8603000c0002c03e4140d028405503424030340b0541c2c07a410250b001900680c0181e40100d50013000c100b155083c3c2007110700031a41000143c50006000c0d201003140500a414003c3c05d20015200074002d01c095045413a00380203407440c1030f1052501c5420b51003103020070750380ca04e5140c901052140051080b60301600c1d502004504200c81541c412006520015142c441c1d8007042c0003190004051008003800b4030041d8002e03403109961003000070300c0e0000366025035210b60706180b80a14150307030340c0c82c0300d4455a802c0a00c07420b484d4401c1d80a5405814890300f040c0248980002d0703104407980c00a00400418804c072401e001d40c07000c10310100d09846c507445016 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 400249856 1250 400248606 400248613
    0xe040602032a16050c040213061206050906090403230403060e0f061f090c09080f060103030f0e041413150e03030106030930020d1403010b1e0d0606030b060a02 70
    0x40074403e41d8032402e40e5007203102d8021180c0740340500001c07500380d800003c10b00c00c03240c02a10b01488203640115401f803002d01080b40402400e45040001000c0c00e0010705001c0c0601003200100e81418418207110054607224004640328050402c648445680300e807000b501d00324a0401c419011130300109443c10803074244c400400f40e81e00e1303840b51100120300c5100e40800c01e0600c580c1c0000c2011142c06089480ba1143d1107540c1c071640b07401102418801c584d0554402034100500500003e82c001d46010040c10007450f001100485860124008010400d0000f1300303540d092042260682140c45404101d074400c41503030303114410001d05003059400340505840b440d0018001800600e200e079000000881c00340326480010350510b22400d80a984100c1c96690840511b2180c00c07050b5010854038031b440080385808481411100034401e45030006001d0440d81c3c1c1c0c0c1c0007600103041e403408413181741003448800c401c5664207903411456004110b2840707031201190070010000c00714601101900e80302c05194018 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 400251106 1250 400249856 400249867
    0x718111305060918040b040201090501051c020903070e0a020304030908070f050f0f040903020a120509030c040207081207090911070803070804030315030614010905060112150e040602032a 82
    0x8011881d0043d500c69a04040c5812100c06400d5107144841d000c0c074040d8881e01d83d10f08040c0001407580b400c541140e030500ca410001503a094083c1400218400c200e0000140c85d11a8000000e00303000007540550015003000c005c1c4110803269a0096008a1203a101c800209980c0c03a4040e8480b5050711640c069145503103410811400c081c0f64195409200038070f1340b1404882c4000103801c50700308a00075001039004941c1c2e042004030000e00b04211554071305046081500203000a03a03102042060b90f070081d80c020030b111303003045007540a9507500100010340c0002403400381d030b0090200000e03110300b20444e03003440d41000360a90104c08032044150803c507083e1a40da21000241c984603000f920840401d6510360030009806515071016015500c2600c0100e65401c80c84812940600103030040e000292a00003408a6682c02618180141102440208410030f42c000380e84201981580909201c0103100100010000654000e51156215007402c40507072804116200c8a1070240d5074000d683d00c001c001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 400252356 1250 400251106 400251109
    0x1b010908030a080c0f120601020111130302060706060305010204231905091503030d09060e061303110c0a0324060e15060d0906050105030f0d05031b07050718111305 72
    0x16541e13000f50880811454020500ea48803900d5018002000040840006100b055030b030a014455500d142a0241420b22080b003003110a05503451000a21400c00000c407101000069000840296001030085440d550b581c40c03847d80388285845038101801005101090b1450801400701860030401207803850307507060074140030301c250000c0d00da2000880c01c4044031040d9501007005081c0d1822400e0f0100c0d48109514014060b980e1000c0546180d80100c810041c0c00391415070160501c2d509443d0801001c079100400a042070039140659403c480001404014071034418070000442c145100840146403400b03c5e01c10807100ca078050b031350290b011382003c9403840c1417203900d00e404000010714452918200ba0030900c02c803115480111001c5884a00401c401c2c0b90038400441505400c1004d021a00415000209113110017441411130005100000316240d0b245c10a40703607803075480030844000da41c41d8189180c0c0004091183c03a074450400c140400f42194110a0390b044a9400445902c1d043c10b150 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 400253606 1250 400252356 400252367
    0x16090305031c1503030f030b04051b03071211030f07030b010e0103020a0201020c150f0903040305030702131419050105060f070f03020a0f060501140f1e01140c1b010908030a 76
    0x10181d450f5600022030082c030009041c0214400e0f00c50740c906019100000e41541e40320f030400e911482c5440c0800c030740b1070b402c800403c0f01820072004041c0d1706d56641c40180c5114079144414003c0a281c28a06149010a40700840c01010030400b640203547d030305803048050b1110101c1842c001400c601840758254000d0b00900240038550001604144002100c00d14042d417140d0380c111172a01810901c0300e0a007603d40f589070004441e0000d50b140500f5500c60565a100e1070340000e010754220902c40784c03c000180d002c0750001e000403010f4030840c2400400007209600e44c0b40c0a10407035140c4070002515160881c1169404440e10f4036084c1006a40c1e101c107007007816128800d50039809000440c1c00003400070240c1500c0188100c0000030254180489914607445403590180604602022401a9030700c0030380206041e5481209242c5000d03c01004840c460110081810050800f050f054150903020502c004111404c45080101c803102400442d414000c521944e040394004110540605100d89c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 400254856 1250 400253606 400253647
    0x1050f040f1e081b061903200304020d0f0816080306010e040b0a060311190f0801050d031b0203010b10260c1213120504091404241b081609030503 64
    0x403c05411300b403106c2a11030504222488050003c3d0b5100c41c004845107150b0b50545145280c3c485080c2189030940c00716480050512000c0d1680840c81c1400d0100001c1d0812100541501d001900c0501d07aa45071184540d0030594a42d80803996019000800b03080174072480c05459402880214a18504507060b00144541014126100c004001c0c084030012803542c42192007804e907a80c110901114003009022810680219110300d401c07105400100e60f1200c2c80300702c400302c40a03a0326900740c1188000382c01090504c0020760040211000006100c1d0014401903000c00500c8042480e46c810242d81e24a0540840380b00110311030a114103030b4400300c1d0610340303540804801180000c280e4aa1120310700301d40d990701c0e100000f03500010103000500081c000c2d20b103542d0703103000850b02506082e070310b0300003c4110181d00c80e880003600d01030124005454200030406030410780544440703005010001c2c4030072012644e04100b0f01c5401c60350400c442c807070b80328041140d42010207142072044440d600256400c80 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 400256106 1250 400254856 400254859
    0x1c05030f1c1a04021303200108011d0a020901021c1101060902090d080705071d070e0d05101a09010f03030e01110604061a090703050108010609020a0504031101050f040f1e081b 77
    0x11500f0206c00034800d042500c003a1b034103041c0d001e10f5180001c40010404041600030203500290740410103803018065165a80100b0000350250702c8100c4100100c2c9880c0c0000c1d4240545815512088012500501d0504150102c0f80080c04896200c075a058140d10901d5100c80d0441d0308801d1540100d4418005002140d00c00c1d4160b900c01c0340d50300e08110110040d2460303a00c44044070010f000c0d4044d0000e0b20010031600c20307505024000c007952035441c4c0710702107007940740c10480c0c8420207058005500749035840c2e80075000b0000c82a550b100e030101801480140070442c0410ac1741c0c20348445941c050300f5400b0025110b40010003071540c1c0c0f81c3c0c80c2d0340541500840942483d000383c03a10403055485003542440752000707a400160562405c04901d0035900c0c11f6002e00e00881c810860300c07024a901c48221019a50421600c02e032803030008004842501c81c0440321001000007080100e0380c5000100608100e4000072004801b10440c0c011021002c00c06208031040c5038010074020600501580008183c0e400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 400257356 1250 400256106 400256137
    0xa03020c0d1e0809031506030a0209071101020a0e0f06120109150e09031207080105030a031107030c030b010326160201021002160c0e070504051c05030f1c1a0402 71
    0x70402c2c04840c01050454007224103203004101246941020840384182c90034001c03541c601c90608002003078079034110380c00203400391303100000103244140510014460a80713840002c641c3c90083c050f0080c1400602801d0f80d11420b9540e01242252404506448160104600c1c10078641d280800d403200419502650010380c032002c0c10000340210b00c0203d15845a1683c0014580e591304070328640072039800081030f01c0c0038030080700300520090724009648110700f54181403038490310035044805031412040d90b20041c11450710800210406c6080f07102d050480740b181d0044d041b8000070122900003114940710643d038002007480b442400220710400e42407100e0040c01920481ca42000c07001c1300f0b0360f200d05050082000c3d401c80282c100f01e11030000c44010700302c10038101c681381408240200f1510840c4a098407841074141c6a807250151f4030a000d0920b41e00c0000c50359a6a207107041d80e5916004102c0c071b003807003c40380101c508030000b07540601221600078280c0c0302640c0f200b540401009402c24040344078800c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 400258606 1250 400257356 400257383
    0x4060801170115030803010e060405070e0105090a030b040602190801031208151f2a020907050c0f011418100f020405030f030711010914061606021b0106080a03020c0d 73
    0x1003e0022907805103014a802641d00c0d8144404000300050180900d402070386040100700c0c0b640d80c05032070074070300c003200b46009039440030300c0d60004121104a40019200d8031407403080c4400c02030a40d00034a4134001c6050000310181c0c800300e05a40301c06017444007428160340300b00202c100b1880b0300c5100d64815608240c229090200102180500040c540c3d0040e081c0c400650060006070030054102810840d40c42da1401c1c0010321140212100a1120007806441ea090100f40b005000e441960030449401d422107424640e500d020501800900c0d03403502840b07001d00e0100355a2503110b604544040c08000c01030180500210304040181010a4100c00b80c0d07a0070700001ca450365081c41201c00c108110750003140c8407015820321041089840d5403241c10b0000314181049555030140064198820440c4c0f02500d82d4401f080c02c200540020b40b000b0a06480001c1000300f40503440c0d0355040c03080700c130310033005825100e18a41d5a2200d22010290259201313900d4000117191180c5601c0c94284640c42090508 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 400259856 1250 400258606 400258631
    0x1206020d090309060e0307121b0506030406090605180a120504080706020601030b0f06090106031a040c2024090f0f030d180c0605030403021c050a030e03040608011701 73
    0x101c0d040c081c00c90029078036031820080c01d13a01c003200d0321541748201c1c00b424540c3e03d84501550b00076100d4000030300c00c01400b00c403400e09804580e5503500819010b031401d503aa19041c500240205600c1d50111586071804010600e41060a42000d80d0002803100514018145d03440341008040031031284010810b040001142d0a001803140d0001002a41c006060a504514096100300e6000345540103901e581c4d001c0005941d00c0c00c52141c11504282000a070600000b0b00c004440042900d2071b03900a800d051503416915885801004820103ca80c006845900c541001c1c0d1282c120f100044405102d00360941c103511031091515405c28171080031944620100e140c600d09101d52100d051903550008601c0510742c03038090248802040d040c80300f040000300140d07220001c244050240300c0070030030080f0002c0c04040c000c0000400001901c1c0340c0602020481c0380040866020000180010341805001003050400005840503600d80b0384807051030740e08001d41801c5c4081204e009120320342d2180a021502c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 400261106 1250 400259856 400259861
    0x8100504033c020d080a02030405030f030a090204090807050105070e01020c0f0a03140106080d05040612020a03090512030a0f0203010e361605030627030f2802161206020d 75
    0x1031082c942c019190300105060040c1000d4001003070509483c4c0100204400070300048101c81075000480c864944a4840d5229280241080c0c003000350010b140c1070b07420050042200107002c040348120002d1010303540d0100c0032180e15603500b221701c0c0903a21580038a5418038040310080d042c1c1070098903003902c0c15529180d001008000d42c050300110b940d20301d024054a042400740d58088642c9081107840c141c90450010131030140700e402202141c1e4040783c400c4090b0320a8200700d803040c0e001403c6855001502d00c0d290600e51043c1d44c50317000540317001a50070038040240241e9040340d15610105800303a807400810b18041d003440d07046007006200f00e01560380380d14203d585e0842d012114001072100c0c44000c4c0d03401400301c444da000540f10784e001604001a100c0402c0740204004000141d401003aa010001310b8a180580310801030711a60120318547c00c0700025505141200d40808000011881d030041a0303207440c254106280f2030182e8000c02e02000305849000881c0d2480380344014544032559801d1800c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 400262356 1250 400261106 400261217
    0xb090c0d170d15030521030103060c1b0c062c1017070c0201020c0d23012306090a0905100506030715020309030d020715140d020708040810050403 64
    0xc0380f2030a800078014030a041221144000c600d590016406491b0306ea151814081480000c08454a420340041020320414218500248101e05010030710150314000e9002007241c007a407c0003910000c0c003c1041c0c0122114031084c01072510150000070005414810070b00e4440c00c880381440340400c0200b5001204844c401d208600c541c0d100c4424540c0d61000904020141c02558810b40c0c1005440000c1403004156081e0461003000c0114041c0d88402c0c03032405049042c41d03110348450385861410182c0b102c3c0551031303c1008121038540c0c07d541c07099041c000710303201c44201418030361180c0d100542da6201a80859080b0f28000c0031200d90a0b96600301c449001890300d030901c01a08080303060b070804d0400300003c1c06c01511a0003e010801e01f000d0607946403c010081090421a00c550b200450103480d204680101c0718203a42995911030b9801c0240c2c0f05c0d03005200b80d0718280704080030a850044107100d4180504e90540d40c0c10441584500040f5611b21b0f5900121200200c22640c030b40000802d074440750 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 400263606 1250 400262356 400262381
    0x20603010e040b0105040213060e0a05040e03040603060909050607050f040e0103080a0f08070813140f0106060f030c0807120f09030f030b0a031101140d020406020a0b090c0d170d 78
    0x80d080c6003e190003101402d06034420b900950040c8500c2c1a50000380d9592400c1d2411440c1c40402c2502140005111341403c0c0e00840c0c01900d4175482c91010340c400300041059500c203440a2007002d603122000c0044642030310002e0001d070480c00c080340105200b07000178803803040d100e200700b0b00303050300c46c209410010002e90003140c000c2800165a4107540d04125504c0c58248241003c0c41507140c001d03005400142c0003020107144a103401560010804480003065610078041f017200d4411501c04070090080031703a40621004a0810006080547d01c24000d581d030a07404e039030714210f140e11421410754551340d000214544240d180d80e908150102240305000105003781d59030680780e00403450190840b05040700803801054a810213002141e0600c0c0386c02600e990038600122001d030300f503000c20614000d0440f101682400003030001605540056525441c500072144d05a41d91140f089450369a83c6001c1e00c0c58200307891300e10354404140c6555001da40008181e050b5494a401c1802400c200c908010120 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 400264856 1250 400263606 400263629
    0x31101021c080a1107020904080a0c0812180d02030a0c170304030206041e05070b0904021e07031d09060d06150308031501080103031d040902090a05041209180207020303040302060301 80
    0x101c1c03200144c1c0255501c0d81d2440603120314104084d00801c0c1c3d520790040c000780c00c152002449046082c400d0b1040c02480c1d42201d1301035244c0020319090307003003000c0584008114801c500b0410410141c00b06051225290700e400851400d2140441602d2030040d299003501c0c5d0321003004800400d41640b40c0154841c80c440d90180480b4501890040c40503200c511360000d4502142080200040c4002001401d8844040743c840d15000c030b0500240180c8244980000c1d080c0c10400c0c2c02c0b8145c114500582002d0344640c8809030411555403005000010320a901d560003440440419654100319541131119070045a01150810203214800600003030fa42c0100d4064000008000b41101c1343e01c402d401d014000d103803c09655240d40c40050580320300e9141c00c041c90032500e8003000070740c0d12a070001c001541d006d880075191780341100030725000b800101d6050780c400c1041c5486103205d40c4030700101c20035180d2000900e4000451110410000d4114034400c07a0540310801c00400503940b900c010b14001d1640c0b2048 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 400266106 1250 400264856 400264861
    0x140c060c2a01020709020f0f04030c140306040c050609011404140109171e100c080402030f0a0b1305120d021c060f09020313150501081603020307031101021c08 70
    0x1d00110410050841e0381e903054020000c03034142e81c046100d030110f41e040f107000b585500900e001c0c001c030791290000840340d00000081c00401c02c9004411801120380310031440120707055003c1850345458040720014950040c00c0828045460709801600a00d2070600d043c044c0c0d01d403050800317610761b0701c02e405c903100300c0110b030519008541e0b00203403400140c81512100020f8064405215980c3c40f0100c840c8440311804084011082200300720208494100c402c09209481008001621a12058600340d000380603640031072607080000035411002c079070f10105450095031440ca901d6101e1103040c03006c1b106401180400702224900401405109c01c0c00130005aa80044a54000e0b03040a80c9025111003130a000c0300304403000445030f0701e00484240c00009680c0eaa136100107000d1800520710b00405000032801020181201d960007281070310444811549188282e01c030310661200244402545544420f0040c000224204e100c0c503208a410b0040344c8800e007400e9070080445162119400c0000d141e42c08 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 400267356 1250 400266106 400266133
    0x1704061b030e0c0d080c0712140f0606040c1209080409051b0405130b0301090f0c0b27040b0a0603051b09060d1a0a09020d0506010203031003140c060c 66
    0x100c44003500350804001c20461400b00c543c80c1c04014a496101d07124680d02d14081c000010104e418801042d02551585501c491035001d1118007480c00303849203549040305044d10b460000309070188000b804001c1006541d010100700140c20403082500401c400304114003000f00c07450250300d40c1203204160f9551110700300320408045900003081800d03a4400b00c8550084469000100c03011b603441941c001c0c4820014003e0b80e4041c1c0708000c86a03405d58078201c0740c08140503c101c00710b01c1d124031035202c5010382a5500182882801850000034425a6041c040d902e104d040d6558014452400f030310108810f0741806c0041d0003c4601d0380401e001ca40c0350002c000440041c50b850710301c0d08514503c51420308a608010400c18041c081503034241903680c0403403100d07541104410209816000f05030119580d107070640300c0c01135080448010030702406e02c40410010340c000300a03244510428900e410070036145803a0580c2c51080321820804600640747d4a401c2922204010072007a02d4010040c6500003c0c0f48 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 400268606 1250 400267356 400267391
    0xa150918020f0f09010e061807020a0c0f0f1403010e150a060f06080619090e01020909160c0f081c091e0b011710150602060c0903030d0c170406 63
    0x103070b8840c81141905007110345651101c0005042d00c41940c10149141d4909001c614484121550361203a180c020b410000040c3c1c0c002041000c1d41d104244020006698241c2100c0c0c003407031405554201d050b10001401000c0d116013400c140d90000070004520002e80e403108a040c0072100a900c90708603075080400025802078050640104400307044104900d1400c4c0c03005245400c00341896104040c1c1c05442032503104681341c0b40c0003600322581d0400090300b00605040c000e5201e10304c40c9010b0803c02c000a00c1003840174241c0026400c03291140a40551555104503035000102c0085034100c1061060320100d40800d03000445600a04100191002260900059604a0030410326502d0440c000f003100040d0041103060441304106203a2400758a105541414a044605200e40b001c0c6040d48040b044051030001c0411501c1c240c0980b5403645403524203142d944075515017942c250b40700700203009145490741d100101e5106145482051582c0c4034200082c00e020540b000d9565035112414849c252500b03a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 400269856 1250 400268606 400268629
    0x10302012318031c09150e09070f050d0204030602030609162c06270a0305150c04030f0f03020d020c0904060b0d080c010e190305030a15091802 63
    0xc1562103240c20100c80007004900c01c0c68510010602c2020701d02200340ca04001256280d181d01c501640d58002c00d80d40242015240e2184007161000000303100c0013a401131601ca1146180034001c58180da070f681c0400d58420490f03c526008000c4200b01c0384031140380f04c0c40504095442544090303983e0074103c0c204404454003600c5021250840340d1401d00142c0c0010046407010f2155014400a034608000031560780300b00b4110300e0b0000300006880c03404800609912800d0410000b884401c1c1ca5450700384180d05400c0d0000a00d99802160414004148080c50607400600550458541501d0390349800c049900070108441c0a00011a50010182c05110003005800c69100030b00800224a0004800550260000c0d010607550344108450761030302054400c0307542c2c0281c002596034540150840c0209610251140c6030302907041d0540180c1c802c182d410b140035402d030351060f0641d105d09107000d006208074045e11488840085d030024245144c1d020f00d80034602044401001180140184a500c2034032 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 400271106 1250 400269856 400269887
    0x50d03270320090406050405101107020a0617011e240206010630060b211f3c08010f0608030301170a0206030103061b1d01120b1801030201 61
    0x1215400d14098071003c1045901c1a0850800305080d211828030605080c0c00d60942c41801c3d0400d18107420b02c0305008000c122180c0300b565071042c03041d40c400782141c551029100a546003060600104424003c2c00404005101c5129003542c48a0b40d5840c188003041d41e0000142c031001084501420854041c4101ca004081d60300b040349452518088480c07017284412036100c1c0f55010792204100903149540444098200444410303554141e40040380c100803180e01c440003043c00d1200c0050315030b100419000b1802000150742020f52401c1040c0000c03c204042c2d450b1803901303031070103203c41c416038034000c0c0075608200c0c01d00400055042c0003100d802d68074244800d9049a091280801111200004480c11150740d11034a00c1803445059416051034104c0e04040d50105010001109021180d0710010315404045d0465446e400e1041e0117582d11980c24600f071140188500c224000380d4000d4506a03009130b045040022411548000110b181e0002a12041d0f0650020010710440d41c0200c07803441000314 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 400272356 1250 400271106 400271153
    0x5010b09070801052d040c170f061c021507110a030c090f090f080a02071d070906020a051510090501030515010503030408100f020405060d1a010e0109050d032703 71
    0x8030b0460422000085c4d203c140e000d1a134508807208190722810042010340b503c40ea003602c450900c94601e8503480c0081d500c0a200750600b4501400e0300f0305003206980207503409001c0031403a80240d02d418a6a400c0880e003074440000384020403400703031340e2640303210055403003a102c0740c401c107040c20303040b078100e580350041119030b90320f0700381c1c03034008a41c4003115918419442a40c50f03955800018040303083c100c0d2640038011841c800e00300754114000200e8460f1054116548100003030355101c50803641c4520300c00c40500745400c190380d9440c40207841d540407a4428210840042c450341c0c4c5020010860341c0981c0241d50b2a00f168928564124121100c0e60040108034000c0d4101400c00c6240d540301c4401c4400501015605d14005002e14126010342e401000024101510307450955030100150003004900209001c04801c0d403060341d03000d0951036805440607903074416000d04140a00c81301c118515419070521401d000182c00b0790700d2000c3c2c4040501c170075802ea404078510394035140c0c0e07400d40c1da9142c0e04155072f03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 400273606 1250 400272356 400272409
    0xe06070f0c06020a051201030c030b060402041d060a0503030c0604050105090a0201120b030c1e04050a18021c020a030309080c0d0803160c0209090c120102030903070f05010b0907080105 81
    0x150700c200d1108a4582042c0c0041c0d9400f590541034a042c0701c4c0ca500141401c000c00000000c0c05404044034084078050f0312000c02c02c1d69004104001c0348524015203440080c800442100011206240c50f8403e4010303016403489510358002924680201b2555501da911142c00c01c02003240a014654122010500030300341d640559002a020300751000d0354902d0165502c02c000c4165404000109000c840589600d0400d80e0382d001107030004440e02d0000307000c1c6050002040080d07146102d44040d56140411116595035a94200201440c020040d00d4101d00d050381c010740540d807021402c100841c800d85031480810314003500b582c00c0c00b8100001a01c41c03026108940c021a0161080760341c040300568512100940b40b200990b4202c4180102a412071514410002c13180400514400c000d03c2c1292442202c9550903e55400e0788012031702003955030410b211000c0028407140d69403113154402c5001180d142c000001003644048221071000c0010100c200410190410301f402000703c0e02c0300d2582c0c1e04681d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 400274856 1250 400273606 400273637
    0x40216110d02010e011d0d0807060c09060e010e060f030906060a0e04080a031d06010f0906170a02092d01091409060615070507080f0d0215040813080d030e0607 70
    0x140c600841c16041c40380e1035070117074031b036000b80704510204440040036100715a03840c0c10041c00503040741d50200c80f42840d0400c12600707035000744569030031200d25035280600c40000000450b0303c40d000001441e007000b4140554005a940348019520410b4100014401c500d8038600300100704101d6804840805005d0f000c3c000031136241021221101c0707050401084042e521040b00040405259041c1001cac0074071000454542140b0804c0e00c100c03044024103001d8292554111645503181c00010005903101120407001070802540143e0300814001030322014503001d0740030203441091003148240c5844804014440b515042c46032901c1000c442074140a1854942c61240e42c0d140060040c40c803071f580d901e45003410b00359040200c51010358080261041c480e900c000842e5241000c004804c1c09000d070640040340705100241d1110903104100000c0c1c42c41c1c0703580d00c1d51201c82d8004507800034801155000462a030204000500029126550001d4448901c40e0f12504010340030703141f501001340010f40d40015 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 400276106 1250 400274856 400274867
    0x40b0910030b060f18070f090602061801020c150106090e190e0309060406030603020a0e1006030b04020f0a0210050109050606040b03150d05030a120b090c0a0c02040216110d0201 78
    0x6a81d0310203191241070f100c0d2800214002207495a85501a41c03500403090b4440741c510806004005c6501c82c0a0540152401a1150541344c06601e005a1012000603510782d000801c18000d1600280014038041c0f0300c803591420610650181500543d2280042003039581c03000001005140c1d26400d0f105605004036440304181c55100000304454a41c0a07000881074184201c4040700c40007459107944698801015000d801755110582c030a808010002076450441c20b4030b00d109084004500c6861401c00d18150001e141000c000c2c0c0d00f203503082c0010780c10038408000074900962660000e107210091031032507200392801600f0864801c0d080c036080c0519516101c0680d01a503410030000c80c1c8030340da00a048a016a02054526849152002014188400440140b620000c0b0390343c0c8107150804180c0741ea041d10390038031800b80c1084007000002c25100144014100304e8981c5c3c64401644102034001030160b07040301c05c2411928000c642c180c0c04028020754202c21900c415607140c500c0c0c546a8002900 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 400277356 1250 400276106 400276109
    0x120b090304150509151309050f040503120c0408010c0e03010e0d0e0f040212010e04050609030c0a080d020c07140301140c0403030513090c0201050a0b1903080c070807080c040b0910 79
    0x620030013281000060303440c0040c903564000c02000f01c640307030010f119925040c130030340b403003511107841c94000420800d814003000584a076030008011440d241c1e030910884010325008010501169013400042560b170420f010f1010529880d80c0d9100c40390740f0880825007103a200c0e83c9011800e80c480c504040d0500c0d00304403101180f01c021503641c01c9400303480002c14064400c622044848000002c0003159070341031004101c0c023641c0100d00321240d07a511401025900c0c81082800d00842e84010514400681000010280c84280c8040503003401c171404445464035038a41c01c682c071403003c41040340195080c240300d16564115940100496400d100500100d42e2045000240820100003004100303c80681c00c2e0200078942c0036010030120b0286900203000b0501940c40302c0996081c500f0010035407510100a0708038450780c0084d54501071455503800b82691003136a00c08070f1070299006c0001e011000b840110000c12405e000b0b420100000c80c2007000329001458420302c82c0c215601800480c901c0f2498040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 400278606 1250 400277356 400277399
    0x5250503031e090d02031e0d141c09050303070e030d02070308032202120703030912030f0c110a080a06060b0415120902130b040c090503031210050901120b090304 71
    0x959641c80c0d078012071341440702c0040103501751080044908180c079003042a810030104400564074861800c0ca004c54000d01c03c405a168142c2050001e0144ca0040c41e01c809c100070446a0009030802969582ca411600101c1c0e80c0400b041000300d020401d0b0409021455250721a0b10141141d10f0550340c801400d0702010301541e014000c0d6150005002c2101c014000900e074004018028921401201540d62129804103c0000c1c0070039500240e080780024514001d103605444000c0300f440d01c82c9080711900441203040e198425001e10100050b07c0b00c80440300680740a601034040c082da00c0c10403000785c52065010080081042104001522100090114108483c6000410b030280503841e0b03c0039050252010b540703c00d448a042c18032007050b6104040c0d0303100c01c0c0c8040c48000146001960102602c0c03103855050340040184182502185020607405803041c0070420030b198039080801c00c02c82c0c09802681d40f50001410000500603224a841e1b0301402e094015450a030610100d00d42030280b042d10308 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 400279856 1250 400278606 400278667
    0xb06031507091427150f10030b0f10030b0306060d050d200106091a0f0a06030f020c0303090c031905030904050c12091c0302070b0609060d0525050303 66
    0x1c902c40d50341c0343d828040c00c0c0000ca190a01101d004041690f82101900c1528503000440340c3c045c2207045c10041107a001400509248100b2062401076000e08090040e56a006807800b0340d402c01c81c1e40350074031080b8000da0340c2d40006040000d4810b00d031501c100502038500c503128204921001030000140c500a08003149082400c001d641c0d1040b41e41080005a401030039402c0802c045104120b07a801100000c0c035200c0c05400e04c0b004841400346503915100e101c0d41154440c841400300c030740a070704041d1300300012103801880c1c040700da0295400d6400980754481141c2200c241c00782c95160070000210115480100034001010984d5010769034414028242e01958072100040d4076503405c4810350301001007141e0701000c0352810840b1a03440768404040400d01c1000090043d800521030701c20340e02e10b15441070800d1840e031a400c081000b4400000c0031280c3c411250f14002002400603c1441315034001c14290101d040002507080b444408603420840c044c0e4024040c01c580401010048003082d40004600c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 400281106 1250 400279856 400279889
    0x50f060a021507030b10110d030b0d020d05010c140309030301120c09090309170d050409090c080a0c08060114030a0204091e050714030c0d0b070504120b0603150709 72
    0x1030741000780b40c07410000702d0300080d0100b001d5107406810111042d201100c0b101040443c03d0821350712174603aa4240040c982c861101c800b8054065808440b4414005140012120352540081d070207072440442111165158503c581d03030160440000340c20320380382c01030b42425407821031101c6a90303010510031002e80c6450a032040050041031889240540161241481000c501c1d040180060003180300e070300014101c10250f03a002a4011070701c08005036056444528280c0b40164060191502490555140707c2405c4002101001000403011030340c03169541c181c0340c038507155000e420240168000006c0b2901070342e90648650b03000c500c54400030b40c100d80005076600c003400c01c24070b4121900c0700400118500d08031181803280c001508800c69103043c0c10400b2a4110b2018191903841305005039800012941003c40044c0e080340005501143d0703031900324101030b980c0c026000000030101003a1790505121301404140e04040c0a614550601e2145098003410a400002d00b583c0b1184035a1040c003803041d46 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 400282356 1250 400281106 400281127
    0x708030f030604110406030209210c0918010c08040c091103060105130b0f070b060d2310020d02070b0f0609242107061803120507050f010203090d0306050f06 69
    0x858083c00b061510402c5c0c480c0c0c0c035108040d0095002c0b444017807140c2002c100c034600b03a014060991403a40d544501501c20b414614050204456014101a0724124122001c9038018030903c90262610416950145103003401d0905404200c2680c0100e0103180c100104250301100d01002c403a0000001e2914580d2610200c815584106041d00f200051075000074119117919480c1c2d002d8510280a5140202640c48010410008902e0042c0040144080203061090041c540941c4031102400f042a5001d26140001075422a803054400e100b00580c0030444a0a20400e0251103034845000994190142400f00000349489002025840003000110003500746c540a441304420f0140058481c01c1440216200c0404881d001c03464030031240b0460400140c02e902c2507a11000303031401108529112415503ca045d0700c0ca895080da002440390402540000450402000d103492000070f000581f00d007030840056007006040c100450405050800c144000d9a441c4201031400000b1a52156030700d00c1c408 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 400283606 1250 400282356 400282361
    0x9040327290c01060902090f0612040807021f080106030507021b06090d081804180f11011413061806120209040603020a091406010c030f140408010c020c0a06020708030f030604 77
    0x2d00ba03407095007096000214041c40340c01622070407100b00d4850554000076424070115004101701d0000e80c0c02c01d00040b034045000c2800500701c0074006480c000500d4409080b95140c5840001c0d40c0002500440042110300e45c548540d64208a0038405080c02800907010f0422513402c1e464214130a07800000e00c01350300c1d030340e441603148080d40c4404e40e5074541c0400c078070108200841f40f12060086007401d68942c1d40703034a09801d407021a948000b2a41509165445080029150441c1a414031403044403e4a000080101401c050800031400d02c4010307082140007010003100d41e81039082008840b00c103100c42904600a01140c007403146005031107007074a07000075001d4201c0ea4800b0307400904c80c940c003151000a9802002c2648071703107001d602e060344544c00111105690b115000e4009402d40c0022502c00380700d00320500100e0701400c2000d051644907411542102e03e40b0744040e015a2041c400c20200d410310610000003030140c1d0018106491070403c8117510392040d41c50740448000c00000040850b502ea6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 400284856 1250 400283606 400283617
    0x1c0801050904020f2403011a040302130203040c03080c1b49050f07060c0c09090203010f1a04060b0f0403120320030108012901110c0904032729 63
    0x42200007601d1030b50750175403d00f54000e0281200703da415030000364118029004035001c407507000d01600c614003221038001c4000c0d003000d041101c1421040c00d000001c9074610000e00000c0c0000b00143c0344d440c925021101c0e510001490300790044640c7c51a2030000414107841c0f00c250704d1813440c0001306884581003c1208002e880085a14071214515201802030000c1c0d00466070f9030600840d0b2040303840310029100c010080c48028506080d0220611452480780c20081600384040c0011500b2001700740340c201640c0100240030441c080c002003140c0c00b4982405800d00909281302c8161910211802c1d40115108a01020f0100b2800704288001c2901ca6800604a442c6100034000c00d98a01090508117034000c1c81103c829600344222143d49808800d04002000c460415000e0304900c554011340c1c5079040303107141590601030300000c140652140482144164820765500c1080d101c01401000c440d40e2081d0810000801480140001c28481f2081c0c5405c001040c0103240605211400c00c00620a4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 400286106 1250 400284856 400284889
    0xb0703050436112110060318080c0f15061e330d05010f08011a04050c070605010f0510080405210d1a0a050607050a060b0a0f081c0801050904020f 64
    0x10140d81080210021240c064240940a541740a984402c100c09903540c58440380751088600c04c440c1c001420610040c01d81c0c507003900540e6500d040446286041034440c0d044020100b006d0030030810507141000c608122440c80900000c8138a55603408615440d01c0d0380801400074001206180c0300301707540d02c0e003ca000c100c88070929070b5404801000c0e0b0701415080c032030464020294800803070075650601601440d54450819510491441c4d0300700700203000003402400400d04100b04100c046210b1f8094580600031000b0401d041910349418011205420300710b0204000c90b9009000006101040d04012540c022024401407068182e92011070700c13500c01c1440c0c80616010040446080001c648801d0400032505440580e0f61001440303081d2180c075000030460b420160101000501d954400605104080c01400110fa191029913610070220380048074290300c1100041c101c01c141c0c0e8040a400400c6190a6007103504d0880800c411440281000703105141c8507905150503140c0941c2800f200d5607 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 400287356 1250 400286106 400286137
    0x204020904150602100b10050316050408030c0f070603020a17060112090f060c0f02150903070611030f06010302070206032e17070f08070509040c0b070305043611 71
    0x3e4654001e9694000c1060010b185401c1c100718034014a40501d0b8000400c0c01c94079070502d1951940450740c01c44441f0b04001c028004c050101207a202404c202810a240350003004281c04d1007121140307403502d0744660124013018010401580700c1030b4480714120610080d2a5551000e03154200141c0d260001003510b05641c03032905402d075044c441c92241340d0003100d00907a01080318003801141124040c0b0510905000b50b401541c00b00015040c0c0315400740e000801d6026281844000e1b91980183c0c1c0c00e40c0864100d1004c08003d020805000035072080e082807090030304616181007503020521a020041892842c0b1400715080c8c411400004c1401d8205400c081c1e0a940781a210103045540044600c070a01c1148a9480c010903c04001c22034502555283c50050481c0c0746000200811b20030010000c451146500c0c1002a0b00b501d0b4034090021607211780c0750661902d050082002000590000000d619200c40e4600700881e247e14940d41e4503104540b4010800e04400715981d0190b00c520442204030f040c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 400288606 1250 400287356 400287359
    0x10906110414010207150f0318050a1703150d05100501080d0e0301020f0d0e120a230a0f030b040b060708031e100e10210c05120703020402090415 64
    0x220010010310540b0941542d00941c03407841001242c1e50080c1d40a60000c01c1c0c035008400080c680900281c05c920307265450301040b08079002240030305c40e031100c40085800b940124049010000100c040c0e9160500c614462030440c5011f10b251010700128180d060b0084106000c0e1105200081c000041500c1c043ea6044c00b055079200441c40d55208040b60320b41c00115500069072440c079040c002c880e50070000c070b0740759810808a40c06480c005c1001c02c86130205840b81d01031229078102c10714040c15000f8440d85590035181c4d180254402180e6409400441c130038002c000b5144419082486420080014540040c5446006000c50300500c44115101e40c085408122072041202c0540118450480c40c4107004020010b000c10185105044e20f21300000c640c1480c1c00c1c0003400207a44006d900c40020528156500d5442070646080790401026030501d181d01a0b040052044514540c03004080070794000106500400b1100c0d00d42d62140002481030fa0001a1a541d9a50320340050714134030949a500b58946 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 400289856 1250 400288606 400288631
    0xa06051519080c04020405061b03040e070305073515061209010606050c0a120e0402070f1103300f04231f0305060307031b03170405030a0f0302010906 66
    0x1155600c5801e040c0c1c0f0882030106028100780c001d0b00c0850f0009800306080051900d0320925620b054860000180300600c40050050500320145000ea2455107000515061920000b000010310308040700c410b40f140c611085075440f09110500800712103412298441d155811064600310342e4103c8198001c1007c04d15500d034400d108211801982030380d008004140d902c103020303951401071190200c959040f0980394008501843c21071000729005181070805407000030001002c80c1c1000740b00b942c022048100c1d01c010001c941c01014114002100103080c941c005414102001141c40300a170070148803d119002c85000f114141d541c03c40e48900c07a030f0b49172500c80d41044168a550800f1003c48908500091564201103203c00d080103d43c1030480c2c02034030b400c0015806031101810307c80e0144150300000010858001d62003451542030040308610754a181015968170840c5801014030850030402001295400128800100d500220390740790018a801c05900415122501402907801c080c0c03c032124 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 400291106 1250 400289856 400289899
    0xa0608061009050115090302010c0f0c0902070201080a1506030c050702100201020a0f0c0f0b040201170c03180102040e01060e0d0b070207091112070809100908030709170a060515 78
    0x15182c110b182005184c0ea1820003680c08a5203101400108500150620141d442460802c60041c050071191480440c136595031a1ba0072100c1e07009864455020400804542c3c0c0540c8071904074126007024054440c010010009c0d5528a100c0e217000d041d503460b001c0c480b140c002d070107a50f40c40d5002480542c10516101019010754000c0a142001400a6000703500c0a0b000c0c01a070f0075041c0e040050b00000900e595641c81d1442c0c0043c20036418040e0304008440701c41d9500c0c7d0840d00c101c590106041d01ca0425030030714039038800100038035446640180001c1c04002114499181180d1052510f010034104082c0420603100c15100044e0042a1000800402c2c0750001010000c0301c2013107104004607406240a18564003403031420700110407280001c0341216224081e05d0340c003c0a0b090613a14592980700c1140210f0321042803c8a880501004220720180c01545c5030008110360002d261003d14800e40d565102e124041d001400c0c143c3d10f502064209200000c4210b5480c806050700d0465031080e07000148 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 400292356 1250 400291106 400291109
    0x90b360603091c0f051c09060c020d03060918150b180609010f080606090a1e0f0e010608070312020c0a0608060301050c0c1b0411040609140d02060f030a06080610 71
    0x100000d0000c000f54040c0c8035000c01800314503a41d903120300380141032030f00b8560304074060315803500300e0b0325951594045680340c07140e811003604a400030041c494500c02c026080d20410350190700c89600c3e10055040d6026100020f4158680c42a1703906441a0300901403001042c824100603000207401d9a56401000507020b0356000c0c0000f04d1b8000f403280c0c2c1e90021007001c203c4600400e005504500b01081d402e0500319000d82e080100c00f10702081081000102d210f061444c0600c1442150b01c60792380104540403841030745803000500300240041f0f0300305a503641d610741c4a0f11000b0403010041e202c1d103180520070f101442c2c00050003417038866529654040141801000d403070213440b075440c00000c1445002d000702116031241c4040c0c0549080004440750800d90b1000c2000e20b5006901c40f003a03619040034000051018004c01d44510901c00c0c1843c59000c081c9506010f900d0007101450b0428003d655060141c80301e404e00100c480f80e6070703690000044003400d000c0e03015070300340d20400c414040000d44840382c000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 400293606 1250 400292356 400292383
    0x8060405100c05070605040f06020a091a070b0c0f07080301090f0c0c050d050c010915200a0206130206130303020d0f0c1115120c040303090b36060309 66
    0x20110744041c96114200c0d410000d440e07000c12420843c05001031940c3d005503501c140106040c0e0001c42040e00c4500503a400051400002078100c801480850700c5850303002c1c2208203c084072824a025a91a22899900508402c0080d6000300752006442c0300709003120240c80e0700541043e16075940d02c400341c000d480c0c61071010150601308440c80c0d81c503522940303030b44995a41140c01004400082c49042d903150f4030100c80091507540303410740000403d030160080c81c2d6500d0b540200084c4404101e5081889040090034940003100801c1500c0f5501da0004140f40c00c11041003041031085410710000300c4610800d582080f00d089a08000010f0680110f10390100b510181c481c03045031032140c02e040b01c1010316440300401c10b000c100c50002142c10310301290406204a91040c0385404002c4011340556201113480c04213102d0006000e2080590103c621f20080c6400d10760700d4180768091414010b903402641890b030b200c0c0c0300611074800403407214064a07000e5101420850340c9080601a65880d16294040031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 400294856 1250 400293606 400293613
    0x703080409050123130b060d060e041a010e07050a031d010603150209130e0109050a050c040606050325020c04110403140303040b180109150207150b030703030806150408060405 77
    0x2400c4110852484e119031000052400c01419941c050701c000420014082640050040c404242031440710720507500a459244000c01d82031a140c0b502035480c20103900f051a12101010041080c0b001000b90b40c0d411464905250761500032110044008200210181051490714840e8850030074040d0b100320b0969000e42d50a01095000701030a005a01c00e02c0440c507005600380c5020207491046030b001d205426590400820880c0300b80d10707024603180905805407450740007581121098905440307501700604850038254110725268806c0106035881400c80d05400300c00840008015200f0300580d20f0240b001082007180d80f2421b001074026401c00d00003241c04039038000a2190021002082e0b030b04c51940309034015019955903c2510b1468840e101140e07856403140241c00010718070900003180340f1240d1200603211070560074120031014122100c4881140b80c4014166143ca0100b60072007640d0301800d00c002c2c0ba03111803001c940c5026122401e885da5180c08203021038400701c08111940164010f1049 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 400296106 1250 400294856 400294889
    0x2030f060a0501230318030f1804090201091e08120a020f012c191101030b090f0601050f040b04030303090323030a0b04180b16020f150907030804090501 67
    0x44d02d801206910b030600090288144515115400b0001c581c0701003c00242045e1004c08604985560400080114686030104603280398444984401c1c268140440b4244020400c0d500041e0200500e4011020403811030a100d03440d0540c08020b0034000c0c00e5101c101c884242c00001c10761450b801c12240d080040c0180c0d51010241c00050083c135002202c40c0703440600c0890b10300c1c0c1d16003541d20030704000c030181d008414114058402c1e0700e802301050790040d17940b114031500801c001030840d20004100d501ca0100c0d4010b22620412420f003559010314203081c560b075104140c01030903907180102e5100d0a003002c40054080700f00350741034010140349440798807010203c500b0b03013040c0c5029440112030040007850038030008180d040103030000c00c606040507100080d001034540124036541c039602825a20040800c00380000c69030004451100d500c0c40d8800f620b4140307810456180c070740301e40041c512000c846500100703102c41c074140154401140c0c803075000341e0707a5907592a401e800b034007092040c0340c034007480c1408 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 400297356 1250 400296106 400296109
    0xb0a060f0f050c1e0a0b0103050102040e090120090f040915050f010605030a0b0406031a100b12040803060103060510030e010b01050f07200d060b0423131502030f060a05 74
    0x1602e400803040c0703000c4c010b50012803c4888050b65502d001c8400e501ca03142d1100049010814224041c0d030140001595a500f00840400113030b0028091100c96850424010301d00d46041c0c0441c85042e40034001250388024400014180804041e810f81d40186010001320400119241e40406080d40c03450074000c540c0d40f20fa211034140424031038403021070000c10000d4010320466008110510004100081c41600ca44a280800b41c000c1c2c04202001003060510024000d0000d806004110721513441c0d1070540c0d44010030b6201d080c041c20041452001001050482c1e020341c2000014001c00381c030203e091204010f008010b480c081401d00c3c8907500c0c14612482c80d51003001116030044440314850700c2e11040303030307200c00c0b503001da16074242e440804035400e540040da00d00390052102307401f50001044440c403040c104000c0f64000850102c4824454000701108140102000d50020601e0004e004518081c203081c103407481b0f64124001450310000812043e030341030556050080314195003403064140c4450 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 400298606 1250 400297356 400297367
    0x4050a24052503120c1d041506030506041d1b01020705090612010b03030c070e0c030103020d080c0708102408031b0304030c0b04030b07030605060f0309010b0a060f0f 73
    0x64075400180c021618200c150081c40810000280c4640303002e56130303c2c50704070108044070728030b0410100080e002c50280c075400c2e80003980b00e03901100c1141c0401c103905060b030316140550400d03c00c4005050b183e0001031101d40d56503101e40140d1101101d0900d0700403820403040c0d214040145149441c00800003803003802d51000611038103480001d0000c0d11a40c840c0000c04ca00d12254425090041d1348864071031301951000c0c03016145844040b0b00428481e401c0078041170400700010b056181c05c41080c401000580d0301c5800d41d84c041a00013403c43c1da180d4000300200d051680a03084019144146030780100d40e409181e2002820318009003541d050300c19268103801c10900c1900c1201c1440e80b040c03084500a90b25580d82c500701009080c1104e15160f81c9a440900d00d1075503a100d0400042c0c0070904006104404290340d81c0500c041ca03041001038100340008500740103080340c0d194000d10220001c0c00c80c0c90254825042e1b45401801c0c2a80c059a03190024440711400030b0070000140c0003440c401007640600c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 400299856 1250 400298606 400298617
    0x204140a091b051605010603030e03010c03020906070f020310050f0f010b071502092407030305071b0303050408091201151205070302040504020d020604140a15050a080a0204050a2405 80
    0x205003002c04101590021280b0b50090340b0140e800500c0d00042d00001042417059100441c401d81f5444d9000351401c0400d42115040005034080c036004100031605903443c2d82c04c65901903405001e100c4d0314102d0f07002203403820f4802d0410045041c548010300c0707248a481c00ca007a203d0740c849c0a45041c203a80701c440500b454000e256000313207130701d00341d0b25a00b024480f203030050126100c0c0500701e10a00304003003082d000101c0ca81410074913043d00000f403d109155150060651200300d908200ea51803204602103c2d80b101c2d501006000c055580703003c0f600304040c64046031980c0b200100054800006051014001c003407429004022401103000040c81c24050200110115080320281c0b8100785150280070240c80b00070012a0f10031204031007540103a8030780c005000900100015901c84000303030310520050300c24a40240f082c0710001101d03500032a6100e4212600c104051805000c00c1d110f80c40c8410190041d41c00c8641d11010406000c00c47c00400703113402800d884600859026000742c00320a803450700c00c6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 400301106 1250 400299856 400299881
    0x1020304020f040614090a0b0a1412070b0703030c14032707050112020c0f030a05130e1003231b0103050c040b09010c03020a0803070e12011103061003060302040204140a09 75
    0x200d980d00d980a24002441b03da000030755030804920040c4c6013000480a50103500148500c0c5907201444105082504004841d003299100034580c0c2030514240031000d01800d4002010551500c4003819003612036001c2038240019050303095180e0904507049001403041020764000022800301c444c0510358001011000c031001a102d000b405818a0345c0000650701039008208144107504070700010f42e504000a18009030f0942d241621005020140a9906100d03440400f8480304c80060000041d40400e41c0d404803036000d06140078248200d44044898203102c400d40401e80a800440780854004603413101104009070b0b802c0241c0c3d507403003450708154015070180c0401c44070f040c000801554040c0d00e19a01050090040b180d05901590b50a419680110f61a00014600c0d4141c40c40301e041124048030f401f40c070711000703116500801f80092001d001c0280a14400d20412001000c140e000740d00045c00b55130041c10641d03540342c0303480f840300e54041c442d145503014210406000440140505c03400b4500441e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 400302356 1250 400301106 400301129
    0x2031b10020c1e0604030b07030603200906010804050f0604290112080a022812050711090c0c0f0706020f0d080c0a0e060d0608120c062d0901020304020f0406 69
    0x1034046a04120910f0408043e801200401000c40415030300c0e04a244a07010700d9501185150852a03d10120386034145110700c9640350084405040e6200545640d00403028038058040c1c0e0340d00c1c10302501e0094911003c048500550b8148001d00031000108101c441782c0c0c640140410f084820700b101c00140900c00c503d80e030504250352400081e480780007004440102c1c03048a104e1290440804e038510b6001c0b00900800f8088115082000410107548140d06140d052090403c4501d031903030f0001a13009402248550410400201e00c1c0d00505c0542e1109580e100844580c8504030001070f985122a00500015105129031000030810005141500b580141d403000d516494001e00014180c01c032031301c1802400028000f84015031140d030054615405444001714800d4507128450b03050610f000030026004004004d80c80000b580020269003142028024001700c2504404000384040107228455040c0d001e8402c0c031004002c15000b450046000315270000e200c40300c0c64204011a00701c0d21130440e8100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 400303606 1250 400302356 400302379
    0x702070513052707081203071209061d0a060509030f0703080a180f0b0f0603030703140c0f07080c19050103050601090e090d12051312030902031b10020c 67
    0x25541015400c81d040103c0090042d4503a050907861501943e0405a143c0c02042d04001c84070040220945c4001883c050901d18180818000d1040041130680c06000d526030540d0380c2003050942c0301440d10b03035140c01100c008000e0ba03c0d080751101c0314503405031051070409000c01c01341c2c84007004903051800c1a407000751518032241e40644201d6001082007124554a0800c000702c075102d0040340080fa8420f44010075100907a20f4074441810001d00f03407001d014100c80c01c1203400e880010840e118103416003071921500d2240150045c081c801e5a002488a0050301c2080083ca14001060001d41c3e0319075080e0ba43d800242400d103d0498028882d43c1e1300d140a4a1040040f54043c0c2c0c09280c1005040c5040c04040e902d583c00c010355104c1c140c55101c1507a02c00105004101d80c030840c2c02030402c2c4101c4050005041c02c0e844043c205c07518a0020780201c080ea428803040c18025400709022560150a48028126905820720310381e00304041c05005601d60700b0380c1e440e201d20100350f410080400400100826 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 400304856 1250 400303606 400303639
    0xc02040c0c1b061b0c1d090d0c080d0905070f030b040201020f0313060e030a050a0c062d18030b0f011a0c120a02010608100522110105071109180607020705 68
    0x22800d05a06a485140d1000089a11082032800c0102032001030517021150410f4007241d45002c8c008000c20040000c0301155034001006c0c803007101c03a9945010300100c5ca00240d401c01508043e52039201c4020b40108680000030001c00e0b8044130b2245000343c0070350769500140c0807010b449102e0300702d040003170543d0769200f400540e00860042d44018005000c0b100c40c140035907500303031400d0002403040c0c9480d52110010020650b029017003a035008200c0d03000010600459034040ca42c0043c0c042c0314030910030304d080c450071090f410b0540c98000b142c20100c46400d5040c07682c820101400e003030141803258003500d0f40026199403414222005001f008000300078540140704081c041e40c00440c0b006085540390304000447c40381c1000110140440000300048a04080d0b00181d5101c8805808108090700d8007040d10100e060900440f000302403e0800d695105d88914100000001c030440a941c40b400080511400000516a161b4210700f090222804ea880300313034059903641c900b4130030a0350010a07110968443e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 400306106 1250 400304856 400304897
    0xc04030204090f08070501060519060212220e0601080c18010e010513090509060f011a0a051201030b07031523030c04090813150e0f010c02040c0c1b06 66
    0x82901401025020f61100c0c1d4440c20140e0200e0b000b80c82d188e440f0041444503180090080022800d0310030415582c2d403500c01c0c0a0344400d5070f9071011059000118122810b0852006008842d12031134072030303000581d110740c0f94413030414059a41900040e0403000203031186100400322586006070900e03064071954050011038616080394412410010148642c40c43e808107501c10030042d04003d1400705d0f96182041401c0d103044c900914070b078120041c0302e00400c1402e80b00012a40900303c04078200740d036908080b000f07a92620030160800460f201241c00001030100d00411039020301419a170038850307403100c0c002d484030031440b50058188190211040da412000a503103120541c00000c0e043e108500c1d40e91001a088440302c5206a480b00000607001c01e0003520704c609400903285298100111105624004000d05003524a503030044c5160707100201d4583c0100c288040d232503030040043c04000701c6020000c105140b0007030111140c84402c0803194078050806000300c01c3d15499900c14400c90110000443d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 400307356 1250 400306106 400306121
    0x15010c0f05100f0902180601091509050d030f02010e0a030f120f05090303010e130512030c27010f030b0f06090604080f0a0c06080402130e010605040f0905060105090c04030204 77
    0x382885501c9a09007042454020308a410240d04030020b0000c9040c01130040315940c6d00f118111a030042010005940c0e003007440300b015103120305802c042c0140042000e0352075400640100b64000405038080d420103501c01c019400242c1c031a4000d0140594a003603903075861036001c0f8005c0115000800c0c0010b028850606d03507590340b0b82d401c0046094004404131404503042070381c405d00039400000040c024200504030321508a0f0340c040031110480b070152591921000429092010b50100001081c2d02d0862407041c0c0c1c8030488040301d074082030310081a2078541070b41c29203c9035000c80c9018000080c0309001c1d1040e080c1c030120141130345c42140314800c100080c0ea4044180070b50b11003014003006c101d88004000c13000100000070300601924546040c429440821507100c1c0c001c00c1103445c01c020042e1500c1e00d0719020401c41420116a840034070201d5800750400d6046290811f18084500d2103840341900a00003413070051082d151a86d80350810f12552400840f170b03005400707008202c10001424103034000d01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 400308606 1250 400307356 400307363
    0xc03050307050d021305010e2d180906010302030c0a210f0c0b03010905182d0a0308240306040312140705032512020c0c03070e01090515010c0f 63
    0x500e4500d07459480e43c201c2c0c0000304c0010302007a2600040c00b042d40c200c00071215200044600a4400c81240c061540341e1070742d0101c6002c0c071580d4841006050300e0750740c54840c1d40741580764400a03915161900c90390740c031303001d1009038400e00c00c040391709407141070140329481500d8501c51006104040340b00e1f540308000c900c0304101c40c81c5d84107610b40b1001c1041588008058544100c1442e52075140000820a440300075082441c0650400410310040c02c00090b0300140d100035459110030b08a802d030451a00d5000540302020500440049108141d0300c0000c9a01c54000018080002c0704403000c0d003001107100c01d8000303030907511510128004c207002d0442c1c16030b03c48203400085a5282c0450101c0420101910300f103001c58408014442511220b91460b03201c81503401900041c2240c3c01d50052001e0002464010305070381c002130034900703c00c060002031890f8034054105c0c5c0c0c510381c1c0d80c042079400710424421124214907082c08143c0b0603101c840b0020680c50141c3d03886150005640316070f241d6140c140004c0303 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 400309856 1250 400308606 400308617
    0x604152711030f0d030606030b0901030b04240b040e060112031103130e0103060b0409051f0902090c03090f0a0201050a030203091005100503160f090207150905010207060e030a0c03050307 82
    0x842840e5400c03c14440100a02c0c4090308a82c015000b018050369541c1d0880d005042c00c103103920b180c0703441d82207a6a0449030008075465040d00c817070600d000205105610000401c0d00d0400c2c0382c0403500300d44c0100c41d00c60000d4404108401032006001e8981200780190345d500d004c14100600801d1040002080c410501c4064921f040351008991b801c00c045940691402040d4a0040003481500d1003000e60300071041c0d07400e00c4003a070b2543d00c2d03944500e0a198041510f51201c100c1c4501841d540d8001040d1a40c0609142c00a0820080c00c804540040322030b055584110502d07910184408540c07044c0c0305030706842e054104440300c40254003a4100800001d401c0c401c00a0034201da0010303000301c500858001406a0b0020708140502d401c0101c000020200c0345d00c41078041140b4043d90310303070800320303000d820340183c45441038940103c680c51200070f0b684d82c0e90f090004c10002c0c000d040d8004e001040c4140c0003000020f40140f680e07500da001c0d000c1c1000110b9070011100c8042405000115805440761416 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 400311106 1250 400309856 400309883
    0xc0d0206030a05061906020105010e07080f010b0c2e150e010b0711030a2618060c0309031b030c12150402041e020d150b0a23030906041527 61
    0x1400310b030760a06e9000d0300c0141e440301c0041058002c04582c85400c0b10007482c20b17003020310b4050302c6a000540c06111b8149079400000e8800c034407078401c0c041d0b0400321650380e00d46002c0d03c0f01408035020801c001003086006514146003001e80042c001283d80c101c6080c1090141c40c2c0e8a402445c142a0f0400b000940e0f045040101254040c5e6003131140142c00d509c11010200540050046024a03100715034100815240802c80c1010802d140c10410044190850b4150b03558418a40c0403811340c050400d8154042c032440c80382400c403d0000c50b100c3da1070841582180d0614209504211100789455807507800e541007050b144011741c102e1080c0310b5000340003820100e19401c000016044034600d0107060054030341c0c04a520032900440d805155000d00a915910300e01c103007072280400352031007010105414418224030a0b2100041c1c0d440100c0d84010640c100c03034603403a24081d041c0d29868100c4003120803010120291714004001e1240783c60703500c14a81300741600d151a510310320040c50700540580d080f10b0928038 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 400312356 1250 400311106 400311139
    0x50415051003360512090a170f030c0a03020d0201020313110d0215090316031208091f02040602060703090b01140a0b0a09050a0e0f0a0209011806030501080c0d0206030a0506 76
    0x3c50b60b00100c5040c0e02e1008919003000f80c10066407116603e403001041114442030313a241d158a10940d146807041900d40410907684a20b4207100c40944581c074003010429084000c008034070a12224081d40076a5140020780c2800c07800c0380701c00c40e07000203000c1480f40c0803000700b0280015240ca81c2c602a010400302c12482e00002d90ba02c03c000b004a04100e80081ca403803060409211011101d8945401c1c0c1482a040d65a012101c48045190b0350070441b1540010358805403c100c9078000303512041080c0c41128030038540030043d51040c001d2401510620000c10b0326a07201e0b00c941c001458100c0642a030503400d15002c40c1d031004c6180c000136030000704c50342c0c0072624141c8580148620b440a888000005103007000340b04002020341d10240039900303403c04020343c0e0810300b07203000d0703011410b100d0041c0c1d5914080c00588644445a100b49008007484401007480740d0940d1000381601d000314100e440140e00c4c0410032010141500b0000d40103042071000c2003410b030064102035040807000340300440c144503104 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 400313606 1250 400312356 400312421
    0x908030412030e0a0e0a0b090123060706050f040611120106050a110615030c01140703030b1f09061116035a03020c19090204060306050415051003 64
    0x20410b045e100c40c03140502140100c54455201404004e94030300e0070303640c50103c4122240380d1411600c1c880c01070305081801d0558a05003101e2069a1000e803c00c014201101e18481038901181e003102ca00746001080004d01d09003c007521030740704032646000250380c00d1800c122900d421281003031081c00031152a441e10302c035090054500c034100e451030040201c2d03002c42c1014507094400390814140403c010303a0210780c9003c0021181b54917010306010031000080008a82041006003517002041c0400704c5204615601c940c41008807103c1c0e6035007901c907d80404c0b1403030700c580701d04145440f805141c450810001701e9109403038003502c110301c103088201c410319422001400e0104143c0100d40e09420f071100100000c150a80c40c0c0003583d49070400800c1e5903590f01a6440820110540c400d02e0081d00d07407815629041900c2c40a05a02c800540d03c483c0e803400042c0180000d0302400d44905c0c10070016170110455a00d40e102202c8004000da5080c61009030150300501c5d82d0b40e400a005100140b0100e01e60b000318 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 400314856 1250 400313606 400313609
    0x31d010203100f03031706030a0b04050114150a0e0406060f060c050709020f0301051c120504030c050925020c1008070e0103060b030a180209250908030412030e0a 71
    0x340e6a80b5029584018656140e0007449400502c00710500101e036200d042d180d55201c1c00c3c00c0308507243d107401300028903040306018010f06910000040008020040d000545070018116000d9007170b0310780c8121105d2402140e000290844103590381004142e03541146c850708503000d050005500e40e112500707034034009442d40040e00841c0100051608010007004220018500620214203080c0c1c11040769034030b80700611519110f5401c40001161550112118504655029202844614802c60068055009888107540c880340794800001c542c100864a40e10450b0100116102d2180710034428072400429a4500e0452103136026115040e1034103003103110005032540790b035502c500c0d00c50307801000c600c1c18400242c105400d04804210308180c00b01540e4100702106004540c004c40c2d04894805406040e1000e50b201d00383c10f090200c0914001403040c082001c0f0302081146111169007074540f0120340c0b16040f855030007044104150704254400e508444e01c01d141c004c10001117200014600c0310035 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 400316106 1250 400314856 400314911
    0x21201030f0c06020303010e01181e0f0e150601050c2e0b0103020a020a0809010c0b0c070323030406110f0c07050306090d23120408030702280f020103 66
    0x58180c4001400711002e03a020080c2603a00c001c624540c102144911b8141d01032041805004607000c09083d0364049130801c45030740359400a82d42e20706c80300d5694903015000402c82100c01926021200074a0303000440d8146004d0340d2055038182e280c444c90011189584145030102240c001c0d0a080074440082040001080302a021303901641e00000003903404072041c041e500f505140c410040041c4080c0c01150b4000d82c00e40148080341c40754603980050399400014a07000f86141e45403010801c07501d0286002e0400e0038020341c0c2c0e0480c01c03180b0000f081d01d0311135051403882f205142440090006207841c1c000e06400c8039180c1e0300c5810711103440c0704903c054018141015441d08403580502c107a00302088540c3c0d00c1606207009007090085200098041c0d010002422005250350703607103401c540300c0e03c021140159000407000c01e01e883c050521141030341007079807880014001c0260705020052042d10180c400e2240c0746d2150003003003080d40e03855030100d03030204120306058607141d0004400b40d8003a40008540007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 400317356 1250 400316106 400316123
    0xc0d0f0c090c03050a09030804020d0302100e15010915030605100320041103160e120316030801060905150d0e030a02070f0504020a0e01050c0c06030c04030b060d20010302120103 78
    0xb11840240940b41c000b00000700031444c01034003c0200754080300da03a0300141c060321446141411814201d060070b0890107200d10340e508184440000450010b204200032001c06d44000050b600c641d110003c0d140300b41410b20007206203182c00d001240e000d52000c1e40000c0e140380d5810a607a6699540342c072000c083c0508007000038084086662134189070140c07207860000800300d185103140030807058190041c4000c8207001c00c142242d4402c03040d280c040030441c201400c08c0c1120744074540080c240302c0c42d00300c183c000c5000900c00000001e000340100c0919041d1000141614000f006954581c40c0a4110b03c52402502c0d0f290903100d018084140018001d011030380d400b40c110181409648095000580d000b240510b00c10000b500d40b45500500003545200c0c00d103002d950310807540910500e1302c80002031a07503000000109109005010303070001c00459124200d40035031a40c81408016001c00070b910007030190100c2540c4040c012040d0000207603581d405050045c1003200000081c0d2107203200360000ca0340550f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 400318606 1250 400317356 400317371
    0xb0a050127060c020f0307031502070f050601080718020705030403150906050109060501030e0f0a1211070e060a0605160210091205070618031110141801030e01060302030c0d0f0c09 79
    0x10f00360450317010004240e00401303d540c51640d407100c0446104c3c2d0a506110f0340820302c1001c001d0080e9000c5016a0017008441c403658481009e203440e00350603c03a40340e9451002d800e5004552142c001c0c0c880c41d5030007070042c1d8103013442d68070752505003449002c46803038150f03130350b44040009007141c1f00b07d0340a0200d02c071000501c2c6040c000050101c400c21034081c0241d034444048103d1070b80000a45403102c59100f0003185800008031030035540003807000600d0b1000d004401002c1085107401503250f100310300c225035005446503076140c1640d01e44504241c805564045103261009401c3ca6243d0040085032850447e003032035915600801d42800d44803084849400903481001880d520070074a003841429003500c00c7c4454555503e4041d00d16080b03660380d0007422181d42c1010514010b40382c040361020514429641c0d40722424401c40505800b1500c140405c1c6022076518010905102c0c3d041030b04d501030000d0040090400c01c204c03131501c03040000c452030041225000c00241106000500400c410000441c110 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 400319856 1250 400318606 400318609
    0x5060f091f080c1e07081204060b0f0901030203060a1119020102070b01141c03020c060d0b0102060a02031009020f0c0f0303041e0f02061617070303050a0b0a050127060c02 75
    0x11a40034203c1d04460308188542c1150484110045416202c02d40003680e4545a51030003810030b000e1000c0380d19005800300e0411080c0070070fa4210280c87c0804503020380c00c1551520820054034002c0c0400b85d01540080c0c001500880303194004031541250340361150800d9644680c0340104515030680c000181d401041100401c00c3c0329114601605051000003240008900840e5007030640c070607101f550b0356a1080c0401898020300000c01e0b20680a855030359107000d10080e08010309018081d4500505c540307000124000c03458402e50340900f07207240140c1103d918040710302d40650403080940390791a100708a40040d180c000c01c03200b1800c1c21508059502c82c50541030072070000302003c1200d00340342c50310300706500012110411514220b504441b500d8a81007090400420051003a900401c05400c41244040c645542d0001c0c2403071920907030f02071025550b450740c444143d031805103a80c0c0d08020103200c00e00196002e12b05846144100a04006191055503281d01e5265841c1e8030082c00308010320340074000e6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 400321106 1250 400319856 400319867
    0x2060f0d0f050114130f1407110c0a050409080f030a050106180e0f040f120504080f01200c100f0207110f09040b0603010216140d0f05030105060f091f 66
    0x81c01c8841d03400c000ca903140040030034860944d1400b4a201d814208a081840761a40e4025440d00075a10b01c100040c2c02d1040b91120708203c25a5080c0c082000003140c50f030001030002e1340007420200a88801c00680c40c10003440701a0058003803c440540041c0b01a200b04110440994801c040380e0300c0200b65545031020241200600070010341c0c40d40c190110504c83c40d401d2181003a0010701d2060302d5200d0380d449041086079290f2031800200841c517110080c65406a1010240c416a4814019074884021f41121a802c072903610b800c004100711480d84050b0326a0b041005012003a0002007074620710400950808200d510100c481021140d01240880c1801800c1e2045100c0040c10f45401d0300b000d8104000940903040140001d00c0221060b0005001c1c3d1807c0d01034541c0f80b1072703100d980e10080013685003c9902800204a0f07940e00d12031823410030185407283d40f10380301050315600c0e030300d1840c3d09083c14007405a00c82c0001d62403400042040341e80d0781e11980c6c11444501c1c05003d201e23481c0919860000d00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 400322356 1250 400321106 400321121
    0x9090501152408060a030602160221060103060b0301020702060a0903120801031a0a0213090204090510032001021c050a02060a0c210612150605032d0a02060f0d 70
    0x340340258030721120445000b0380b41c00d00c6500690611001030b0303032010000360b0108032581000b0140781c004983d071801c89005200138401d80b8800c030760400d80025100c0c84194241d2164085060b141d01072801000401c03516444800000800340c0003500c2d040c42034010480c00c0d03104031029000070300b0b400d00c10014010311120308010f10606103807942081d490354503a81509826403200540c0040007002040705001d007581154908002000d855890300c0d80d819154000b50894030454205130b00b000002030400b11001342c94002c0e69404014000e41c0d612030900c0041081030f41940c039040d44903040020740200b201d0032500031504819070b5441e0740c511007004000d007000c078050310810400781425220f110b020740061102c221029071030034583d20418145ca030300000e441c00f9400001c80ea8110036074001404200d0b0b01c81c030701c50105080c052144542d07480515031307035000b08850040d15078240c00c040d110342e54040240001ca20030110456080c06503a40001300140d115585e0340340052170005048145031050f0041a0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 400323606 1250 400322356 400322369
    0x705030303070507120215010f081207031b150f020309190c0621020d0209030f0705010e060706021c1b02010608030a0804140706050702011b020d020f0301060909050115 74
    0x5007581056a0040c1407402400c50080c0b1121001c0e906003241d5108009050850070350040c10210f81d65960300701d104548180c014a00d040c081c410780240c5034818ae000b100e07080740e0702d80d5035010044030340040070740b4240d0950800c0b04c034407505600448401d41f481c00303410b2104000400050740c90501120151a044d03011811141d90051030005c1800701c0d654120b00b20450b41103083c40300480301080d1044260500884108030441c0c030205130400c1001240d4050014400140c0c00c0b2a420081401c0d2180d9882c0bc610071030340001c62003001c81e100f40c1014005170800034490000581440645100160171501c0204454039441d51072885094454503554039591801060000300640b5080207110307910380c825805c0c690240903040003c202001100300d0070492040c00c88055505a42c1c90303030f000404650100105074002264400c000318941c07140360301c1e80011a401419010342e40303030580c288403503640e910000365815540e070640000d4045403401207da02c0c61041000184100503441101c2080407150000b8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 400324856 1250 400323606 400323613
    0x507030b0103140105060c030705190b090303010806060f0a09020c0109020a230607230d0306170d0c0305040b0a050d150e040b251106010602010c021e070b1605070503 73
    0x49400f107001540a03040d520140d0305950b44403420180c1034518420440024a0f51040580c6080400f200710480280140b04003c0f0f0440c9482d0a4501079980c0030a01800a944e040000803403564078040c01a10740181c40030303080039000d035591581007040340c00c910381030354640c3d4555a40608514050602601409640c07501001100c251414140e050ba44030700c0d82070003500002042418441440340c41807612a0345080c1c00002c812203c1000e8032180c454104e02d012906143e00460941a4a5041c00c840d984041c020051944108400c40720100c4000c0c0540c1800020040440d000400d030004202c04003540c2c546550300c2140b004100111600d40c2c2100c0c1e0020300e01c040500507c443e80032425001031700141307800300648031070452840500d015084181120000d04600d248550001040720040b0307c19015a0320307507a62600d0590a07110340c0c0c008200160011a81c0711510035000c040f4002d017500354000c0b2500140c07075216041480d405410344070000083c00390382c4020410104000b4000c0c10096000c0d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 400326106 1250 400324856 400324871
    0x7081e16111204050409060207060603050703210c1b150c0201090509060609090a020c0102030112120e060d0906020d1a19060c1e050d050310082103070c0507090507030b0103 76
    0x18481ea00484c000d46100b161590082002e004081d0140c96985412050030007409075603281040e035030142440101ca016002000c2420751941c02c0c0001d021840032030302d510400e00d041c2e81e210032501c0e10013002012070981c54000400c1841c0e8002003500740c8000c0761640740c444910342c0000750124840e680058402c060420800c40c0700c0e10b4000590711450750941300000ca0b038403130b032108001074011030301400280d41c4080300004220004004040815001d864041910701c0001006c0301c0300c0c00610304068204c41c0802130301ca01c242d41c0e503000407040340c01400010b0509050400c03c10603500c0c2d1051540c2e920000010344001032400c06070750040428903c25000046140c042c0292964001c44e02c080c01d81540340401105040d40f690281c40e000d6172150996046030340d1004083c081e0380050311808140c04a000c0003040d044400034661000f845c00048041c03d600c20035500b18080ea200800040800807240303601400684c080050700040c000569004c111450886130090444d0301c405800b504140c2440306 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 400327356 1250 400326106 400326133
    0x2070503060c0f1e070b060a050306040b060919090804050103240302010c0303060b03040f1707033606080f06041802010305040c12050303010807120b07081e1611 71
    0x85407000303c2050841601d0b6403004009038101381c0c01c0c990042c040c03080042c00d5400c20610800e1507101d410b04441c0101000d88450038140e0350b120450b0014413607403030314010078028a042076990b681f0035800303131000b002e103800703c1300003001e0350350105044030b4083d00132805008070760705405103c964110300490104c3c0c651420b90b004900d10300510019040c840004004018035100b0b8000e0f4018001e14000f09039207090501e45140728142010007519016504040e0034200c0c00c840d021108150b406075960b04004000340545441c141100c0c3c54500110103002c0c40482911260720281d00402450719283c1700d82c5031080800e00202c000038003d0f03118074600001c105208021210451580f81c083c6400a16942c0b1882d16520401c265040050200341489107942001400401981a11084020b07904c046594401c078007445c08a60100900da40000700c00240414440c468059001a1101c4124520100241c0500a160098605000056840b180080c6280d0001500305142d44220000e00861280340d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 400328606 1250 400327356 400327381
    0xb0a0b07171213150203010620070807090e0c0918012d020703110f0a350f070213020406020c0a0510210c03050f0a050f0a020901050c0601090c0207050306 68
    0x70100c0544440c030000480034805103007110403001d0013800045641c1d584810001d0103461007031218880c6c44a01c86803000b0070000210f01d01040742d0300303c0c005020203414102c0740000380c258061080964480c0000342401c550350030248501800d880c1181c9030f910440320a071107082d5900607050130111104650180180d100f100d5800d454030084500068842d151407404545040328405041405c1c0b24421071404046401300b290380015214022004101340d03d207444101c10440c0314042c40603010b601c0034030036000302c0b03a8004110f07c22446403507500d0441c10303600041d80310741e601d0b0260000a81c08181404070580410404c8a543c1c812500c410801d0f14100c000b40050702060000d03805c026110440c400c07840c1144510382c2c011070a400052151400c81c8070000c004000c125400b07440100790001082248940c4e02c9428090480c0f803451034601e03510f07402c040000e54080c000b4141000401c0150000c01c500a22400f400380280d0900490b0480d05408000c0c9003100a0304194801d8000600b406042840d06 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 400329856 1250 400328606 400328611
    0x7031101051603181b090e1504080f04030b07050706060602011407030c1404030501050f0708040c0506030402130f090b01060e06041e05100210051308090f040b0a0b071712 75
    0x3032402240d02c1031504c4181c00d04840d900c0380200485010000c5500d003481c030465580030703100410703010440c84818034149541c40070b4000f0031118410714840410701140749a0001c0c00c0d011714418032203103450742e25688c0c0c0302400300071240800003803c040340341d03420450207004400041c51540b000784496101400509060341002e000c201c2456954001c61030031a010701c0802c0c111000f90910b0544032640c0b41801170203020125103400428403088009a2518000c80c0018011500074240d074001a040005001c0c1e2680094400c0e603000346d0b40654400404502d0180c03141c429900310011079801003900e07107049c000006802842c280864460303000010b86990f001e48007101c3c4007104015811442d0f0b0382d029541041504a640c00c654030003040d0000c980c0004141c19081c510398402c100e6031f03440032100407000c0c0d0b1580d0001d10181d81041042e8061070011081c1c040f560300108006491076150001500302d80d11341d4010440f540020074a102848000884001658111000d462a14517000e01546120800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 400331106 1250 400329856 400329901
    0x90b06030a0f0b0a030615061403070c080405091f151209061b2a080703030b030c030d09080c0604050d0b0a0209030304031a16080610020a020307030303020703110105 73
    0x42d010040101002500904079400d03000d441c00001985904007030000d00340c030440f0350489803081c000c0040c68501c01c02e020719040c1c0c0351040301c03401c5803100700080710680f501280660f18401d061001152a0340d692219074003c000034140e1640480740c4541c031780034400c0d0710380c0456a13203048d00c91070301200d58220040041f414070500c2e0018500301c50349401c00080440c0c1c1b1012911080c51200c4030600358100541607030350401484420764100100704040c02d41ea0300340d40020041c80041c002d40000a010f40c0020304052001400d481c0840f031075101180c908418000404005a8964001c010550082c021000c41980c00e4407101d14040c24000070034103c10720303c01e008015121241c002011500a80e05862460030700809072030380d07075923030741400d60120710131010341c10380d40401c80b000c6035100020500c90100601e20340c84030300c203541d128410419030708152107448082d07001301c10000d40160f07401c1c80004048c6200c0d0300c00507203c0d095405c008050329409001480161314103000e01c2040b44080d40c0c0b10350071205 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 400332356 1250 400331106 400331111
    0x90a060f2c060702010938040b1801030e060f012d0e10032f03010e0a0605060a03060618050105060f04150c02100207080c10271e050406090b06030a 65
    0x1840102c6102c1c550b98004511601c8407101c1f0b561141c0c2c000b4800c0540e4240c030700400000641ca4a00e044c05214610441800d40010400c0e900c111541c01480a00c1c000141800180140740d0010107090407401c0701d081ca00c423210725005000500766070030540c50504e06500c4000390710074208540c0856019501410089031410800503000701c2c42e030041207001d03550144080400c5824010030450340b90b151900c000302240104680d5015060500c190740880105000801310502035468890061202902581e00180e48072008804500325000e610014500c00a91040100c5c00c1d10b480022180107800582c0b180c01c0070844140c0154000b8165000d48a80242140c20150402401d6862489030303100203400c81135042080c0c08198000c1a00402c44904800f51043c421a01041042054841c001000403a84100d2070603010004d280c0c01410500303054240100782e41e281c2918546510b10300025084403ea120300500c42418030b801080000c1c21107503414450b50f072528001070400d00000f400310407000d6 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 400333606 1250 400332356 400332367
    0x80c1503041106040603020909060d0308131e11120a030203270d03030504020f0a08030f0d090506280903050405091003060c020a0b011a0304030f05090a060f2c06 71
    0x1111408101a000240451380d101e035104c6024001c1e402c41c4035682d01c0340014000041490400241e00088964542d850761a95900c1d1401ca08084074100d4081d03c2140d0950203000c6800c0060140e000d01c140240d901e80058200b210410901845c140c071045000e03041058118000f0b0340020990381a20740420244598030b6081c000c660b240790689542e907a1160340d0001500038550103038402e6008134000d4030358001400500c414000c400d01036210b0800107502c2003282520000481c07000d0300d28580d0080c404152420b140d11000d1a09a095820704000480185880000d1b07130480500c0c000d59128900a01000c09140c4002e411400303a88500341c0100d41d50400610320110b0750011a000e554444030402602c0012a0000e5403916816811038010100d14000729070406560451180070303220407a41851a529030382c0451350003079000054400d001e014000c8034950340e1982601000703441c00b981d0345445880d80400003405c900d07280d000c50b0648030501c066200107600d00403076041c02d1030301950b03081c1c1e0300c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 400334856 1250 400333606 400333613
    0x906030b04140a05030d020a0e01020c0a1707180e061501050403030309021c211b0201031806061203080a020306030c0909100501090204091407020c09041a04030f020601080c150304 79
    0x603c02c00301c014014000000d00050400e40e41c0e02800b45d0000c1507455228451001005a81d6480e48100715035205459060820030200c590100c407401d40311070380980b10426900c00121600f0074199860f08801ca464101101c12792204000166010750302941d5141a49400c0001070024840c50002408050300e0f000c0b01030070b64071a46141000c0c150782f84150125094241081001c100103864599851003a424034075040e544075170464805043c2c0c51400c02c003500c0b411790056004059480540c0c000c11409090384012030541e204078002004481c21507040c880c610701d8010845140140207104103441801884010303200018020a0b6400568002405803101090325140810340d4007400f41e0b090404001066000040d0090320803500d0640040c0704980d8054403441d0507810071116a00181e101e420040340c28070f07040c03900c950071034082d2070400d01401c030349485e207625868121025400b04545110307043c0c40a504000e250300500b4800003400121090000050181c807005001040c0c0d620040041000d1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 400336106 1250 400334856 400334863
    0x206070c080a0c0e0106020a170a020f0f0105090606011b061a030d03060f0503060f132108060906030c060f07330c02011e0c0909020a0302130906030b0414 68
    0x250078004212484010689000790041006001d05030340c015558000168860000401b480c1e05136110845440510100c9150021174010510300011440349101355a075600040c02402d811744044000403802c0c0c030342a800c0304e18060024010718100000294844e00c580c10b51613880342c22650001f00410711350810000c440211218011345a814017481d8140711485426600c0319086a200024171201c442c0e41d40b007015113442c022102840240e00000000342408401ca01c186000380c03184150b03980300040701100034844c3e07071400403010218500740d05201485c0b428004e101c1d44584102d0050400440c0080401d2282c02110243c2d0001c03480818081c6c00c2081184d50544100c5c00304900d132000d49800d8000791082c005100340501c0c1030340b42101100000b8030600850341d900e000420040d00d0f003581140b903030b002010344040050401801000c08903103680580010000c9010039980544c139070180c0101d0060090b5107030321610160745002e10410000c0c1160b01200d5000d074001003802890360808114606 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 400337356 1250 400336106 400336109
    0x40902010c0602042310051b0316060203153a020d030f0f020a03021905031b0d020106061b030302160b070302070c05040c090504020c0705060705030c06060a060c0206070c 75
    0x745002040108401c0f000200301e8a090840980c00c030080303031505052001545500714100c0014600f001418040c0e8420001c6400b08a08d07942102d04e030000c2401d4600c0c02d403c10603c11a0020740000c144050f180c05003c52200244040710048031402e1004640c032031001440074504542529112480440841904190342c141d402a2035007046240c9442d0091030700c44003029400100d851f80944482181c4001030342d1100030b80c503800400c00d196081c10521201660143d044420384801c0000220039904080000302d1140480000d200441d41c2c500080c0c203440c1ca5400c9441040f40c4001140700a06140501d0300b01550581001a9030b0004040300c803011810700b82c00034201d4403404084c4108950b260f801840c4850054042400460b103410400c003e07140503d1080001414100040c072041c41d1507030060118000c1081100c4040b0f80d500081038043d0070050342a41c0b19000442d43c6418204180052580f180049a04540f03040c144170014040245901c800303130044001041d14000c20880050000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 400338606 1250 400337356 400337363
    0x109050f0a1e2106112d0f070f030905010201020c03030a050a0219050a080f09030703110c030714040c0f140c1617010608060c16061d151014040902010c 67
    0x90409212080c1c0122600000008850142c80c148940036162140d0381070303c0c400c02c50445400696160000c41c03000c0304100c4c000f890169141005587d54240b0407400603caa14800d03600c0191043c128103000d8108599130313101d141964010000d60710728030008070849a205040610004007611580034280090081280d240301c2e0346603142c50440c8068100c0003904421249549005065440812007464120156801a5154001e02c5880d00190081c11820051001c3d00c0c00c40d00000128400070389090440d41c0856080c81140080b20903506042c011002e42c002241080c41c510002000005c6c03a1116070b20311070500c8038022070300d418080c1040c0a10680d0450114400d0134164560b4036118001d0303200d44041d0402d40ca0070030000354006002c590303540700d000030710080b50a202010326500d1881005041c06c0341e825070384032032100f403403107400c00b4600401c3c00c06801001e20704248099030000ca40301030000c0c1d55030141410200203e2410a1003901032480640c0c0100c2c0510705031005031007280c00b803600103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 400339856 1250 400338606 400338629
    0xe0f04090f1a01080c01050910050d0e0601090b13020a14070507080706030b010314012d0b0309060702100504051c0e03010518010f0203060d020906010c0b04110109050f0a1e 76
    0x1080b90740c0d851001c15050b10b041d482519448561440155000e209882086410800d0829052559402000605041da0200c0004200c24071410000f6007000400d8006116065590129000c281008816265108401201180b40c0070b150040600610200d0001700b00ca6800001d400301009000d1002070300030001e00c170848a501d0f0300d0303e0700540901405041280060714224100380f480d120034006a0403640149540c05421074072514112400c046492505400c2c0c8030b03480c0c0001c05015042c000c600c150b4041010b04200e090407903000741404680860699400e05000a00010035000b14150b5000c880d220305403002041d030b0020540c2d41480822640e64194a840d04119484400c00c0300441e0500c0303100020058039640080520803404161401c581100501076031070700504000211a0b004041410b11120b4819107035642e0382d200504640032229900c1c000c40802c081d5070005405000780100310349045610080a000c188100b015101e5203151256040c0c1c0e141040b0315840310b0b8005070200f1840b2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 400341106 1250 400339856 400339883
    0x4060b03092a0d03140403050109140a0321020903070306050402010320030a02070f021c030f0504081002090109030209130515090607030506221e06060c0303020306150301080d020705010e0f04090f 86
    0x10074020040c40c00141c80e0040032f03003000c981d500000318080c10070a80c16210b030701e007865000c0b0301c5082c020742134542c1d80c41c040d500b08001040c598003006a20000c42c401c05000c10f0501c0c2c03034030004083d200f08000d5a861240074103100080032650f0710617aa8450601000181c4500013402d1071740b40a02900c5000e500003150744026000c200d090720080c0b00c100e0103a10398000a6460100c1140c482c440c45c800d62000f50400490a40840030355001411540c00c1450052140c40e22500044e030060805c0c0c0c2e9501081c102c1c08261810414207005144120f8000c0e168481c040c90700310103550326018010400b000305036460300042c40030754070440004c03000a500d2803214518040b4181660080401a8078450701503e0000252242c50240c01920305581e0030703554020250596940903000780d0400382c100c1d5400082c688260a45107401d1015600130b0032100000e10340c1140595001c0e003406044c0c0c220070304010321510010b020b0b032641c181d5451842410f4400007080b80d410b0030311211040c10003000401d0f80c14205d54 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 400342356 1250 400341106 400341113
    0xd1a041104140f060f0a06111203100305010e030906040302120a1401091a0603190302010204050603130318051c030302090603070e010906320904060b03092a0d03140403 74
    0x200c55214000f5035260b905542c0b6a0010080c0744840000c00d0b6a00600b80c07401070154610510b0800707154a911011240030781104421625150400c07580744c00390351201803040003441003d0155007036004000c2d002d545021108400304030030380f04900001e0b02a2490201c1c0c0068002c04125955030790790040a01d420b2406c180d40e0703d41c00380020380025a4000440c14003d44003102c0c6440c3c00f0b0080301c0040c010800c00e110880310302104d910000e0140c0640d5030034080010640c941c4001184510182c0086180c4805a0b00c0d0107401c921038481250340040d9012014001912007810720f20048420a40c0b20700015160310b0101c000e0b215003520a42c12131800300500030303101d4001d07040c4000b400c0242c032070707c0020b911500d084a80081481e45100111019800d5900c0f2034403e4540081e500080c620741780c0791074409800f04003034403020350014100003400000c001109000b800100400b81c1d2149200b000c2003040d448403e5060400340c0c50a208070b01c034020f0b600c1014082d400309100d01c40700c2805252510b41e00c0c107 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 400343606 1250 400342356 400342391
    0x12100f021809060607060c0216060207090f0507090501110c15030f0f07080c090d080309060718050f0405270a020307060509060d0c26150d1a041104 65
    0x5500302009184424410355440c01074103681c4200b4018165500f48882c54991b40050411900c40405600480b8041754440003540610740181c170498008009103850500700100700d4001e0014100c01d00e141c4401d01c040d060303000282c1d80890f00e09103032011000044042140c180b80740d18500079030004004038011800d04000f40650b1291301c0583e151a80350303542e00c82810118200f03c038088000343d60725000804540f0744c00d016001990001c0d00340b4419484032360355401c0d070394002d46042640d0391109007040702640e40002910b00c0c2240e10026001450718000c00b050000c0c50400102e4402c985400005680361310020058000b603080809205c41c4ac042d0310b4002d5115821184240d0113806404d03000324445002c1c00858107800b50141c0a2850950045d4464000b800440d2240c4200102408020070041808401c10a0500324840190075800c003014800580501901e11900844404042c0008900c482c4403081441c11034450807402562203252044003107240c041102e60140c40c10703605070500304000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 400344856 1250 400343606 400343617
    0x1b0b07050f121801050910050c0418020705010c0207080706050714030301060c060b040b060904051305100c0216030503030f0c0421060506011701090e030706061401090f0602060612100f02 82
    0x5a01925801d4600680c00c0c0c00ea5004841c0c4211b180c1c0100c60007040585c10b136001550181e28070415a0030aa1102248c040da0f40a10f280323070070140d4011840c0c0303050142c00c1c400d005121a040c0000d0480e03e2800000c3c5840d07500a22078001030207400b095001c18042142c600741104c01c04a000d499880d0b031540e4002c1d100070140070041d50311034503000c950855810188581d6a028000602d8981020b81107400c200150000070003081600401703024803000190104107124030355407180404254480710300c80007482c005c90f500c18143c040405c1d010410102d400802229004001c01d039901381d2940e22406141001d2080d580440c800524010401c1d0b0401019071240d20018130402d401d11243c2c490034011500d2545e900c1c816000988001d004100340405a0b00424058042c0c0c01074034140303909525050101c410641c0103110100c6d041910096a40c0e00c100b500c0e000d003816840c00c020b070758100700000755141c0008142d140031310802403400240b00c40410407010708140d40340702800700117291b981003400384d0002c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 400346106 1250 400344856 400344871
    0x21b030418050708063c130b0d03050a2607110307150515040f15061103190c020904120f1b080703090f0609151b0b07050f12 55
    0x40d4000704066a07028000d59005070143e6a4104043d10b0361810001e4203084540016000f0380c070381521050001c240d208049042d0100d840d02c0c80c04500ca43c00f400181101d800701d0b0203505141004003205542c0f961001c016040c1c0500c3e000b80c0702e400161040c0d8120b8001c0010707600d60b40803200e200b002c00800c60200f900c180600e607100c004002c100c01755169217025620004003d510078110049569086500266106800500c401402c051000104003100c400450b400344d56515085041812104194081c005000602d45451a5000e8422150b2240180503241d614140341000ba00303266480f500164118a170018500d004034101442c00c140000c130a1480300010400c140091518a07010712b180c521803840104607940c001c0e00581d1803915540c0800703812030520801c0700010443d00703c142401e030050441a1240740b00d490a01d0b01c500c04071100c5496400811402c2d030150103003001180c1c03582141d250300c116a40e00d551a80001034a05026140400115110106150580b0000000c0c2c13140500790 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 400347356 1250 400346106 400346129
    0x3020a03060b0a170a03030f06090c09031a250c02120a0203010501150f050309120c03030714040b04060f030905060a14011a0405060f22031406100612021b0304 70
    0x203440c1181c0d40c04049180844d43d01d50484110340005c40c2c002d800405444000103c0041c204c0e40f240c541008030742c05a01d4080c0041e5200b2418010020f60b000b4843c400150b0502242c1c003454180010715a08602c4441603170110b10420000120340c1c01100b048030010b600038110380d40d04503a00351a07035031400700c3c1e1010b83c480c0d1708242c00020700c0780c0840104065003586a031504008640d03c04180c401c0e51028211401e18825034440b82021038a01c000340c800d2860710400396a50307040050b0000c01081e030615515080f000f08100401104001c0c03801c43d0304962007400d1108100040030300c103400814490502801d140101d1042101800d1940c3c0912030840d100042000c440e600c2d1829402e910300260701100c1d040d0003c01082c852454140042c1c40c40003a0407014901d0220307540051020b20a80142091160003510428010000c00c131007000101d442170401021140303403010441115251622845090059042e0041c4520100f0b4044076258218040300e80508400998420713aa42d11510038920f1120 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 400348606 1250 400347356 400347359
    0x1b06070c051902090a090c12030f09140a0311040f0504080d0c0c0213050c0708180901080c0112020a050d1103070201050601020601140906060c0d09080c01020703021309020a03020a03060b0a 83
    0x110300b408011a843c0c024104074419964001c000d0001c102004041c3c503101d0310f26900181d8184121800b00c6100c1c401e0342d4403d150606640060900485604101c0c104210f01240398116151244150120f80c0c11a1583c031130307001d6420200c2c0040c9640403805034494106020030041c030070504018070041c11030300d10821012080506c202c8084651040007540074510340440b16000011b40c01c440d8018084030b240d80d02d803040c159240e01c51944840c0c0c407850681a64128502c45d4588442c02d24010001d15005d04400007a00d80000c000302015038244c265954042075007504039118070191080c00202880030400c20a1003003a02c0c3c2c05d83c0044a4200042d07080c84001780b501d51020074a18101c6c1d11611000228108020801c110000c2c000d00407500301c0c80034030910f4101d10f420080a2010106078035601d41660401682d02c0c105204950031905550150000300300607150781210500345042410700080d0170fa0b040c4005006883d941e40041c0d131050704104003000b4440503034050000c001c011215000101e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 400349856 1250 400348606 400348633
    0x507030b011214010e040305220503060c04120605100812032410050717040e0f0709270605040903050301140d2001180f061709060c1b06070c05 63
    0x840e60070f038040000711040b5004211160741440c2e469000f41c072034103000c0c1c24282c1380d1424200d030b070001c80d150288495002604000c20304041c0078050300041d10803003292429003010705554101d0102240100700c140d45100140109250404e110040c1c002c1006551602003401a01c3c0c6140d00f06840d10b62500264001d01c5102071514442e0399062000a401c0030071207034070000305a03110b400000003034501d8246414100c07220002c1200505c041c1882829102407424900c01440e443c0400500242c20721206030007c0c00b40440c02e85491000514a01030825214480082c64000d000c081c0e00044c1c1003070505240c0380c101038100340a54180d500001148442c140050200301c2902c82428000d040e01072601d00300490308101c004d00b414040010704000b41c20081c43c80207903a01641e1580061352480740c164080c003410754400580900c1d402c2a034243e10a41c00c084203010b450341d1001c0c14560f4080303000038074000c440424601030020908944255880d03484c02000250601540481c01c50702c0e40038565044040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 400351106 1250 400349856 400349861
    0x130e010f150308070609061503030210140622060815160e04022505010209040c0306031109040201140406020705011b0b040209090c0a0306090506070804030e0d150507030b0112 77
    0x104244140c00c0c401e0301d1a1604000740d031060307600b40d40c0d550702d40501402040c0700340100c0d40c1c0001e02c1c0564224941c65410001e003001110a91030b80e15600303103032100803280c1c01f80010640151080300e01d0b980b40740d07255a03013084900b80880554491810074000040041005c03855401d10020031500c260b0550b105419480c4481004003580003282400d503507149517040c198050a054408041d00200340b1055140461801c0c0e51000102c0d0145c1d000034200c0c246080074011494007180c541014007000741943d450740c100f5140340c94240c1c0240794031000103082d607114102c60411480711041542c0e0345d075200c000081d11024180125404141c0c0b445076040d060558000a09e8a6900981ca250303060b15141d0802c01b010801422500c0544141e03010740d0190354600c0e03059070085205000024080c412850134a040c8480207001c0001d10582008000200e60030a1071220f1000d0102c0e40050b6459852030441283d4607542d002c04111481c15042240e40c0390180c0c04500580303000d0321034018003070108514206 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 400352356 1250 400351106 400351121
    0x27110a0e09100e181e010b010c08030f040327050a0b0f0d1a040204060201021b15040b060402070f0b19020a1211220f080a110d11130e010f 61
    0xc8040e07400c1c0c1040805109051960000c03807201c0c503512078000d02c2d01940c5c64805101074000b10307840e60035051405401e00740b10751007080f4020b007012801300b2800d483c0e0305020b010081484929170031044c000390415210710840c40d1499000140b0318094000f00016880e10b56072030180c94011f4400000114044002e181030381c2c820003d4648d442d2034440038140c0c04014103104810840480201038400100ea501d0380064401351025500068540b031080d0200c10704402101300c01d10090304030340b0001c140c3e924141003055016401c092542225120040410003d10440101400d50b95180d0240e13001c2012034170606008101400c05d50740302004003001102280310708400e600110f100c0e40f0750340c0c2d0048002d4100840314106089854148000040b00031100e80024150804100040d80c0500075a54686200d20141520303000900d61015950f0b14100d10008641c0894450313a010b1030400100490007050200003100a000b1342d0007031502610303440140448041d9910b4950030011485815000c902c00c080 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 400353606 1250 400352356 400352371
    0xb0411190909030903020306090102220317130b0a0905030f2a010c05070b041a0f0a0509030a061b170606031303050d02070804210c27110a0e09 63
    0xc601500d4042500002e02514400f1414000e501c1400009607509202c1c062041c400b0030009607403004444900c1d148682558000849031020010500100d03112000000841003242c40250350ba08030111032209104459202c2d1403c080002103000b00280d005007140d00f2114140d0403141c50882169410f41c655410760103c40c0c103020303c0207000c14610300c132a90303500340c5c1c0006040c605041c14940d12010b0a10740c264000030344480c030002e42040308481d115011200741103100707102800c05aa0ba403241c01180300b2101c44004002c004180040c050707406100600103d60f00c9902001f010503043d030300045080700c890451011901203c002c07540f20114488003845a54000c08803403030350f51451510300c1c0c801c1d030040d0241c7c101700092040700a040014401091014050140d2076221881c0c11440c032110326480202d441c1e1010002c20010014001c1c0b040f05040c2c816203206a40c82000e012502818111050012101c060074a00c400100e640c51900400c0301d241c0340da6610401003003001c14041034400c1940c0340c1c1b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 400354856 1250 400353606 400353649
    0x61e1404030f1107151103130603051504050f060f04020a050304080f04080712150605061b0c040204030c0801140103050a030e150304050607110111070b0a06120b0411 73
    0x1900003031207110030b401001528100340d00400120441d007803078284d40d60004000001c00c404030385c58060304003601628084111006528094031501d41980e80040f03849410141500c850104842145041e000400d401014004100b249003107200e501001c1e0741922040c0c0600c8d40a1245a014201802192055040d5031a01c07460350b2103503030b03440099500075180b510311164180004100c0031030506c9440028800d0505524802c81c41d42080d00030320f1009400030b0078440c0b80c040100301035100d02c0103941000001040190030b0b0452510518100030422110300c2c1d00c648000380201c20410030a030460117035010f51008110303c01104041c116103000c00c0c00003070a541d0115001c0ca0000b4895500b0f81e140210260009000b00c6488c00e640840b50401d4a0840d1140c000b9410402466800350b40b01000006420007444410030344000e201c018480d408000d042151140c00040c41481c1c203810042c002c3c000a2149000b010071802d1030a03c410b8203860031a41a003111036a501c0501d00203200403014070024604 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 400356106 1250 400354856 400354861
    0x120c090a0b0f07140d0201050a05130b1015020f0f010e1e070504090f110108061c17070305040303170121050f0d030506120307080d0506010c050109061e14 68
    0x1041070b0002d140c1c142c0248010007038000056001841c411319010520001d0030007004484010382550b400800c0b40d202545044100200310b2032410302c0c0b142c051341000c14850140c6a140c20030000f80c1c4107030800e850303c803030b81481010807540c001450030348903149a0070307260003202d0003c03540e00381d0300410054880c682c460b00c03030112801f100041c90000e408004041740d550640e500041400d4529150080d58104c0c1c3c140318020130f004c10801d441034980000d107800e482500c1c00740e002581c5a100b112200c000d81c003403d0905000c0011468140e642c550141d0317002e540342c0c2c00c14500200b49a01c240030071000100c51011103141180c3c11030010f8141c0380714503a10015101884c0200403402e841140079506845600740d40140e4940511041051b1265a640481e00d403800d50180070100048410b0075000358030400560000c00c14840030345000c961814800710303103501c8880c0125460000c0010240440d4a07040c07003d010404180e100c007404041800c000507160f00a448400111481d4450415641000000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 400357356 1250 400356106 400356119
    0x1a180f060705031015030504030801150804110105070209040c0f06020609030a03020a05161406090c010e190308040b0304060b010504080307020d020102070b2209020327070911120c090a 81
    0x10f1a071211040d07012003011a5104d080c08403000380244010080781d038400600080c107502c440d5560150100a10041c451101c1d00c00003490700c800240040c00b506204000d4401582c03081c000c07034525030f030020024081c505290810310088210307842042082034080324000707a407178008605603204000e2600178504000c02034a06a01941c00506039108000c020807000c080d40d81c00e8048084582d0042801c4041244014400313072034110f000d8040313090356108044044460780d10050760b91030307000140c07110404081542950142c0700201d800080c078fc1640450081550520400918030560141030180041003001e001514140b089010780140c3d50420891800503042413400089d02610600c105c9842a0303039140410150b0b004505580111048a903440030000c0d80b4580040c080e0081c403604520313606101c5a88d105079120700c804200c04d2010712510146602c400d108500003044028000d0040c40007585051b00701e903000c1c586002d0403030030385400724614010700002e80700410005480c0c03070f4400b400c001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 400358606 1250 400357356 400357367
    0xa06081305010207060e030d06080102031005060f0d05011502060a110f032802180604060918180f02090f2a09060f0301180203090d08070302071a180f0607 68
    0x903825202076400b00042030002e85a8801e180040603103401964540041100030300a440256006420326030040c81480348117100e0a500c1011508102ca207142e4030800c001c1090708a02441c0b1211030014500800007501288100b0b4801501c0307019400d039451030307803080011000c40d0745100e0110810f250a2003a69441000304e0025604400d103820940142524084242c03a50300d00c014480d25450380200340300141405180352200c96410495603c0d003080e04000d0300400c028180d1061200c0d443c0c0c010100040039010758000c0c0303200d00301e662981c0c0042ca0700d424030184100100408a010b03611080018803d558401c0c0702e00c0c007502001102c0e415407100d9a0180031200c0815440c541003a03810000c4141c641e503664010710f400c198007415152a50701d00303020720b1261201691746404ca20b00404c1000355005011404168070340c3c8070300307000c00180c4551404034020300400e01c000740020a450100d480400350f00380712620488840901201d9801012181900c0d0240a0500d0348150b1254022800090245 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 400359712 1106 400358606 400358641
    0x80102040509040204180605101703120a150e1003050613170a09120b04020901090c0516140607080601020607091d15040e0609010b0a0608 61
    0x600450202d40000344000e110b43c1c0c0d104041d0b036101900c012150640c50b0041c0c0704000620b0000003900d00900d9900540001c90008171203d0042d00d00042110030062030f4040e0458503850b108003100180100141500101406020109107660f03419a001c0c41041049010003200d807442c109141002005454480403031602c506010119001104201c181540705000540e83c001000c0c0c1100c84154a41090074007000300844441030000b1641d00c28040e134000c8420780c8050340d0714500e0500325810a000070010030b600f0700c44404060044130303024040c14000c0d400c0702d0384c5062412809043c03102c115403030303008035400b81b0600050796410811254003500e6070034208010345c180a0706095810304142a400310072a5000081d00c003491110309204503400c09002485941038509a0300d4503840121903c0c0301c2c540c42c180085400d4601152800c0490701e060320f03118a01e85417040514600040c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 400179856 400359712 := by
  have h0 := BRFrame.cov_init 400179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 400179856 ≤ n) (h2 : n < 400359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
