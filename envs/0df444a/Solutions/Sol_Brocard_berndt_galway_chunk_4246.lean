-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4246
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:59:48.31388+00:00
-- url     : https://prove2.me/submissions/da190f75-4048-46a6-99e9-734c05305c66

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 763489208 ≤ n < 763669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 763490458 1250 763489208 763489241
    0x5090303070c1b030f0c030302010b09060a180f05090307200105070201080c070b15040509070509010b09150d050f0901050f18030c01140105040e120f07051f0906 71
    0x5020301c9550019001c06880d0f0040d02116080c0c0302100010341091556101900142c1000385134010400041e00320300c102c2c0d001c2d9000b80a012050303410060407280586c0c11660200b2200030401c00f88218404801d06564101d04c00924401540c03800130a5440442e0515210b41000424404101c2c600040c9018440040580e0545c0da8142001910364421108080d040c09441d00010f03400428150032070300c00d50f50000301e0124a04001301146903903800c484020703125a0602d030024400c000d0005c0c5610444078020170001d00d41e460150640465800020b03000d802032840c038a1008804400c070014100c50250320360004061900b40300b0700000032805030030030304507074184018030600d00000c2c22981d4000013911364010880c03480030000c51451161403400c0354154244016840c2a0b00700c0b104050490710181e605104402c1100e0041d80c4410381045101c6210209102c5001c1b10899640075000980c86801100c504084d100040280f4450341411001000d44540751807003040264041c1c4410000010403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 763491708 1250 763490458 763490461
    0x30c05040308040b0c1e010903081f1e05060c1b0d05060a0b0409060504120e030a0c0e150a0305010609150815090c0a060806030111090d081e0d0f05090303 68
    0x1544841071095100320070b0320301070100c1c545c0d0902605100d1001c00b03105600081c4519141142e04a01a0104480036400b281c50705e00080c00c0759906589107203404800745065407546e0705041240c0c0900c42c048070141a2034043d00070205598031401d00528a252511004080420350081e040f19828001d1b48030034003034000c07000a000058000216190004060800403c1c21103051002c1001055030b0080900828140014403041c407a9120f40f0744662141c569410000113001070900d0fa4480356140d00420045080d00c0800102e00110903841d001030700c4960161300751302c070100002d003007481503002507400da50764620400c201100c6100f45424518058050007101e86407100d0f003600d0780c900100c1c6070340758104140000c1d0704075400c1c840326000000042c01403c034151603031401402400c0c2180c0840c0250f2034034080101c501c9018080e55100c2100404951520b080c99448400030342245988800da4583c243d02e085200c142d000107407000e01e00c0b00f00d00050b45e210700d080b0403042d100c0107014044160004c10 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 763492958 1250 763491708 763491713
    0x30c03120112020d0b041703041401050a0216060b1818060127052814090105040c031712071e0905011d060c010c05070213050c0a030c1b0c06030c050403 67
    0x2c040c2e81d04a070032040314a0560fa40e13041c00341f520340500c1c10071101d9000000c104400c105961810307064010b1554003c026940d40c3c0c00c038140407441019903000114402d03440300d03800240c0540100e041484040c08040714020780c02d40154038070344195080840301c04112001c2d0072504080104500614510b02c160340c001c1c0b2140b04210107100c944a500e030500b40c8540000e440082c18000054002c0d400e005e02c46182d5100034528001004100b0213205040074203000b003100c0117014011240100d40100d4908481c1e442c1d9030303520310894010882c2c072802c00002c1c8441645406203500300303489910262580445084080b00c20314132903802ca0300801c14021105424401b80c0d90046170320070300000f124800c44050003050002440c6002c0c0d084001d41d40d40c20a07200340d1231143c0c01005060514402e0300c20301c07038460645610b001070700c9003122906011142440a801d0292103138000401a12aa00f0204800920b080300303065a250f07200c50075902000007030000c00000e41e051007840e114103003600d413060a090541e0b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 763494208 1250 763492958 763492969
    0x60105040b03151206390306131a0a380408011e060803030403020604060518061f06050f040308130e0129040b07020d030e03030c0312011202 62
    0x5001c1c1062040c804030006080d103607403020460b18040002c0c09034029843c140c80c2c142e65860111a00c806e4805400030342c110300300c02c000408200590814014448515003a01000d454000074502d951010041c408041081c0c183d10520f4040c3c0801c4d80c11180c007011550500400140543c020308007005007034071442c004140d101000c0007849031924000803210130013850380074074017403500644165440e0034607143c20003c855580b0b40014480e020140f0500e035403528402d441e07010441700a005a004003000800040d0345a2041d0340c481c0d2402c0e601042c468645c1622442c1405c02c4078100c2100380b801c4190f8400c40e900321040b07001040c0d285019440c0c040b020416500501842c40700401084022030821400c441030041800540401c000a200d02c1d1394990b0b401e18290001500c040c1000c3c1c60ae6503c00c2040e080d0011102540c1d10f50202502c5d0a1081d402d00003906801d0750b0607020041c60086503d01380c2e9007130006041c800000d000a6840ba005010380044c9118107a00002030070090310b0404c00181c440 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 763495458 1250 763494208 763494217
    0x120604050c070f030e150c0705040b0a06020a11060403062f03150d170c0304090f0b060a20031819060c02010f02010e01150806162c060a0801051503060105 68
    0x140c41c5c2140c1080300301e004116030b104054106800b40c2008900c651255000154445c1112401c44003804951192402d010f28800c043c020400140c201c0309003100440c103050300c02d0030400e2002e8006450950780c2d440c2c1c441144d0044a1403002164a180001225803101c02480a00c025042c022859401c040d45420841c0482000260059041484e80b00074400c0501504105511041400c0d0340c40000e08a06612a0b01c54080d01040c1450040b107000c000c41544100c1c1c12082e400f4002e145003650012050300d4400981013882c0460307049403181d81c0c01c075800f403000e42402c03420386030302500c0030210721708114010f00d08540100f1100013803e41000f500c1d90146a100e0f0a540a0804a000c044161801c03405003515400b045600c0d824a90803840c0700202e030310341200700c6042006070380c02502c1d1301e2042071288802451040005546140d070070b44500342d00e0f5040c40303201d48080fa804026442140454115082041508040740d0602c00401003402d00c04440541e0106004e40180340d85403403000603169015 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 763496708 1250 763495458 763495463
    0x108060a270305070f11010207170c01031a10050a39080c0f0703141908210a06291204022803060605030c01170a020f120604050c070f 59
    0x3000407a41e8240343c007074030840b4500d40d00050024128012414010704105644601d213006102d992800074034810f42c85036551034820104090454680c5500045018122202c0e9104440d00304803d002d0340350780e41c00000e0410781c015447e2242c648030050000b4218100c00d05e0444003901052100183e4101600001c1032980e5030f07440d0f00c1941244a083c103018a0260180104151142d00509a041d240018011041340d22071882d1162405000003003d4403034186141e8000f183c0707200c4003182d000803190805800c2c80300d10b110307840110703a100f03500d12402c3d05d9080c0ca038071020540e2a1800d00040410704444000503041c00003aa210299510651416100d511610080b5141c49004a011981c40c1402011072184044a102010f018100100d000f03034118403046880c0b80c64032030009628100400c46c40c1031840161142c1032104540c1c1560741c070508004155603440e9500300300e400008080c14016061811280884403240c0c6003d0062104030703000a000c080003030b40700317105040c006600742c601c407002c465 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 763497958 1250 763496708 763496771
    0x10606050a0801092309060a050a0c020c4b191a09130b040f2c15040503180d0809060a0201060b0f090f060c07032015030108060a 57
    0x5032403040407011400c00645c4907010f24003c203000307030410005001405078107044020001500c0b188007040403202d0038540a80035030040b07074964510703240443c0c0e014145104908400040301c807052007000301d8940c0010b2902c4c405842e604201041c8049410304624040079190320524040001c21140306003840e1003401c4481c100b00c01c003948103000707083c1520320048014001d140c044014000e00c03009865076209150040d0f281103102410b400785809494484003d42d0316695805040180782d004100340d910130110b0610440c40715170079201100e41030510982c01000a1030b00c5107200705401c0070011308052154443e04480d52071202080e011021500c034164110b44541da81e0324442c4090b03001d881158880340c0c01d5900400c0d891590f5207464000e110341d100858040c4100342c54582040294014021030224503130100310203000040901282c4040e603242803410107480020070740003071f8240b178080c91141c030104004401041040810880603070070216119083c00305080c08610780761034039540c011011062 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 763499208 1250 763497958 763497971
    0x1e061605090a090212091501120615061806020601060e01051818061c0f0209100b0309030706270605060d06050a0c0e010f020c04150b03040b0603010606050a080109 72
    0x128025001c6416001e0301034111042950344880b40c0b0000d4000150304260b00b402c00c00041e00522020419103000e61225405443d16424012542c2c1c54044140089440c1540c0b40c10006000345000f0920000382819502ca00c19182c000802045019481d40201c0c155444000140412900214a21480034080c03078262307203c03510024101d94010712424065040140a1020b4200901007450203100300b80a80d025130084420300360300185000c01410140c2040203260800005262081441e0340040d1165414a840c90301e4000d02c030880d40c030560340081039620004031001009400d01451103285020494020300700343c40c02801d000d10941840c001c12641d030304d00c0024495a101090704454030b0b0000e00401640c030385000098010040d0300410340100e568120b452415600c034201c004094810359010b030503070b0451403080c0000340003c0c5000340e807120410b02012a00c8107a410203544914090480303070740941403603c03c2c1030031189290402c004000e010030040e441150440e0a0382c0c11500c40c0c901c0010780 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 763500458 1250 763499208 763499251
    0x4150f090905070f020c03120301090b0303091f0f0e030607030e0f0109150b1012090609120c02210d05160f080408060606090a032303040909051e06 65
    0x188806078001c0d00d1203030b1030203003800201da900c51502d04c500440b42c0c00701c5000c1486042007590300e00381c40c00902100c0e102080107104412a82d0462a1210806000c49061050000003d6211032105019440306400489907800c615400440b500c1101100d003803a810440c0e07854040388c0c84032001481d4205060325100010580002000580d5000304860b0003004125918600807002d000c46080d0b1010241c28115882d1251919101003058183c0c561626108010107142e96005440c580c1402d40d80303590765000c50701c085211860942c005400390f686945240c4094410400d82030205040c07409541d42d80c02e07007461000340020300d000d20a01d0134101180c41c2c0140050028401c04a840d00411030804040d198003003000700806802622800c000b84d8105545480900113580202c0c00790f50751050307010307004002013440004104a060003d80d64144145992604c0340c1c41e6070300c0b541c06034220b00c0ea101140d030188002448006039845803820034140e02d0781c202d000b00e50b8034440540021500c001c580340321080c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 763501708 1250 763500458 763500467
    0x501120c27090f20031203160c0f0c030308160c0b150a0302120303041703090a150b1801090e010e03090424080c0915150904020d05040602071704150f 66
    0x8000381e00960350f41240d09190046032041c0050071400b8046e00c100c0b41d84d01c004411520541e489010707580c0e1207090003910008120388034800c01c030003034449200e4400b00d08040740c080401c1034051402034444105074240750700f0f43c00400c025801300030204820000040c0c00503c0b0000700a0300300c1184103000e040c04031340700c1c000382c0300d0759850b44020f510401e460b0070341282c42400f001030b6100ea400740c11500d8400381c441d801c0344e180c0c0c48121150700d07264110307082600000d0f400030b1260088520350300000401a840342c011076110004a900c21044a4007400108559003107400741050b880c0e4510024488182280c410540c0ca01030700c0a201d11550302e44850511160410f0114450104081c2c0041b00242e928480d16486100c801d241c64010400040061100c5154298000314800d014114027002100040c3c0160241c104000903940180c0030001a020070f82c03a1301405c0d005030700500005a80c0c050714070f04100309021003e000500203070280000c0002e903400c0201c030503818a890406403032030b5250010888 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 763502958 1250 763501708 763501733
    0xd050c0c09040b0411030703150c050d0e07090e0c18040201020102070f06060602160617090715120b09060604030303021e0a0806101d0103020c030c010501120c2709 72
    0x150003600360740030003040c008070030821401140107850f40603418540d04149911000c5a00007d44103440c00351404200aa043e07105000320f03070365460724608011a0040300c0741640d203400241034282c9d021400030311035910a40300305100700c10b17020000c090352078440e004030308003082480b6243c03608098140010251790007901101c801a90201004c0110049850843c00800081c0100c01c0103100d03005040c204007401e5144d1400741c0d5050384a1400103600c1c0c3c0c21000c1c1c1c1c041c00030804030850042e8900045c90b000161010009180a03031504402c2111075603220040720034030001030780b0644915041c0f0445071155000c0701c05603030300341c0f030050ba1324141e11502102d00740080720168600500040c0e04002d0560091440d40031b410200c5044441c0350030b45604a40d5142d2503100120000d000101011607503004c1c1c0c2c0240500e100c0c3c03900352401c00e0f034188007903405c482302644003980144e44024441d0411100403001005083d1000ea05045000e00d056000c151003150f20a250100f030740d481007203090090345038000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 763504208 1250 763502958 763502983
    0x10e0a03020603043e0f0a08030a12050a0504020a05010f0302090d060203010501031a0603160c1b08100e0601030b04030c0b01080d260417040308030f0411010f020d050c 74
    0x6940c030304081c83c06414003042c903031581109610854013804501d182848100042c004000ba1201c0d2172071000401c03840340f10400a443d4011300f444000604000103101401c4400b040380c6400d01080201d10401d400d0300c00052014013100d10b032500300801a910405580d00341c03842072810302411107840d00240c00900c0f41340f0056521001070700c00502002529001507040ea0002c2c0d9050017600c0351440c400c00c0f4184421516070f8044801d2002814100e00d428220f08118818940f0ba00d64010903186c200d0180d10450410200f03036120031050008100400480a0602400004101401b03050780035136200c242c1030100801d0550100301003424144070303415182400b80c00081545555a480218654595401000342c4c0802d4140c9003c0c0b0060b1500f054402040620314041c508658940d92241d01c900000b0700450704c1e105041c00048003003241030010314419550000050b240341005e00b402c0c050720034580b404e10b04120700584000380096020982e15200c03540c90400c40c1d210745910200b01c1c101982c0e070050 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 763505458 1250 763504208 763504219
    0x60a0e030c060c07140a031d0f060c060a140106020307030e0112020d141308120a0e0d0c030917030d0b0a051917030403051c020a0b01030317160e010e0a0302 69
    0xc2c800c01c002003c00400540340b1070b8644944490307003440c2003529034503110000f4003c0f41c250740d85004070f0000300b030071100030220080a05621002d0800018002c0e0400682545161f100b0340400118207260320071042001c01890544c0c60540c94184025540d1107030803001800c0000074040481c543c0d005103440400404500e10554880b0360200300e410080200d8000c3d034080010001c00f0030181c02560b0700600070305412407050303443c28891391100c3c00201d0000c3c2c28000b28a644404d50a000c010074404040400565512444042c40034140140124143e4200c2e082e0b0007804804400f031000700200300e5100306113550020480c2d418080002c0c0500002d54041030b00040807607440051804407180c20000e0f9000403180c244201e040089160742d9025501005089921103420004019814401500d03407055905c1240c2e0515942c2e51510504403007030340203c0102b0240c055050101e0705030340d001c5034425510040002030052008000b0310300b1181c03c0c4228140100c074481c00b50191115010000610703000b528 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 763506708 1250 763505458 763505461
    0x6250c0f030f02060a0501050a1e0b03011502061609091a03060109021e040f030830071707080705130906060f02190506040809040f090308100f0305060a0e030c06 71
    0x1c000d0852a041070404005004260000d12480c1c003d00ca80c0d81641e42c043e01c9010441c0c00c2001c00c0c0c40d0b10700e40c01d01c0644940040700d800944c072203800c002940600b00c4800500c0010100c07200c00703071034102d001d0500c2c0519400742440c05659903000e1410011500b0b0004046020003031540820f41241510440581501690001245080340b5030010900601e2101d071141c0c548031020142c480c14020350055841074240d4500400c00300d1f4000d0054010900945004600c01410040d040b280b1500c00411100114007201001102c54200039160b00b01e01c0352809414881c5803c0c0300c01020010b00410150038040045501140314003c2b07009040505000f4a0800c041d0b51240e5000e4070303c000508100300107104901d090401d18201140f8a00d2182d0700000410b601d40f129901c80f00c1c2c0d90400e002440e005030340d5082504882400d8059071074018001d49424109040c01c802c000300d100c08a03000070696242c58481040018800030301c0a6220f424885c0009102c41e40380741c41810343c412072041c41340500c42c0a0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 763507958 1250 763506708 763506713
    0xc0d0911010e010c0203030d2705010504020a0611060403050c0c03060f092b1209020603070c020918150a150b0c28110102010e070608010e0906250c0f 66
    0x44a50034050090300d5040514500b1001120a440c18690094143d003041c004070051403d00d8000642610801c0c902290708044180c5d600712440348400182e440ea0b441c1c038144000e50511a5055000d00124036021031805071340e241d900d99071000608000c1c10444001a203054012043c80103503c0402e00134240c803164200049003a00035101a9504c40140c040c10ba10780490501040d00c0c035083d8904615074400700c0e10b0100040c1c0341144280c00100d06c0c640c50b041580c0050361004019031281c0c0c070310307212604c0b0368583d401441880c42e40100000c00d1680d05000c404542c03800000d41c087c224492841414803582d0b03180c04080a4100c0c0107160252000d02da502064000e140000707040382928660444186000c10801881a4040fa9032140003400b10108413102207641803002915054040c000852008001800ca52a1001c90b50100300000c0c1c2a2005000d501078403c441e51300211040700074009410882600010354069a40001c42d101c800a038202c282c90080c0040120143c2140d10a4114070380750 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 763509208 1250 763507958 763507973
    0x53102030705210705030f100e071a0a0f021605151306110d050a0f18081c12020f0a080406060503100b040507090621110703020703021c03080606030c0d09 68
    0x101030740c6403134002c03808007040343c0c100052001d511195140042c141600402000c0b00241400110030b0020b0180310b00100303d00125008440354082400c489955501c190000100109080107070f01003150050355421a10342000c0e00404141d03042101c10722040c001030b000c003107050320035040d40c00b00707440003180001081500000e1750340800c42c1c5503050b0341e006e0000c440100e80620a1044060103d4a0b124104000c94030170210202d01003034001d0110b41041d1140c030842c0c5440d51380c4400705c00044412a0b0000c04592002064214025159095060031490030f08180f03c0c1c010301c90000d042003980c80008060126580003280204000340680303451854140700c1b0006030030503000446c0030b6411700002c504220701c902d032520219030495031080409030050030b56941c41c124052015982e41d0300e400b681d000040e019001403c01038801d8005140c418550300c1401000c034124518940780c0003020494001003500b000000340d1212044950700d60f240c0c0c440d048480d01c0c2c080c0c5114007450500d00380d08a41005942c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 763510458 1250 763509208 763509259
    0x1801020a02030f010c0f11030301030311010f0504060c0e0405100b032e0609120b3d0603112805310504020a020c06032503020706053102030705 63
    0x5d40e50b00d03200b2294141056421106103002c17203566510400041002c24440c0e90200700f024000b0002152241441d41d1102c240c80c02502c00356402c40c0d8500c41000c00030b8000344040d00004080c3d8040c822441d12901104161a40e03200b20205000c0c000700040112448000140011200829001c004101c3c124102014100c502800012440b5a040400c2c2e041d030000800c000b02e584808403008a640741c0004140d280000c141c4080440490800c684d0720181e074825a0503041880805034039034514050700101503480480c416501840100240d4042d21690042c1782d105030710720a07106030307440d120b042c0c2103542d0b10400c0f8030381d50b15010100b0002030141d1286843c00700d00d282e0310740c80443c00b502e61007044120f11680c9041d1015030301400c04c2903101e04203007000d15030020b180d41c02032a00b19101c0c80b010030a1409070b011140002d0f0300241050400419200322900469020540d41c000d151046400c0c5060b0b020b03141e076a1010945c04080d20071540c0070000c7c0300103070201818a50b00550380c520440d01c0c4480 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 763511708 1250 763510458 763510481
    0x70b0a15050306130309120f0b220803130c08100609050c0703030b04021312061b05030402120f010f0b040509010902220b0d03090302040b0907051801020a02030f01 72
    0x4060200e60205035440e12031040c1c81004014001c0b0b91141c603285001c0f2051124200c05020003244000b8040c040c4408a52110780201c400d06034040040c030f4802004e6400500b0010080f078003450309900210b4803901c444800d6442100240ea079115050701e07110505031b8200007002c0340f11015010500403804222611180c0c103c2070107101c0103841d00380305410340d2002c40700700c0f66851040c00a040401e2180e00009504030010303000601d019140701c0c0d80075813110a50048200080d0b050000c00402c030131481000d803070364140c0c081414100701006000b072880c44064000b91041e21802c00c8280036400034450500f83e040400b008010600a401008000e0082641c2d00ca01c241d24060001da541101809a0000a030380200980c8a005500100801900d005044103442e2a5683c0c0d110001c1d80b5850b20282d0b07942d019488035a03a05242d4810041928107280d0042e00410314002400344594001060714000c031a240780b5440c00058400040345002e14140d030203581480f560781c01741050001035000c0b08084a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 763512958 1250 763511708 763511711
    0xf080f0c0d031a150d0f020906040e01050a0b040e0613291002011506030c0c05012d020702090606091203030c21100e04150e010e010c0f02101a06070b0a 67
    0x1040d01c07082002040f58911301000c3d0f01420410f50310105c0f1203a20032444c04400010050801000d5000304a245c0c2150700040080c0c800a801130100b4500548070200812200412901c0e00307080602e107604c14000034101e80d0082c2071061502121040383e42040c409500301c0c1c504842c0c411000c090f03410400780d4141103240911101d03c1c54946040c0306004002284034020f5201c5911450410110001d0005014100c20003e5480f14040014801e0144021801c401c4018040448001c1e80c1c40401164485070888100e05c1081842d0050315402110ba510040c05c1b6481350701c0348544d13004a640c080010300c3d21446800f000080001050105014001c4810b13415840850019015040038141d0700c20f981840b41500307403040c104000e0240446181d4894414420385070800d102c26402c000380c65495031140a1651a001e04051880e400d104840b00c105103490201c5802c076101a000e0744900026020041154682c0700c07041240f25252100500d0820181a1a607903041504000d41e1054040d695940b155 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 763514208 1250 763512958 763513001
    0x100b0f1303021e191a07020a03080c070305010b01030227030106080114101a0d090503090a0b0910020619050414030a08041e03080109022d040f0f030f080f0c0d03 71
    0x1206448401055480c008070449032480001c0d503410280e0003107141242d2101c11608c000c00000d0070781c005443c1c2200114000d09c445400c510700742e82950030315000c0d14100f510500c030007c10a074034124850128050892210021760701035020a0240466400690041d82001c00004106484010b868400e5003465202101d03c1e8a030f4820028810000040101d1410188581560703100c540e8008808144a903040300d140c58294008521400c0b071690103505502e402007044181801c1441da10072012055201804191804c2c0000c0c02035100d0003002078000c19503401c00034040003013494095103da441e0800302c913112084914001d10b01002110210780741840500f10fa40103e4003105080505a416207940519a003024143d4009401811902001c003030500c003101005901c1c040740782c034401d1400741075560f11400d24001c1c40507e02607034044403400b41801010804203002e105420302d400c3e8081030b0340c1c3d501e200e003c88100850081e260892054084d082550802e103070164080001000c9222011f50712 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 763515458 1250 763514208 763514239
    0x1806041d1308040b1309110702040e152e300f08160c0803030109060e0c07060e03120a1b020a0201120509030c031201060305100b0f1303021e 62
    0x8020380a50020202c441c1804280700740c6000002600c59400350f0100f0f40c150325503c5281c0001d42c3c441101c8000010782c00104a42542030a00038000c107220480010100b035800780c40185807064000b4031810041c0007984103820807a0011034644c904c4018040c4e948038041e1203601c41d14283c1c0c1a007d01c043c1503140303400f0240d002d490a80d40125280d410448a0380580071a1710350b80c0c0340e81c2c06040201008180a00760600240f444590038000e4000b0600a50302c80d8100034401c0111466500321110206001c0100312108038040c045584003580904003245001400401604d03600403a0b020100e0440400f00b0002d081481b0761141188001080d07006a030b9040744c280030380e200d011025020b4001004440c200d0b03030b65403843d00015003103907040045034035100240160900b1500500305c1030f000189810010082182e06000d80f54003c220b886034054124600301c1030140b01d219840813014154404600009210131504007a40255000707003600544060039906901c510a038030001c20300c80ca0221500b20b40c07 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 763516708 1250 763515458 763515481
    0xc030a021c0804061505030f06060906040b13091a070c031b02130c12020a09030b060a1d0a020403060207050a06050c0306060d05090c032d1507051806041d 68
    0x601c0c0aa80310809291510348864000e00403c4050804d480351580000902d61410450407014600400140c01c3c0c0d0b04151040150408001d814244900e09181c0e00104c41d60780c0190502200354802c00c0040e21402d40e190001248142a2560b0109030122080000d199000251542803512955a02d51224050710b00052200310512300a900100d6552a4800b002e030954444031400a05045c01410b0502a0401906a0b4413070a280c00004c0e8441c0ba04200b006901c00580742c00a1048403005803541c10f04483c41c4507a5001c258840301176441d440400c50302c0555604640c081c680082c3d040d940d804032810003a41d90400799104460107490500092060188541540d0103108002c003068a0701712405176400250802400032140c901031190000e036190b40401042030310400e404031035802458250342030803480c000400300803096000320b008100d01c0c000c82800b40f070f4401c40300d05006441d16100000039103515106a0384507009000080c01141c0d040e1035204150001d86055032604065403200020403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 763517958 1250 763516708 763516753
    0x8010c0f02010f1a040c0c0c0609090506150f031f06081e04110607030e0613051c02031e03090d03030605120c030604060c1803060605090f04030e15040305030c030a02 73
    0x21340f9102807006060685440d81100360042c0030b0b850107031480042ca03291400c24218551015011038554101080300711518024242c0c010f10480f0307070342d1841c200e14050300d42501c501c0c540034544480010000303d100300840f0340c81d600c440c1681c401400c002e031104d801404a4030252003400c2c0c40310303104205c032010b808005c84d03291003554001d4030095241e610406221558200c80c074110240007a40c038007030400d51190005880316220420801c1007692406062081c0848c800000c0c464014442c003180c0702507103000808180c8100304480c0a1044c4102a03085802d44c010a10324035030040010b80712600380350341a001031054070f008440d1042d0100d04100010382c1c0b4100e1081068040c1c00c4100040d003c00c0181d840000c2521003810700c0e840412b020009200c080482c1e810882d4250b030354600500c2079052046090f98400780034803000140b4142500c01400c0042800506445000c401d0154800d0281e008280c0c0c0c01141c2c04011030f511031403008081034603500f1400c1144018400d80340e805406645501100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 763519208 1250 763517958 763517981
    0x1206170a02120c130c0905010224250c05071e170f0a21031802040506120328050f0319061703030717010b090f030708010c0f02010f 58
    0x34001038206900707122440b110b9a515094030300400040080e03645502801c61035040352100c000507040c000b1000a40a0135140d040503046601c42081d22900021250003052609251704c0d400180d5a20101118440b2a00c11030072040c150202c40d00850954002000d0003106218406540c101e640381d00100107040d40826401b03100301940c3c00d00708000d84810802211250010b0b00f88d41240e9901484245081007440040b40c4109400202c510b0505041c0c1110285801e546000d0001e5103c80150000102601201130310035507a42d40030030401d0b0b0307805941c400c510141e141660380304c0055040d209030080c2c5584460303426941064102030110f01c40c4044035410010400c880d81152250094202214010b1800b511850769591000c5a12501d00195a403c0003071103005680d64540000010000034404041412004818006110944c00141903440d5100c007610351040300410400001c2c036003420382e408154654270344000c040382140d102c0c0000c421071354250000c0c881b8030034920646040750320748440c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 763520458 1250 763519208 763519213
    0xc0a0311012909151503040f020d1b0b07031d181602331b0403060204050f010e01050301050f04140702060105180f01121b080c0a09050103050705010e030304080706120617 75
    0x303040b0b60172181030246402c0790240c00d4240e001c10007540800d005803900241910181d2070600c1076912008010308880203460105011405d03c4401d54001e4226948810313185000c0300303000803001164947c042e08042d60740d2144031002c1103080c20b520034500c40d40018842c000601841007242d00d503210408401031500d10810400f02c41d203030340150030b4144e0074010300012070150300d508c080008000040041c04c0510b0180d0001a551854201040400c590122009050245030240301e41c0340c0c0e03009015039044540913103881c0303180004100050018058003041c1c0003040d40050034041d42640c0054058107886051b42c032810882159003142440440c100c0301d0710440080100140101000c1e451441c01c013911030100c540101800800e101c80c04d10311074015006d2076104400307000d95464403d25541c000c0c0005942007180754110340f1040e4413030186016030303410320107180114015a1000c1084138003c003021801c0d98012a00c4090007001c2070f4041c002044480c1c00d10340041601700448502400c0391424000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 763521708 1250 763520458 763520479
    0xc010b010e0616080c010905010f05090f060115020109150b0108010b0301081009021203030703140a110d09022b0b01150507030e011101090305030412050c0a031101290915 75
    0xb920307038109610358101d1305500240b2529001c09824014078072210b204900204440b01d00078415400c513040108000c00b00ea001c00c1c900314a20b0808618607055805c1c000c0244410300d00c1c8c0c10705074050240c21000500034a500c03110340c11180302541c04118260f0099135034a8240e40c1e00d04035640e1501081c05a01d0309904121070f182040413040d0b004052240c80600082c50700055085106d0070360300200c07045000719850300700e087d000c184a003030140e0744045400740401003049a210010001d00a802c004010300b030b545c0005209545d00d2248540440500d50f40303c0c0c850b0710011107010408401013400b103e91000000002c0b0381441307409000c1030303401e042e0366400b402c045243e00e04480703100e0f00d03408580c10711200940e0202c24031800e001d46843c0f1030080d2600e0b952403e02d49050503500700f082c0c6000d001c00c4004d11001100502c00300c5d41c8006140c15181482100d503005411500401103210405520070b140600c5104d088034000d000e220f11179080310301402613a10306110056082c051608a54031002150 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 763522958 1250 763521708 763521727
    0x50d081605130b0f0c10150e060a03050601061e03061a0a030603050f03071a06220f060e0403121418010b060d02190e0603060103020d021e0c010b010e06 67
    0x2805004500d0b645100c40060303030303951080484268052a035a103c06000001e190003800420800b10068000790321040218241c14504046210300078001c20305603c4d801c00201d01250346a0001501a41c0c0200503200c0950b51108058008034640109032040040d00b140c02c80c80c0c4d0300920a800848100d00396008003d403600d000b0700d125600c640407110600d5039450000c00441d0082007a00d05208200c6c0085036610014108000c050a0038070301010494a41020040d071a00d036040b003811070402d0f03004500c80605201a20102404541d000c0c000c00c80e1a0510000d80040d100861502a90181c0c50b5142c1a5941c0c003504001c0e6003201800107100e03020100030454800540c000d090303d81e1030900c00080c080b01101d0002e00d00381d1000070008019900400e91080c0c55400c88210b03004880780b81000120054628045180c5000c0102080d0526074040350021407a01560101c403a000400724101c0a0b01e8190b01c08001683c0201410160940ca0415904000e5000314142c0c00000c00040186080a8005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 763524208 1250 763522958 763522967
    0xb0406140d021908060a0e0c0409050405120d1a091005150c070e011e060c020405040606170703050123060f120607030e0c0108010608040303050907051309050d0816 72
    0x903241c620719641c2044900301d18061180380900c42c00041c0e0b2001c8040c00c1920401415908541104000b0501c001c140020090b41b5803c450407a048a90003103800d075140d041941c20300f036211450840800c000200000841c203560b21400c1c04088041c0f20440301c10031001404146007085400c04540f48110744103109525008a04000e40c2d802c1c502c01c0c03882e291004101c142094070755407040902241f047d005015550b400c03042e1684000c4080010703100a4a0104001c040c035205500203402190781d0000324007400700940003040604006000c0c6407914100000113640d03030440f0310041e192075180c06507400421018080400d400d048800500b1410b440d8441001098030301c012080d980280d0000491880140a2007503034891069603d00140700d0362400f09840c1011001e141c981c0c1004008001481a5600a0500f5070081e815140000c0d007a03886000c0f15280c8500c0c2d0300810380c00352484148046240c0310f80c00c141040381c41002034488842410b102550000c0c410b884d000441c00282030080303c40f0340304 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 763525458 1250 763524208 763524217
    0xf080744030408011d0d02010212010614091008090606060c1e070807082103070507030309110306012c0705070f05010b040609020702040c0906094b0b040614 69
    0x10303000e90303140c5659050b086007180c051022211301c140c0e2540ca01500445c0501003a045c07030105000070341c604100708600e0803070720f4014010030041c8492030b4955021000c100050301c80c910000f42c21175041080d490009046072104884035000ca101e0900000c1880c00c001c015104504180700040c40801e000340405400c05a018211903028482c901000907124420411100203211000160101100c969110181c0745d20340002050030090401c240f0003da507201084078101601442c00180c05c2c02e880c1b03040c0790540940c0e1922a4180721340400480d0703090010034a003215485906002e081c103d5042d9195814007001c42d61140443c1c81031001c01c02080001a0300303020f081c480d400000e100640c0d00001b504503003041d005030034025808076441d1f0840c281441071050103c01410000c038281e01d8203100600da80314034003442c20b0042e1200300c5095440c00d69407485009039414511906141150480b0000141a03500e01102c14002500001403030715040045800b0340b1480d9481071891608110300ca4503c1c0d20 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 763526708 1250 763525458 763525589
    0x1503030406300b03100e0c0d03030e0f060109060e090604020f03071a0307030c0503250909052a0a022d0a0c090f0b03150901060f0807 59
    0x2002c0803000c00c0391594880340c4140c007105900050300504160625183c0303031a0025801ea0249480300c040d9003414005848a41400115044007a502d034524084024011082c1d10007200d1040b01c00c0d201c2c01006c0840e070030303044c0c5180040400c42240e40b001940ca40d4581613072146d1042d00500041800b6007000c000c862101e08026044a1290b640d42030170070320007091500d04e00d100034008000c5c440f07002d5040c010080c03961035601d0201e0440c2407042c08600710b680c00342c41c0c60004110581400340c0c198000c03404940104840b41c0c042000c0d1400300d0804203164940010382d010a95070b82d05083d00d01000d170061711580c40455008000d03801c00309103049010300441407404040120a0960040b01004001800000b84034445000187d4a40000981620300130714030f10007418285807101a05e500d00241c1d58585409880c0d034889030303031a00383c0c4850052030940c0000241e020380042c0440c420344000703508000c032480d4540d0b84a00f541100d40b100500b4920400440c894030101004002c0c0f1a084030701513880c0b130b0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 763527958 1250 763526708 763526747
    0x1413060510090504110403120e130f050613020703050a05030408070807110102370c1a07140d050d020d1407020106090b10140a05041e030b1503030406 66
    0x30384480001d04500125400c03031001a081810a1050f41024080d0000058480c0c80c1e8174203050441d622840c400d5284011242080b048000c981c04035614018500d845900611080092400b945910701c00b91601711040ea004094030807428040c05d8452088681c2d994265071090b08240741303c042200c03140d1000d0000e40303284000380b05120110f1808130041500f1841444800050308003d000a418a6007412594200403640e0302d0581201c1142c0ca041c034100c0e090700c044980c00f0440340c5030005000d002900301c1380c040c00401c0307070380003820130380301e0007080500e02070700081c01c6011401c0e40c410754070980351403080005501846000300440071a00030b040e428160b80d4000c00d521040c10312465010400301c0b0b130940140e4480508010300c0f00548a070f0440c1d0030056aa103101d406405401501480e0401b0700a100340700001070501000f8400c40035180038201000200307045c9541240d1340007006d0400d02050b21181a91404100724504403c0b00d9030454001401440c20725190007019650f2600c11001109540c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 763529208 1250 763527958 763527971
    0x30405280519151506050d021902030301030c0b09030706030b121f060b07020609060307170412111c1803020d0b04030206060303030c160804050402030f09161413 71
    0x100c09020140c2c08034640812101001043e0030820032140351908031219051400b66001c0103480d1040c522001d0b10a14100700742d4940340180c540009100c0d104001420041d1014115030041c0d001c0000e5040780e01401409182e240c9a0402203140c0c40b545449030360560100b0020410603000303410071a0700040040c403c40c0c0d500c045c9041d040c00c0100c4101800540d5002101c1006201c1c442c0c490640603007000c115050604640380d001c80c406124035062180b042c6030200016034514800e40c0d81d0003503400c03616080d0380307a401c251624011112030541c945000c210885035124828400040c20403100054010411000c03900f04000d443c0d1111442d1202d88031080c907040480036032191031028400301d2207945400468680b03400c000307003840313009452284260404c0050001e034203048005c2c0c944074103584502c184401d142c1d2900036034620403948281e4000740040100040240c0101c40503104401c80b0003990041c81c0100f040400783d840e98007400c5001003c911040740710f410700c030240c100c21a40380c00001605 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 763530458 1250 763529208 763529213
    0xb060a090f0510080a03021207050a020604091a040b03060a0509120a050d0c09050604270507020f060f010614030a020408011d0c040b0a0b1e04150806030303040528 72
    0x1641d040c4141980724540710b400b4003651018520b041001480c4000c05007903c0c18440d03800a44950007400a0248a07601203080d900f4842d05004443e181a4001c1920796616a10562400900300c4440700c0350749441641321100544c2001c1c00f0f0340e801000010040d05607075584000d410010b1001512480706031284000f880f1030302c1c0c2d01c00010030030501d075900e880d900c0d11349500d046804d4514240f0a03004000040e0010001d90311001c05440c241c5056a5045280d0344a400c0650b4640c030b01d60001401184c10041800040c58010601d200c0011282040d64240ea54031869008018400e06c20140010b00314140d40800300381110241d5040804620301500d0156264031050a482000300d404010340810a0300720a0000100709400c180103042c1e505106200081c40051207004041c4200e00307402100080072240d002c600d481c0059460003003030003a521a40c0780d441c5040c40950340c0082c1c42c041856203020608601e000001e072442581c0c032000409120f1128000f104084070000d00180031008109040c000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 763531708 1250 763530458 763530461
    0x515030d09030627120201020f03010609090b1e06160c15090f060e15071a060a0b03090c0d050f0706081b090d020f06090d061409070e01030b060a09 65
    0xc42a001d54508000d10300754140f50003204c5004440c000c402c01c90045905250f9580219044120780104030685009100d01040c0d019110384103801c4c900690000c00030440075040b8011500b51140030340304006002038801030007540719146a42a518015000c203900c01442d14000038881e5542d841c120307484c000507a94030610101141c0c0c10464202950b00041c007900c507030000c1002c0003004207c1c40041c40510300b0002429003206c440b5407600421701412501c1c1d070b084000781191000780c0d0040c0b054580c000c0c00034011031400d4056031503038842c0a20040005208000c40140c030301520781c005c0904885150407042022848120401300e42500507400d0b0428000310a00419000f8401e584a0b003149142c4035121034600040e42d584645503010911030b015540d02c0b80c0304072130348290341035942c50001d20f2074100107513060040c1c111581c1e20a007000c08603410000760b0f40091050340211689210903445032106592501c0d6180162060451640b0042000c5510a031189400c4240a04048041e940300d450180 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 763532958 1250 763531708 763531723
    0x17010b0a030503070209061e060a03110c0106091a130e011d070905060a15030b06040510020312070e180601030f02031501081b0a0e06040b0a020a03080a090f020103051503 75
    0x195150004513001081d070500380c81281c0c1c0103074101c904c80800e20070117003110a4001900c9800707001c1e28004c42d50408040c003a500c0303200025a41e00201340c640102c4016203000c0c0003280580c0076110f007080d4030703008015041881c5000c0c05100400c0a60304803c80c44c800001414100f0080940b5074907110791802c4200098495281d9909a001420301181092485002d5900c0501120f025801e02d500402c40494681181103a4002614001c1240bc0c0802c00148160140380c020300d5000e183d0f042080e000607000030040040c1159510401400d50700d07002c00350340c242110031846822032015904500c03e41940b803640c680c03181d414180014148510280c0504907081220a000e0110359020011180c1da08001030310382c0000100000c544590060303d1038983c0d8090100d8490030701154108081e00390b40c680080e40c02030800150144d8641140c032000a43d1610842419070200d1003540220300e6590582c00303400c81c8035401c045d016400803503540c011801003034010500321302c141000d0b4180c00740d50345c2400040c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 763534208 1250 763532958 763532963
    0x5090d0b10030c0b040b0a030203250c030e120312130602070b0a1a010e0d02010e03030703050306100306060234090e0f030717091f0c11030c0a17010b0a03 68
    0x2801d01c6401c40c0380251080344079801c4121180780a200c01c20068580c04120381c088106860050384030340300c0710300c403000200d4080e020740b0404e407804554401c1c1d20780c4241329000b01c50103036440171041c01c40c1506000e81e02c2c102e0b0004115680040103180c2c222621240d0030740d080029401080340041a80c1c80328400c9811001040300d0100c0f441c070a00615281501501c0e500d0150003081c00c1007000e45000182070b2200306c000c4603004400001c01c850540e80075810f284590384000d41520f0340d035481e6150042896008442691040031040c281c40e003c24031034420365080c0e450640091220440400c4110f9541e10350035072402100b01500c2d24044101400c402a4000780a050004201240000003480c107001c054040e90480d54020b00c043c1020503405104e010494030051111a610041070002c501031580491010607050b100140f40080c25511495165155000750b500d1004041d24008141e1075a802a42841d41f010510000348040c603808a60788540700c6442000190464030640818803d0105034002d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 763535458 1250 763534208 763534231
    0x110f0106050109080303240301020d050a23090d0810051306050103270f0203030909010e061801060f1409040c02100e03030709030b04030e0a080a260a05090d0b 70
    0x810007941c2106903c40a0215100594150f242c4500103c140355030030104c4424010b21002d86a90a4400394111007840550f04428805842c01c29482800740c00500806610b000143c030004001101d401302c081d0050b440e403005425542280310b0112841500030b469450a50824070001a46607203044001c105a9180c41003c210740d494480090304840d44400174070482ca04203072440c04a6031142c100d000d4a80c0d40b080f4007459059480c00883e1031170040c0020560400c01020000c43d6804204910314031800007114541c1070004480c460041075a003e1041c100450324103200902040e0140402c4001c0114003010141441c5110000900365614100700201582103071180d542000703241d0007044201c008020003140703142444c6c0c0d8000d0144200744009800c100102d00458100751048100f4a2000002449601580d444004035a02c88480b2201103c3d107040ca40c00100000c0c00420503010000d02c00a181e6080c004c05c914240d51b103a004101c1180d1160701a0080030004105a894900030b05c100e0f0107 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 763536708 1250 763535458 763535471
    0x6170406090614010e09011a01091e270f0b1c02010e040f02090f0307030209040206130801050a02041d04030906140c0609030c0d02030c0c0d0609050d02100609060b0712110f01 77
    0x2d1030841c3c140324600c0e48050940000f281050341c02140c203104030395440c0d40002c0800f084d154a901c08c030702f0301d4000d0388907400d0a0158911100220102c48450801c40d00108041507030140100110390804c025290072030130007007a490413080596240001079006060040c540305070040006e0407103e0a4200522095001ca01d03410941021440d03000c030007100341d0060a580e801d60300080c4411100500080c0b01b100c0000355101c0222910600d03000410005000f48114108265001e003e900940112090043c000ca040c40008440c1914140102d8140d1038039462282000c108862886014001e51290401000b160328601410011180b003100c40d00044d54072009072452090030801d10b643c2000866209121283d0b20728804515401c0041007124040424404d51401c240982100b080c0540607005c1c1d80b030240f004507004640d0002000d01801c0800a127601c5a01c0340c811500d460140071000e20303052060000241c4541e0382040a10380c9420704c812505440e12101d464400c901c08002440e946490 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 763537958 1250 763536708 763536721
    0x60903031b050705102a080f06041415030a080d1406100906050913050a0b0f060a020307140712050f160e280614090106170406090614010e 61
    0x19140090740e1040c903041e8542800c40e03c40d5640ea908000380d1a592035070b11100c2d2454036040711009170145401c012071b105400d019000140403060700700c482200d030401150020700c2500c2c084c070a400c03070903802a180c00c4003615000901e07201c62561b0540f0319018450360b1201004241400b024002542000e1004281071402c00240300411074007818060207503180340341081e074054000001a0030355080d858a07035201d080000016220320080d0104210662410f03040c45519091a000341412901c150303a0301d07205c480e140e82404003520520b0032400c01600140f01e684001480300242000e2044004111625903840300ca107010000c8052100b220a584076420b400248a0140841406002c80300c011300f07421440c2a400ca011490014400e600040c1141c880071448005d40071040503003404440e0400015440c0d1004c003800e01c0c5407440c29845048010300024403288111005480905c41414015298507256100130103040c0e090406c884a50b03d5a103410050a10f020500b402440030b80320805103401c194 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 763539208 1250 763537958 763537991
    0x1c02090a0e0705030703050618090c0f01020d2a020a0b030103050114010312120e07090902041107050a0f080c1f050f2707150f14121302030a06090303 66
    0x307501c19a8102558020480d901c2d40020540341e02103020709010481e03581d01d0700020a502c000c2602d444041c03400506005c5142400604080f601d9001d40c3e0707200c0c0b907100040059a4460752542c054002400b40d21220140c01d10180000c241c01c3c002101034111410150b000400c0a80715401030080f243c17012004000740b010034000c50040c7c00e6401c9642c012075040d51200440d4003088552078040c032401c00c1d2060b24505480d84100030406000050381c042580b5104890040c0c42d0f106800c3c2e100300d00b07040501e400500800301300d030344040e4040700400d43c20020740d03145507503504207450a40d64440305110401c030010040c00422440c0e03221aa414100103140b00f58841210070140c0001c110309103240c10410000c1d959110880e203841d051030700700b0f000c811305a80580f8001707158015070007255550070b2807200960025003004800c0029219682c4041e142c0d42c0b1907040340252000d001c2205400c40109529024189981807283e0014041d101c0501a645030f10058400c880c0c01100001e907a04d0100103003c0a9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 763540458 1250 763539208 763539229
    0xd050f01060c170307050d050906060f010504150c05070f0602070f0803180402030a0f06081e0d0203030103030c02010309061811060403030c12210501030b01050402030103051f021c0209 81
    0x118103244014010a8071143c4090b02d0a0504142c0d41030000040307034501e80190b0a4941031640d4140a120915212180076100c5070195001d81c0078012414000781c6542c003810070381d4260356140382c03a030740740c3d1034403050403a01c9458280c800c0c1d0b294010504040741c5c42c03405144142c01b9044035001011014501041c811035540c10740d200c21050340040c0800c03044a4411000060206c1c022034000d41c071703921041c2da518024408001c0001803585000c0000940640200300042c5060311103040c10010ba4959181c2e51f01c40e42c038180311a0042e0410801400040e00518000745100c0c018580007698076815070394030007202c1c0d0b05000100040d10b410707801d804100c1d030950f4444881c0c009a9665050500d541d90107804c0e8907401000602c0c40c0c40000000185038070409890780c00c41510310f01d292046603051015402002c0130300041d10a100e1076000401e081c10540201da04881c1d1000c011301109401070342121043d4403402d0403d0056801b00408001c0440450010340c0340725040c1401030b92400d11000700803002c0366 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 763541708 1250 763540458 763540469
    0x1e19020d0f110615010e0d030e030607020f151306050a02030a1508070902030c302206020c0f010c02030c10090b01120f05030a0f030c0905150c0a0501020d050f01 71
    0x84182c084940c000700400c8454100e036265034803a454207948001a5186050040d42d541c1101480910000781a403260300080460019016600d04e07480710b8000301d032242c22007400030080d54403080e1500342c4074405441140d400181d251414100020302e9841106954003511610710440d004070510032040c401c0d104940031401360a0144291a29200b1003589510300b5101e0140c5096010002400d495030400c1200d00840c544c1c1c08851040d01c1510700c445030040280d40c0a03403616407440002c3d44005104104154003001198500004141d0ba99641c000e580101ea0303141c1d01c1e0107030340540302c3c0100d801d00030240307140d0540c1c01850304c1d00142504c29142005103c4200c40441c201040803001c10f503817030103035810758498030050191543c1300d080610105002200080c07441c03200190f291480ea80c004038071045070340d0f250b90903ca003c6031718104480206a84c0aa280c3c00680100000400d8076440000d241804101040d500800480e483d21030880e003008290201d0161148200903c0d41850f0903030501500 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 763542958 1250 763541708 763541717
    0xb010206070305150607060603171c0b060415110703050607020f120904020f160b0a0b0609100f090b03011502120c07060f1b060b150f1e19020d0f 64
    0x40c0c9106410340c400c182d2404c0a008650000351401408145e0f040791010703640011218582090390802002e09a0040071140303010071150003040044031103070080e030940e4134005003054100380c144080d400142c3da01c10340e140240a803c070005a00444c06010510085014101274611b514180c40044d040400480c1c449505410048044220011b42e10030b5507a00e07001039400580f80d00d1a503840b1941d91203817260500f501003110210108015802c4c08061150320b130450b084c000786103400140400e5003d00c0540652082c3c4da04082d5442520503070340c803615414145481c1e8100360742ca000980c031603802a0080c00000000c0b6a4440c14603404200d074541054227050243e02d00707103240c1d00b0281c03245418055034040120307039061000b48078818010030042d00c07403400d420045140c42d8505807005229210b5164041ca8262140c2c0c156008502c00783c64903402d41903252803805150b4100c032207065000940c034100c4030a062000303003445034042980e001b1511450700103100402c0c0843c001384c250509c2011280030403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 763544208 1250 763542958 763542961
    0xf060903070b041211060a05070210020403152403141618051b03010b0a080a23090106081f0b0306160f0905040e01060e0a060e0f04080d0903030b010206070305 70
    0x128071250b000c1c0e1258015002c1c400e2014000c908803a030203001c0707504070b0281c0b040809100c04100c141d80121700072450fa400303c80060f10602441401d134005c0d448041d1032800200b81b1120b0b4148203402c841501045110305040c0142322208141c0c2400054100f0b89481c0c4404d208900045d508014803401040507290f8100002c1c80c0688403c07a0340944002043c842d80c80344040f0380e10403e00cfc2e0725111015580c40079203403250703101c0c402c80f829074015904181c0001c8104000c00e407104200d118a000f2a58100305401440410107002c0400034409403404605650b9180005000e200501018601100d400200c4246040894401c0d0540c0e410203407062081d00403809022900004030ba480d0340c014100e0520090700b03007c04d00d080e00d07002441d40c0b150340c00c2802d0404d11035110350194880c5041e100e00c0c00e4035008a498059041e403c644450140740e400140310030216614240150003075610500c6080d142c1d14040c2c540000500742c0b04c40c1d0004a011985803501c6040c070b581c0501c2036541c0100c003880c081006 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 763545458 1250 763544208 763544213
    0xf130b010801081b15070c060f021606050406050705030d141807081902030114090f0d030e030403020f0604030807061e0c021b060f040e010e13050705010f0e10020f06090307 76
    0x12000b001e024203218248002e05d504000f80c944099580c9550428480894581d440b10050000c0d4240030001d80140278031029085005002c402d070070140e0700951380301801c1c2400c1c84001d4034180c0c404041964103103c20710510240340524019501c3c554107035829000342d0700b40b1030401070540f180d208402050380c0081d00c040c416904009141c00b110f101c3c1c00c040d00c00d40714241c0007181c0100074207207001c00340e0300c808030030410040000107540f4080da80003022250301030a8048200c0071203030203850f9001c00c0d810410081000d803401107000c050a1500528040c0350556950b1084501c3d0b2141408441303480d1240c00c0c6601c5019110050b1094a40f103900c103000e0060702c07201c003c1d2940c813080002a03420307030603100c5e50001e6103440f1309031000f050400d801c43c1c3c0e80c3c50b120412a00080400d20807040c004410900041401d00140004100c1c0d40d03126004041d41c1e42005d00642c0d03045111865601001400000f618440e95203544c0b4092110050300640000d0b02079480c1c0b00c0c2407480050110075507074001c101c501c00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 763546708 1250 763545458 763545493
    0x10080c0a0803070b0a110a0206040b1008070e0c04050a1514120f09011b030e12090a090f092102010605012307061103040308010e06030d1704020f130b01080108 70
    0x70f4140e1202c02040703e0703035a60281e10001c003401c64604607031500104c3e00d5040c0540000b4540e00650083c1c0c1144507960300c81d200c0f00307150340d081d008190561700260800c00100c18002106034000000b4000c050500d52144085581c001c80da600c051011807500030300e0001c050308500e40c20081c41c2c0b406140303890802d1b00000c1c8005018003418410080d4902d42c00201d0629003035111a4506051003003c04440c6401c2d40003c01401241051481501900c61040c4145509608883c5c1514014203414510785c40c0806100051030b000b5401041c80b900d91118074005a000200c00d0348080b18040012884078070014028219010764001505100b28150440035100003078023501040ba01e98106155148458607001e00074260710383c0b400c01d000d8400300501080581114403c3c0c180d03100300e011411142c0d2004209aa51340c03001101b040401c01b00d0141e85050403001d0303602c991042c00980785000e4150310340c003c150243c00d00522030880a98030300000d43d166900481075401420004020a00e081c01904c40c080c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 763547958 1250 763546708 763546717
    0x3060403080f072a02040b1504080f0106060c031b050a080d0c08090c0d0606050a15143906010b0d06090b09070c0f0b040b01050117100b0f0c010510080c0a0803 70
    0x13083c0c202400d11801199100c1d0041180c2071805412070843c07001d820070403400b9030800e000750815070040344103c0c03040540502c11305080711001d6640111461300f946041d07951710103040c882d200e00702d4410b0740341010500400c0074054007486420310b542d454a60a209004845d400d50440040260980c144507240400246540030aa0100e030504400e80c0b01e407500c640142900c0c0d04c06c9411440b00c86001030141e07010390382c801f04d035203403070311030003003108030601d4a03110342c810384050078184580c560303414458440039007500300305400c802404c00c4821441c001d210716140f001d900c07002500800151040f8241c1c41406071070000c007a04807041c030182c0b481c90300044145000804c8142003043d020104c3c014054001e0072a41d80640040c1c01d00703d0b5003011f05140c04100030034012076000c20342034204a0140d02000c200144180e40c4a80f80942d52410000d1203005a480003101620082c424000c0c140369200a105003405103075425019400d19241104642c1003108506105218160120781008210f070013004a4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 763549208 1250 763547958 763548017
    0x901030513150c110a0807140613060c0504080a0b0a060b1309020901180806060306221401021b060f0a060803040e060415030503120f100e130203060403080f07 70
    0xc94190aa90f0045680306101610b25003203115000403c010f1100702001056070301d0049180390841003095504607070b14401a514026180d18641d894400315459034440950031003545070541c5047d0b60b6030041032a1501049003610410f14a0040c0018051a48500720050682001c40b600b4602c4a062a00d00042da51141159154000513403070740356803003180b0800510030b0703c04036407030b0a5840e00c1c2d426580c2e6030215441070180c807031040407401d0420342d6508607255512100d0200c1e00043c0703a540f0607141813100058007d26640901c58099a60300100c1490100031104000f400d00b450421010030354004080d0895660b18035096040c05200ca010049400780c0d1351941d05142c464841601290042a10f00a04003030a20301e2040803080107008401815000100050340d502c1d52241c0340b06001d60501541c030f4084000106a08010001004a0301980b00c5c0e01d400c2820314401c0c003600401d080001c1218102c4c0040c040d001046042011100400d030800010300c2e1960741c1c0c407541148000c0311102d4940b030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 763550458 1250 763549208 763549211
    0xd0b040b0406051c05120f030103030f05030606072004021c11030f01051903061a130b030613140706200a050a141f02031504021e0306030313030305090103051315 71
    0x4040034030200b04001210489211b090b540c1d91801304880316006d800a00084001401c1201c40f910399910400607a40520001440c0c80e140003903550b900d403405141041140030b035446403400d1081d1980d8602c050700141d19004194803661180c0c03102d480490f50024806120480c00740f0501400b0001c2090040c152081510101107604116104e00c0c454001a48020085810508081010b6240f0100b04440910030740da542c001c5613015460006884880129a425900190005520044c45601e181c0c044d40900502005459050301c12400c1c61529040b02c0f010404070303500794048055070100c0008040300300b070182504a216030384854032098000300107410080800a01540c0503010303c20071000c2c0300e0302c0b90b040064000c18a003030400b0750800c41c0c0800480034ac17050b00740e020b82814021541506100b13080b1a103c0703295a00041c65580029190300c2e05840300f03210034038004a1605460f006180039490f501e8030341c080e490004013030360300007031410a410810850140000301040b04001b40c000b0301c50030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 763551708 1250 763550458 763550509
    0x304021507060207060204050a0e070804080d060f080d0f0503090706052a0606010810080309040908160308010519030b06090c090a1404050a0b030d030b040906020d0b040b040605 78
    0x8031105580250500600701c01c0c800a0744000b00822a030040003250404e49068031200e96485a600c034591044902c040421924400540050181402000000e0f01d214001840c02d444e454909802d05883c2c114180380e600130445010041e803c0001d5140000b141c0c0744c01480c51402400c4141c494007503201d050248100030079000b0300c440c03d030542e0294030711500403034000603003592880b242d84041c00d98079107011400d020081505900d071580d80a064890f0032004510708104501404010507400c0002d680300b401c1846004404840c01034588103030340c002d6851040700d5041030200b004100125003102800d2490a80400000c1c01d204c1413a54030003422941548907954421440207070340310b51508507900c05c10b40b001c007141c22440d4500707030700d03000300184c1e000c00155a40e1140003003203440f800001680b59000404101c052440381c1c02c0300c0900700340900045a0131502e941c0c0c010503a00300d000c0703202c84541c07643c0b0251414103091043c40c0e01000c0444007440810718003408207041c00b40f5440b801b0040700306a00e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 763552958 1250 763551708 763551739
    0x20a080a150f02094c0915020c15070b0106080f2a0a030605130207060b1806062d0702030f0601030b130204021b06040201090801090804060503091f1a0405010308030402 74
    0x28002d41c0500b41210440d5a1494801789210685500480c00c042049140042180e00e40790b91740e0b604c2084950010180000303c0400c202c0e030103001d624806a00c1c0030422010b000100e440b00518000c01c580c1e212526507080c00b217646052410010900d4080e041e030700e28954500041100101019081200c00a5690420b2034040f00500040d030400c94002c442c055281050807952750040422900480081284d120030702d01300000c01640d40c0c0740c40c08025a00c03004c24880d244c0103004102076480e2520628201d541019034a04400c5544105c03544060080307400000e504050190700c0740c0c1c01b0504c001d80850f60455a4140c200e0038054050700b10041c031519804119291981115003070000d81ca818501209510b19451b44d90100f150220300007034500c2f0000888510501540c0c003410303031206d0030508140c2040f401b120f607a00028908074240c0f1988070820140303400900c146404a40d180700c0410311001070f900d00140044003a042c81e0140340361800400128200c441501d801550480d07a841035030701c81a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 763554208 1250 763552958 763553029
    0x90f03090315221506061701052106280e060a0509120c16050306190c2015070905130f09020603100503100c050313020a080a150f0209 59
    0xa0059003d0180e0204a000601c20010401d007050707915075000340400c03a00c4850448011101c003641080116183c2c0041c0b00ca8a0044140e55019503404981000b4100c240c4506280640079501032012242041f43c2c80488800c070100704088214100d410b01c000a414201d107550b602c002410700b2403441d170722000b04101300307401e1090004041040c032603161260400103a09482d8503002d40d019035003c0801d4400113060070f002c10b030039201301030014154030402c02807440d40c0060080d40c4130003030811001c11884100190201144002034450300014000c89a403501c03000e07505d000181c801d01c140100403404004a0b40c84601c0c400801c1100d0380081034400080c80010301900b0102c20007548504003204100321b4108180030001115000c4040f034064040207600d060848816402c0f010016000300b0008141414000313130b0329140c0f0700c0a8485044a030b6200070389410a100c01408960040c1d000f00440c50080d803a0041260f11078600404524129a0400090044610302281c10235445900e8503680204040c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 763555458 1250 763554208 763554241
    0x7060507090f0e011e0509041203020d1404051b1c1a1801060b07080307081008030a0203130504060506071502250201031b081f0518090f03090315 64
    0x80c680c00104003503c545503108003030001d0050b05400c517904e1080007060031190b44100100c03000640445025201c031388030940c0c02107903082c0000038035400300001e0010714158861151654240e600740c6005003820729119003403c0350000140c1c407000b507042d01d0103846d580e140d4a804141000c2c91042c03031076215600e0072121000d008001036482e074000b02d00f04008600b500754141c420f00c1c41e1400810003551140e80c1c4100900071180c0c00350a20f0340c2440025030190080c541641c100294141100d42d0554030120989150310600c80c51006800114403800603980c2e9070208070142800726418442181402e0105a05014071080030704000c01030104266142c3d62a4100c501450055181d081c40e91092179140c200c030011190100c0c0041d1a02d000002c026421308070f090b030383e03103010360703c0c0695031315940000b01e140c1004d030a6240d20b9000700e0400148607501e0a151040c03111420800081a00e041683c0c5410300d540c1c1d07004171303e558000b00403540c02958089208841d0307074180c030a000b940303489210010803506030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 763556708 1250 763555458 763555469
    0xe150406050919030b0f0a09030e04020f1b0c01030605030a020f21240c090a0302010522120b060a0b0706150302030a0309080f1621170703120b01050706050709 70
    0x3c0c400210038020001c1c082d44c0b043c1e624150180c0135032981407440301150030782240600020300c1c8540500503031030103070024a640768140060070300700910300c20701000113034502494440d140d1100c001210340f940c040c01a08010417044014000d80301c1c4c00d0700891b0303c03000e030703c04014030800025580c14203041a80700c40d003e81100e2030049545900d95485000e012480903c1c080d1741c941b60aa0005403c0c4502804452804501070504a0301d00d20f151b00544048d0071030089150f00d01881f40140301813480300f0a00c0001000281000100c200782401d04680d240c4028248074000c1c1c0441c64140300303150903141203407031071035120f0f90000e00440c010040303601c1010582c000950500a5061080602d54004059401c0c0e900d008240c0c0d048504c458000d030f580c1d0030000c43e25501c20400b179200f000055002581d030040c685e445200024031400903914100d40c4030780d407074920300c215401090500900d54082045132a4001e1000e042201a480000180c6240915080117010a032030340c0c0020354070b910400d140001080b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 763557958 1250 763556708 763556749
    0x603060f090f1d1b0906030a0308060102100261081c05010f290903011803021510030b060d0203331314010b0604060c030e1504060509 59
    0xc0f07046000e40c98540000c80340460f0044503040c08410315080010600500d00280144070640c280e135811b07500300c1c0c03008102c03905501a07410200c2c1d1607140c2c1d000600c4081c10b89030803d00040c500c440d01031140c1c1c0065a2841e445000321307a544c0d00d4001e035108100282940c2d440c44050085218856284c0d0200c0241c00414070340d00420490b01c40303082000d80c0c44840c10341590600c11681c9a010780021200203110382040d810786078881ea2841d8084001c403041e44a64003d20600d0140e40750301107404d42e540d8005400d00030905180e201c05041d818000da410b100c50700309001c011420400500c0b411504140406402a2004000b01e20b096a4500380541600e901a041d644000b0151603000c1420650000c480c1c46511640301c90748001102c9031555202d03400003544903850164503260901c030103c0b44200a4025980c4115a01d419558400503000800c0380d80d039009020130321841c0007801d2105400c01240560b000311002d42040d1995030584040d2050780c6405911108102c00040c589001c0032112407928 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 763559208 1250 763557958 763558001
    0x11703041505030f060d0305030610021504030504180c0507110607051006080d03060812090a0e09060a0c03020c0705090a110408010911060307020c0d02120f0105100603060f090f 78
    0x1c0c0d04000a14400e482d000000d858640c0c0300000d110888906000040010b03408100154491400c61403030f801c13561551046505200010b00707030b00740100f001c1d0b9041d80451700215040004103910251031407000c1e549001440b80850083c0f0142c603a005081005049a0b030320b0391010311a440728410b84080311741200c11201c8079580107200e04010800340c080c441c0c207401103154100405010380140b000715001040141480c90031200f240300705400600d819075000300c80c510002100403580907590300a0b01d81602034405420141d001c4801c50f42d1b0130740c4540c20b250050201c00c406000104550742112010343c1d080305640e039442d210900800c08103034002c9420310301040100c0c00c0c0038154085a0094426040107540260000030422a400b08a40980060f0f0050b81d82403010704040a000402500c0034200d0f0580301402e03081c2c2818003c07400740f02c01550f0741d101c0c208421140429a040018541c07402c0c1042a1820540c1c0b688400c00a405140e80e182d848040d440311a501690055200d6100d0440c3c12445 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 763560458 1250 763559208 763559249
    0xe030d0504031103070b0c0c0106050d110a0e040f1b0b0f070b060a05221107050a020102070b0301150e0d0210080f07170720161e08030301170304 64
    0x106400d54040d030006024081001d890f0b00000b0031200e0464024281d00284d6646104480296004100441155403650030000303240e11800ba82a400d5881001d00100f0710401c2400d010b251001c0c3d07400782d01100e42c1c1c90305102c04100d580c4081003070301e0741010410304110342040c0c50040b941c401c1c0c3d103c2d51068000164800203c0d0002000c0c087e07040c803d511540c12912034004001c02c0d07003018000c03168020000000c070ad0361000c3d03a80210a450100c503002090320b80590000101541000a05403803641181108204540e4140004c4002d000d121041a055504010700001680c00710784280303003800a032501c030707000b00d9032040103034450139a00134a01c03040001b2081d80180600c0090b1080c6101c060a40c010408642c05003901514481140000101c07503030701c9080031200c074030000e1125a00c441c226126803071703480c105202070515010025481718100b4a01050000040c41e540c0b0009071140c4040b00601c20600c001c011a4110344001c4a43e840c1030240710b90701c90551240d5403000101040c101400c0f4030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 763561708 1250 763560458 763560461
    0x319052e030201122022060503010e13030807030b010314011d09120a05160606091d0606060901140408011a0108010501030e120f04210b091903120e030d 67
    0x2900d01c00c1e40c03041c024000190342a819104200580c0004a417120000035000d1131610161800c0c20402102c6124282c3c1c00c2c0d4100510003d03030b00468002507000005000302c00040d100f1a07000105146d44c140c910b9403d4a0040107800701500700000c06803030f02c0e440030080c3e200345c200c1544110016072042541d42c0d0f070035408940c5c5601401000490502e00d00141c259180494075032102410450054601108090120f800e0750125002d0110703650514542000f040c114407400780500062070001550303e4104155065000308403ca05906601900c208100d50700c4207400c0e10700c000b0080c02d141210382641c0d04551050301a0350403003001340d842c150408401001891240f00002030030f88404001d40d817035100444c280c400e80d1101c5050355012030003406950300405c00410002c9080c4400506180d20b07241121000310018503942c6811a41100e05001d2040451445801c40c232400300405030441c0c0b5004081c54405201e0010301480303485056a807045540d5048602e0714020241520380e14000c0f07448420 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 763562958 1250 763561708 763561801
    0x40308060613170a02120714060d020412032109020f0603131e02100e032505180a0c08040b010905070e042406050a0e0f0406081c080c031905 62
    0x21b204001e000702d00700c1d0003000400e20505a49a100c1703030001c1070341c450090003c01e80c00305481c1c151450b0300b000b00062a98420318001d030307298803c0da5240c000f0880026000c0c0c1304804410030b81d034058078041b03c1d07034010303a520002c0b4011990182c3e8065141c0d07407000c00307140b1507a038006005080c00c100c00c4d46900c1ea0700311034107000352418801c036640300b18100b405070211703441035608a040c0d4144d0b100c040540070702a070f55103c02400c0d0030804910007a0b26201c0000c1040c145146e205120356000d050305004034054a402480004801842d081c2450314164842030aa01030620450f41510f64840110302268031641040403883c1c8094818041f00c000409680c1c3d80c1e0f0aa1030800c01448420780c0f002c0b680a100d042164130300421540d030100580701c0e80d42007004041400100980c40ba640e42c00014250105100782c07101c0054000c014403410b0519000a4500c0c90000c01d500190314040080110204c0d04448115500410b00f02c001800d0f90740d6125a41e000d01841381040b8002898541c1c01c3e21101c1d280f1095 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 763564208 1250 763562958 763562963
    0x309080c06130c0b5706060f06040506070f02041b0f0c0507140316090c08010b160605040609020a08010b040b0f0a0312050403120f1106040308060613170a 68
    0xa035541d035540010498003070640000305d600a030f6840e00e04010000c032400e102d8061000d070f01c40f200d03d08450348652100701030741c1c00041c1d58007000c200c070261001c02d010071948040c099542c0e00c4001c80700c0000803841d109502590b0711a090105005042c0400a5120300d811980079008122001c100c940c4428400070328040314000500304024049100d1280c580111940c3d4000010041d11703007400381925400e17481140c1c1030b8051240070501c8001403840c00c10070005020801e0005011180600002c2c801e2105810002000b14208030714031b030442190030b141641c00d4003d00001036a46130361a1000c00b5240190001c4d6103c0c0c02d854010441482c1035100c005501c408640c108402000745092000081c202080076030300411001c0c0c00c2010840450b48802864020302e4130324034158032691903c2850b811841c50301c3c001080a03094500160b0080c0c0e442055030320b400e0080242d49001d550042c03404400034000d601402021504010900742c02109002034031001d0b46c3d2625504034040d183d5902ca842d004107 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 763565458 1250 763564208 763564223
    0x5011409193801120f020f0d05150603071202180325051c08091c050c09010e04082704020c010212010e0402090a050705070b04050a0c0b09100309080c0613 68
    0x40c000250450050a012603042e160503240070403080c40e4000a064090b03443d00e4036502040b40c1f44c0c0c00407000004000203c0d08550001c1c180c105400c0343e000741010069814000c420801c10710030061341009035002c51038078507034001d60707210000f034503500260107245040d41c1c040c40f6017540388140c1d40700000383c102c01480b14200d501c44a40c1c0c8800b00408400c89c022200000290721030a0004142c0000040a090101418410094031b801954110002500310161416081844000680d1400f9003d20b401400221403a01c41c134101703900c9603142403290036010705507481c281c00c1a001c4561089a078040034800100111340741d0a0f9400c1da135000c0d510000042130001804000420360250039400310740156005080a0101d41e43c00300340710020040600104103220080c4245400034000078101c51145220308084c1c2a640b5103407510450020503504024000e0a0030301c140381d900c0c1c54960780502401258540441c0318403050510b2412440f51688588503802801c0801990340f02c0f100f44880c0c0d50384100724 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 763566708 1250 763565458 763565531
    0x31703091c2a0b0103050604290109091a01171603050d05030c0f0f210f060f010c080307020c18090307020f0402191e02010501140919 59
    0x1005441100d050710004118400161200051688094a103802052803002c0c0804081c3e01c0e1401074207826402111590700c01c00410003005080034640c80308002070030001c0b21000540c0c501c10002c0c0b4050290b03580c000d5a50f00004240302d105410210311580c0d030068401d25585032007454410040000c0d080d0b000d440380700d080070b03131606011496904807908030010341625040c90004640d83c0d440900110000082804201ca2015800000b40348115550080d141c0c0e50940101050102c0000b070740c1c00c00f0311080c10b0200600903030307003c41a80d0311070f10448101c1d058084890050740c1500308020f019050b10404001c002041c2c2d00000c4038600f90200304c800070001c0d10417002e54040c00d4000c40f031424040d0014032420005081c0002c03441103071480108050304240d00d05c059031003118034071400180042c0c1071058400c003000e10541d6840c0308040034402880300b90304000041000080030050359000740345140c001100c03003020000110031074046410038010f1012144620010355581d0302100e004440700710f0f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 763567958 1250 763566708 763566733
    0xd060b090a1d03041503021c02130f0902281106040b180f0309040507050c06040c14030102041a090102010e07081006150e1002120d0618050f16020703170309 69
    0x1040d81d08513001003c12448160081c5e0044020b034100144001c030001e00030620a503036584070300142030102c107020042d000c4d0a291024503590458150b101c003200314810000c40010403512100f641010940c0f00002c181010010b204a40c01c02d20f490340700d0320034001c400502c0300b040b0090b9601030141c901440340d4a6088080f003800342e1228440da400185c0c0394010002051242400d401103070b4001c0042c10101d0904078062204e90074074004450440720b02d13852003010300c0f052510100e0304c8a8048240c0007141070908014049030001d5011400000550000c5440b00d050ba1007500b2909400900ea03080e907070000c1e41d500c0456510f0704400e480349a41070500e200410006103103603000e06169840d0303681c001183d02d0041441052000d40315481c045016010010b02c0303004042e001001c4004904500244c454580030300040b50b0503003100d07803102d82030401e01840144451050025001140305211524080806100740e28150031783d400105078200b42c130410301d003144012010718481d500d0794060b9103800a031007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 763569208 1250 763567958 763567963
    0x1080607050703080603071505030f0a02040807140f030708060106020d02010b010e090a090602031005041802010206240d08090f010c0201020607051803191b0b090d060b090a1d 77
    0x200c400900165041c081d072000300303114000341c0d03800a6000d0207888985450701c0600000c0910300c1c905401280d000014004000c4051864a902a00501e021801c0c5411b0a024a4484605200b408a5582c03c0c1842068641e00d0403d00d00001d040141110783c155518061551038581c24803941016008440101d039025006000e1128007000507510740503680140010401e24181c0078001d00034080d33441e5280ea000074a94402103008408124246d1645071500c8200801c4d24880002815001c800c0c240300710041c1d0700002c0964001000f04000ca00344455100ca43c00380c00284d003002a480041c00d09241d044c0b240c01e00007400008010741d200c1084841030707001950b03014110000240103030700c940002101c3c01d10440290900c01e6140200c011040c01ca580024034141300c070135030480c9108c041d0812504001c110321640442030000c120340c106051801071200a40c0c014920801c3c000c0d070200002800704205613210714400c030030003041014142807141445005000d241d0880c41044000c180030b20000000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 763570458 1250 763569208 763569211
    0x705011e181e06060303180611100b06190305041104021801110c09040809031c02030301031506091a10031103190b0a08011e0504150b060d06030b0906010806 69
    0xa9060070096101c01c1c2e40d5200d1802a282c0b0103280ca40c16128900c00095420b01a2000440c042c5d41e80c1014010504050001500d00e6402203081c0044803c1001c841400410103200030b0340301d400c0000f62907060b600459940d114102005200101940c145020b103609076104500450180034240c440310459001d100491040e490081041c502c410300c05003081d8820070902d14034503541c2c0c00303546410302c0b9480440c1d10900b0607981100c50321800301c0d400001c0d060802003e12a0501f51880c40a00510400c0182d01d80c48103000c003800c00860103541c0d07000c88042d03401c40c41c000c1c1340302303071041200d00d220062248048203820f60790ba00c0391a14440041026100340160151b00d031007141c0701c0385140c8800b5180c1e20642400711111392640d45404c11480103a8030140c015000342070400012130015100e1507480341c4066103580101c00d251421003031102156880e000c01400d2810540001740c1404c01d200007030502e000e414662030085013890300200070041150000e500984040c001c49100e41d888804d840c1d2103080 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 763571708 1250 763570458 763570481
    0xb1e0c070f02270a0c0e06070f0f1e0c03170301030b04080c03130605190915081503030a0206151e0603151c03090e0717070909021b1603021f02030d020705011e 70
    0x41041d50527011400c04020039240e144101080822a1104d0105818100142e01c003a039030f1144028080041c401d4a2030211494000c24500b58030f19815583d82e80d4044001030409811200c001c01c849024400810884050000c8004824042a940c980c0141540d0000c203c0740043d000c2800f88074540340c007440400003590008030912034031034160001103079040d03401040340452214119404425480500042c11400d895501812051900074403840c02c800d04c18103142e0081819106010464540303403034080310700e0800c0310403654a48564894220b1484929027990380241004020001c1e107008003480b110041c401e0700d50014150b44d0b000501c0d000c0b441100c47c900840c03441c40c45442e044041d1480c8a50110050418120094460071120108d801208410000d04011000500c603010100818100400340c11000d120303460840d800b00e29220030b4000345111500c2d00383c81a1241a00074820b482206060b448115212180b60030310b58003a210070030b403600d01142d40c01d45d849901805070280000d00413 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 763572958 1250 763571708 763571723
    0x7050904181509120c05071208090a0806070c0803041401060b0903070609050901030f0f0b1003020a24050c280b01060c030f08040f0b1e0c070f02270a0c0e0607 70
    0x35130504c140c0345c51084040c1254136010b900e0000c1030040e12443c0c00e808182c0101700b000d440707a00c0d070382c28410060a503401c01001c5511113420000c00560004410029550290299889864030310300760b9080002c61004503115420b1120108903400c24401401507000101c0c00c50b0360190307860b1425514282e450144a800a155a0040c0301180c5400b0225052a104440310807030f980d1203844030203a0392802d441e200a410b0b400354041042d86003081c0c0020140000c1c99000c1d6002d41906420300f641645006000c0622001264000945a00748242e81c096550308802a920000201004401c8030045808440110484002003a001c1c0704000101038039505072500720107010010b80503604010000c104030764903207029010303900203054100404c0c05088207020a01c0b03400c191034502408494000d00e01296000d0038800d038800728000081c180b032401d405440100c08841200d030f00d103000e09081041005210983c10900141e2240c84d0301010399118280c5d20786080944440070003020f0b2080c91000340108 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 763574208 1250 763572958 763572983
    0x30206070218070801140f090708090c0d03030f05011a0a08091c0e10021902090603011d16050a06121e0f020a02071e0e07050904181509 60
    0x1810500000d1400c40d00080c035005031541034864407403200c00101d60420000e00700100401802da0000305541c40e072a002c03215100900584404a090020b0007000310040113030344400700c1d20000c0d0034820b0b10416a009000304e04516001c1c20090082c104c84d403600c0c1c8a036460980000b4400b00c0c00c4241441c0740604581543c0f0b801c40010044031402c90160002050f409240303d0200359542824002c000d05266031079040050074500b08220182020200001c29034010032080d520711074198181c403020303030b070f046806c81c5942d00c0300030100340100880174100c01410540002c3c42c0d0300f54000100c0b4080408010a83c611540c0c4030424004100014030505011880c0c1c2c251400d5000d04030380009420b00119405013520000322a1018150b0310b10705082022503500180f05c0c40003641c14020140904100d1032801101583c01800030b101d00301714801c188850340030342d0100d41490f215038101c80041d00c00501c14051100c0850809007080740343c02c42200c68000106045200341c101c2c2c020b90003481d4102011842c403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 763575458 1250 763574208 763574213
    0x6140403020303041e150f0f02070b09011407151509090203030a0309112206050102070f0b03070203070807050601051c0c05040c020f0a150c0507120509011704030206040b060d02090103 81
    0x481140c4a4200040c241c4a6004149411048106c0c1651034250343c0b60094007907099400703018820703080801000c640000c401802803c0840c002c9030f65121083c6880ca0b01241003d10019203402055802008003072103070f41140800d441e5400c07401241d0002641050f00d1550780244034102e8000e688029050b4009200c100001400b980c00110030a01640c200242c60502da80000c00350040c0c18003c5a1250202d0a0644641c1043c0700b6000542002e0004080070790030306a051090412522a01c00801070010028019910a0040d204030503440100301c0c0c0c6480652811981360350f000d0103880d003d002c1400d428540c05c82c501003078a03001038010310380c12402030410f000e1001034034015002d5402c0d44545904004082c900700076440e0003600071340303540140301c80395003440050f0780d5048a43c0080003800c1c84032001040e00c207000208820041d0810b540c1da1230b0031740c1c0140c034686ca000030380540c03081050040209164012134003e200f0361180007070902ca6520081041650007040b807004c2d403c00020f5006100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 763576708 1250 763575458 763575479
    0x270105011b1203090f050d08040b070e061605010e0a12020142051509040c090b0301091503080a0816081504020309010f0903021b040203011404050a110f040614040302030304 76
    0xd00700e0003074145c451041042c0c3c44482c03404014000e00c0000404080410040c4600c2c115608c0e0006017030300d050500c4400c0e8030001140c9000d4030707542101d16032030724550030b00300442580441c24900d069400c0e15150380c420b041048a402c1c0088030303107000d5400c221043d1070f400c500680303000003030041044403030138440c083d6503820501ca030302075a849a081c0c81e0b0a0105071030742c0e02c0c20503840e480507074131226964502d00000d010a550300c00d4001014400540c00500200880c10300b03803810340300d0302180001d0941d0480c2a085201e81250310140c040100015220b03003071a40401c081d0700c01e012000003011001405441142c1d94441150400004981c10403807000c1440c040c1c00071740c1c00480100c00400c1015041071b03088220348100c1c1d8202c01503407109051180032104080c011841d91002c03a4210304540c54030003a055940000507403a442569180d000600908491f8440d40803004100d06607900c03810080c0090310141d0150040c880402e21149481020f07103030401c00ca0713050700e501030007560030b2070b140c580104c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 763577958 1250 763576708 763576721
    0xf050c0406030902030705090c070215070b04030c1e0b0106180321020a02061908160f0e01020a121d030304030804060302130306090c0e0a09051b270105011b1203 71
    0x9070305001b02c036000a5699a540203d0f8010b04244076825074a6100c1d1041000f03007441d02c4d40c4401d088405104120100d40ca404199511940608201942c01141d140607404010000c902f440c04100d0070000e10103008072404a68140c8540381c90f0403801b5084481004c40c00951480000c080d00c230400c0c501000e2241e41c000f001d0010101c0c1c01114403080300e40d8001495500a900d050502c40015031012487d00da124200d0398001101c21120010138280d404000c003440c4002804400b403207404c0042050716482040102d0b01230b074000c116800007a602c804010092544080c0040650424191010242c90007004a4080b0b03540654035a19091070312100754040d400c00e80c02d03400c041e107201c500003010032040d00a140d0a1440f94046900603820f00160100100010707181286803450b0503020780c00200000342e0500504446c1d000c030000b0f80020b1000aa00015580b030905800350304100c3c0c0308410045500300c84c1a1a026242d040580380c01000b17030300340c004e00b00c1006040803c220001100d014000d03402107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 763579208 1250 763577958 763577963
    0x20c0304050405090d0822121e030509120c1b010c02060711150708090f040b12010e0606090f1815130b09030c07050402090415030c0602010f050c04060309 68
    0x6038249903031a40000d048800c1110420703600d4010301e195060890f409491103074044022040220030416a40b251880e242d00709400600400b008400780314070a02074000811010303c41d140203002c9945484000b0007a003002c0c3c1d22070320540300d980b03c01011000d4580176904130f07019060003440240d0390001d51448441500b140c0390305004002c03416801585404005001d1180501030403006071103034200f4085005c400c51011884007006002920000390702c04101c0301000401c40c0c441d294244401c000078024100500410361240603400710007038007401900302c40c0003040c2c44400c0c0d50056540006001c11210121400300811082100042d001d0144501140d5424000c4084521081d0010750300240d031103080d20b80e4034001c0005101d50b820003c0120200d41c2c0701d151032000d141060803241c0c1e1180c0d11016070184511850f0040b80689840d1501d80c0080b50310580142ea00c8405560781c10000c040400c20b004030001035007400b030f070101a004a40222402204000301c0306150900e032440880050070001d108 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 763580458 1250 763579208 763579213
    0x2071b1d27070321090512100e01140610080708090c15040512012918070f080a060501090e19050702010605010e03280804080708060a2706020c 63
    0x250030305030304407041c4141c1100307025004040c414210f04201d101843c03003848641511061030303048102c6560100000044a00030780c0c00c0c89101a00e020302d14200403001c00309565044ca0208411420ba0054004801683c000d03005000c640e1650024082070451503450840032510010100386054416080140d01980b040300703581642c031145000039054000000d45c80003210340480c05020915140301d0000c50190150000c1021b240e20120246030626410703880d100d1401401c0c0c600b60183c98090150780c1008100301c0135031451038116006001c1e000011481c0001504034800118034403a03c1c07103020161141611400400351800814500c40c0706c2c01840a0f1860709106014840402507001e01409403146800100d500343c01c0174001000d0500525455201750b02038018030600da0040612500d00e0007030300d00103810600041c00d2507146845654007480e40ca01ca100340010b005803001c25110f0141c422120180701043c40c054030b280b038100700c03510791f80341000900c070b00040003032003981c001c02c6459a034005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 763581708 1250 763580458 763580491
    0x30403110102070b0f09030a0c060b01090f0f080c0a032028170d05030a050c0f3403020d0c0516080715110604080d020d06030602071b1d 60
    0x9207080e41c120707400449113088103005000348001c0100c54144d010480e180210705005401400420851070f15001070041c0740e0712020141280d218050803405808a0000810115035600004031682014442e90446000d100361302035507403810022007000c49401c030140c10f455030001c3c07455001c0c1c2a0f941681d540d00060b0b035110000c07030307102d000b9070344440d40c0f250b4200c0340d40c0d146081078800d1110a80b410a50381c94000580c51000c080e0028240c0760801954000041d0540e5101c603030345d0703e44c46000e59100c040b00000c50708540a85007010311030301c0c000380c141800d00502c0040c400d1400300c20000c1801400f5030400352603100141d1043c40d00d005c03680d018001302d5040c0025400f202080700000d4004c07a0103900400c0090180c0f503c40f032038040b05032000d4900700710101032101d44e01d52a100c016000500c815130000f82c240e40784a4070340548041103185030701007204076501d20b444c10084d44030030300888084252900c4141c038032070302e51703031074030407985c50103441001d02c3c00d00314061800d58802041fa0181c8041d440 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 763582958 1250 763581708 763581737
    0xf062802010b181521010608010e0d110f0102030f100b090a0302060d060302060406031a06090315070c05010f0c02010b12120c0307050706031d24092a040f0b0d08030403 74
    0x10b40320113407441c030717049440f0908041805400d5132541e400030041c981c18002d0302800503800103908400d52005161041341540a4a4400d04140607007070021019030000c070520000703139400807202c0c0c01004e03810b0350442e440e03980d12201c07080790040c5454294000b00b0303000200050b05000004084810303034010001444d90701c9a00003600303a0400c0e00a1030001b90b0385c01143c0342c0340c00102e4a0304205841112918200365102000036902c2d41d089800714800e200e5403020901280c010407239a0700080d440300080c030211310180004001080d0100c403500041d0308041ea140b00500b0441442034070050a10050502040520b10b0392000f039109540c580200e1004010300703000715034180020409403103241d030b0200b240c03e24401032030341d28440e26a141c910fa41280070300b03100001c400c0e40085442d458802108002d540d60400c0e0781e042c18071010611005020649080c0c1550f1a2501007140b1124210b404000440194054100704d4401030351158100b400700152401144084000c0c40c1e0161103407600001255114 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 763584208 1250 763582958 763582969
    0x5030a4116090b0d0b0a09021e090a0515070c1d0106030e06150d060618140f1603021207120507090e040813080a1421090409020f062802010b1815 64
    0x1544902e9440d40e011815500904c03401116252202c060691207040c00704020000300c3c0368142d44103250dc13848000d8081c030f0407031641c2e00c19508010b4018005414460743c1d0b21648809424400c0110450942e00c000810381c00e000e2311640e180b0701803640041c00c0544e10310401096000c1e503e0140342c5e0001c02c68200b02c00052681c05548090f0500700c008022400004030580103a640390080d2900003010501084540740400840551010f480400d241422802503010b030002e124031412804480c4a80d410440826000855500c143d00e800e14100020342d50040d08440c851140e0082c90110300311500498041503505000c0c0c0b6802c400c0294408501d5038618101d0300d40800c400d41100c25818480740041300110500c11042e4800002001c1c07003100030b0b900915200e40c821010441d1003259550300319015502c800d400f004100d1800f03400c01d591241d4845042c0e5107040b070000741c3c101401d200282c000c5802e106016200c14000003405050070350311003c54216010704010075108111105003195101680c80 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 763585458 1250 763584208 763584229
    0x12020a05030f1b071104050c09100305040303022a12091809100213090b0a0302090a1d030f0c1c0e130b060a030b040c02070605030a4116090b0d0b 64
    0x50309005c0e8104c02c0c00014002a250000c0ca54240314100303002802c0691100e04403001d1100c800e240001d0f0303581d00ea1074190700038020020502a0134417290f088000c0000360780841403800c0001011502504414076128041c0d1182d915800e400c480d071503042c1010000480310041d001124a42524607a0001c4080e0400f20b80005406030640300540d0001c000540f118400d141c0c400a096404440c0c4c0c90450300418204000981b00e40c00f20b03683d9107500a94542094000112000203000313072591040605200e218a400c484a0002d0078050f8641000766880c03c0360b01c14500841c5c0b0f4a03820520270b40c41c010000d8a48152500c0c907506500c505607400d10b80c0d01d60303004028030100c60703d00003201c40c0080148001c0b100c400c051401591f1100d0700c103108040d04107069990040e4201c902007040d48200176051800c406589081c0c103a13001281d2409400031801a006000e404814003440c0140d40e007000e5040c40040080001002c01c07000c4030305000481210f401008168030b4240081220a00003010a088100c03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 763586708 1250 763585458 763585463
    0x3020903030c0109150504030915050705070f180e06071b051f0501060e01080c09010c08031311010f1d011b2001030905030d0c0c2112020a05030f1b07 66
    0x1914060300c020000705503c8007803414801d040403c05454195006010140349e8046c4a1100592000b410480c5d44240103c68006034408207460b01746070303156407401000c4c0c1a400361490318141e24940140851252050207140e1070f0047c002c05680d100c2d9142520340c1e0780c000d00240c0e00700558005040115904000040091000074400c05600840c040050304489040c0c000208100d40b1685018050382e20200c002e0708601c9604401e0b80d1042c1d5500187c803185005207005120881c08000c10000070419400300203c42d0003240da4010a20303070000116403c030032141d80303000031a400c580c1e0b2400014024090000211060400140c0d507140000000190541800308803422034001c070034280300d441043c45403482c42d54203080620030039041d0f07580c10341c8070b0060440c565081552108150a0300740300300c1441410369000304866011174800c1004020002001c40034001040c113a03040c240102d18a8421545a1245651f4060540d00c61610800740100f019084502d8540552034a80d0040d04802c0240002403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 763587958 1250 763586708 763586711
    0xc0408070f05010807030515090c19030605120a050307061e050c09120601050a050d1b03051020071103150a020901080115020d08130606180b04111903020903030c01 72
    0x42c0707031000041c80554001d1407101054240014805030f82c0181c140c1441b0070070102c0f41c01c403c0c0d41d1415100403003030244010112030700c2e440051203140c0c1c075056030210050b1001074904011944007841c082d80d450341041c1c001841d5500400c00b40340442c00d50b9108810300041c070b0100200032040144e214043e504162101480e030600041c0a4903103281c00391041d80d0811466000d03000350740c5410000342303c4c442d40f44101405090074120440400c03420005a06e03800c0181180801c01c40d0b12810200c0da11040d485ca0710a031903190203000141201040c04078040301c00c1105d1000c1c50150203a44000204a4101c2c01507054414881d060004800c07003001c2d244500c000550040e1941e8031400010090300c41070b0700c54100092240a030510513170340858860500030740c40c1040c0a1a4503800041c044000600e8805010240742810100b8828000c0300400f0070b40c03c0e145d105010350603141d010841219a0703002d0341d0b17054060400030000151010101848600100d0400600b088600f10101e82198810a48903000340d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 763589208 1250 763587958 763587989
    0x9060933200d021303030e09090d14070305071407050918070501030c030b03060f09010b01030915200703020102280c02090604090b0118181505040816060b03120a0503040b0c040807 79
    0x5081448c84158010a040003e0004101c0da07800907003103d03011030002075551800110001454050411074920310360105d00100000100c0c40c0503034440050f03002d6a0700c2544143c0100e44038401c07000034000403a0861000c0c10016107072800641c02401104040c0d402e00d5243d140260040e50700740f040604c603c0d82038002d1a054940180104d007110000103006041c9890084100c012420102402c50340b0344581800084045a10b40300c1c0d4446178000c1c4c46864056000a512400c05a040d000f42081c074042010a9036924030300d00007502943c1001ca000c1c00000c0400149034054601542101c3e0000b901a0001400240c0b07601c421012075400d0b00b141c040c0d00850917000b49610514031840421086050061280c5021a50380744003942c0030038581c8a410781c80e40301107010300080000320380c0b181e8100c601003c1f40911a10380320014200d04014148240220454440703005001801c541212281d55240da295a0355544c941d1403012001c2d000303110584040c0004100c4800400801015000c4007030116020b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 763590458 1250 763589208 763589237
    0x506090d1e170c0604080315030d050a030c08040b0f040c080109050c1e090a02130914071808031c110c0303150406050d020409060933200d02130303 65
    0x442c40340340e41c0c0e0008604000b942c0034100d0101c3c001d50041c0d4890f1001e07a82c0d0322451090701c0511420044140e040c0144c040300748e107803608080200700950180d1814001c01d030f002c81f01540e0061003150060480d45000380010301065145100562140c03003240302c101daa9031a813401034212850720004813800e0b072004014130290301d00a20188041003100f01c7e00ca0340210b443d00414100440580200c020640215108541900c03002009010b456402420800308080300542d07845510141c3c0c0d514082a0180200b00081182c0788400e020380b080d20006601e81000741c0c803079a01d194060200c0310060703a079a0442c208034110307a1000703081107070341c10000f15102d041c000707440d00070b030542340c03214500c40c0d4601142004181c40e000218040181c04840004580820b82000d9001c2c0503240402040d00e02e4000340000740b81e44204910407005840e0240c00b041d440c0c4410308000300e4008030000005902c0e030040b12420550144001e2003605000340c400b50408034000c0540c100285a504101c020840e000b1041c87d6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 763591708 1250 763590458 763590473
    0x151803090f32030109060203010e0a2007060b100305090706020c030d030209041d011b0309152706050a0b1021020405030303040602190f02070506090d1e 67
    0x16003103450319003000914020a010790a0700c0b000c00c4040d02c0745140c14100d0000440c1010040703080c00a0000d01c2103c500d4580a0025482405000d080450a1003c14100201c91017840c10300a00c80392101e11640c00d40000c4442c80e041607004a5030301e038581c42c4d17200f40ba468070100d8034003140c8107490108441c24803031012424002203801000c2190301011900402d0b9800084040d0f1454003402c2c01a614180f1070f0209003c2c080c5002c0b00d401c0d82c411484000c0c1782c0c80381503020082051084c110300d254000c410340b0407419100c0d0f21070041c20420703a0600d111a20101c0ba407206000ba40e2103500303d900c3c03409048130340100032030802082d68065a80c80c01c1291070000350040c0020717180115a00091000001400350038903507400101a0200200e880158203018141d04560151030024100ea8513442d20b03142000203507102d44901d0202d0b0420483e01d502c502d0081048148001164014205040c20f100620180340c00400090380e001c00d8001c84000820380d03803181c0d48680720071595400003640e12410101d4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 763592958 1250 763591708 763591727
    0x3a0e0a0e18011a0a120506010902070602040e040507060306080c090a0507050412051501120201050a110102040504020d020d1d030a030b06090d030201090b0603211b030a0f120c090302010c151803 85
    0xa17281011002000061004520103055075100e520068548010b81890402805143c004000e000c84c09414031060060009800084801d155014003445444250503915403e2903006190008540c1011a07205103485c1c01103580301d0200d140150400d5a142d05030380d81101d150400b80c540d40c110140d102d10300c801c00318016000d804c0f4611600c464445a0740003c0161041042c1c40082021091380c02a000700c00b0340445d4003d110081040d5147d05111480400a5101c80164140240703404162454030850145014040100310003650805c0d117180416002b90140b964ac5990100303082040f100302d995180c41140c83c4d103010b80d00010b43c0c10030034540302d226000043c0c0b1182c0329070f01039510740b001c4200b2000c1030a03503d07a1403003071030351250107001d51710400038420034070851140000f1034642d91541c3e02822811822010b44c2c1e81814905074a40c0c42002c550080c082a070008039049070610155000c0c80d1001d20345c074440d0302491710329120315210004a4012401080400900d500ca0f4030034168022400c5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 763594208 1250 763592958 763592969
    0x172a040b06072406060921140601080f0f010b0a15030b15210603031b0708011b0f0e0108061018081f14183a0e0a0e18011a0a 55
    0x24580f50071f00103602c2d61030220004030010070030f001c6850400c009031000c04140180603002117403181d58407041c2c11a00e40980c0500a08a4442c01c982440544014040d1b4a40080c01500c111724140c2410018003205c2c10707446100041c9031311107556068a4403840c041c2480b034119000202d86030a1070300d8418041e0b242ca4034a402406280800b4000c50341c2e0044202c2e02d11140c1004009030315004440c425042c1002503201c5d1259501e4960b08440801c0301040810140d00d030340d510a44156138011050780c0440b00300700b052380040d6000c00025a0340c20090401d1810b501a414400d1200c040204642441c01c229007183c0700a80102d0440303000c85c03802602026031903160b01828070600500f41e40d258030503500200043d10007220500c0c181e4000900f4042c961085240c040c170440010041d01c2c880c034010b480043d0030401c4070403241d2103000644c81000c0901c1c00e1000100100c15061801e0304c1501c080201500c4800d403002c04c00c0e10410350020074400e2001342203400c81a9560001c6800400c40f610301c855010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 763595458 1250 763594208 763594217
    0x7020d0e04050f0f101d04020405010e0c070816021009030203010c0c0f170f040e0f060a0b03070f031104030b0f06120304151701172a040b0607240606 66
    0x140520403004240c0140e020760022000c080c1c540c3d80c0c02503a8000030242d0301c504009104106c00c1400007080702e911500c558000c1c0e0702030145076a41c42c46c042a03a14201d0788032198903000c1c024400018403110090401c041c0003681094019a9500006c201c0c45c0400c1d100d501088100700200110308007030080054890150405a00b04912030311080d60380181144002c0a00e00300d0317186000c2010314001502e1210380d11b081000c5e00d580e1204070150165106072903201e0220b10340c8002410903c1d105104e0415104010707641400c0d0b4403240010703912101a60b1008007071640710340d86600641075450180008601800640c0c00c0c0d03040c80d80022011450240ca00c5010718040f04400c1280c1302d0000480f005c580902d50100c2900b0383d8105c2c1103422440c0503425640d44000316000042c8200c00000300001c1032100c1d0140c1d0742d140050a429580c80907400d85e41c400700c4600390001e07101c030324181d4801941001c001d02144c0c40c11405a945000312661451842d6001c1d00f65159440503640c0b910800700940f009003403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 763596708 1250 763595458 763595461
    0x105151504050409020a09181e0206070f0212010e03130b0406080f1510080402130522031707030606022811120625020a3807020d0e0405 60
    0x103040858811070041074007840c0c4500f0304104544600e40d4900081480403410410400d8440e101c5078100221841130786c085000700d011070580a90400d040f500e859005040c1450f0130015030f1000d040c2400a03000303030782c000051421400710000038000c142180040c40003a5907903801c0055074480f21003540d080069050300a11040c000c4542018800c1c1d00100d901c0c51f40c18484e500e1160495007019040030942d00040c840004032801600324070100d000e10310854441d42004c040100340c078202d4070102c5290881a0000940040c11044072046200c079a010b4500001d4266940d842c4001d0320001780e0f03548001990b0f801041095941c1800361100c0d1000d05040b056104100c3c0440504107002d80c0b001901a0a0400c110303c1e555031040c905401000f84403040c0c40a40c6060038003610b600601e00c9204121900f90400c40c81c48a00c007140600b00b681c2d015106207420400024405502c8805501c0e1100c00401003076014000024201298405d00490b03004044503414410001c013902351224419001e44d09090 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 763597958 1250 763596708 763596739
    0x52505040f06030b1f0302032217090111060108061006050a0203030615041806140402090102060112060b0a0e010305070e09030304060902030709090f0b090606060711040b1002010515 80
    0x50580488506142c0401c00020b03441c0050b10740c0040e520100c03030540040d48041822034247d000b0354800c56080c4180340309021141611700203000e42c900b009188a400b582c00c4601c42100902030f0072040720602d4500072201c00f0107011464013200fa041520540d220800300f085200030782609001070003c0d854242c0c20500205c40c065541d000280205106c1d2000c0380c1d03526003003490041520001e1000361068650800c00b48102c0000346040d008541100c00c0d510502216410300307000325903441c0410f038010b041c40c2c0c2ca01903103445010b11a0408480040c0c031105041d81d0303030381d89021000243c9450300340c03000d40d549540f8005151402c154005190325412404221340031401005036039200343c0084001c103c40e001480040d08040440e00040c0070355181c0f1401d43c00788041400020640c0c3c9c03149000201584421410542d9000116100d945c02002001950b00103140c41e11000c1190201038404601c0c11b400500280c02d41401c0b80700b40c1c4c0140e40d07403002c101c0d007460100d642d01d0258500380c8290ba4040c8028 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 763599208 1250 763597958 763597979
    0x5150c0d18090b010221090109091803030b06040512030406030c020a0b04030e0d05070b0405031213030305211602011508060714120a0608070e060607021c020405250504 74
    0x602c106112660307591002d01c0745074020301c4103590711000d413800f1142900320051000d180c0d420400c591800100e006d08081030164aa104000b441c1c48031404144071409207036800c0700a410001310b0690082d80c00c1c4070019a985801c0c00300088000f0740c0d0091074075941041c07002400c90342140100011035110451100c00700b81c1c40030009030480d401d031501103c8a04100d0224601d81c00040004085104000700010146c0c611400360064400890503107070181c81d100114505406607030340f900045c0c06200720400009010384020705c050400c5203c6c888500004800801e00c2e25030071030f8502c00d104207124806440b69030a220341c03940c0c065082c4211a83ca030524420f5a611480188050306010705140007000240e81001902e44d400300e00e0802c000b0303034035000c109040a0009445141d0071781c46800404200281c1d6070207191301c00c2c40007030310650508400f5000c021a0003109c001c0350072400e249a1070030340903842d1405014880c074882851841c2c251088401098201c110340361000030800e0a002c180a1040f18 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 763600458 1250 763599208 763599257
    0x15060f06030c020a320102122212030903080108061501050f09030604050a05060702030408031e0f160b06010e03060a0903030b1f08131212020405150c0d 67
    0x11890002690040e49038143d24201040f00007800e00070b109255017000110010380c0302010b4508442240107441c20a2215081c1c1c018040d400c040301c44030100042c20740100901c040c04007141e4864813201c44240d616042c03803a0801c201e18000003911040c084c0d040c51740081100b80101503900c0181114034180c0da0210f0024481000e140c1081800036120f950701200c80c041d1541e0001c0142601e420381840d01d0706075a9000300c4075040710b0300c3c01600e0001d40c0303890010080e60221615600514075041c4945d0b0700c0910801d1403150520343d03a07000d03c40c011082446201402c040078408103450103600c41d500380078440b40c1d8003c210504010b1490b0020b0b000703071004141c030354014040a0000c900210301d0300d81030300a008180b048580104640c282c0c260720000c3c13120001141902d0b074031003a2a0340c550010003001c140384c070702c07003d4018050a0300032041680b084840110710180040c005081a8942c4006144100c0d07040038221070800c0410000201001440070066a0352282003100f910040143d00394110b480 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 763601708 1250 763600458 763600469
    0x906060f09060906060c030a05040315050103020a17030403080a080717091207110409120908011413170c010603020109050a0509010510111c080739020301060f0315060f 74
    0xc50f10003080890303d55405582d08440d001c401d590312840c0155004000350054402a02c0784901030601e074210088601c1600e0507640c0282410f5031042c280f0030f20f1100768205501c42405840200400001b01d00c10b07801a14000d40d00380d07035962030307810510002808146041e48000b0b0601945081c418a4240040e0501d007007900900160b89818682c1460000720881111035504030341444801300c1080240500140700c1045074466040281e210600c0d14201c034106094140350001034000314401b03000400c0440700451007400340c0c81d581410940c0c0e03a14a50010808115180c0d110541482103682002c141d1014041c20f0702c030000c48501d040000790b1030b54010700c6030a008a8814140c0f81c0c40308d21860080c455500800119208140a0304e1200040011909460001036600c80441e6109104800c880780034220008410858007602806001c00907010741000311400501c940313200140c6081c09040010312240160325021841c50501e040c0503041e000c80c441803145050018080004030f041140c0c2560b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 763602958 1250 763601708 763601719
    0x33016030b01140c07030219081906150803040f140a0b0c0a050304031505130b0703180b0901020406030e0601031a060402070803040c03060f0209030721080a080906060f0906 76
    0x20301c40142e8080142410740c403864800050280901c20001a1001c00c880c820346148000d026002450350301c0906501030301e5015080000310b50000140000040d0031140205c40000d281c84481c40004c140c0501d591000c03100d030300082020403600c89907092500c014040c50751880c403800c4814000914420040c001d4030700705100810181801c0c3c1d000c0007140f030b08580c0007040340e6843d500c1e41061a0204c096140e1100b0050603c000117400030000652400c0c01540440601c0035a2950314069000d040d030004002c00381c0640c0f0510402040049032030a000c2c81c0032000043e80d590408500a081c2c5851110700d042c25407119004000180f03d076543c00240000c0c0e0318440c051a1140070011700a8070850178041c1410f9000700904c02800b54560680e021a0b11030042003065007909261241a4001c0204d840d6040d0082e18042100030311546009a21250725080281c14213040d5541300301a40040c54644000b40f404030801402d8841009641d401803401c0703c02000b07a400a40c00280c0000000300300341e0140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 763604208 1250 763602958 763602971
    0x429010e03060612010e19111f0c14030417150c0304150204050925021b0d050c030109031205010501081b130f1706011a0405010c050a0503301603 64
    0x1640217505c5814110383d0003040c0c0702c030302c401c0d07c854022880c0305843c02e488110f10403c4200052030420039017070b011400c4c9400c0420303d031550301060321400180c02c400d8505035000c07440780c0c100700c1d414001400030f450f94601c036030240442015094a028078030080d174051081010144940e1181c00e8062b00d90259001017000c040026405030f0708064080c50b803200b42c102608005200b1030130111210900c81340315606e0182c4c180c913600c2c407049903a00052204a880060300101e43d10803410b240306a007141a010b00211f0f0300103d15003001c43d084070240082034001403040d01ca84410140300d8000e1a00414003440d044690381040b06054841e80801d0542400c225000a16046603025807081b00700109840c00307400080c03550741d100b440c7e1304400c14052070a02e070043d4000850b0740c180980180150080102059090034141001920710000d10001034840c2c0c4540402840064030400090403071340d440d00e01d512104400e240c12441d440c070304d010320000300b03041c007208011801c01e4461500d68414100d18020034203 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 763605458 1250 763604208 763604239
    0xf0d0204091406030f010b0f0d0501110d0e100203060102120c16090501061202041a0703120207110f120a0b07180e10061707050a05090429010e030606 66
    0xd00c215801007071110309115404508260324500248507000c04e600350386403041000e40c0b1702c0c221594030b50600e42c850440e500c1c4211a0030301c102d41200c114030980000824400342d450301d5a06801c00c035907032034ac404e80b1000c8050b084107007884880c54200d40001c3c01d60460a0910020717444c0c140704500383d40c204001280c040114401001410f29942c1c0043c810f01c6840e407610b81c840e0151109000c0c400c0825290448500911300701c0c0300701e40884a9650168545001a408440d039503448814282e040010b03560104040b00810300c010300b80b852161448180001c4d0181c20300101d54280c05001d403040862402d10b101d1450040741044419520182182140da1003101c20b0f035901491812180d0007644005c00860000d0308205a18052180700510600c8556640c0c411149800407a94070320006c010328001c9084240100007510742000d603420300720300304526034020400b12001404070385444134200c0b20299000c0101d1440c022402004c0c40c0117005000307900082655004050441740c09400407200c03d110 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 763606708 1250 763605458 763605461
    0x10606050c1f0b0418020a12050307080a27030605060d0f170d090303051e0c0d1802060d0902040c0810230907020a1a07080105190b040815060a0302060f0d 68
    0x2203038500a00801041490002e16003002d414541708074054142090041107660615090800440c2e0000040d49410314030764544459030002c041d03d03001d100030350b541828440c03d1a10258200010940342003c00c5103542042015180b0240207207000d80140409030010910048080002caa00300c0300038000c1003000380070b050071232043d02090000c20303103410600010598540c2005e806012541400441d59008103a02c000028003138a20b2095201c040022412450864105940e20b0b10807820402d0340121940204d1481c0d0701524100300103a503075411000031860248100c03903070296549850002032402440c1855081910300030300c014407420112003a25031401c070300461201e04000e41540007608004901955942000c4800c5a8090408091001900302c400d041c4d485006250b84401c1181d10b044140407100c220025114180310482c032012500e002142c00420041144800505a940450314801c4004c03802030040d03445200901402c0015984440540702e45408006040f651588140701000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 763607958 1250 763606708 763606721
    0x100f060f12050f0106062303010605091309080f0d0e161205011509050f07080403020a0b040503120f01060f05040b040603110730170c1614060702010606050c1f 70
    0x40f107903081003004a20a58468042d01c3c41043c01541300d076040c10b4503000c2d01d05600003405030100198003031200c0f10b0781e80b0b041d013104031b002d00005500140c10a95522a502d19a200b0010343d40b09000c00280340c1900d0980344101c480b080e01003009002820700409030000302d00c419201d544601d1070340921a0080c07010a6004036850260205504481540c908550024000840310f80700303680040000101ca05008142c66889154143c0c0501761f08011075031030a01285020340140c585220074416611829550111240174040c0840851102c0d8035110f4018070449100d1104020840180000c1044500c80d406440503241e4a080c04204800e910580308114000e01350003a00307680003080b600c0060907118407500e4501c107100c00f0082403240c5c07102d02a04c100c009060700100c852801d000060203405407c02900d400c00001d1401008491a6250629803188a40000566801400c2800140c0d60240320700c40040880d070500364109441040003a8840c41008951041d0705020810b65070034100d0f40d07000f01e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 763609208 1250 763607958 763607983
    0x20180405060403111615030b1c062307030e160305030403060209120706050309150c07020d03030b130b09010602060408120601030f18060b0301060807090902040b0d0302100f060f1205 80
    0xd841c0e590b590a402a103001c1d06c2e0a1307000c02c0ca000e00c1414581058090310f103807801401e01c000c03030321282992020020301e103040500d003080c00c143c0d03d11068517504004440c001c0e0240d03600803d42658400016042c00c0484040c0c11300c500b4401400c20024101100b81d9003203d4001e000162140c18020100d100304060b8071043c01c15015254001c100c958000d0040e5000d80b240004803520700b800440400b0868000b07940c80c455500f401d002d50b100501d414408426401c4c400c0c03030b01003403440e02030000c0f42c503a005030504803218a4640341040c03a541443c06040f4014000f501c010019804e158a496030544150304004d01c8012071701000490ba0b901941001003513031400c5104102e01d9004542c40e801c2c5030404081248c14508100c86410240b905019040a880a0300c0141c268180741c85801c0d0010007080c1d501300c0e00961030303811514040c5c0c1c034040742c200d880e40a0b801034144036410099070003c503000081d407685868a0a481400349941c0740c06540c090b2900d0700b180d904520407a040040c5810400384a1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 763610458 1250 763609208 763609243
    0x2100e070e0117010f0203070c0f0c21110d030c02120c031c0e030d141608030414060a060303140d0f0c05130611030906162018040506040311 62
    0x200c00b03c1c20b61554602e054072100070051040f0600c8030f0001c3e84404d4458100042e03c8200110100300740c0c801d03071441c0314411780e9080003441d40c03440005082900c1c1c0301e10504048284122000340100340c1505813642d40211003850101c000c0c2e075006001600405c0c0043d000ea0302c540300c0c54080c0e03034041100c1e10343c0c008018216804041e41000303607201081da030281c0f00002030001c40b0044060900040303280c016403050719a800785c02003031000202c42d500003507448201820321000031004298460300643c02680501c2480d10643c01713258009242c00c3c00601640703000ca107818000c00102e68810840034000004205096854100c400b04c0805480b200b40306030621440d01480c540c0345a000401884011302c91000703042c05654038281a0746507401c940e801e5919800401c0030f84840c0c40c1450040800713840004031415a10103903182c0048501c0110414201d0000000042c1b006280c00084440c180d100c0c0404c0a40d1440c00381c0d6071070307122080908000c0c03c0c01440040b03859980c406228908240001094 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 763611708 1250 763610458 763610461
    0x130b0a0b070615050108191808040803090a1d0f04081209060f01081204050f0103060b0412030305010e0105010c0632010306060605190c02031c03020c06070206010602100e070e 77
    0x30b0810050003503003400c101c1000003070000100c9501400304207114041c417920b0310301121201d0305110044c2c41c4050100b401810071050960010300181d02820151007030f00010b513251803401003401103284264100d080f148640c02c3e80c014126221035402640100180840495500c40d890111040d004240c007035600307140c035102007040321880060450300c5410b41040084659070380d10300e4140c1303596001d14500071800c01040203020078100720074440725140c0f041c500003407201d54840121020390440d410548400e103c0f1207102e42490350601800c0e01405003400554065498800003030a041b0140000803c2c05441b050445480a10354a2000740013013a055004800718548032002e69104090004507291882c1c0708003c11303550301c62000d46c0d000301445480300c0700858015409a40c0400f040340100d03030601c500c0c5002c00e04885480703000c84281956403000b5841301c0c000f240c0c0320704000004180c0402c561141d00100980c540c009500c00150f54807110014960b07280860340390621030240c0021071110075410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 763612958 1250 763611708 763611713
    0xa061e0f0506030c060f04090b03100e0d111603020f0d05010f020703080901061a031003051501050420041e0509090d020f0613121b030203180f130b0a0b07 68
    0x1001a0302c555403c80907a00d040d180c1c0303c10071459029844404820503000d02062043c0805903000a0782404000c0c1141d280e401401840c2e0180c801c45030100ba451340000b1030720982641c0001444000100c00d40207007c000450320361804660710b15100c007074403643c01132541035000d844000a00d194560010002d00030342000310800d201079401071504400040701c1000290040806100b15000d139a03a1000d0282e003008202c01070360f0703c0d030006040d0701c28401c000c001c0000000c10030003c80e000d2103450454000290314000030002210b01c03580d4120718040c079141042c480004030400311400e4980303030300d91180800b025020b83e00360009a80c000ca500084c082091000e07c1d50002600c801c2187d80303600300c4010030f401e01c030301175250700d01507031594041200e90040d403001820001401d5201c01d090303d0b20b1f1000800ca03c644c10051006c403141640540c00005070886028031618040c006d50605503061400003d0410100c0d001c41d1442241d019150740d40c47c0b00d400296101c602c01002030110321301c42e580b582c1a07030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 763614208 1250 763612958 763612961
    0x92f092202070f050d170f04030c1a040b0106090504020a02060601050a020c04180c2102150c0a0b040b090732060a030f15050f09072303040c0b0403050a061e0f 70
    0x1540c001b18084608140c0c0c0c00070301025280c45644030010751841c0f612159000e07142e15908031000c45040304981030802d05101d640d0f01e800d1045004005100d603c2d450290068407548040e0082c5000781c0c010040f0070a1a900003c200707410503000e18000e56204003410089040801c02e003805544542003420450280e0750642d0395101d502d004010600700e0341d075a810709049281d0f00034440040c040207091080090703d001010740c0503855400d80d07454503000c03c1103040d60920407043c808a4210707020900788414441031085196024042030010140c550030121640c450240d2090b040203a40c2ca40c3c0803076042150045182c210550010740007503211030b00107001501a18080b00116101460100034040c0c80319003003d030008681c006403000340e26030141018041c1c03420004040300f00740020009115001220909081c0c000c00d2840b8031a5205c0c1003500d4151848101a0310071b40312940c09000a0010803c04201014550340c040300025410004d54003080d005c010544d11241c5481c40d05c0456140303032416 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 763615458 1250 763614208 763614223
    0x41104061d0703020a02060c182e050c0c120f06010e1906120308060f09090a020118060206070f110102041d0a2a0306092f092202070f05 60
    0x4001591442c1c1d4403580e045049000703410000c00141d014001003009101d6450090a829140c048003131825503602c004642c05a18014940c0c240445070400f44500c0800d54050b09204d411070314240349041a80312b07040d0755410010001034801ea0303143d403210b5598101040b146000300c60000554480c0d42c0e5550740307800d590400300c41e02002035242002a446104007440303204203a840005014104c41c905031800c441107100182280d0300203a44840095680d91034012140c4030b07041c108020704162895100042100103d00342c0f400c427a0300140c4041c072010350041010707548105107107408802e082000d40100c525202e0010782049551000401203020002d54800000141c0c054800032a284c03075603040441190f081c90180710751203003018055a600000b843d4020001c4410b032401040e81512882c03c074048441c1100701307000b40c101420039150014103445141c102480c80c604400e08010856020900250560410380009604c02e102e8040d001c1071613040c0e50801d40c01008203002011680b40141e9034150327 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 763616708 1250 763615458 763615499
    0x501050405060f09060c090f0910050411031504020702030a0f0b060109150819090b0a0b0909070e0a050a0e0f07030b0a0e03090d02030c130c0306092304110406 70
    0xb42c540000c40c1c0e502d244019a0142c1d00c04001080740d60384807601c4120a03040050001d912100001d034641040d034030020620b0040c07446040000c1400c2c0740500300008c0700c001c864010702d010800d10803c00f000942c4202c004080c034007501e0260703a90000d0300c002403c01e82c6520000340682090b02050003400720918010340703d16003c2c1ca90042e60394540c2a80d2552541403684440000c82200000b040000000701c059924150104003041c0c801c4503a40c0c400142d8021104904000d40e1404240703400d103041103041c2c0d04507568070081d001d4641000b9100c010800000d180102494039000403c0302c4075010781c440030f507004440d000c0e07032030300b6620805541e2580c281c0d21054949020010114090007036500c59180c400040c03400035423414a00c1c401f448440c265503501603a150241000304102c50b1101200080e240d046240d0000d4a509480d50280c100c1d42d1641102840f10b1800702155143c3c0c824440020181c0c0307548401c0081541c40e4030f440410056460801d41e040350520000080b254880c903480d10b407619 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 763617958 1250 763616708 763616713
    0x71208091006050f0f01091703070c061403010303110712140c035b0c050306010e24130509010512060f0c070c030b1f03020f1e0301090501050405 64
    0x100921250054405070301820354040104da9200c4c2e818030b0440e40400c507581040c1012035049584401c00ca010080309081c500700b68000158135010441c80c0c1c80c00308043c122a0801c41054180e044107080c40c1d02050100409202e404c200c003100b403100401c61800185040104142100f003079141000301c01d0720700c0d400c0300514801c5070410081480c02180c81c00060f007600703e00d030003030041c80d51804900184100d100300900e84c03d804c210903e110480458880035115404031100006144641402c07a02526040006c000b024405c0c006181e900c07154184030403108031000e420b0399501c1024030b1242d01c2650303110100010005040b11070556081014404c031b5a0071580c0a00aaa8030340074803c1e02c031070346112940ea6030800c50008202e00e012114a46e0444203078a0b0b06800c1c44001c0d519a448c4490980059841c00c84d0034080018200e40c4c08042c40740d0000391100094420300e9580420124600d0100541c42032001290900d59400019101000c0003c000c0090142518504000d8000d0005403029103460 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 763619208 1250 763617958 763617973
    0x51003110a030b0112060b0d06290906100c1a060a060e030a080a120c0801140102060f0c03071404030f110418080c0313030f1109070219020d050f0601080105070e01121107120809 78
    0x200707010000c1810044014180201a0380c41803700305224136419a61010310880e0340e80170000c41c1740c8094a4444030070b880005c5606003800800c00145240c2c42c0d1080f0100030403007140a220f52004201860304035800604207403190b107400029a0300403211100206028a4140716000a0340d202e031885049900e04840f40c001c1000c22001241c07158401c4569905641d903007808220a192060000c50b030054031031804c80650350084c0312140741030348940d00590350041c0d03404045007442290320481d001c00b0400c45042048154840810943d81080c04016088450200d120424030300140100d80120b04800b0020100710384130b142107480480381800c140c030802c0e0f16500e08146401d08049103030003104c0d29002840580075801030107628400f4007400300d0700003a140c3c840303900040b07003009240000007148000e09036960620000500b1194010706501c204026030702c19030341990f0024001c0600b10708608d0042140903900b03101c0c2140f4401e48500030303c1d44100b1040d0f40c0c0c5450b03001c0c40c20b5002e00c0d00641515580b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 763620458 1250 763619208 763619261
    0xc0d0c0311030a09030809190902070201020c041b0c051c02100b03060606030c090303070f0807051612151512030f080c1204030c06051003110a030b0112060b0d06 71
    0x1a40254000c1d040401c1d907840051000c6225107000d884141c47c000d0919004050015040c0003e103803a83c8040c080c01e0f00491004110340e0188510143c5034804e60302000381d00061840044400d59944811017844022803070b000078840b092200010300a03031394100c0d041200310340e41c1c001e41d0f40d00242038585186152103000325103460041000c03130140400400c400e0940d1100b90303090750154840c0c00c0c410380c1407204201850019080d88020482c090094107100c1d00d5840724141a42000c00058540c0480700e00103e0500042c0c1c0c0a4118242c100d410843c040745142c00b9404001c011f0109030009492000c0030440054080e0180d11119401442660b40c8140620b20500c26202004c05541c4000440803d1000c10602501d65110076403060103890200440d001c141c039000c045540a40d05410725003071102d81031040c40b8440c50300c098200700c150340408400e803850300c0e400049401070054144a5002d00f1841c1c0c24010b09403c490940c12f00180650b42d052964900300c03000705240300c118121602d041400c10f41 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 763621708 1250 763620458 763620463
    0x30c0615090412030e1609050601030506130c030b06040f060207210b13230d02030c03031501090b1201060e120c15130305010c27050f060c0d0c0311 65
    0x4200c44090311041c81a155070b580e034003c8a0400c01c0c00030401d80e0b100070101382100d040001c20410415106007401460900366820140d40004100f18141405c0c1010b01c6026220110f0700130001c03103603034070000f0151110b440440246c810881c0302c65000101080110343d00c040c0782c4160007141c1450302180d05256584810035445100800d8084030803030340307180002c0414401440c8903800820004d21100c0040c66994141e6009003565100506181e200c00300380184208104800307410480c0c0c002141442c2c83d611441c0d82c2c0e4840208500c2c1c2c80e080712000c2c0611330340620861809010141c0060f43c03a0001c1100c00078244a0074802c40b00000c0300c0712950156800e10f171188054002c202000303002c1d40c1e9090401d020320700002114030440614104800034066403149a503102842c0300340004100808290402006041c01562200000d448030721424101d030001700100040742c1c01681d41c912140c41010029110b80141d03050908503000d81c019120800f54009511a01144280c0303946c0803d22040300c15030f9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 763622958 1250 763621708 763621741
    0x1701050f0c0d02070c0b0703020d020706180b09031504050a061401030812060111070f140f10030905030904020c0a03090e010b0a0806040921031406090103020f0f030609030c06 77
    0x2090341001080b03100700042d0000c0040901503e04013902030b598909807500390703002800a400582104900303e45541e4148100c1006040f81d251244000b003ca503c901c0030000ca922400c0700c3c00c8000150702d0300c00c0c1c070b0502c460682c008640c0f0f44414240380c14107200d91034504501c030172940a460400c0081458042d440c071a810b0301c2d006601706040c000000071001c059100031703003854140442810742201e20310040148401400f40c90582c503240d2071400c41e02c04040c2d854020400e2040f804044404e1032503c40c00c4100c041507860740313400f00300c034a9181402400c61142149282d0804d00004201e0b8480a000a4515003035120340c3e07030036003015a141500201904203000d08003088400b0440e880c8024404c855041d04500010000103100c1038940d00c84211200c0071000700c100c0c0d0039048071012041e415205148241e440302044201c10b150040000c1c0d404801400700a100342d001050108403034882003a025000c1074098203c840c3c03401c04080d483d6603034003c420880e01500c00d9a000804035006442c020 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 763624208 1250 763622958 763622971
    0xc060c0a0e010807030b030607030c08060f0d0f080f13170f030313051606030e1006030305250f050304051005070c0510020313140a05040506031b0406030b011701050f 73
    0xc607815441c020044541003405040c04d41003540300c1a48030525a401c1c80460b010b030005840000700c14441d190041c28002c0020841032140c442a8000c00e150780301c50f1103100c5030300d83c07201d44507408810701e2508034001d00031700c5060040c80324003144011240c260340d0300380000d80b2445e414440010010044159076010506001c45a0703800910101d660b041d11200030309a09481981650700f100095070303035000020001d6200030006034441d00d01c021800014015482c0030701001c0005d100032421500c000e440b44c42003000e0014007081c0f02d030b84846120302110003115210382c406261b0451905905107655170b50001d0003801e101e0404d0a2050115034020f9080300e40c0e859000100e054042c2c509420865401203031350200042d40010440230508401d100c2c1c0b01c0d0f002e04490f00d081082c489005040c480e0440c0350350440b034062883c10081c00f0381e03540c00285990590f807441044202889600740442c000e000140d0004010f081b54038004100c2c4518010400840110a40200074aa403680d683d003a016405643c030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 763625458 1250 763624208 763624217
    0x90414040f14070915060324030b070c0203030a080a05180703061107083121020604080318040e0c090c03070318030e04060b090609010c0510050c0c060c0a 68
    0x4900160019031210b612882c030005451010b50b881e84d9060940e440440f0030303928400c10300418040309030540329440700803145140600c40c00b00315201d40c0c03004012502010f000c0c920040d0001c1c518511516503904038075405000d1380d49402c070080001e0715400c000d5031700e401300134103100014070481c04841600d111002c000c002415035510b5511008000c107007480c0701c0020040c08206020120b021040200341d1186c50500b4071040e0564141c0302800c1d80e141c401e564038a485140d1040104035804400214086286038410130130b0121480051210b00c145c2d805404903000116603e0383d0000102584900c1c3e403c01e940500284440001c01c03611020380044580e0b1240c003481c0840c55128000014651102081c1000143c2101d021081103205280d900214001441c0d01005074580c185400b0711001451440b0b205801c2403003a500249603802054412810444250548010710404000482c101075480c5000c020f5814491380c140a02c3d070040c0c1c4051038034804d01011403080744540d0210341e10707110700713695 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 763626708 1250 763625458 763625483
    0x1092303070b06030304170312130c1412060a2421030c05031215010207050f102303010f0e010b0412050c12100f0605060702010807170c09041404 64
    0x2c40090011010308441d0301440180070101741042001c00d03e0407c60907180081d610344040340480311641000a000c195081c405400c2c140005135001100001c0e07400c04180309107a034078031001251030459600110081c500c21401440040f0301143c1c007501e01f05806003011207000b146900044c614416130b114541d40b04a2004210030a1690030340c405d82100d1103440c03d503e80301103944586180d80c20940320b100c1013100071000e101412608200300c1c148140f0a001600300b81b80750100041c0d1244040b0070b502e00602d51614164120340c416801d644010510b40907580044120200044144d0030034055680100b010303200201e82c25003920445812036220041c0c0341d1900c0e0a2801040c60005109000c95652003000c55010076035440d9189060403240712001840309141d4049403906407200c6c0711407000900d1800c003060059403207039000c40e03410503020f00301080b5640703a0b00d1048801d00403ea448002c04540035060120b0000701e000202010017045500307114111100c80c04030420031064600078406102075030b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 763627958 1250 763626708 763626713
    0x4060b040b0a0f1209060b0f1f11030705010e010c08100b03060f010e03011a0a050a18020705031e0c0114011206090203031306111605010c1509080703020109230307 72
    0x284180102c450600d00301c07900055501e0040c0c05e6817075129003210080d48400060743c55040071084c4414141084984413601508480d82e8104526215071005c1084000000305a0000b010411a4121a07000c4020000001c612030620700070b16a2070600c4000503004408030343d00c0282c90002000340e500307191002d8555101c07802000201c0b00b20304840d90501040c01012826540c0030310610808000001c41c0703200d211618406c00441c0074168120504c15280400c00344004080192200c84482c5003410041ea0307600541403051650007061491440390341810888141a010700010f8109520f1060091002c90700030440540ca200090248071029070303104200d03002064071900284103507400a810307a4542410405421040d05454001201080010b821030f5085c2408104010b205281401d45202503403e00c1e000030611206001c000e415940e5a007809580c0904c26403040c003203282e00010040ea102403626020340a0b2208030710503a19011104040b080c3e10b403d24101e10f80c50401c101c040c6240c03410a0b03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 763629208 1250 763627958 763627967
    0x6150f0513271a040b0609070f0f1803050106080d021501470a120506060a05030415090f0201020d1e12020423090108010c0801090504032c04060b040b0a 67
    0x10320305450500b2251006243e081c0c01030103040c0a41d00a0000d0012445e01d10184886400301030810803c0003003840c00039a285074083d8808204089502e0300703030f07049514004031264030002e80d000981301e540307401800290b0b00c50004003003804c4010741d029030f50508009421040d140c0401d101300914418185c0c0006158000c090052040425210b802c042c00780250540c2945c14103116100c0c4518023002618281c09900521200b4030031040480034020752510001080490189003049024400040f0104080191050700401005007000041151001c030303041182c0c581c0740c001004d901501a444844100d24071442c042c100902d8a184884107030800030108032000400400390f640da5550034000401d404103d06440c050706004040d820f02501946001c004034824103034043c1d0503603850004043d2160b900b0104250454600f044002050b90300c40c181034441d400c0040d1000400340300e00865003030b203042c64110320303626003c1600c2c1045030f19102d1134181d191340304500070b54050001c14000301031150300c00c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 763630458 1250 763629208 763629281
    0x2115023a11120f06010e040504110d0302030408010e0102120f0906010513020417071a03010f03110a08031c06050a06081306140702030706111c0906150f0513 69
    0x2400866460000d0071500341030b45060980301250146400c40c184041c541e4041024110400115020401810640d40e668803c505207500e0fa800b950012070440300340b40c0280195402485404020302010608880c2e0a00030742c03004501d04014080640451111705d240030003070784101850320080500d0f908041c20005468080302e20f03190340700c1c0c0810001c0340c0014a03544010618250320000e01c443c504242a1049501342e6100e20303005840140010450600405180c00c212900a00c004040c41c0c110800324110700302c0794001c0c020a200000b0b0301c60f1300d11111b000c615904c4007220810072410f0745810400609048078890a40040e822001051056061040c0407030828400e010008810040c00c10304041d07160304891240142c4c00100e07020080c00802d029000a4403000c0e604c8600c2c2404040030b0860014080702e421681036600c12031501000015404070380440140070501da455982c0345010318008040340603150080805000c40081084140510030706030703a20010300184000200c4100d500c5425 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 763631708 1250 763630458 763630481
    0x1b07210f02060f040603063b1914041403030613020c1518240117010b03121803150c0a020312070e1807020303012115023a 54
    0x41140c3c500003c584030007480200615100440e1991401120030b03650322451900043c6210001d003503c0c1900c90140e40c030418106070a5a0300d000351501064081482e11882c2004026858a000e100b01e405051940520a600c9400c92a481e02c40103005e41d511781c04243d8800d504007414040c260089111034028000482c0040201c40013107000320340000071413106407048281440a1305c43c442c102c0000b400511081114045000c803404010704c2003001a040521402800c410111156122001b080d00004140d0300000c1c12104542c0b442c1100d080726070b1200c0c9001c14540c8049001c560f0754180404c1c1c100803801090700c9a40160354000c1c0300c100c140d1011038640e003140410026040c045507015a100d002d1441a81d580c4849101e00f000d2000d219422400210301e401c0d05000c0228071a40081180d0540c0c0340116110b0b58841400d04507148440d040f040203008040145661088601e02d501030301c03175404417600f40302003d070076034090304e6a100d81c000480d0340c20701d01c01c84006a00300030340c2c0102030200e6 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 763632958 1250 763631708 763631719
    0x3090507060c14030f0714031801050c030c01060b1306080c090607140601060305040606090920010c0f050f010513080f0a0531051804060c0509061b07210f02 69
    0x140c0c1e0100303a0459005e035141c600040004602c0da401d020351010f40e03045c035415140046240c08124084a8009100d280d019810810001000c40b032202c0c042c02038540715100d000003802480c0c1c480070801d0f0a0781213040115580c1c6030600780011000c2c40385101501900e0343c101603901c4c103603642003444019801460140c44825014181d00c804190402245008106a560000707040c1002e02e0040c064801d250302008101d42003241160100744010070342c0c00c0d018a502281004070660720016a138144280c51701400b0300d01c4c841c0d0107100b4032070302040c41aa4004624020003031580c844101c210007010421024104410034000b00c068800d0090081142d10268284a030400000f100360903840c428103400300c602c043d07507400000c0c2c50014080c1d180021b41400c40c0c81c1c450441108030011b039150001031002d080b403038884c14401d44260240046641000c0c000d8412959800080c0201406100350040f90045200303405000444c5094100b00c824034444294003800c2c0390015480394040e0003c8400b00740c0c0d105 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 763634208 1250 763632958 763632983
    0x51213050a1a01061404060e12010e100506120127050705060711040606080712051e04050304170a031e030b04020d0e06180703170f040609140103090507060c 69
    0x1d10002550304050611240d11010b640c1808001404640d503503801114526003840144074094204501400964003524401600c1c0e650002c5d0601420005c900305d04217009000d16102070400c6900074034070031041600c400c494040c00030061400c03107158411310055080703490905500d5103000c5084410303181c010400c445029032a04001441d0f50307c511012581800b003240c0003207c50500c0c1c000c02000b084d260130141e41e01d142002005e0841c00c802d103000074259580d24001988007401d031582c5040203149128000d018034240c41d000b13540e0f9004d03020380200e07803440301000c1e030080100184020600b40d241d690341c013040d007101c000728842110035602c810a01d40c0700e4144002903281c600c094520b000e2002c0c1e0110301c00c0c00c0340e071032907082060241c40152400702c1180e95110450f4001204c10840e43c1c00003c80f80c01040101c81c034521405100304600155800040000d0041e600400c10415540b240f1080024611040b005404031402041e008020360004082005028007803000c030183c0302d01034581c50300384 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 763635458 1250 763634208 763634213
    0xa0f14070b07080109050a14060d0f0b01031a1810021810030203070e0904170f12042301090f0b0619030c1707030525090e06090d051213050a 62
    0x40070703821110003002440c598010015541710340541500580c04680410501c554030351110441d50700140a5802000306864080c1040100e04c40c014146800164990540d40c5a241240311090344e02407954820107a407010415006c80200401d55441d004030003000d5025407800c014002c0e40101080100c502001d10350380449071540e0b0700d00701c0b40703a070640c0c3c0050f035074a41084054442d400304d442103400345031668104000500c140e071207861840000702d2415200c036015000a0f046109882c0c03003210b11610782041c8001c002020031807114421031107a142c440741c0d03450090203088502d41d8002410310700b481c00d500c0e0045014801c055811802c00380015601c0c4c660f43c55100c20110f055401150340807440d0100704115240d00381502404032420018000d0303185107441d0385944643c0b0440b040002500c0d200d00e400807407c0280e01400419803500180f24108140d061151151000c407803907001d5000c0e946880d100140320304200d91000b1400b100003941c94441d9a0280c243c001509002c803514401c20400001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 763636708 1250 763635458 763635473
    0x10311040e030706322e06021f090f1101021e100c0e0907050a03020927013218090d0905030304150302090315070306090e030a0f1407 59
    0x15802e02800b0b020400e81c4c0d0307605d03111000c2003950002c1402000c1c0740c102c90b49500e841d001c2c15034110300245200166034481c0b00b025001c8042007854041c00d00140381000448a4000c5550302603511001c5074032842c030032001440c806a900100780108001a1a0141800658640d02c40c8886d02d2040c4110f6500490411046440c500b203195559403e5102445c51452042c45002e00003007480380b03181069103480c501d00400d00d4600060402014008003107a0b007604107200b68145d40d08071100a219502c41d00c6060b960000e84401000782d20640342e41480081040a280c0558011800403e540d8440501003c1c1642c12805424100d0707a510143c040200080d030098001c803a130003052600050054181c1c9540c01070600c0c0c1042c1c0c803260081d0024001005091101048980d04d0751a81c00c02594a40520001a00744503210101108403928817003804050355059104070103403240984100006200c1410542d80ea01803415440002400011200c03181d502c41d007513260009049154080c2070080d15a1000b1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 763637958 1250 763636708 763636717
    0x100501031e050106030b030c04020901080f090118030903050d1e1101060308040308090901090905030405090c070f03030209030c0a0e01030f1a0a021905070f081b1203041415010311040e03 82
    0x500090300c41b850f0b214a441d05010120a1042c00c88045207484a07880000c0c020368001000020060b011030000b942c0502c0c207420120003148000b1701d20100b41100d2902505000d00d6010a840d18030801030382c04207450140d10040308070103910a080744088121941200c074030200d0820400c04d5500c6940010001d49003102600145110320001521803d40c18103000e01c948050384040c40702c60600f40c4c02000f140001c01140c054940a450520603a1ba907401c800a45100c1c03014024152000a0340780c90138190305074041d00105030200d05039500c20340540200b0440ba031281c01400400b03a0100f0040001911010030110300601c030326108910790041410f000f20600c003c0703840c2c1c58559000503e039041081100740101c811000e82c1405810030340315449982c85058100b40050840000207859105107000719503c1007003544602c201e8000700d0f81088181e0340342c0c01c20f49044840040d401800034901c01b01140703614040010904512031a0320315220785040311004410540c01a40c0c98506850303000d410310092 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 763639208 1250 763637958 763637969
    0xa0e0717010b0619080601090e0a0902040b1c02011b0302060f060d1e0317010b18040e03041d010b0c0d08060f060309060f15060409091532100501031e0501 68
    0x10940b441544c0009402c81e03070000c00c001c1c10000a000e0600480c24020a443d4100b4006c080008d130381c0c03905102181c020401065080d03400481180c02500000070000c209003075901c01e9841202c0090011403000c000c4218010080158001c8400144009000218254484d06c010710001e80381450307803110340803800800500311150f0003510b001000d0507006851f403181c55403a068600055803400e5800e643c14082e0711102c0c0030b126000c110601c0c095540c0e405c503520040417181500e50340e6684a40755100c0200980800d111030f040740d40006080c3d00c4500584410501000c0640380c81c0800e107104895410b801880c030342d0310859002c5034400f280ca500300610700c076001400c0106502e04003401c16101d0300ca8001d2200045140104140740700f40c4803e0300f81c4040350000e800c00710b81d041d15031034a0a1046900b200f804507403443c107107510030054882e00d0030072121140c20000003640c0e0400101c4080300c040883c2c00305881120840708003d154071981c800c0d13002c00c8181852035034112401442c1003d0310801e9004c17 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 763640458 1250 763639208 763639237
    0x2280f321207020307030909050a1401080a0203010f1b082212390c09020c060103140f0a03112d0c06070b0604090f08030a090b0a0e0717010b06 63
    0x88030001c001036410302c1e0070048a000940c2030101a550082800102c0d0244040040c0c4480120300030016640000c40d01c0d03030701000800300780c0d038590b141c1a5445c12203010a9200b5801c00502010302e81e41c9100e040360145c040c6031000080c1283c1e030000e84003801c019110384441c80c0e0182d203081c3e0317004903020785908072031050303c03200380c0902d9403800100140d8000c10b81d2081030302d81c0340c50b515010200854205819000d1114103110041a0500d00400382882d800300c04814000221602441000b1400b076040e01e116406481840300791032210340c0ea84144201140003030740725900c0d14010074010325414500403450012180107405c91030302c040701c0311481503d240c41f03100c0d480a03100302c8030000d03c1052140d44064809905200160f1540107090601800c400c0c09550b80d803c119050000c0180400300c0e160304070b1950b540c1d078107081610000400c600c0400383d80c41c605a4010034600303c200d0082c6141c1c00d07881402130203d903003030440000450a028541400c0c5640c0c036903204200b611400080c00c50354242144 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 763641708 1250 763640458 763640467
    0x40e120c01020304230703033501030201170906010e06060d14010609120b060f01090e070f0813201c0b09060a0509030d02180402070602280f32 63
    0x400c11110340b03e030000e44040030070400d004200c41000046c0c0c82d0440760540f0340721084041098200c42e04408480f500c103600c04030b00405c950b010703404055a5040300d100380d845800b102c0d044030b000090480169030340101904114010007204084180701e80d04240c00400661802d601c1042c10001c4038070450384202840d2006c0010041c5035046045840100b804200214000103241d80e00c0307140740030091142e403080748280c0785a0b03101d9108030014009401e850050002e07030304107854040d2401c00400304420001d44010001003440e513600340c51460207980409508030240c00c0000c5c85040440c000620b03600103100701c144505601030745446907c2d0700d01070080b20600d410080c0e0b9090602c440100359a40d202e043c2818091084000421201c10340900540180c6403010321400f00110050460341030f034054004212101402030075401004610240e00c0200b403029000c003c40c00364285800c101380d0101e0360ba154034140709070107080e1041004060750001102c031b0f40800501482e01031802da000ca80c05c1d00220313 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 763642958 1250 763641708 763641713
    0x3040639020a050f28030629060f03010b0a0e060a030f05090c0d020105030703060b040611010c08042301140403050318070e01030f080d061403071d0105040e120c01020304 75
    0x20079840a0035096500c400780c6002100170a040c11199454140c41c40308108180e40210001c2c2480d4000d180d2003002440100f040e04601052a0f45a070054032003580a81c40359a4030303282450885042d131041074103c2d400e50b841d051009401e03401104968080c0a41401180001c1d95080c0090812130742a0310001130201c1d54015201c12101d004000c84282c1c5d000814105d8039030b43c8c4540c140c420582c2460303d60364955844da400c030003401c001d030701c5103034028404280803a44540101e000f908101e1282c00030030a03500c0c180030403204000f0607100074080070007044481d8030580800b2108101c01d5098000403446801d0550701c0c1e1440241200c05400052000c814440441e140001419600c01550300a040040c1031030701d801c5031180107101c01446032800e0100c820400c02e490090300c0c00350792014410401a969030b614142110104207580c3c4c86030140780408100b11410040d40070694102c2d0040e031541da070800003070100500c0c3e425800182882203103e501c040c04442001448000340ca8800503890f401c040c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 763644208 1250 763642958 763642969
    0x40e0d020d0302042103020a0b010306050f0c070c05060315060c01050433020315040507020a02010201050a18060903030b030a110f0402090d03120e0f06010e0f090304063902 76
    0x1000c1d070040500411040004410382c030098041100f605901c182c101001c1c1ca07040e07103000303003118000302403c541200000900129501507485000060102d90b000e0b5101212888941b05060740101240c2004030148460305015000e164041c401d4103600007076012210008003607802042080e4401e030b442d00c0c00c1004000150104403244a000303810303440068100d400070281c5002460051035150fa020000231007000c0c100103201150b00000e40100818100010000d44070090780c241603000d5801c1401040e040d98061041c01c441c801d200e032080310040e4441e61090054060030341c0c00d904054031040100301c0ca81d420310005480a10802e01941000300704010b01009140501502d4480d034418030100c4040d0300c030a003042c2d0351281c0c140b400030400307185051000010004110151040e118803000350700003407800100a8142c8074568401061540e070250740f003003000700440e03c04215070024030007008090301501ca00401e00400100e12031001070060468610402c60320507030b40300525490340d00070550619 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 763645458 1250 763644208 763644223
    0x21608030301050307090c0c080d060b0a020c01020c01081021050105070906030c1809150317070201020609010b01090317120403030b010806030a0206041503060b030703061a0c2109040e0d02 83
    0x4a80c180300e182141d05002d400c100041d440274141c0300001031041501c1d98545d004070041e21800742e2058441014900095850710365518080c0503204081180c88590300a8400900c00d259058007080b00e2402c0140100ba000ca81241c0b02c41c4512004000c100040c1080c01128402d05a503a5400d43d89454a403005081c0c50881072440e061045074560300e4154200c02c201401503900c0b5500c0819001c8081843d10820000360b0302c040d0048290050600405020b00c000b006000e000341c3c21903d058407903c1c0d80c1800c9420705220503011541d000740400008140490580c01262030100c0c141c2010702e04003d00c0003d803003c85080b40000d50340c1c1d030402550b60b0448150380d081f543c260300070182c00c41c0356408551284914010b0078000b83d01543c544540500ca90440710150800d070341229180d040c82440030300600304d140107401038010f00803070500410000b4015250702c0e06500008010075103400010640b90001207030304000d004010086500382d9111801200c007045640401000185012a03009051012 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 763646708 1250 763645458 763645469
    0x2060c0301030506060904050c030a1b0f15141b0d030c051303030509040e03120a06060f1b020a03080a0815010203041215062c0c030702100b01021608030301050307 72
    0x814001440071800026009a0042080d20010039a407502e0070b040d45000e42d042d440503818801c5044010400c00b8443c0125090496681e0741d550003512000e240308130b9030080c02501084c85681c803485013940c0c404c01c1101800022414001e1030045d4a694030504140071309080c0004d903011900d4080043da05200c0d810b28001545880d604203407407451030f0200d248003071001800300080804d0a02482d62240e0104294039180402c4a40d0350b1600079040c46080000c60b051103259241040015407140a41000224250b4650780e0007042d85050980a108400415050344c001305074000c0440040c0d0000300038005031100751200b480c1031400341ca4000c89003c24800e00790445d007051000300814075000f803407042410380c0215040488800401703404014400c3d580700c0c02031150400842200c038100642560355040007807512840300d1f901c0e404210002d110545103000107911031070078190240c04a40c428440400140f0654001450704200310740d03a0304240e04035041075000003004202610b401c002d000002c05 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 763647958 1250 763646708 763646731
    0x70512030402091501180602010501150203030709030f0c030209010303200d121d06100f0608150910051f08060d0803041502040f0f09200901050a0c0b090a030206 71
    0x50a90b001c078402c1e290203804d1100315092441444003030b0303000c5c407044ca41c00158540614191603071140e0081c0a40000e00c22500350040d007008180304144007100700c91040c0f0342500d42c001d07c00c1c696940c0301c600c42c04034101915000c4460201200695482012600030360081da5207131054220207100102100201840c011558004102544503540109441103540050b407400542402c1580350002c1d00c000301c2c4c0e80c240307150140d401081180c440c4400b20505481d2500c0800e010340e07403544025540c049060350801c0076003080c1e90010348103141036040180c3c0312603c1c00841885c207558001040303c0101c485001004484250040203c0d03a500a100561140302203480500800d0300c1c0e158012140302c0540090304000c02c0c5000c105903c110303501110028a0060004600a5651018415a4407240c0607481c401d0b0f080006030348401403001d41e2106968190313000030b0318140180e00155110f52140303122101b403200701803024021468000c142e80c801c980010240460b00014500242004070043c458a00031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 763649208 1250 763647958 763647961
    0x1f030b1206010909050f250b0f0403120c0c0902030613050c0307180f0602100c030203041a100b0c16150503070305100e041b060903051009060e0a0807051203 69
    0x5000010420304540da0743c0030014100c482c40c03e12034140340708081c200720607108602d00480c1e1810403c812080c41e042040040e44180d03126402c4690510030845100b00110f0240300c2400461a0f0710200900e1810a050a0106041583d121584025140d00c0350036040d502208010081c00c003052000007148c0242c6c010441032601200070740702c0340000f41101003001584510307100c0700f098009102c0050004400000000c954514000355110000d06c0c190481e21f040040c01c44402d406802600e02899100030a07154841c4014403007120305800a15a500c0f00c84800000215101c6d142e0041040384a0380300a450703007641c1b03408100c10003501540302c40715000000b4a0b07100c0b50351703212069982101c3c1c00c1c80e020a07142c40c0c0003084115502d00784c01c1a042d4a143c076083c031081104641c0c202c0502c06042c844010b00701d56402d8141e499604074400907006400c40f845c0070040b441d00754411402144a0308000400318040c840c854607008126004071b0f803241000032040113000c42040b20000c02c6600ca02141d240d03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 763650458 1250 763649208 763649239
    0x9030304031104020f12041b030201020307021e2206052d03010f0e0a020301060609080d050c2d01051b040603091a15090c0f040b0a020102091f030b 65
    0x8034440c92101908091a014016019a8580e011078100034203a4060710380b01c0002042401c61000c0c2540c00311404030407910249030b1a0364010175201101d805030040d600300ba51b60340030700522583d050034030307145401015400d590558603412000c0c0c1004400424050354070120000a0488001d5080307244a0003d169040c521204115500399000601c560b1903000c80e05030b440420f001d8035001c034203011b01c01d0601288010340b40d40000c600b48098000c50003845075503039505007540c454045020311100e035009050241c04690041c0000d0400108a030111010344d04400c2e03014510b058510340208001c5003000f02018054000d001d283d03001080c3e0959881007421028401020303110714880d1105040e01c1c0c45001c1c017401072038000504200c611408038043c80c50230089034414000c40c00c010606c210312a80101d10200c1e0100191655281b0205803585400d040c048102016002180c1c0d040c01c40d90204000c102c90b46400d400144000e203503070242c03003085869500103001e036039090200d28001c66080160200 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 763651708 1250 763650458 763650463
    0x6190815090712021c060f02121003050d0c020d02030706090f090c0c030f0c0b09100f0513023304060908011b03050a110408150603030a020d0f03092a08030903 70
    0xc560480b6440c048800303201044220141c60317480a440f0501e003c401041700000c68008289084405030304d02d480d03640309105448124502d020140c441c0d0b001c407082e0314640340034840303681000d400200304a0f08607481d40d0010b80f40600369002440000d0f0f03101002c20600b04803030300e85400703006111020321144400c840000c0072180c2000026042101c04154a11400e00a45c48801000c0e003111a0880314a01031005aa031070306c9009000002d64a1b02c5043e80c1100309901c1414013a420711a0703a42e018a1f41502041002100300712515244500d4a141c0b03074410a09101e0340d120100b2020b500c0e503e80c2e251510280a1048591241d0f4803030b41800c07907c8440c0d681c0d0b189222210f5801d8240014180c81d02e20030302c00201140715640030050030000e4041040080040c40252403204540032880c10b60b01e40f418903850340103c04250000d40c2c000c0d1011001c0b14042c9407011101052840d001038461426203038608800c4986484020b50306254032540407002d043d40143c00130303155080040d0716002e03d0340003096 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 763652958 1250 763651708 763651739
    0x20708060403270504020d2a120f02092112190f030209060c0f06071b030e01021504060b030f03180114130305031201081603030305061908150907 64
    0x41410311103914202d41c0b600400f815405010045e00840d151113803568030100400741d0b01d9840560720301e052610842c032990700a100480b00140c3d80c46e4409a0035040900c000741010f0101290801c0c0c0030310203034100b9125102080e0088a21541d40032626224286031414810010100c0a081c1810010440400070b6080038191425885c50944910214443c0850003030103520f9030268003000008020034000c5000039600d00380301c2049e003903076007944030301c101038903060000d00c48903004211041210740868040c00e211001c044040c0140c0f107202c0e1b190814052040003c03501269010f54a136201005810100802d12009a0100c011440c01d0130b2a5140b025100080800034100042e2849161503485001d080d251850203c03907003001d400e6160320345039469401c80102030f401d0140003800082d0300c24002443d444041c41c12071814440314210b4a044024290040c000c0e0340020109001d40d80d54406210120002c1c000c1e100903014810748491704c00203503080074100d1405540248020700803850202c1414 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 763654208 1250 763652958 763652987
    0x607020609030a05070b120c07030e06130e01270c05181c030206070f05190c141c02100e06010b07230106060909150302090a09021c0201020708060403 66
    0xc903126401140024074004121200074402d000e020400600d40381040701030038000e0072102d8946466956900b01c14450b0050940113400941d01408c40986424031500a06030700900c101d59080b42034441c0741000c20524203a1214131440c0a030b211200818402100d0301c4007210030400c00740b040c42c140c01c0703000780300e4064130250030031445802c1d4030f9605641e6040c40c080081c01280101c44008101410301035141d00044485d403002c01e40900400f40f080d032007034085520600310341003c02a1100d046d00101c4011250410403100c0c50b1400c80d5481c8055010420005841c822981c220144200460001d0402d080c041520088a050462a0044d200b01141407419a0b40100c58661181100c0c205071008200000d9000b40003540480100000c4106400220544665848030a41c059a440040c02111140d6000960705011110240014500002e000b0380100035110089104030164001640120800345800e504210a08000e011540c05010900050240ba8064065440c1c1902c0151128042d0001d8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 763655458 1250 763654208 763654219
    0x309021e030307140a02090601090305060406050705160b220203060406020706090c0815240904150e1509012d020d09141e07170124030b0901020405060702 68
    0x16000300d88040003620768154200c2d500e04422500311a58a450700d0f07240f0000c0c0d004e1405000018550350003090f580c1e0440364460700030181903585460728402008090f10319070810600301b0480141201717440898007514082d2102c2c940754101480c40c06000c0e401040540744d03401c4414072040251b640031a500b907200307030030010150391820980b8107a0020046d035400246070200030200440e0b80315001030440c42004107106802801d4480120040b917422501d03051051420f1618220040fa0815407411500580315441c92a0745442c45d405c0300c2c06640c0b8400440300203a1180c405c03541c6004500d406150840700b4100200300d241400c01d00032081e660640341484850324104801e4006090550484d071044c0f031103400420a4110a20f0450003656141a41d051244941c51015281550301c001411600213000020b1200e1440c00e20044a60340c2160310b190700a540c2c03031050741c64100450070780400c1030040c4141d003000035003103240c5074030030540113801c0b103003241c2c414042030001e5140c5c3c904a4005e1601120f4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 763656708 1250 763655458 763655509
    0xf0f01090e100b180f01171c03090317161b0201021c120501030b0402011101060e1503071d0603070e0c04030209190c020102090111210705150106050a0f030902 70
    0x1c9444c010a4a034a03a02816000042100d00c0c2c100002141c162039008100b1a42003003641d180b180e450724006100220fa0458903207026203103000e6441500114800d0408c80c0500d48503800e9910340c500300312002140c0c1d003000c1c221103000c550b00c584010408034840c1440b41c1446038540000350307105003c54408001e07002d48585045410700480140e440e15000c0031080c446581c40b840c0800c00040182c1d001c90125002c00040038079618107000341e105450401240b2200c982e11802949542c503800702e40941c050183e881701140035103d04c030444607041c001c100814035900302002414a4612240d20156040802c00d0500c00c418403282c04a07011603404541200040c2c44000c80190304108100701e84140e286400594a0b441c0d80640180824a00c01d03203c0e0801c000784c061105071550300e507510f540c4c1c2034481d150200c25601c3c1040050030b584c1e070044c0304403070143c4441070a10740800c01c2a04088007044c0041058240c19620441142c1000402d00d010712148c1c0e569800701c6c006e10381c030072480d8141881004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 763657958 1250 763656708 763656731
    0xf09020307120e0307030905090f0621010207050604110a0303020c0621130c0f03020f0409060b03160906090612030e03190309090e030301050102330f0f01090e10 71
    0x1a45800e440d12124020041c583e00540c003603580307520040c01180407640089000941c1d241c004009440f03410320607102840ca80c0c90908000c808a401c41480080007071044405080344401d2024141d054460300c02402e50b800c150808050098040c0c40d12407042400e01d00070300001c0c0d170208244810000c26100340791140e017810550380c628040d4541001c5445013080c108520380c441e0508040c90f45024454164400c0d417030326800c10300302030140000f9401405210481c2098181030303001000c1680a00d40000315065520300090402c0d1030000028683c0443c1e55003804503030742034440c500c010040300604001d42450b022140341d024560503005001d2004803c8914815107090203010521503a111070b00c61948801d18010348507a1850180e84a02481d001058412403000000c41e0305030303041600140386071001c01888810050358480107101541c3e0420305e07120005c0885039101c0c010504500c801100f450280141e00f09100160b0002600c1070812180c2220000046549000310b186202e01040858031704 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 763659208 1250 763657958 763657967
    0x60d05090a0b091f0608030a12060803041215050f04030c0f1e0507050904170304080904050a02030a0e010902212d1002040e0a0c0c060f0e07060503010f09020307 71
    0xc4201a000c804140100b200008001c1a80b1092030104c0d011012840e0455a4010841c0d0180c00790440d40c1e032040042e40c458600a00d1280065001c11501103101c9480d620b16a0642e0440d9200844080e1a4085401001001c0014440860900508010a1410f00300f0f100609401030805407e001c0e0b0708092606102d0700c41450300d102900448030346400d00d4000002d244645140000703641030700030300f2400301c1c00749017000406026a802c44941d0f081d0700300c00c1c104580039a101410468440a041001d44156102c1d401000e11800084100588038a05101140140c801c2d19046600c40d9142030b21071710041c0e94403015446210075001c86000b140007243e45503860402c590000018003898080103210107402660982e5903000c100c030503180b812901001c00c034260300490040c2d17490101076400140f080c03400703580b01c01c02090f060b1600251030707450741c3c542800302d070040400b140a0308c1d1150301d203c11181c020481d020003402d21f490490310b158075100000ba1010054060255041d0b00000811402c500c01c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 763660458 1250 763659208 763659223
    0x170307120309021905010f0c0803010b0f0c0106030b1902090102121815030703060602030a140715141821131e090b0409050c09040203250e0603030702060d0509 70
    0x1d8070024071300e0800c050440c4140740c60b215640c00a8003181130000314600c60141c20041c60341c03000e0002d080d6424552001c1064020381031560b0b205209020241503010b09005400065024664402181c00c000f05009022400b41071850b003518010410000c0c1d80c0da00041480d401000924008d480d80644040300e02c2c4036200008280c0d10030312200c094044140e104c0300445c0244c40c00d460030012103564680580c1c82e0301a2800c104c0110740d202d88404520400d41d002058002e10419070034116a0208100e602100e41e655903251009812908002075010808840d0131071240e40d0004021600703c1c81d10201da034094040b43c40018a0b03000ca000a612100c2d4445200544104078010500c4c4200181c1d405e4594054411140e1041c1481442c1c290350070184680c900e00c030381000250450702e500d0f006201c03034500064822a014420420303403c00c1860008603082d1b0348040d421011210501d04403910109030005010b507031003504104104001070f40d64000322174681c03514100104580e07490400c424100b01340c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 763661708 1250 763660458 763660463
    0x604291b1b010c0f260c16050108130804030804060c110103020333030a1a010906053106061205060406050109170708060c040806090a02031b0406090f090b01170307120309 75
    0xf50b440d000c0140d80d05d00d00c0604095001c800440b8162083d40d141030480c02d032113209081c046400ba0b0040368149030300c164100c044074001c007030140c6050350b607030364201a6038080c0e404000081c2200d110501002004050008114800d103015425401c0010f041c042d123072614511561030303014803003498400002109080d01103003002410380d41562034504010750404141072440c1c8052011000125950429208135001c0d40d4010340b0503140000085210b401c3c58400d40d8800c1401003038078900c810204c082c2c0c000c41010b400903a80b520584d601440c640d00aa400241010340300d04c0c01d1803401e000a0b41d005804500700c411000a040492801c115124205041030700076006501a0314200071807121310f040144110b492103000c40f4030703550b54240315685401101000a5040d08404c210040205e0401c6455041c1d50b030082000525585d5420b901084864407022502c03d5910b0320307003030030610000985d024010013640e11003080c0b51021010603030f141c4c851f4043c01081118021030000071244694420400140d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 763662958 1250 763661708 763661753
    0x1050703021b0d0203030a0b03010219020d09080f0a02060906040e1f150e010503060102071e080c0109080718060302210601080c0604291b1b010c0f 65
    0x41015006020354401e440300c0d218000807038403402c100d1000046022803c100b44c0e000d1360654841c5880d0740042c02d40c50124540c150340902c400c99082c6606914442000c0094004003070b018400700c03010b06600c580c2d9208068981001140f240b6000001c550700b02203a504850f1300d903070703203000100051080c02290001c0f1900004001040008015080140418580d02c9000e85e03400b40c0d82c0061460110012090f000041d0340061412965401800515085501401511400c0d501c466040b43d0321200b40503800303420030b01d008081210980502c040c030300002081c0380c408211420036444a5683c42c551091060600b24043c520071226030650002000c0d643c010151007001c0140d41e0b445003807012084810800c1d001c0c05c000080d40400009106015210292043e8101858101080e00f1440c400107a21150120680707010240e4a00c80d0041c125000320344140241486400540787c038050b83c2e4186003055049801c05803802d03a81107040030414641c4840551a50701440c58104410f90140d80d5140805 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 763664208 1250 763662958 763662961
    0xe01030f2604140a051e1c11100f08040f05070902040603090b0109061a03040501020c031909050303090d0b0601021c0504050f04060509010b0c0c0a0e01030201180b03010618080105 79
    0xa01c0d100005008841e9070440c1090f9401e80c110410014074058400c00b42d0010b408440c1c920904007080d0910201c80c030040418801e401c2c11b1001500362040c038401220542d010400620551418011104070580f036031a0074a83d0a00d140801b400c1024041d001411000e2030500800400c141002004060000001c05548850342d038030740a806040342210403101d000ba00000803844143d50312440702141c41044803041000b0900b40c0207401c0d54000381041e240c554003008941d0a450041004082200e610029640d414028620041110941e90001e40c880d42040110b08081da032050145c0309420703000441641c0d2038447c040180c6c61f0483e00046000300d014025550a2030036080006001150016611035075920111400c01007222283c0c043c666001030010b00510070313002c038070b0094513017003002e0011a19035460f203800051079000c4541c09614091054001442103503405103411150542090341900e0b8642450000380362808140180820001411802d80c841104800d104000b40b0303125000304940d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 763665458 1250 763664208 763664273
    0xc160611030a0c140306041505060a0509030706020c090a0f090f12030e0613030309030512270d0f0f020c130f1d071a0c0d09060201150e01030f 63
    0x4079081110b010341040d14184000000e60300600c01042500700c810070f480d2460b60b455042000070007183c5400740e0f141c24203407004102c90720783d44000d05101603142c0b83d890325440f0603002c0519000345500700208642101618240b2130301c0321610160486006400490140c88050000c401054088805414180c59480d200b00f4080c6140420b0140821590103011454086041540e04d803825500c414110710700d070720000042407090780903c001034800d103001403802429061143c05002d003130381c8543c182c102c10104417031213124074640006c41700581d1019100060f0201030140400d141c84064209010342c9826a0744000d2080c4075602200d400108030788a0011552030410041109e122441c03d220728044000ba0f0f0000341180c0941c00811040082030214240700001c90014040003c034008681d00784030b259a100130034841c0104500e80c44d5100e680c1185890b000a0030b45003c0c001c03040b0100c103400014004180c210b40313030605603030300030034854042c843c20725140710f10203035010b004582c80703500000e503494 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 763666708 1250 763665458 763665491
    0x90604020d09061b02010c0c0b0705130906050f010906121104050613050909070b0a05160c1212082703090402030124090608012303010509030406030f0902090c1606 72
    0x44e180c0e8400018502180080d40590895802d01e0103030010503110017030080060f00c004002544140185004c41c240384014485450020050b00a200000e0721000140802e0910006401800d9024a0054100c1c1d142a0001c8c020054569002c401103444120551002280f2011940240000340c04140e03078103051a00302803540040d0007258820842c042c0403900c00800003a00c1000d4440719807000385442a41d4a09803030365031041c2c82c0b0950440c607420480000c1820761040c94014403c3c803000b20310b120182d2a0009052820715030090501c158035060107210b48030085107503c0c05004c0038603401c4d940c008a9444d880d42c060002c9075541300c2d00020002c00e480e080c608052400003c82d05240301d4041c80108283c801307812a0248000103113818004001c92445504001c1c902036842248800c0c11824502090941d0b00031500d41d08650f10010b0104002c65251103030600350444003904201e002030982c0054403114000d446000000030102c0d035000d521201602000d0810382c031405c104250440da01e0300c0f80 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 763667958 1250 763666708 763666721
    0xe13020306100b0a26180f120a030e030f040f031511090f180a02092103070624090914060f010303080c0c070e06120714090604020d0906 60
    0x9000303004450100b0b41c0003100099001c20388000d68552418803030054801c032211207140a18250301714502502480748204182c000c1c1c05a019244136160031482c101040780391250589641c05598445201d0b0020840b80005440c1a1442e0307140111b0245010030b10360b4614014501c1d41003110100043c00900b111100522200312032050005120f10000300c01000708880d194800f14a150100300701c2514945441e1121b01c556000082286103600441c24150781c2c0c03101704a40c25103031070341c2c009986070040c5010322000365120100e50683c1441004411810740740d002e03000b4014412621034107111008003d402042803038400d1050748031030031a07841c540d1002801d10482c0503910100c0303490910b8900c141c04a4080e10510380319980c04c03042c3c1d2075a40c007140c07032160080c94200d4409040c00301c3c98585005211507401440f40c400c160790f107824807404203c4641191076030203a03e98807402c006c02140700120000e80c104142112031114a41c0c0d120b0204004e446003c0518402c0c85c60321182c0402c025843c0e0110 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 763669064 1106 763667958 763667963
    0x130f0b0c060907030b1f030b04060c0201241a0f070c180203040506190b100c0c0602030319090c0b1c0e0607021b06040906170f011e090c0e13 62
    0x808c044001600c4c01c40b810f607200c42c040c06459509006103042209284e0080c00350012407082e10315400442e105140000e03882d141c1410441e0040f00035141d80300f0b0f1a001e06a541c00c51858104c6400c80d00b130007800c3d66003071584c61a1518900c248240ca22455201005103010f032150000d500c0c030150300a4085007038980340c2c03582240c00d07210348545102001745520b40190964140c98844010100b640180c2c0171907009204220040407103030b040090004e5511400540d010135424203c0c4052881d40081803038070000240d00c44060000004605ca03669a0390003004480d19941d034031a20b9400a513146401a0f11440d901412a40000210440304100410b03040ca4156100004400d84080754071050140e4000001690425410301c1b40100d1090384000070040000000b80c5842c119100c08040c0603000d58410b00f1030200f05240710141c010300040c010020b030500d44100c030b0092906101508 = true := by decide +kernel

theorem cover : BRFrame.Cov 763489208 763669064 := by
  have h0 := BRFrame.cov_init 763489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 763489208 ≤ n) (h2 : n < 763669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
