-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4717
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:30:48.487948+00:00
-- url     : https://prove2.me/submissions/22095ba5-387c-45c3-af22-5207ec04f86c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 848201438 ≤ n < 848381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 848202688 1250 848201438 848201467
    0x1051602090421030506011e020a050601121704060c1b03020a060309030e031c030b0a1a040302010f0216050f030c031b100306050a0902250506180a03090506 69
    0x10006980710907140104030400c9031084600880545680144801c54050b01c420b43c140c8038191240341c0441c404500d242c000810049250b02500024812142480b005440e541d061410a8000310080c0d4094128542800740f1803603006140c03503082c042c052a0900d0100001c01c0540014001800c070890300c409406c400380d11000b1500a550010040410103540740400390041c006201e080303020402031041014940390110b130088206000c3c030b0900c40034400d008000c030010281009110f03807042116401103440d030b845421404400303803050343c0a6035a905500003d08040f014184450465001c0300341800d42c022607071211002c032981603881c118142c1101000908141d0301c4c0388000e8051140d4044004860003640c01c003040c40700c0555550f070b0031403400901142175484a020f442d40084820804200100103940202101611100c81550001c04c4201c5407001d00e0103403100341c44d0743c0d00100c24000cbd01c4c040070354080ca007843c0d020001d01e242d12403503a011340348000701d110743c80c031540c00811102c0317144002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 848203938 1250 848202688 848202727
    0x60607060e01022503020d080c0c0726190b060d02040f0902090112020d23071502010c0804021f0e03012a090b030a0b0d08160201120c0e0105 62
    0x84002070198940d501d05032030003074200d00c4d002c00d08020b9401e0140c510f070b41c0c0540714001a9400d503000d000140d070384c4001641d54000191040c04c252104116071300720000c0031300410780585030b540791a20900400b290100000110b56040c400190040b003401d2665410b090750b0a1106a440344100c2ca4650b180000104460309482c006504181400f1501480349496400001e505100b19500140c9980303e40b070003d801c4482100003904416441350110124500340d80120785203551829030181e505809000340c0c249501a84a201e2040410309986034998080c0a0000c2c142c146181c00d000c1490301d900010002d42d6003801c850407031800800580000d070310a4007030514440010340284018410400c04a800b241e1300341c6084907986440c4c0b08008810300c034490b44000c0b1090408400d0a50700c9629015004100d00c2040642c8580c490000c04001200d50b0007402c03c400c040e4146914041d814000034107031405c2e074004810300900e0441d401101c9a08004d40800c580c0b02071034110340b01c0711a811240c094140 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 848205188 1250 848203938 848203943
    0x5121906050a14131e020c24150603060a051216080d0e0d02240c0a060506040f09170f160b011703040e011401020a0c170d020604020603060405060607 66
    0x84a0102060720854140d5000c0c0009054070712000220241611130100c40d014550744003030101614840d42c50100d1500500002c10a032000d981104c2c0d9074000039101c60380b10b80544542148100100036201028040010380c82c081030f41c4541c954940000000d800780441e000d440d200d01100d5014208103001001404490b1030748081104045403601d4001d65a45409015070380040c502c580c03c038202e41401116016516406030500f0341c107a0200e040d490780d1409449502010f100c050020001d00101041500303413150182100140c181080c2d02403000303880c0308800d90024582070040c0c03040083d0781c540454015150800301d02d41c030350702504004152845601844100b04505450790001d204400301c0b200d040355241c3c1844030b0460f00c80300c010f0351203000b944a102c8445100760010440144c080f1240c0d0f844120504c15103103217070859030b540148168550480801c24000f1425120311b0401000342e144080000d0004044918140d07001521070701c4000c0c0800d008545403000720b9201c2d02c5000940d00c0071603 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 848206438 1250 848205188 848205199
    0x403021507032d201209240f0c0901082206151e0e0720010f0501030b0604090b18030f070803040201030f0e0a110109080d11010501060512190605 64
    0x3c2202250310720072035280c0403200c4a186082604180d400f88404020303c02e1070040302003400c03e0800301003142101c400a02207070850090300206124000d140340c10f1076500304460880b00c09805c022404e0429014002c1085002c01c008011002250303801c00c80309540400c1c017449040580e03100840b41101589031300002442c0700c0c2056100144012180c50311019250454020115409011014941c400c0f040c440c100c001454070340442e0f901445002600ea0028051045265080c0e08800060031078a0f150a980a415981c030f005108001e10000c8036a0007182c1120f003849064890f455111880760003414000710084981400c01074440140306448502c800c0c85e1885032075002a00303214286900468049001926141c404071085445200b80f04401448400074046801c807540c400f0458440b1142c1c0a0500940d16000180c090081014000c03034481555100c8090b42d8264601d420b484044c0c100e0380a000051050440560b1107100b080d0b401901a60b03403401c0003100689000041945030001500803 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 848207688 1250 848206438 848206481
    0x90603160f0e060a03080d0e010b28050103110901111203042004090b0606030a0603081c0b040b18040c03170309150c0301170f0102030f04120206040302150703 70
    0x40c04080c5441200e520407290041a5075100422913031000750301009002000078403400000da082c90f40982090741070721000103044090a80040c49668000b043c0031070401d84901180c0c40100b14100d500300038034003801c0610020028050a14a502410803071504000201c02c5801c2814403c12001c0d1030300b40088680e03070380d80c02e023424030b82100700c036003040110403000080159040e401c06129500c0c61581004140c3c40700c1d2160402c00080c1d501c0580319200041c1c66034004008900400c000701030300c03c01210f00700494440d000301c04013a100d145c00781c40e1290340750084401711907e07a5121030216404100b001e01269580f803030b000c0a4410140c102801807081201204146c0722440b0040d0300070031564080798142d40c003001c3c2503408040f0499240411450074401003100c0201503140350351507000399081d102848810300302c07542240c00442d0309035600d052040500003405003440140382604451701c0070b0441803034140c402a5031400c024910086005490300003d0400c0e105e41d100c060b10321550040b17803898 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 848208938 1250 848207688 848207699
    0x1502070306111e03070c121e030b0102120f0f0304031205013c15020c180a0b033009034204170f070b010e0711060609060316 55
    0x58001070150b9032856000020752980c03c04000a8a02c29070759a82c500d20301c0486d541c2ea100d1603e40c40c4001e00c0c14040180300c400c0404595205002454019980c0001c00d440740100080c0307003121407000700503244002c0105c2800c1051803400c43d0101601000e4043d52502c95150840303200700c813109180b2115241c10008030b031640d4039075102036080340108904c4a203170821700e410011a0481c001381151115003858104020f5030120382d103d0111071380d40160707210702c0040404a840010782030712072541b06159204200e0074005a1090328000c0405800a000d004207440c888505001c031801400c1104a050140c8052019184200e4141000180a42d4207520740b05990000d550074402d0340390450680c8889040340291010b96410925003164240c000b5038407141c40309050112450071807108a42e0820a0504ca0f80350303e4001e0414511501c5490b80a41c50301d0a1200c1c1c0c1c400c003030080403c102c15190380b40310310400060400c1c0c1180c41181e0003e42c1c0d85036100003902d4512141224815480342c1c5800188 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 848210188 1250 848208938 848208971
    0x110702031e0c0a1d060f030312361b03101e23150f010c051002040b04090b03010605060706021803010e0d1106010503150712020d022d03011502070306 66
    0x690313501c04c10b0101c00d500c13124200103100c5a0300381c410790541e0040c00100b00d82800800816045280c0041c984280040401c040500404d141107070b0303601558403e074035205034a0420920825488007101d840030941e1240000e92103040c40c0034114050b03901d8800c0c0d82e030000001a41002c803404201c10803c0b00c207005044800100d01901c122000403902100001c0102642c500c8480c1200e200030030f50200000081d0065400b458000815a5248120b0100803808541e601c02400680880322000c0e85540c5050350280569044181c418001d906080c01000310b900c2c1c200a0300c40c2c0355071010307015071142c4500346180342031841c00c047c1552540c00c01c2c844005d10714000c994106040020380e20b095000b80c04940c0b40c3e50b00c69003032280030b07051307485140718100744c004050001b07801110383d150803c425403800980c0c5c0280e0300b2104d01d035020f1503800104031598103459404460307020407c403201d4800d030300c1407032a5140c20b000511800003441d0f0415201400f032071003440340700302641e4007400411004285225400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 848211438 1250 848210188 848210219
    0x6050402010e010801260c091e0903040317030c1306030b19081b010c0c060f091e031106070f1104150b0708090409050f01050a110702031e0c0a 63
    0xe01081d80b80704100041d51069134200d05a0b01d00384145054012103900c1d210152180c41000001c6000e890f5200c0c46640c0e1780c40c0d00b6801070a03020001c003505030400b11120102007000c2e0207585c440d402044104000342080740d01554110003040907035102d507030390310b6074000e00c0c400c002d400d800501020b10007064054069104004901c010380b0b6090310400468500c810184c01c0e8010140c9030b60010740e543d41c1e03040026801d103200e0074041c501100c80c00c0043d079030151140302070b42101b4045581000b019015a41c0325030180001d18100311412a1000158008189004039000107090b540d06849410701e140c0f540001c0302d4005a0060280100302007904181103072a0402c42d020b4421424003807001ca280015807030120a8840400000b8a04039956441e05da0603480418081d4015842e002c4d102c000c20305c00d20414841000c0900046040e14040c40d040044039400c0702c0701d0070503200034441880540c600003040500d401c6401808081514140d0569180c203204502079540580c0080010803820124403420 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 848212688 1250 848211438 848211443
    0x806040302120c0c150d2f0702060d05060406050604090b04110a0f0c0206130e01050f010f090e15041a01020d0819022206050a1404031a040f06020c0304140315270703060504 76
    0xc5c0000440ca00032000e910071900083c1d0310ac1e509100140a40303030541d03c1150018001000020a240c1d00c10101b110b40d00705922412005684100c500514141070081d50390030508403440c10b00e00300c81013030301800b00405850200c003040b002c5400b09046407550001c4408110310700003202101c966844150941f0f100c24040d0500485404190795581c0d4001c54080300201c800381c449a507400d041c0a06080c008200809490030203823940d091281c980c496109c2c1400c40c40c0c0b540e840e0342e4080e1040340068541003000d4400c6040007100340400c070540000600245400c2c2c0f0a10000d41c3d01c4001210020724102402d03811038502c000080006849a0407400921054803591164100502c0404844555018070320001e011030189840d01507400c81c80000442d8068840e03081409c0d4428907440d20030480c2c1100c100711250381d00000e014041d030030000700e0100c2004821402400744131846c0c0c0260078103207805016894545200502e50b507460f0b007503200034103045807044101c0319070a6803405c0450140400307a0b0f05 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 848213938 1250 848212688 848212751
    0x405010902060415140a02070501120b060a030504061d071511010501240503070203031303050c120d06080a0f230a0b07080f130809030a0803010806040302120c0c150d 73
    0x184c001020700c21080d11281b004a4016042a614140064503048401140b110a1980d40d0814142c0c0341d079900c2c084c1400300786540e00001c0624051912404450301c00415a900c4014000180d2602d040043d0b140240c42c2c81444404180c0d0680009881d032510a01030030340103509100020032900710740700d94101c054001d40b90302014002a032400ba2098031040e81ca01005030804c00005483e00c101843c0c048020303100b803070124900707001c1c000c0740740c1030841047d0188e5070b50800040201032030702940106405000040c3c00350070b031201c0982d40c5002c40900c081000381074644015182101114038400030440840707210035103c8400c41840c1003082c0b039208456110100711200017040c4104915110039110b4010b00e002502080070715210300d0125007010a1903985407056941c920001140c1002450007420180300405080c200752501904100005c6440f00d800c03582400b070461606400521000c0702c10b016251910704120031482d088203403181c00001c00c481418890080013041d404c09103040c1418950a1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 848215188 1250 848213938 848213957
    0x220209040b151c0b131b0609050103110d1a15070302160815100906030503282102040b0315011d0109030318080a0506010914040b0a050405010902060415 67
    0xc200b80140e00315031540409445483d040c0005103440301e03654024442e9030132441290801d5a401050880c0c010201c59866558141001115004800b4070040c040900f807c0c00081c40b1400750134841c0c080c429424117070795103840e007801c00003034031460380c1c1c8020401512114400b1460a015a00d0b60700206045006200700340000c2056900c902c003400c103481048010f014500c0300d6020b02100b03003a0213048020000a010b0740000c0e0300071544100780041d4450700103541c40e606002c0070f1307220f0035a8480c081d050b40090001e815243c540c2c0410b51160f203160303800000d8408100c00540100034002e40c1c01c50084070f4400402e000d08522400458407617840e0990703461040c0c840c0740c0c00001c1c120b59901c0446011403211481070000901403556002c80d84c0c0d103000d00c03c1d0507036070700d100c0d5901c3d1181d040c00a88694010200520443c01d41740500301d0241036503012000d050400d03603a9000f0242000300800c0649503a1000b042c01c004080d00421000c1c0d400414140d107854546c40c0400400301e01030907641c0815a0b142 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 848216438 1250 848215188 848215231
    0x280f020a060819060e07080604141501020105013003020a021c05010b101d0118090603031b020303090d08120103060609060608160f021204060201051005060c06220209040b 75
    0x60381050303962502107062151100c1d10155106031f00500780d01c0e806030b12000c0311243d0540700e4180a00c1066403220642c007810341c001c00a401c5440c1a0040200755548555904915401ca18151011102c2030520315000260b03090480c00c0c82c270800c0d00254005c0031103c021000d07201d000108201c1d140030b040204183c894020800c50300d500410084000310b404485a01074005102e07185e2084c181040c10302d0b01c0c8040d0b06402c0d11900040580080281303035940c01040c800d05a0102052102d042403000344420440e69800081e5240070301c4c400c0c10722070ba0030041403108020320042076801c480080946e8440d03e5031685013a0019040d613000303240c952460a080081c5541c8a101c4240c000d01d09802a9000181c0307508007100c003c070001000c3c0042d44208a015a050315080d80204002d14042c1c0c0002240d04200c0800d1039001d61700d80c07100e8482c844c1881041e601900108605030410104000c0200701c1032241c040c9001c9005044019601c4460501000140261500303086d11814409a10000c403c0781074 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 848217688 1250 848216438 848216441
    0xa02060a2403020405060a0305120c0d0903030549050619090902010c0203030a08070e01050a0215090f0a140c0d08030403030b040f06031b050102280f020a060819 71
    0x1420074410841c600e1100304054205540000d40224010300804207607920b80d01c48a14150700d00301c40200a00c80007426010450052159542c40403042c81c3c2112590310307603207005119014a0310703005250304401c40310281c0c0a02031030011486450240890907141c5040c001c011440035900145206d00d824800059090310301029031001d40644450004549810304c1e01642c000c085902c0d0490511005050020150b40d00b04060a80420299940b11342c624143c40000c2200e21b004280506000b82400003029554000c6130b2401c3c180c804001c0341109940f00901d01d450a4007103060f48460380070380c0710383e00c0902c04071a0080103441d07203a60840360f1288118043c09400d84d08280085d10361082400480e0009209400000d040c40004002055410401244c242122101d030701c115506404595455801c1040810003802007100340050080e40322148509100903c2c10303c60420b428400b2041d080030089458600c40000e50080c14200301542c0703070080904420307807d81d14000313040441d420050302107141c2d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 848218938 1250 848217688 848217731
    0xe0c0a1e021b030309090f0a060e0c0a08060409081b0606150a08100e0a14070315062304032a0b07020907230405100318030c0213020a02060a 62
    0x140d00802e1226841410040c20000401000b985408104005855582d0360b4820f00d004600300710801c089418800741d00c10885109074007023080c06070003000b040020741d04581501c004030340b00d00748990340340e41d000006001032440d400000c004410104e132480d8450382d008952910228504225500343e15400204003024a1209244554140c01c101c05a841449442c0c155044000300580785151520b030140d4444141d0f00b2120844c50f142c2c0c0c1c1c84100c01810500400c6900450a400d0401507d21104035002e0b200205008040c1480408509841440014221208071180603048a42c40780d46a02c2c0041031034511100c220140410700903181403d502d04030000c422078040350349541c035140c2d0507400c2c4844080010006800d02c180003000d0000c00c05010402c2c81c1001c0c136140400c2d984c4d404e007030801500c810354844950405161451805442c02c002a40d0145140c050910030503800b0280700181d0b40140394801071807158004140c102e1615000645980503610511044c00010f4081014401040c01d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 848220188 1250 848218938 848218997
    0x5070905150d0b13080c101b03020a17220b09060601020f1b06090d05010c02010c05130317090d05010606120e0d18051e040f02040302060708090303040e0c0a 69
    0x342c0d07201190724240c0f21042200514480c1c0038490904100b40c40460420740f87d603890a440d076486103046c00b00c0400c0c601c0044940b210701c1c101181010203a400c002d14480040311411000414030020800540030352000711a40540310011402c960585c2c41d0507500f070003003510301e000244150f20101e4410740c00401d001c441d82c849040205500300c00f4880704011039007040801900080f00300012242c5850b8058111401401070002055500180342d00900310b507000013005c81042420300090303003003810703071000c520882c0d41217a0030408440d02c0411850300c1d03106842d095540111514401420020306401c180210341c00b684407081104903a02c420400d840d0104a000c2d0070b0f4002050b02c021581c000c1d46041e42035406001c290003102e8a071000f003800002070015400c401480e180c04a50b0070329041c050000c2c440da0b0710034154209441d6502040da00d009080c4018865800442c180d0b130315480420035100141400f20005015003408141340c1d0840e4400c2507802c1c0003c0c400c1004141006911101011011 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 848221438 1250 848220188 848220203
    0xd05120f0f0408090a03232a040f02090405160807030c0801031b030501022214060304080703030f0501090603021e0f06074b030f0302070203030705070905150d 70
    0x40d0b4a68501010b0703408183c0d129400008200e001c40441c294400705040702078240302e00d51044d0803130240c051402580440c220224011a070b058050f102003655160516002070303e001c14401c211b6008900a400381000700b0303810529100402001d44104140188800306940f1070784010f89403d842102942c01d100c1002005c180d0140040001451231610181e200c000e0202c0c0c401c200b038403035403603a003607038051000141840710030300c0e00d48807011040794500c1c000d1848021144003244082d002c01c1d41408014405070001202080304400d242c000e400c4485000d0740c010080040d0740e190040d01c0c0c0146182c1c00180c9c02641079092030010700141d14084072101c5402044070303000310900340c10004a544002d10444200305503480c1c0c0c0c16904a200d1200d1100421620900c492903010404001e0b0f2040b60007010490b030030300081050209420018624084581e8900944d95041c9070020910f5886042d100400920031601c000030f111044d9445240504480e00d40c21001051100c00c1040141440a000c0c0016 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 848222688 1250 848221438 848221441
    0xc030403090302220e070801060807080a0b190c080114060315040b040b061303030e0105041409072007050f0a08060c0d090b0705070201181815080d05120f0f 69
    0x500d0001d4120113200c440d5021240500d482d014041c050310804600d4080591100c0814403400c4002e009900162002d40c0091100600d008640c0e07948059000e00540b241103050040340181d030400c5002100c81c10844410f2020741c0030341c9801400c402c070910440040401c900c040450707500d80b54040320b00810f10003c40d4591030081108010040003d5180a54400e40c1c0300702414103500d650000e88a240329080b4600c24007499400c2c00b030145002443c45604001c130401041c082c0e408901190a40c1503030540c1ca144103507803010000c0d210446008070103220402070382d042031080c010004900060b100103a480c880761840c004140a900282c5002d044982d4002e80c0025001c40101d0f805000d003440800000b01d078014241c2c070f44e403016034016540d4034000360001844a0075543c02542c0c44040004a034481c8444c00c3ca0f200c1c54001e000c070202d411a075495111803140c04040d4040c400440500304140580e070007540340c0c42000d040c1d98041c040d442820300441001441503040c2c441018411510a121540703e1b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 848223938 1250 848222688 848222693
    0xf02330702010f0f090c0801020c0d18030b1906230108130212060406050903121611031801030f0506101101110d0f0f09020102211e09090c0304030903 66
    0x41900500460466595400c00700c0705507a1805024222613034a0800528203100e0704011000c501c3d560401001c0e60f0042000740f412000014450403c081e403450640e280300c0d8402070349100c1c4003540e80003400c25100003050140744c04580c0d440b1565540c600104014403592080306203400b204c07103c08070403140c821951000311940100c030703415404140540c81012204851740000d840b030300c046024411540c4444208002c10101c1c0c0b003280e0b0000d036014011400d2410030400603141d400300a0030389010141c2801d0030151103001e107404544021a070301c15262941e41c0440c000005068040f8450f00081c1400c0c25440c445800f8031503240034480140203072004c09a040d02c259040500690181100d6680c1c00381c640d0703506400c0c0e0140c604200541d00101d402c0c123480442101b80c507040406204020b01d02031043c40181c0e000900c400040500c5000d55800d000c03142600d0815015001ca41d595070306c51700740311003511942c0ea0010018104200c0f0b07080111b498441c0c2655550200319030007404544d034032005201 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 848225188 1250 848223938 848224033
    0x41d06190302092e0b04060818030307050906070c0621050415090c0806090624370b03070f02071211060403060f06030212030c030318011b0f02 63
    0x402c42007a54254801844402c8048030b0303540f08117141c1c04003150500c00356030701560a0750404611a404140c100c0e200315519120300c00985500300f070050025100c3c0c11604c0f00340c2912076064002c180c030b119050f82d03090043c000030104144902e4885032403c841c4403070502842540e000d10341248117084200a4507901000800f2500d03070a9980c5d044c6800c0000e900c2404001d00351040f000c0c14080c0900f400c3c0071315500040d02d020703541440d068003180c5c008041525140c8071580d84000d0707c55145000e020a10248403940b041c00c4200e05204c59950740440c110f1510402140280746a03504d81d40041c186000407600c48500740640301000c007030484804080f80c82000701c1030417404014a601d00c0c1565aa0f26201154012415003100ca0748460b000c00551400e40e452825411800002e14a004504040143c4030300c0014210401d1410341c005d0009039800075404004c003c0010b0b50f0070f0107061800b6402a00d02c1d410b8007244c000520455040c3c0c0b444880c6452241c0c8159000d0340115580d1034040903055 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 848226438 1250 848225188 848225221
    0xb2815030b1807030309090f18020f0604050310060e0708060a0e06030102120112060e01050c0405010819020c03131208031602210403060e0304030f17041d0619030209 73
    0x2000300081907000321525400f400144011842a11410b0710546080442002d44050f104c031780b03100b41d02c1c150800400b0700c40641e8501c40e540d4100c6403403102e0041c0b507000401c02d0103541c20103900742c422904010b200c804c1035400f00782507a030010351009040e6120034044804207011554560000e42c803900c10041c04039a00795032908640c000b0000740c02d0203075041c0a50aa80026804402c0307000c100b0440105020782071040b0100c01d04420005c1c003452404007000c0d10307a80700d680309103810040f42c0000150105c075040c04000002d110210155034454004541540d690010803241501d0000381500003010350655a8a014055204030840c0c103556484203940c000380303600e44c400700643c0a490798500c01d00881c001c40300d101d00962072015031100e0170350400d00100e40800c43d00c040960b10800040c4042500c4001246880c2c1c2e014038100d580e0a41d41c90458014002c41c0e00400b4540c452212406540402c1e0304114820f05044d202d061552044174135183d00c5d0411444080d4103d01c101021a000000c85035242 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 848227688 1250 848226438 848226451
    0x301051c080903060709030b060307080c0d0609060204120c090209091603090b0702031b010608030912030c0d0e12010b1e010201060b070510050c03070f18030b2815030b 74
    0x790900102e2030102e0708003801210f40c0000514840e900703008000b03c003101c85070011001e80c000d0150703600380b03009182d44459480402c4e105808019040080040d650003403803000341e1011056445590380c601c100c240c1c02c0e1150381101c503070790010804070f1480a14429103000a0004008100a440d0100d9841000c20761072520f01c10076441d00000c0010400e1249424000d00c2a64001c69984c84c000b149030300c05800c2070144024690411000700721a9500000740d0b0711030a821650369100c461010703845031440c810700640700c1042c010041008a02508101c1d601c05208c030039181440700910b03030441d103822107411454a0ba84410640f80c2d00201500500f909808800706000001d80192121001562508504003c0f58982e1041e4406581e000d0b15004185d000307868600c4080c01c5040202c0040d00b00904005d205042142d03140c00f100710b980007640400003e640060b101c000500f880b562241c3c030a4100c4075680030650080e41c0c2103041e044d440c8030740601604082002c4125034116503a416080354042c228 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 848228938 1250 848227688 848227703
    0x10e0d0b0417072312070506040210031407050408070e0702100f060b121f060801060525140f0304060e0d050c100206040506010803040e0c090d060e1b04020301051c 72
    0x320f0f000940c0790700b0748035001082c03400d440c14160065a555140c024000e00b407600e0700e0b00502c040c10001d000000c40c10b400070f43c1185e88142c0c0d40d2117a4411402040c6546801410300c100809000c09241c0010041090740e02c00d00c15699110303140c0d0035501211302c0c2503658030010f230b028605504000000350b01032049588a44008200c00e90b03566000c3d1860f8110000d20004500500144401030011103011602160f54117a4060ba0070310301134010303000c4c2405200340310600c1000505810400c0f007005480c00300f00075001e8a1402904141810948403000c1032150480b44180c40c4d00005410000080d60215403d039a1107080030b1040c007040c03111110071100101d4840c807808c130948079070365a181ca111907004c82c903a00404080c82d090422610f00001a8020345182d00100424400031b2900c40e42584c0c054070214046a45140040108402d00640000500b5071498401840003a42d8045030b00482960b14001c0c02c2c00c0c001d040007c110881c442032141070340c01000f15800d141e103014502e00000140f07000300c1d80c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 848230188 1250 848228938 848228947
    0x6050c010e060a0f050f0705031303030e0d0e030d090522060902030703091a0106020c09070c17130b032e1a040513090b0402221109010e0d0b0417 64
    0xc028900503090343c403040d00702e032158000d10294500784100d90b8010002c18100c1400d007000c01018150780700107000c413031131000901c0c402d109060094015031106143c2c10125441c103c400c20300244502c1e80071800500c00d00464185204080c07162010700161840113203030700e5001c5030340ca070300303410012400038040d10090300c88000141c1e00c0c003540b015611801c02c0c4d4901140245031407404005c0382c0401845031088011140040c44855400243c410a042c403e5a880d00582c4807603c06554070803c03104001d041041030303610070500101d40f8024140d282d6058140d5034845880b4107015410f40411a54000d2140700300b1000102001c1605158034043c40d001302d0380f2500e030f48900d4a41258610b0120f81c218000300080c00304034a0900301400c0c02c0150301c10f407007040007007030540c0d03041090321018002030710608002060184c5801001da1526519825280c00c1001481440604800e50098500c03140420040420151503080440036a048150f10452050069440b55500c5000940c00c1c58491940d038018007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 848231438 1250 848230188 848230211
    0xb0414011715280f05040c051306080a02161505011202090a0c090f08150a091104150b0c07030507051203222102090a0605060406030218030303040c1502031306050c01 73
    0x49818041e00401c2e0400b501907041501b444241c1f02030b01910010094108001c0d4001d0030350780042e206035203c904d4000b0349610340500440c040d0050300340d800c0d074061072501880700300111100e801c0848103810405101300e03030f40c45031004071082c42c152010b5001010321300014020f619a50101540c5101801c0c003059107901e454100749038000d40d1300a8020340d400b080d40719091030080e150f030b69400300c0c5882003030044070510361304c46000300e6401c00114041d64650031000c00003c204c5500c1d501400407004140e4460000201055460070244410b841d1409114030204090402001d01e444000341c00380203500d01000070392010a00c450071151070702541c0da541004140c80d0100c8030010f407041c1d050100c028948110740100586408082c1c0070000c2c040c50300c403040100343c944000392801c481d664100181c0755050021510050904201d805034540000410001004030307070400b4000747c40c08400280c2603081d541c4000c0e6900d1040d030b0b40c80c203805144520b003000710612920041c030030440800004208642c0c5c5c00d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 848232688 1250 848231438 848231509
    0x9021201050115080a020a09030f0f15020d0501080c030312070c05070b03071d010e0f030a0c1d01060507200f040c030b12030f0f130b0414011715 64
    0xc3c2c22071000c00340c052010300301d6654000d000c10340041006404524011452001800400325440003d0440100c003141b88180810340d1290203006420610001c590f24600210038029800414661012450500007051201d0005003034004e0840c0a03008515000700200c441c5d41301b00d402800102040780728440c11002440500418000b0203590a071584c50341080384025098030800003040841c48101c3c2c141b130385103a0780894030307001440090f103110020342c91040100742400b0a201e4082e0410842b4500021070700520f00781c18404d0300301e81c030710505140d0b21010f0485142c1b00d00500601500c6084600340028070f0f03201c100302144880101190444040c040205044d00c102c2c0000501203545c51400810354203042480c0d11044103100040c501d4805c000c022034109000d45c1040320110800800c0b03a8030f0382d10410400d200501114070380540c6440d0741d44219441144040042c1d4000303495a40d01c42e00407415001442c0c012120f1114008103003511505010350001703807001042000c440e030b08000600101e803 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 848233938 1250 848232688 848232691
    0x209060604090e010902040c0e0a06081509130203011b050708090d120e0a05030d020a080a032307180302090a0b031212011d0118050c1312060e011503060902120105 72
    0x10f070340000c41d0312034060042200b1a803014480d0800d00900c0700318505030750f9901c01083c0c16a02d443c10300d001c180d01c814100900445c40200c6950304a105d04041c0301c039850050751a0548540700b14000d0050140343c500000f588295840d074100803d1092151000140d00b800c003601380c0da24080e02c50124412603403a0005404c050840000200700c0b05d8403440800e08003078030001e014110990041c0b0480b0600380700203550710390741c48014ac099040401c105034402d2081d00101d81c00d1600d03400c606285c005000a520380b100d0169941c0020a421032250a203503020200c0650440c0d03001840c101c1e4950300c28185c940903200c0996042d0b458000d85088d02280c2d5482e2001c3d047e49000c1060b121120341c1480030a60a00a080d421682601400401008400c0141522804100a050300420340f0303150f410264019005a00200501014101c0041400c0d0505442d01d410300303000e0075040c8019100300b42c0046c00c0341c1e008211401303950010081440402c13420381002407c2c61000c1e100d550010301e407034241401c40d0f40 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 848235188 1250 848233938 848233961
    0x270d06021207080603150402040603050d090f080616030c0306240e03010e0319120203010b030a15062705041d1e1518100e0d020f0a020906060409 64
    0xa000c100c01d0802841e0469503507000125040c03140441c10440300007566040d02c0c1c006600010030703180005045407180c1d0130005c0213503403007000c0b01c4031500d0001d000707800c40301180110200801c40c02800160f000c0001502402151901e824140f00c2410000840150010010701c409041d1182000102200c0c104c1002008194803201c0380d40e80520080c000b41540c00114030a0300c070740c5c185805201da0700008030464000c0c80700001001d20081c07103200e0030b071525100d101c943d0503910301c08000021180f0070400210300c64840b030081081503000c002c403804e07030502c45c60040500248014600041d41103085c0005c22210401c03084510406680b100060191419070b4100c14403030048600480d11460100070303080c80c02c4011b41c18039200402001d00c030b503507074094850513881c0302d1200c4010030085070b070380e0b101010300c079a6440660724030365158240c9101501e03180540400a108032400c4c0302e00d140c0b02090441520046801415402065800304526420090481da80c404010440000d81000511600c0c44494 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 848236438 1250 848235188 848235191
    0x403181511030f04050919140f1f0b0309010605510306040e0a060501050a0515032d041a0f040f0303050711071413020c03270d06 57
    0x60480d00060072001c0a00c025005a8024481d40010b041d9200c2564207135281074601e0315659442140300e07200038000604280c107080c50700d481c4050070b0170b420640a104555403101c00c0c0e0a5102d0440321071403400650880007038900805410f000141ca03060046802500c402d0000c20402d840d43c1c002540c0320a020040c0c5142c02100000b10b480001e4012444900810ba810316503042c81d0b404a01200d00240301c21048a03007800000041e0540d48ea40c0c8003800c9882c4100840e00388811502d0701c0001404203000d25445070700303504400101307072400000348111000301681c61811515451921088510400580e44034007920b84068090306189102991203a806583c4051f0301c606581d04450002c240601a4606656050208030214000d801e02d1940c003541460001105e0b502c5c050708544134144103da41100b40161140040c42c9508100380843c03208040b100268690f0200c0c104200303e2007608141311a54000740b102000b804014a4550044041001c0e036103003c3d039120001401c0340c441d501007101d685 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 848237688 1250 848236438 848236469
    0x50306040f1d1506090412050901021204150206010506090a0e0402122401090b010e210102030a1e0504051e03130b07031808070513020c01050f041416060305040318 72
    0x90f0380010003550406003c0c1d420a607641060f481b00c0440e04c040c880c010041c0b29000800040c107900c00c03c50115652815050a9126911401d03072840444c20480070000501c81d19002180d07030301c1e01c079044408180000302190300d114509002c540344111b00610983e0720000a1030b06241043c028401011180340c152000200a0600f0409061100c410380003088501e240104110490345c020009083c0700704219216445101500300065801201c90f00b400d40a500101c180401c42096801041601c0b882680812801040040720411910102d40c054642d83c0083c04148e82c0c4808c801c5101c4a50012409507450805d20281116420710340e944040c5042000060030800d2582c0f16081318410091112000030b1546011070442e603036001401150300c00c4d014410304413501001641210b5107044010001e0005182c019451074900004980580b0010f8503800100581c0801042c2c9a00c800300c4401d1a101080c203000d8210014440140114180544500c10503011400b068100004060503445231411 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 848238938 1250 848237688 848237713
    0x140f041d031b0613080c0109150b10030203150918060106091d160807020304080601030b04110616030818010e250503030301090905030909010e1e07050306040f1d 71
    0x31000c0e89201d15400c03200034000e550250410701380e40103070003040954560511050041c010b1205034030040009141d501d165440505a820030f40760ad443c212001c1d40b20ba40c0c44541174083c1d2004990003a0382c480500c0035118646043ca10f0b1507003200da0141d40f0031502081d44443c07440c2c240c003138003e40c0108262100c10030404034410740802134007602c9404200f0743d040020b5040102c2907265004024448a540020300031842081a500103100140071222256540c0c2000010346006503803d84502c83d0311590148203003880c00031075012130365a4142081d103444640b000c442c4490701400000c41410a64400c1220082c01d0069882d042080c3c0b001e0001070380200b0401762295600301aa080c0c07400d481c0390401a60754040140e9044590011010070f20200e2458a01c2c1903118002c4810b500000785000030a107445010758131440b92803c54640603920003450030742d0324030f01400c54148001035020400507040b824103411114288500000109101d101c042d40c002a0348400751840e032460b806030175001503 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 848240188 1250 848238938 848238967
    0x8071104050604090305031305101109030d05070f0602030408042c060a140112021306020f070506070f060b0409170a090512070e040305090607060605090a06140f041d03 74
    0x20800c0b000c490070081510180d40240940c007004000702144840c03000f030582400380602031068411100f4004000c8030640a00030030b103d40184842c24000d200c1d0240318582c65000750103e40b4880d400c0482040300030129505d000103035000400448403d2010301c0000340c4041020715030b90010403e1246214a000c440b02d40d8005008e004055611420194000b000848040903840d0106007080c41c00400c007040701c440307040280c41451000c021204111000103034a40e804034200700243c00c01410f80301040c1e41c50301084840d0017031020240540c80005104400210640d000121448002c2e10204d0300000c580c580400c0c2d00395208110080c42000101c1589007035201221030040c010403940f0342d04465503001083d40e80c1200e802a0070301890004042000c1c1809071040d5150824014525a9151020300e800e0010301824030800c0d000d8022a40415000030031406102c1c10f86613626030b05000c210001d41040104001b2107681c540066940c007402c0c01e0408180c10402d05507041038001d603503030581e0307030010b40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 848241438 1250 848240188 848240191
    0x1421030108101533020d020d020303010e1602010e07060302040513110a1b050d021509030a140f12011707050d080d0f1b1e050c1c020a0807110405 64
    0x2c0d08034681400040e000440c051650155400c0403500c03103800d01400c802c416004c00c6038035038180700034440040c01181540002c110f058000c0315420b540054a07480d13030690ba00e000a000c2c0e0039001c002e46000405010451142d400c44a41728800030840f40e0108007214100145a080440002e40015080c047c07818100341500480301015802c00001c22440e0381c1d25554014034040104111b120000d00c240002405500c021603900b040a80b90a40c5e000640a0369404900d403540107450040300004001c944d010081d12140e0480d6203035140e4a0903107020700901c591006541050420b400d100b180019036003030068034080c080d68809080740e8a100b4071918a0701101c0c1d804180715080c0c1520342000221400305a6040c01590712002c240004d0b2181310002401380108a40722000101d940c1c28007280d40104070310400248980114030b81c80c28505d0440d07461144800602c80c82d4060791440310118820102e1440004087c415520001c03c140c3c2c0e003603005c3d0b009501c2611070603c52045040c15183c24030925 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 848242688 1250 848241438 848241463
    0x302060f0709030f080f1201080601051f0c1209080d02010e0115060c200d150b01180e10050303040303020a122c01090e0a02070c0509010f031421030108 67
    0x1940320b03481e42c1daa91050f6016003100a0065030003090200304841444141c0e038403124402d1500c42d056840d50045030b81c4130400d103c2c8502c01d507100c098410004035010710203207003c880c564640c80c80300c500ea00c41000b0326000c0e1071b00b0030802c02c24240010304018140301032169018a5030002c109110300c01c180f0350950720100300f02009110915030810203141c000c4810610300c2d030f2001141d41c81315031003a910045d0000110840390410001b24040c030800c0502c2000c3c80d0342803040c4804015450090780110780c001e24555000e03088010008082c0546a00040040c0d0310402c082000c04086460304086811500035a208030050307400042e030b4504110600c2c096003050002807424008101d1100c511070503550304110852520000c0c40200552a40304805030b4003d480110441701a50030031a9a05000794020352060320071101c0c4c0b54001ca802d1801582903812103002940c040c2c0702e1800c640303e42140350f00141c4440d07114856000851a6020020342003040c2e5980c00c0c104a861390300d40801c80d030400c0c80700000b9 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 848243938 1250 848242688 848242697
    0xf12130215030702280201020f0d0e0d06180b010302091501090504110c0f0c1807021c020a06050f151c060e160906030b060609100f020313080304060f02120304020405100905040302060f07 82
    0x5401c00b8a4bc00b030f91211a40200702c070800b10003001c5003007290007850000c003106181d0340b8031003981e001c1c0714450b403601741220f2081c4c40301d0360241c0d118031300c91070803c0804001c2400603981202c2000b41e40b4241e08001050200e81c034a061500503e6446580342125994052005802c40001884549804039070501c512a0209847c036003460017901c002d46030444a040d60700582c5041021f02040791003080401c003003d6001e1340411180c20820100703c8110400c841c1e41003c1c4602034205002c5081c655205442044204a106c400c0e5060b83e460f10050b00c0009114050f5204005c000300d02098035000c00c0d8018000454002512419410642980103004181d940903040c20888282d103500c810480c8500c011043c600224a0800b16004a003148140c902014500d00c2c1480b001c61002d602000500c200c030a10349690041d000d018505030b850302c4603c41c00d08880f1009000150160030940c110941c410300413a0005407290300c030020b40382260700a860035001603118a0810030000c030f10b450f200760480c2c0075080 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 848245188 1250 848243938 848243953
    0x2d0103180b1b070503030a0f0c0203040503031e12180c0a030206162402040e09060606040e0406230703060e27010905030f12130215030702280201020f 66
    0x1541c1c894907078054802c034000452000c01c0031500b0203580550390b100b80d020090b00e6032800c0c50000e08018001040310700f001c49140c140f04c40d030041e000004440071100050007070350a06002029991003c00009455a69038108108040001c1c00034000c05114040d06100d80d1004400e05610901e44480584030030301070804c2403000c1c03000d40d488802b5034506203080586022a902c3d280303000c1c1d400d0014002100340d082c103a841d446012070500d03000f6200703a13104418011110341e50452016070b21001a2412604014108000c0c40103010240e03200c0c0d8041e00401010030b00282d644103884030340288001660148032148280306416034540100c000400640e04218224104803065080c000072200607160302141d1290200e02032402900507400154200060b6a101c204103a0380740c40a1b401100d024181903044400644440302007400240044d801401c0c4112000001056000c140c1c00940007005502c903c1c910f5404000b11604040164101e203e0940c000c0d00ca5480003910700351141000e038501d500a0030307 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 848246438 1250 848245188 848245193
    0x70f0c05090712020d060f0f05090a020a050702150708030106091d06100f0c0506011e0611070e0402220e0d1d010c0f120f08010909030804060b2d010318 67
    0xc042000f00d9624000042e580c4041d090813400508082c3c1c030001080c95080300000d01211030308020000c0314003d90324100d4a03550310b002e10040b80f164502d04004035a080c40204054104070540c00022141181c09030328104442d00c6460741d5800980c003031000600040824030042000f510604404900c0d140d1342291803c0c1100051b80c6000d10090f180104082d9800840b00c00303100314a0a00c400750050300b07403441546c541c40b500d05a8401b0401481e846040f140d0700040303941c800c248001480c072007078016140080c00e1800001c041013010300700345c1c1c0c404021181081c0640141c19059603010a5500015103a100c40c82c990381000c000d01000f10a0126040c0341b42c100d201454041e58402209181071300100206103001703c1c415480c550094803122402000342040c82d00000741c1d182001c174944808440d86e9880760114161020740c80024001303244d04000c90001005a040039102400c01000c41c2c0d0040c885007000c00ca5107001440101e82814000c40b490be141d41c040c410f13074142d00d00352048000c0b5507034a034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 848247688 1250 848246438 848246447
    0x6081b12042a03080c070512030a030e060114040f02190c021207050d02090c160305070308010e190b0a090f140f09030a0e130504140c03030c0706050c0304030602070f0c050907 77
    0x91102a022920000d0f401c5c40c208814424038000c2c0c00c0c0144641007907440407031800e58940001d07050070042841c20032000c1c0c1e07081e000624641201c40000310403100340780b08018880940503070100021b5081d001e014045c0d4505504606080d600381c01e0f41e40040b09a81801000318450351440070030790a0300000020f0003a5110441021203d03a019136954146460b2005070703088a10a003204940b081e0740c0d024400080582c00300050004602903618904180d880d40c1d44001081000d44607000100c0000901c0c64914086401c08450958000c101c00441c03075035980048250345049903042c2e107050b503420340c81d0410fa681c4010240c2040b55030b080c50001d0f207801001070340e49101c1c801142c418000000d00c0126260744040000080404100d030500590905182081e40ca010b4a6019001d1b40aa189141510f007000404c0c0c0300480b0380d0030300411105203000c100350b51540c4000f4a10300c1c40d0204200c0030021603402e000410213144a00d208007401441d03414100c818a003141c001c01d12443c44d0105000100c0e030301 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 848248938 1250 848247688 848247773
    0x7121505100309080d110403140d1e020c09010803041d0403020304180f020f211909080403141e0c03030423090108010e2506081b1204 59
    0x2e00700050f081c1000d080800a6016030100509020705102c01807200100301c4000e00101c0748688590000c04c0c490f4403542d038a403428010342c6000075a260700440034443c130510300d400740301d08640103644c1035451400c08280291000d82003203001c0e41c80054108400100100c2021003108684044c86445c10a554000d483c0e2080e8851503160168500c0103000c1041c403035001c44028220b20800319698400c440e24950283c1042d402907401d1051440c24080a01001c8240c074800c9202c10040f001c0fa02c030400c14800106144041969588000e2102000207101c02520510107040d242c010449090803515054012240802c0d0030f1150304661190036450300c000050b41c01740c0b4082044100c04034403180e81c004c0524074042c08260310110000c00051445019484202228841010340c1d040000f6a46400001e40c0103100c50102c4421410003081554880c0f1401c80e08248081841e580508204c422040c080d00591040d4405150a0302400100615208001894803403004601d900d088074000c0305040960 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 848250188 1250 848248938 848248969
    0x11041a095202030409150e070c11060c01093936091104050c0705030304020d140703123c0320090f03030304170a0201021207121505 58
    0x5085030920300c40b0b000f031080d10082c02c8007080812443c00382c50002e0410110510644101182c0c1c0004030316454440e18440804030303008640034031102200424480d49910014440c46203568401f10400020161000c0020f440b400f24010024502010101c1d401c0c0000c0c5d0240000401034540100000302259841002d00090045510040a0300c021110392280201c1380d0580d019251048403410003003250486000f01400b510200000e40e103150038000184101503025000750710500000b00107140011400e9241e6200b80340060a080d07520a48510740f400c0c1d500220f0300c0701080d456101c0890f033301203420b04801c1030703984c225000c0d0780f280a40c0020149030101e030100070a00000034020598000d4100d44c05421140100c090541c01c546e0b410303501c940008280b103104031840a4948103c1c54008281d0f400317581c10441c4481c1c42d140f02c4c1300701e0459600403002e503819075409001408034010703000801849807849480d080328a00241c00c2c403004840e181c660140c0b40d54030880d007c0c03005803601c000580e031822 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 848251438 1250 848250188 848250331
    0x40f0609030611070209222906101b0501200c010b01051c09050c0303040f05040e0d0e0d0303060302060d060e0f0702060705090a0314011e02030411041a09 68
    0x4042220121f1201101000a014100b03250103c01c00000350360305100000002112910203030300c600007081140030f40d141480340018051102e603256485460048101d90744108000614450054240c0c40103a110210b44840400045a20b00b00ca000a0050300c84200091030620b207420008803a2307842c20403070700001c586000e80ea00c02443c00c000040040e03521101000303007141d464581d10390786150f001c0c45a01815005e6418003207440c00001c00069034011102150f200c00101c000410207000000707040d81000d40070140c0352000040962501c0d001042c00d01d000090208440741004004102a500500111007201d0f110040200032580402d600c0d4010120f80792469849a641d0000785d40308080b508060913200c12042da00119241c15400b01511f03001c902e11485031180305010120403808111005000342c0500c04101449150039808040d40760014030b0400000940b0074007042024408440b0500c0d025081d664440e82f03000c855429440d04500c20502c0c0c001c050030003045a4045081e01d00004a01 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 848252688 1250 848251438 848251471
    0x6090b040b0d0c020f0a0b010503070b030f04030f0c0f0c0f140d0213091a04050f03040b0910030912030c0e031b0f01170c0915090306150303040f0609030611070209 72
    0x14401c0c4000254174004030100c40c510346143c10081c502e00e00a00c119131091007107810010b8442c03464402d0324420b0849480d521031550380da4806440110b01e1044070010015010001400940d1507041a2203a60060104c1e44040d4240254800c1400c0240c000000d000c0403c204013040e0354030319a1400030341e54107940b091000001050f58901901d2034220040c040f02c01501910340000341b40d15840d100310f00400132036000d0044c000d00c080d07c0e40b00d14003076003030141010010080c450402520500d02401c40745400510719060352220044d8012800040300001c2d2949001046194006d00101895000b20080d01a00402200c0c8008a840000715940100014105810180c3c003903c81d4242d03d210b40ca032545003e01d040d070618989544407807c518410b181c40c0041c5081a8021425954900c4010300146516261558180041c01c108400254184030800c404070783d295a40140d003000b44803a0b2600c1400b60f06618000c1c06a81030720490894184080c442100903958400b0000d402c07002455824889 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 848253938 1250 848252688 848252711
    0xc020114040816170705161e09051e0702150a060f03030804021201020304150c050304031409030a050106080c0a0b0a17191a01020609120f0f1c020406090b040b0d 71
    0x4c0301a258422003540300104216007407181c01f040d1003d0312002404888009a00d45000002100204022820303c511040b81401500b609501458104d010600e0056800c1c101c0000a031341c51404440715001a002550086005a42c000c0196003041c0003100c14401c01d410302070f07074143ca180c480c48080c0402c891030020070b0940d21044030b0007900243c114000c0d0f5a9250038100260085148031040613480c5c030780f000f4030b10514400c1050307a020b550300d6503d0301d4a60703003003004610580d000145c400e0b0345401102e41020001e4000d00c2120010040d102c0504103055451041007650b0403aa80041e503000d2040106164196020a040e800180400c01030502503c0c1c50003078021083c100d00850800324580100081d0000141100c81c440c20310036422190f00f50348041c10f184d04c0b4050810b010f15052402c1c0182d120b00b105600c090900c0c010020405401c00800384940505840c15040c0071042c10780c009001e10801d544814480003422110000070325091500b200c03807103207119a041c164803881d40d41c0f501144 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 848255188 1250 848253938 848253953
    0x10507120c020718200a0801030209011a1e09090a0522110909030f1303060e16170c0405041401060b28050d75030c020114040816 57
    0x400c5d84845041644070001813030054110359003808164030a0411000010700245c1500c603072000c41f040a800b540c20107104c505146150a201c0081d6088410b0900181d0032b661034880d60580308280000000c6018100001d00c10244000540d164030124006100b40001ca54040b6101c0c5079000161541040e139030325644124214014518001c1c0303144000544281d9001e0351400110a0f01c0c02110b080208010158065075104488036403c401140c1405040010302c402d01d9402100850070400d0310001010307100001c00b1542d040f14100c407016041d5194901c401024401e00c4041d0019900c5d03075240000440d0701c1c00704000c11040400310b1208024452102a01c20700503500550b088840c14002c000c540b1200704a40310040d40d108000501084000700c40b4600920601c800c0e07485030300c841001c5000c07d0410b41c40600f281c0c08440000403202026000c41c40d021078404181c5000390340000b42d040c220700303000782560103000300e014691407800140804521480101e52000c8030341d48040c803400e44549000300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 848256438 1250 848255188 848255231
    0xf0a0302060a080a06121109040c0902210702030a14070614090604120503060109090908040e011707050a050105040612110309011e11030f09010e010507120c020718 72
    0x39040390002c00d00c881c119400c28000e9000b03003d000401c0c842a034641803403407958000f031040a050b02041d100d0800b12410900c1712a42c009014800c10b980041d00d641e08001079034000d0b0388900403e0160100f0249031b02c50040100e8000040344040c500c0d110f20844004c0c13448410403550041a580003e500c41003112503400500354044812081003686480454203455031011101a01d1212510240e041c8840c8901d0491b0b20500c0c0c161114048036061480382401480741c1642103c40907010040483c0da8108548058001c100c03c11044144400241139141048040c0c0d01941c02000103840a009a03030b007002c00d58081d90307a0f40ca820300910f801e00e24440080c040080e060040c11400001780304403160107400081c0d55010b0003640524178224201d041c4200c40304401800d0b840041807001c614080710810f4800d4100c0100340c00400c15820744003d40c3c1c02c40c0c40907554030b00030030f0032000f00044d094803a00480040ca821400036100303180c540040d50a05428024030b61450a65030003411880b600c0c0d160340300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 848257688 1250 848256438 848256443
    0xd080702190c060806010915050c031303110a0b0a0c0602030903161b060206010f09020a0c050d1e0f020a1b030503040905101e0612062304110c07050f0a03 68
    0x22011022039080402401d95540150400602c0c4c0000085455000380500d80032034020301c42c1c8800b03030403901030708031000d4000502c0032186000412540c000808048584400385004d030250100da490214104844003c0540c40302c442039000b0310072402000d8110f1070703802005400190142e61f80e82c0b032000d00c508500c074030502010342411802d9004284561840c140e0159650003030081005503c8038426a9103030006d12036188116809c14040c842c0028a4002d070140d41d629003003400084225942c0d1381d081810244000e000119200104294048081a100850020b0381445401d03c820307100029141c02003100090420420b90345004800302d414004032004503000b0040d603403074584071031296024102c00d84608907000c8040741c0210703005a41d10041151401c40040a5803120700c1c1420644082c00070b4040703012000d1b541d81c030001c3d00380ca50046101e00d080708100551403034581c200402c02110b0301040320101c4034030300380094094542c0000e40e07036003aa84201d6919401103400b030300141c040109034000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 848258938 1250 848257688 848257723
    0x150a02041707091a030a0f031403091006090c020a020d050c03011a09010501030501050121060f180e210d1107080310080309090a0209030f0106060210110c0d080702 72
    0x122680e40724081461429100c00b03d034203002c0341c0c10020145800c038802c3c00c00954550419607640d000119407000803407045129041c54149014100003030212500103c0f4030f0b80040d0085541408600b8680c4150b502506145004105c21010000c0c02543c034208404000c0c0102c2415038900240841080942c145440c001c1c028828100806029000c140c036070510940a069040d0002c102507008e030160605860044c1c0d1440300412611944010100b5103030b444403120355031801d0220b500203950110a0280c01d0008130304448040e40441c28040b40ea6180380f400300764014241c45a008030013045580781500c49943d1a940701c010104904008101e402c400f811051b000040d07403002c0001c0c4001540c4220b1b1242590828183e50f10209074586c49031007066903104000d800011101e60305035000e0501a00003808031038210158550040c00c46106070040ad0242e4002410242d00c10454010301d000e0000d41d2000d6410001c01c0c000140e640c103900000d06040c400075030001180107200b0800b1851014201c9075 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 848260188 1250 848258938 848258969
    0x1e011205102301080a1119081e100c050f0a090803041d070f02120309010e0f1b010e0a0302010c0f0c180c02060709030303110c0f1506030a05150a0204 66
    0x6444882040310581c01d002c24110034000900c50a0104622407045d40001c1e0040b070400d40582040944841c0b0220f03280301c1c520312140850441c00c20004010b2070314680c0d1810003403540c484e01003850b09045d10046c0005904050f451039203141c0c418203841b5403070300604d800c5444a01e105010303103034064150000c1640d40700124000510f44175900c2ca000700f821607404010700503184c50790b044031004000402c06001d64001016110060b0900b4029944459040000a00c508a000ca41c0b42001c1c1c490002034119400b00c482c000da0080194000e411a46090906801200902d4003242c0d801ea181d02c00603040c805080c3e150001e11001e05401c0b0700507070b03001404e6500329885200c0e0b07034070808404458040c014900101c0c11542c500010700709000d443c0549904a03524a103580443c01b0349010401c104007100d080c0310385100700c1c0003000b8210210504401030a00c1098040c035200b00743c03400801c21482503110011040c00315030081800802d40265014000ca01e0307403603552013000380c445d561003140c4210b46a0f2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 848261438 1250 848260188 848260211
    0x618090f0b06061b0d0915050f1b0a05060601030b121f18060204060207090b330d240b0304080a031104061112030c0a050711060c0609061e01120510 65
    0x4001d1603502d0940c50b0101c002d911130460280070ba003034292480c08214100081800c8440300002b410144141e1584043c3c0c0404125441c2c0c146402070200300c640d50304c000b0520060b0368060103200944481030301c000c4021001182490b13941e01d02c10b102c5244c0c4c180c5d001c0050780d0103042134015818820b0303007a400c0034205a5a00d00840254414403584006000d02140481c40c11007500581e0341c004002401d8010300e40232200c030a00c0203100e004080f8508251003d5901c28030400001410b0514110b110000c0d420203418040c642031f05503206070b03000c000c8103000f00b0b201c188189425690819041a08140c0340c480e00607042d0010300c60030031200d942800100d400030304154031a00d8004206075100541b02c00b841018a05282e0340000e03102c0661000051080b42820391283c4068650300340074000503e001281c400c081091130780922020100354104000300266988108119504030008180301100c0042c2c4929030b00c24040c06000380241c0c0e201d07200f005014090100b149141c21098140b0070001c801c0e912 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 848262688 1250 848261438 848261443
    0xf231e0c041d040b011d04030e03010f050a0e01050108120a050318060f07020c0102010b030c0f0d0b0a020a080702031c0c020c0909030301050a0617071b0501050a0618090f0b06061b 79
    0x226022a580c01301100003061038802c0d034002c580b84101e0100e080d030454940f981c050f034400a41a07002901036584500d8031408840c0ea005980c042c401c09180080c1841e40420860700b0344a050300078166560080382c0c05415210980112401c0748501d140c41c0751a91500e06c585203400c1d4207120b00c0440c1c1e225148c00c0c07200000c81505118000c445c65000c84080700001c00059080c0d640c127020095061300a0884c041d494100b061020042c1207000342801d264002c01d6031182e00c9882c00340e808008450380400d10f210426003000c1c4090300150707280025401d00e81440010300055004150364803e082d1510301c00d6400b903008101d842407115000b4049070082c0b500d03041c2107640790002d100e014440e0b2680314001a40c94001d0070342d80b04400102d0084c88080c1d8404c18140d45d40140c1d400840044440615240e010072401c0c4541400790720300c1400031600318640101900308040c3c000d1003c1c201c510705502c0c4d40000b110214504103c0da8001e007201c4281e80c1e46400107040b4040c0c0b0b1170b0090500d00c01a0400702e00d0101 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 848263938 1250 848262688 848262691
    0x310050903091f0c120e0a0b07120503040f02060708070b040f02100e09011a160309030611090d02090a021b0627030a0c02040209040f231e0c041d 64
    0x280c42e410030380500800e118a0581610080310003284d40048090080781450750304a0005046060016550141c84045110001d46a00442e8040000302e454401c10410020400d40340019103451411800c16880710f804c06101860024440c4600040c0340007040101400d480039941c1108072800c1c0c51400741000d60542c468810200d205840100c50905100c2c01802c5607000c0c00805884910107070f080240c645039160748600802c03a03008043c0001131445c12442c030403000d004e2099075000190307440c5140c201e0030f171000c811072803511400910000241d501c03000300e01d041c0142c0454001d0095103900d41410000e00c506c10a05211008902d0002101c160000369a800f480041c4070425680078682d40c4c096110340c002403008510b810412040e4809807107103036036014242c001400146030000820001f012100350401c0200c1264469a070041003082444024204028100b41444145841c80903040128a03400200301c107500d004003c071381c1c0410072030160340c0580f90701e0046c012194a0203100c204000030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 848265188 1250 848263938 848263957
    0x5090606060301180b120a12030f050103080f03280b1f02210f03010312030c02010902031c0309060507030b090919030f0c060f02091302090603070e0310050903 70
    0x59040415601d05210048904035060081c0000800003850201e00207802e9a2500692009800200c900709280030b00800500078824012081c1000c42144082c00342c52039505240c0d080d5180c00010000319a040c6c0440e143c8028800306641c6c0c0e80e41d00104012134802c1c0c4008441215416120001502c00561003801003003c12200071708003290300740801e00000001007140c00160841805220030002e9003590064400141080d1800c0000c3e484a01455030007d03401070b00e5101c00002d140b80001d415104410807941c00e44020300481000e40c0109030744e600300c13a07000303007000c81c40303900841c4400e00c00e07444440025400842802182000100100500314079016103108280c40400710b4040348000603090750103001020703183d207004c0e10303034400b560f40c41d200c14120010b0200c21405000028110712800540302256035006071201d07980d205002a40307061044d44462a441040a4a125030740c0105403a40300d0554601291081195800700c0e0420301440f5000c01628100300621004c2440800076101942 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 848266438 1250 848265188 848265193
    0xd2001060f0f050603060d1407090e0106150806090106080709030206131a0319091a0708070906140412140a06091e080a1215080604050f0d08160311040303030509 71
    0x207444608100341341c801600d0450f0712504003c0307500c00103a0700801d9101c4c0401c3d580150b800d40b83d620741c407038819580c00401600d51070f5134440060212003c0c1401c40d4a0020311032400d00001d00d001d0000c1021124113020704000d100c002c3d0006211644203c503081c01440e4081e100b80d4036040380303012442044419024409082c0358614100c0003070454101070340e01c22086421080da40c10440042400244142441920700c1090f000105107006d0010362018003450245d0784d8804503281400700207041d00c2c1103400003420008000741a14260030b00009650a583c504100c40744000309610704001081141341d6028254059200000207210056110095003406009a10749050402407140c1c0c210100d14401070009000b0f0203015601c0c4e125203041c84503180140000a5040790f8080395601e070000036400418940d01520400c001c00c04140420308100a81000a042108010301d005e07000038030081c19004181100410340ca034080c8250400184d5215506c0070b0355881d03840303082c014060b00c41100c40d6600c91 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 848267688 1250 848266438 848266469
    0x306061a1309200304050309130203060609091e01080d1103090109030f240b0117010e0c070c1a09041d0327120105160903050d2001060f 60
    0xe21000c1100d00340601119040442428008400001d00e001c0c1c188144489014102155103d000001540581d00840c010350721a1071560030046402c000d20405041107006006020858649100f40e039480002212803007030540d03070190282c0145100c054094503071610b550000405034800304400e2100b90281d03807212801102c6041ca651380384600030300e580c00224900b01c1000410408000120040c1c414003014882d0400404911000c25209500b00811569491011215a04a4500c20440612070101c045c95850400f1004004c2c40083c40d04d00c07070300b60004000c010000400c403003070080d10100090030341c6000846520944ca4203c060384034000e628100010101c1e460707409402c010b88120000544c86e144215401c41d03422590900d110000d850740150341111607880046404010013090000690b5182c02141c2400140f081e1b482042031040c8000103102184020504201100c05410003462011441d40010790314100703100c214082e075181100101d43d1487c414030f030720304803150f84040c2c00c0c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 848268938 1250 848267688 848267729
    0x90d02060403140a1e02060a060906030b07031d0d1d0103050906070f050c100b01031404080304061e18060c0f0905040f14151f0c200a030606 62
    0x80e4202520050046001c40c1c000306a0200f900d002015408010b1820010000302d0048035a0003e50480390304015130418410441c0d01035440c411000106850402842580d2458444016001c40034044004143e00c0c0d1800240014a00250703540c030000c41e20499403e260003c10050100c914140c501034585d2840b90020199031103401010f005d501800050b100c1d60321141c5054841d00300b40355200b0709204050104420fa12014070401880e107032440f50209841001800050450311400f41c8031305a072004005200100f001502540e0340306600031000540a4541c6e12003d55004030380c04010340880c1803060001000f400506072104191080381c091081c80c4803004141d45101c600300d2040009407240900b082549001d400451400d00740032170024a00000403148074020307404540d15444960795007428010341c104181590b8445503403c40c40c10003000c0c841002851790480c3c8001411342c240980d5102d0300c045c4820907078040d00d88014600c800c815078a1030580042d000500c20003090500d03c1210754dc0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 848270188 1250 848268938 848268943
    0x70b1612080603190c080304060302030f01060903031d0105040e0412020c030c1e12010c320f0d15080a051e0604080a05090a06120b0d110d051f05090d02 67
    0x541c0d4000c014004c814810048000c4030400300c00c00f902c40300d0901d0800101288180700400203000156800741c0c2d02d140c070416291070707070b10117070302c60b6042083e80182000070aa0100a03003c10b6803440b0034040201000800484807402160803044203030803844c050008016000c0424a03208916400b52201c06542c0380801da203032412a4510380d002800060a008003009001108030110f0000380251601042a803d880c03c42d44030007201004114441a20f045c0008254001209810948182210030600130b41c1c2d010240551260b040c0c0b41c11001c00d4100c50f403c0503030041c8294100a1010b041010b5550100c503980c3d10340a0f105445501403410b082d40c40004451210301c1102d06070000702111789656641c20a151b00c8000880104101413040100d5541c98241c1140100103d1703a1790107061094080c00c800322070345402182d1080280441c12000a4011480c201403100c045400140b0f079919810458101109908010400b40c0300d8014001c040a66900903401440c0c0c40c0101c3e150f080300602c0999 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 848271438 1250 848270188 848270191
    0x1005101b0512071e21050c07080705090a020c2d0a050718050108061f1706180f0a120306120609050c010c0503090603040c0e040b0f0903071106030702070b161208 71
    0xf0080241824521003030064012044071102481c1b070881e1074011080310081c00c0007404d412888203500300c1c4004111626090840315008800780c042145400c40c1b00c0301c840e41e0740058000c41d42e046030341d0b025540104014210030742841541c900c04d0700c614a51901d492621036003940196581000c00340b0201d04000c00c0c0748105416038280f24020411034894501c0303072004400303070308400b0785582e00d514020800d002008114480e10304000014034682c00d00c000c108400e850700d60141c50a81c1d10440e0008441d200006200001c15002a0f400c03c00440c022412009401143c04c80444503a091030b45201300060341d8001d40c403244c0203000750b400765180c0500449210070168806072081d801030000801c2403a054005503001881002056542560348c0c1c101040d00000315400d5814040290420203c14680030700705a0002414002c1d500c3d280842d0707243c21140c00302d0b2001c240140700100c0010905030003000000d0281c10b00407842a2070341b03000c00341c280700c14210100440d043c020000408081500825416 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 848272688 1250 848271438 848271443
    0x30f02100204030f0609140a150506010806010e0d14030408030c010608070501051b03130306020304150c02150411151b03090d020d110402160b1005101b0512071e 71
    0x11444d1813280d858101c06805241802c0d1a0704d441e400e0888464101000b40c418a940314044524800021a0080080300c1c001844a414001418100043caa0f40504490101c00040303c20003001505401c10003814141810800b920744000174011036481c500002a15205050b5802403003660f8440711380035100c0e90a48070b101e0208105020004c134424200080d9000039800104a906181c0081005000460341d5482076980c20f6001081c0400d110b0102e800b00301e560102c100c184650f00300e0140003966802c83c024104001c030a403101140030480760210b4041d403800010460415a0300e6800c2c2e0902e254071109100401d110170b0550f000d0304240100a6030301240e0018040103d2000039000c0c440c140c600c103201100d00c2204810352104070b9455202414030250302a031603441075626450401c040b154003904410310b007040343c841045640c7d51201c1b41a219115860800c0041d080d20dc0500c680028140000305113019240c00d1100040c0001d0140035064007950841c01104041d80350b0054070815a40003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 848273938 1250 848272688 848272703
    0xb041a01081e2a12060909190606061805030615011e050a091d061c200a06030212130212030408010c09090c0f0806030c090117120a0c0f0305090d030f0210020403 71
    0x40c105182c50104650b0107c8003030140c0e010038030b8400d0490020109000c0841b4110b50f200300901c0101d60110740412a00c010810b0031050724109000243c3d102001401945000c6a44040f0380c2d50b64480d101514111540301c504000350400b91102400c25008400840300050707405138000b41142040d1610361030903001c401540d010382c17101030620402c01500f4080420010f08510710000141c507a02200a410400c0d0b5080d04c00e42e40b0400412000106070f51046042600501017400b003420740455441d045044001c1c03444902d492480407608400c5881380280d0903001c040380014243c54103411a00d08803040c0e507525240c080c0c4402d40e000440787c107441e41c807000409031850300041e41e01803d082504010000c048458041c0c10710b000580000b000d07000883c1c0d202904040003800740c41008030a002108404002e170420a040300020300301c10b901d1074043c1200c28134240020505026000321504550040c020050001d5582406482103003a103104400610608041c0003545010b0701c203490039650300c2141d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 848275188 1250 848273938 848273941
    0xa0c030525050a0903120c0c050d0507090b0a030b0a0b040c03050c07020103090c0b1b0f150c030a06050904210813061a04020c060103060b041a01081e2a12 68
    0x10803181030b00462a42c00c01d101d0b130030304080080f50101c6120380b4079100a542e114601c8040340b400001600a80d40034500804000780350310300260700031030701405927501d030500002c840d094440080c0000c0140da00c0030b0041c40c4014140810450340e5001070304d43e00340a64046c8110955a0801c5040f40c1044030b00640e011024414400190322035004034001a0240f10380311041600c403030462085030300c824041880481c2030460700c2c00c0c500301440344040409081d0081d1140801403a01c20440030310003800402d11000010010740442600d034041c00142401034004051860689418070100c0a160180002d0801040d178a5850324072400c03406200703002c3c007540421072195540e110005450401c42461602202d55500101070f00c55102800030322490a000300010b5146081c41003c4507510802e0f40c0c001d90400024520640c0b11240f50071840c5020719050319a903599001109030183c840140311401d4038009c00b40b0a09645005802e18075030382800340d800325407400440d1100c5501c1403e0b1052501c0d0020f00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 848276438 1250 848275188 848275261
    0x5071d060a150306050915030609010b0a0501110115180b0f010e0103020a11060903120907050a0605091314010f0b0322081303120e01020c01021b0d0b0a0c0305 70
    0x5050391015504000c2030903611741001920520085482c2084400e92458100c042d20301008030300e0300503001e80001c0043d8a00800810b00c1c0c600d1a029003814041a082000d40303c00c425803200d400401689042d11030700ea1210b01a0b00001c000700b02d001901c608011070380d003861402c60040034000d50305846540c880034817580194081c8d0801c2d0403400610280c8454099804001c3c0701107403140c8100009140d032603004415498611101a01741c40482e0300040c2c0034019070b11180c0c00310050b03030500d0820545516261000507070170104c0c041030741d41c020304043c10440303d20301900405040c1c510341301d218120144c94a1300610103001c01c03950341600401042c5100d03600d42c51203000c900210f0041940c1841c01e041100210385030501c40d44200c1e14031007400c401c00786140d84442d803081c600700700f440544444002c0e10300003551414001400010b03501240036810907540c0741c07600840341d640c2c80004810540780441840008100e8003400402082c1844006a00d01200f521240c404095800da22003034109010b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 848277688 1250 848276438 848276459
    0x3110f100e0f06190606140307030510081b01031b0903080c0a080c0337030c1b030503010504150308120415090501090302120324061605071d060a 64
    0x189071035049000b1031018002c0c4020502c1981c0c0b1800b000c0b4030b0008807078400c04103603089503840d510641c100f20b104515071245907a010101c2c0e4020400c1d1030007260a46403461b00c2c021094003a030000d60b56104484c0000a500003101c1e0402801d48241ca0030040e02c22120f01e0030000c0b8040c4440e401c0050b0f4000303000c0c0300045402002e4251191010700321084000c1ca555030110540c000314484012340c2c008110a402c01240942c07030f141c03040c9101981c1590f0041150b44940500c1c00300510010300d40c0703a101d02d11a4a120b101c08201410904a00c00c00801507400c000d0801e03030081c090540264100002700401d0550b404403141202c0d40414003524105a800e10409400d0300500225542c0913010201107809115009640384070340600000511001c10745800780c50f0001035200e03c809100c00340304101c00340100305c950700d40c100606650281305203594400104540702e03211121404c24910715800c020700000203850003d03188410748030810603480f10425200d0703001c12030b9103075400000c4020901200448 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 848278938 1250 848277688 848277701
    0x3050c03040b2113080a03020904092a090905030703180e0414010b10020721021915110c01050a0c0c0602100b0901030c0312050c03030c0703110f10 65
    0x85105890030076440303405070300031603028a2494100d0001c10b4050031000c1c40103070109801c504a6560719003610072075a40d4017194010a0404c2d000d0607400b142296464950340c11442031503138040100300c0050f00c03800b55139120200022030800c81407190240495820110300c592002140c11000450901006903003c84040700c0480400900d51100c450002e4031301c02c00c41049026500c00c060010b50805011130352801c5503420f8072868030402c1c1e0720030ba40c055950040307401c000362400784802c0c113414103185111701c2011066200094100000c540314248015940300c03801c040d241c1c00c051604820300b218208650007414a1145c400341e8002d04480702c869805400140548440c80c10b100c0c4a071201c588402041c2e41c05a03100c0409070b00700c00ca100028a80e02e22504030654130807500074056504548488510003c1400020110130301c000d020b20030325001c1e034113540c0d003481881c0403a6a64a809418101030b0b42143e082100450400110400e23004030228800c2210103000005025801c145c0782064040c2c0305 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 848280188 1250 848278938 848278957
    0x30605031c110a051b060a09090c030e060a0207031419120e100501030201020c010c0506060904021507050a020a0504020721030b120c0f0402040e04031d0a080a02091f030305 76
    0x548002e88411450500a088500b809a006010110700d5013a82e01207003507000306110b1160004018210380326070446491825503203004000101c3d4455030a065005004001ca02001445058100100035402d5001052014440c0da42c0010390003400700d40d48468000d030040201401c0017101082c01c40c0f40324500c016003250078490086005482d00940c90300300100300c2d075100102a01d40d801031040d56010080e40d8050350003840c02c050050045d0725a00d0b02d6030350141201c2e214851001c0030605668840429440c20290704040d03a80c0e450301860020b90b03640007128224014030490341c00141a144c184207491086801100c00c0040d103c507a010100c200c1d888d0f5032401c090503940c9110302c0d44e589030801540412042c58004108a10f0507804014604506481c0c2074401d40c01040b062120208040e43c003030308260b00d800d105588000c40152072110001003d01103030131150516001400801c005480c94005000f13032051885511040500100c0f4480d0011000704031481c00810000a840764004000011 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 848281438 1250 848280188 848280197
    0x50c0d020d1103181b0f19240201060e060f04090f0b1603061203052205030102030c030a15080c151b01020a09121203111225030605031c 60
    0x55412003050043d03041540c01090800034255084104402003004070303440c000c8454100341d0000d038000020700201301004014040c5035016070501099911548007000303000700b40e08548032140c50401d04408c2c098908080001507007007210006086200071091400b03410007404d4541c14202c1035040c40094151740c0b40031a850858100254041a07407104d9003070203800d02c042c0307009000b00421030060076640301e9084400c0380515410482c00007508141102c0300c940c1542c6074981c09103503c0060f00b070804441d80c8169059400003080007207a040400c000c61198007440e8040001c100e4001062a00140c80d000da15299403020040c0141032904115041110000d1054140340c407410407601c9681c1c4c04400d00580c100da40100f41c1c1010302d504179500c140a00381540b1b6080e00011143c1300c020302d01510b8640c10041c16541d21000700340b403031034204641242d00381340c05940700d9042c5480b00440020000b800300e9140440d41c035104080030301c03c2c003500080721002001440c04840f1160350fa50411541d481001c20322 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 848282688 1250 848281438 848281451
    0x70b13020d0803071413170703080406020115090b0a09020c0f01140f180303151c05070e100f09112a1011070f0303060b0d0b04060504050c0d020d 64
    0x1a6a1400301c0341c000782c401c0c1e45140e200d040034080513284000840000107464820300101888400800820044904076003040d205980008141810000d040d000a0312186c1c0020b0041040b5805401c44110014406554404c5075500c401c10390403207115000303c9612182d6094108103140003500a8080e45003820700741e481c03442281078020b00b180c010000a9a40d50038170380030000c1049180c01000c1d84901105108400d4120a0070f107552640300081c4904842111201820106d454024030b1020ba104812490000086603041a507521404e500c1000b10141292001850501615206008440029002e444010304010030840980b100c5151103c0e100030910200e00030008545492440040104041445070342a070b00441c10142001c4004086a04001c000300302c04031103900f11140d80f500902c0b5441040c440f407038224060f2105500c0304d00c80d12400308101d42c3e030703111903030144a01000c00c64040040b03a54580a001c02e0f01c02c1101c1d0b4000c444002d100040894107660010100c0716034003400040e40 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 848283938 1250 848282688 848282693
    0xe270402040209120a110306070f080705070213051b13090b131d1002070c06080a0f0501080c1906020a021e0d24091104020703030204050a1706011208070b13 69
    0x1400c0d01c0c480009070320392105d4183d5003840644846c1c0700b003142d0700b98054201c526104c003001c3d00609403403040b1000c116a09001584091240040d2092554001d0890404014098a9001600c420340d0702188200104a1480a921900c012071321482c005000e042c00c100d24288904009145101010b5000407400106000c814090304c100c4420740d01140900c4120091010365500d054210351102254034410460440490620aa0784080314800c0c0b500c00540d81d00c00301018007801600e800124024204030000c64441408145041d68102c19180d0341c080501c034106010b4812000d108240150300500601001360a0030407503061114035034141d807484941500b010480d000101034095405001c0c038400013000200f80c8107180300d43c0d052038105215a0300d0a80741d44480301c5000c490184140da00081460425000e40c050750020003000f450407501964034041c598203a0300c3d00001700064003e0000205400c250044a1690b4035003100d03a00341401c040703a66441c514400908040a14488990003400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 848285188 1250 848283938 848283949
    0x1020d02211c09060e120310050904060f0c2304420206010317071205091c080d05070f02071404060806130b2d100b190e270402040209 59
    0x940c3c0c800e000000b010000340a5050a01404003400b2203440c401f0818030141114025120b82660421600705406444900d0320340004c01e0b02c20304a4a00c18201041d0203850703900884401000b004650068285101d03444102c0c100e44941e0241c21249803120801c0e021031180c1001d81c5807069503400f103c0303028402c0900c0f44001d80c0021420140140d2143d001402001000f12a4501046001d0a40c40c24442642d540703903051821505007070100b10000c0350010007655880d07141d10354440d5000c80790220859a080076030155006000b1001c0c120300b48400314640c5031181002e102d40381c0040e40a881924103201c900407503091160281540162078080204602d201070108a0051007080d00a051004d4185841100040020054408117644d41d5040c0d10081c0500c5030128000c955900e900b80903074840c10700202d50010b5030421038002401007680ba0310070b5a001c82da04e00140e00d0340c80d038840c4c205401e401c001210b500307503a038240e40000084070000c07901e401e020f0850300f141c4014405414409600003081 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 848286438 1250 848285188 848285201
    0x1031419060203011410020d0e06090406030506090c0105040f030f0203120a0503040606140102030403080306030a06060803070515061503151302075001090803010501020d02211c 78
    0x160402d82c00001044100c0001d2100c90f140402900c0380c0108040c0a400030b034403414000ea510061110840c03104a080e6188000c95114500051041004035203a0404030717603036001118508001e10a030a02c1004640c05403080c2c41c04c841e079102c25115854199520928002c103407aa040b43c141c4146984c01002c409a080604079005c07995540c1d82d100d1502d400e001003541d100d039109540005001c1c00100181e40c0c0801118150ba4001d00d02e5a5241c43d400c0c0400c0c03400d40c03c020b000e46164942080450542004401007988602440031207000c030041441001c2d850070140e43e01c80d442620307000c4d003508103004200030b141d021454104d19407050b0850380200f9080048801c00d0083c5560010380c54080001340e8424100f0200707042a2880314081ca070400070307540b817210250920000c1000348180d84045044060a40c100c0c540e030001d001695451401c100709070020f01580380540240d5a41c0c00441f803000601d400f100040b00354031800b40c902d4194105040d4889080f00340240c1101c1c850405044482c003614 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 848287688 1250 848286438 848286443
    0x180a080325090b090409020a0b0f0a18050d030807030216031e0e10140f0f0702040b0301021603230f0c06070c033f09030e030a0b01031419 61
    0x800d42086801c48121020304a103062414016400c42c10b0040600110644d064800e0075038000503140e1486c00001c1c40408181c2c0092040b6a00161503062120700d40040c2c00e051007a611902d0002e102111002007800c03542c0180d0341c100c18141e00c11004030344a451a42d8001c44e01d8140103281120302c1da44410031072603288096003c0341c0c90902411030030a4248020900c076100d4505010301602c9500002c03114590041c80908105080c100d0301d1200341c1f036404503101e820300500c14503619103034070000c050b0340c0e0060340c0141c2c4120700e8040c100c003247c141070007225a11940d01689404040d540d03a400e6810714042210003880390300404622411000c008024000c11403041401515081d205180e00d24100000b13200c01c0c1004200406640003e401c5800d501031001d0003e050148a803401c0011099001400c03840f81c0e8200703500500c510040c0e140e40c45001640c1c000d82d100300c0c05150007010316a9400c1c0c8504d0081050031030000400102d4000010402d0542d98901510300b035aa0b09030110710b54150b061000e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 848288938 1250 848287688 848287711
    0x11070303050115030b030613052803170108060a0f06350a0503030a091104020f0c010e03090d060f0b0910060905010e10050a0c150e060a06030b180a0803 67
    0x600c000c0001052000100803d4a800e015844554000c20f40701e142c05015910021f600c0c6503440e003000340c28004601280002e4290088501408161424103541c5a2044c0e01081c03100d049016600040025581620b10001c001c0c45203403191001035004208000e18034003019034440020645215411828062440142c095080760750045c000346410304040c01d00410550003041d02c0d80000340f022003500d500001c0100000b410301402d0504501c0608a43c3c010b0340c2c454030000d10120050b160344050101001003070000c00a920341c200040d0781d203101d180c40321540442d88181c0c240014080740c00040140e42000130115103c44060003003408000191110b004841c00c01c9828070030158081c00c010000c0800340380c407151a411540121700841c2c440d800c00c0d0f080010000d51303120818048d01d0000003035a8010241d00c991204142e074000101310000d4408021300031180403ea09130064040d000030b60fa001008880c40380c0321205a007040c04484060102d043c000da100e003602007808070002e148203c074003041 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 848290188 1250 848288938 848288941
    0x10150302010e0d030e0d0807050a03090608070f091a04030209040f170301050609010806180703051506091503192301092c0304080102070507090b0a080c060a031107030305 75
    0x54120045058058024041c4030010f90101c2c0d400081004160416610301d50b4510301c1e0305014600c0c5c812000d0142c030034861007030301d0004c2690050140c002ca401d1907441b00310329181c1d00d104446400419000a000271002c404c1840070310440a051422105250883d5141540d01c2d404100e61200459040d1048079080f45400203018130160801d124841c0c030024075203550704140c00502d41e4000c000c241410040320f0000109070751a035512103503072401d0511900c080c40c0f8006074000c001d0001141d0b03030080031100496000c01030030160213031610128018014011b0780d500c102100781a0f0001044101c1c45550041c40f146c030480588915101290351a10000700502c055407031044120b01a4485501c503440c00d202c44d44441040011009549140b00780600140030282c10f46144d40129000307440c1a5200203074080030014009402004c0351606101808488010010808124494841d0071110340100607a440e851820000511001650b4180020300d20340407404454a40c01034201180031a560b00f0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 848291438 1250 848290188 848290193
    0x203040308061c061814030f0d09020d1401090c060e0d02060d1104092306130b040e0f0708060f0f0a0f0908040312090506040b0703050927040b09060103170c101503 72
    0x505e1406c1e1100c040041d4680800900e513601e007803040d5100341c0d210a036160318660441d03640344204140039400c500000003143d41a0600750080c00445000c44881c0391b0003e001074030601484e002012107038018809028036034640c00f4010326920a42074071440c03503a110040c40301e086105001e0310180c4401000003890384542d0300882c0e0350300003694010b84000c60080400c42290754a10000706404400384010881d0040b5502050250040e81d00b00460742c020041131503c03094001030448116402c85085583c00d44500382100401035003a1103040740542c404000481900454001f0f001c0b00f144542c000844030044d407141c001c030303402c1074000300d800003032807002480c1c02e0358458110300250008503140392030180f41c82014050751090034401418800d0218131342443e81e4402c1d41004542c402c0d40c500030921103a12071a41010041140c08880700d0360001e01184800b000003c1d0f05050340c1d40b21410300c00805a6518507200790b040190507040d80d106003540508910102c0c0140407500c580b2828400d402400c52 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 848292688 1250 848291438 848291453
    0x20318120105090f12031b130509072109030e01200a0b0a050a1505041a06070501020a1412010e0c0c071707120812060a0305060103080414040203040308061c0618 71
    0xaa0303500071400c081c018403043c182c80705410310301000c0d007c00da6692180c050030212501070041d400a0350121001c010081800c0d0050b803164012a4107964481c08002040400c1040340d5802001030001b0b11080c81604465000c0c01c10185407166282020030000c611401d1b141c40e0103545403089507039450050600c002d502440c099503070000003004061102d40080d80350003140c242c2138480da91055455514074808943c514100c4101140003416199071440f0f18103002c0d0117984640c4c7c8400005580e4940088803803460800e5814485c5498140741e0541d04e018054603c0300c0b4050040401c400d0104031190360484200306410040c01c8011135051440000d020700c60801c0d0160303000302d45a10249400f600015001b00407103401d4800001d6030140c41d00c8443c0495000030003900010014460343c2d001000340320302c03003000d001294414140400320341c00311b600780002d902090f01d004000c241010082182c03860324016845094408201c035081002c06521100c040d20800d01e101798002620aa0070828407095 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 848293938 1250 848292688 848292703
    0x90c02070b0f0c1c05131217030a1107121710050910050d06060e13050703080a02071a0c10060509130203010b0d060501050a0f0602060a0e150a2a020318120105090f 72
    0x20496000c096883c680302d541c03002d0382880b048c1e190b01800200203081d0010325401070b80320341d0300640044e890351158503000c041c4009200c3d600000c55004100107802c2a15105002d02c5003c0700200808464a818140108014040c2800005a10803038010440c3e485141c549400140102408a12640780071640c010304070000e000001c1400d61030482d0b5001c28800540d140441e5480451340e81c1c1c401c01c56004909256168203d0010b00f049110610f120f01d011801424040b4111010b440c400c03030b0b18418a004862151050582090711080010000340581404800305400500086200c0c28035500140e22a1400101214090b56840051103542421106000940203900f14490071906110019565150051407403009030f0700c8848051081d035081c00031581c002d0304d5640d01c1e00c07d402c0ca045440701418481c4591600780c43c0c403040c11160501108991000811260041c5142441c0400c4646990f181c0d0701c9441d0f0005044c030701c81d2071076a01c2489181e1040606070040d01403030801da0f1159042c81c14 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 848295188 1250 848293938 848293949
    0x220602030405030a02190f0f1401050310050d061e0905010e0109080909040503090402040b0910020d0504150512070816050a140903100f06090c02070b0f0c1c0513 71
    0x414072007844507803000104c0c4140366404803500040e220089680c0264950350360401001c604c20100000f070b8480140c6404007d54400011105080d11342100464041c001140c410a0780100c040040246041c0a5007140503540035070000b1a64440d0001d00d01084c20039050740b05c038107030366951200043c032400384140c9a00f5009000280154901034444503c64004c0300701c10740c840d20412000c43c0800208004642003900301400664a132513448544400641000107001d01607040c50a40c14040d03803010500013241180c035101c90703040500780302218043d00e00304a100d6080c0141006210400343c070381c0080311301c03d50184d5200ba1951500020048200300000076290500405000445405800a00c0c0c08800110070308003546a80303516000071700d04801c44c0748a0240914094501c540700c0c180d0b0b0412030030303902d502c4814490290381b000d080740d07204d486114186a44006218050145254000520780301412100b168881d1a01140c2c4480503c064103042010074000507400c6070703200160104070010070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 848296438 1250 848295188 848295193
    0x302012007031118040b0138070b01060e03060103080f0c0f0c1915050a411c0510050306070c0309050a0501020618031303031211032415220602 63
    0x10181e984003a103003418015404032405a000d102d00944a41441c65a0980a12102d1450908408039200158880d01c9c0645441184030008108a03000e04c0c0000d03c010b030302900404c12a07213141c458540c41d81001c00030b1002e40d0700400403074a001100f00100100c1744403560241034100d4030a03040054442d17a00320070b000c080094480070090084100440030480300c050400541d510201d800c100d401050b1004200e18048003281c49514035840030340c3c003a041d1075140580a8400380800400791642c0070302c400d9a40c1110181e2002c5500300c017540c11594101001c0c0b92039180307407a19203001034107080007114030000080d010b4140f14241640a2601401484152188203c25041c900000d4441d08000e00403421240024030b0081201000c0085a00b50080c0300c0440940720344a2a0007400c01051800441501b0706003243d210602e00c080046038080c0f0411024400b01e907110003c0b5505044d07070084119803181414440a80c07040949006040c0280c0e84c44115900810100c03800b14422425044842190f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 848297688 1250 848296438 848296441
    0x100306080708190b0604140f060f1903030e1507051f090f020f0109050a0602011d2b050d0614040e06192a050a110c0108010302012007031118 62
    0x4040f201c03070024100350044d0140020f603a071a0007141c003030a801c000240c05002c1f071404003c2c1101400d00514020b030011211100380140080030002d01c940c2800810100c800155007c1001900072645450058800b5201c80401605405007008640200e40f080d40e1503001003802c0720344940f000310941100c03100c190007000340a10540b150505080c100d08001c3c040c05100c60b000001d0303806204118010640201078000c8207403200c01c028040d2030341d107007801403074540303c01b131070280306404510000340d1040c1d1380c80f0070311015005041c0310001c142907019505118003005508042d103080d004510191100501b40c1082d240c0701c1043c40111400d002e001c2080350041c1c0c05100500d100c1004014900113661004910b03018090045c11a201c0401e1240c146c1e05140c160900c1408d4000019150a032001c1d146c000c2d00c8800802e02c0c40d1520700606905000035203600040c401503005546080f0ac10301c03006a541c0e6070f21001c454161a143c4290003d40c2c0030100304012a0403481c107483c030f45d0b4a41e905980140c289 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 848298938 1250 848297688 848297713
    0xf0e03120405070b0c120a0c060f0b0a05010e100c02012001061d040c050f12010e0c09060910051903060e0a140d0903230717060f0f150f100306080708 66
    0x550f1014007400c1458807001442e08000c43c23040d04002112a0424400c010784000c45208200511035220100d00552122100040d40e6004032400650003001404618112140e948111818100810202d061040301804d816030548c220f8100303514442c0340c50000030a6424801151416001a0b5040b420101e8000800c000030348805003480c201c0c2c805840c501000f00d1107000040c0403e44416909119600e03085180e10325500002c1c20210800c001d440485550300c440c0d00340524108101c989048480724030104000c1e90401c00d000105211a400c0340c40e0f43c003038503596888246e03214070f0f0b44c2464a40c408403482c0c05000408119041c0f4060280007004981c1551001801c1e1080030310001d00750094101b0108003a01c01265034018200544068a051035107901c03039520303400b0f0f24104090951060000040c000100d681d16580138441940c41158955600c1c0340120301c269609440c01d03080108600072280546815094031800d20280d10042496420144401e1800329203910424560b070261303844441 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 848300188 1250 848298938 848298943
    0x22b050601061211220815061207080303010b09010903060606020a1106090a0b0c012301170705010e0d0203120a05250b01030b0c0c0a0809010e03010507050d0f0e03120405070b0c 78
    0x205503a5141400c1c5c901404080c0c0610003e4681c0c0014024000c0c2034030004594001500203100750750440c3c0541104120320091540c0d44400e00a55005500c1040103001c900b07042030141808841c145002c81041d80c903641e4440030784078554441d001680c41204801d042000b901091218101e040d940c41d401c00307201800103204028584511b6981d003130001140c0b8120a820340026040c2107002031241800c101c2e201c503c0c1981c000034494900f20302502c201c41400c0b9200030894404861050f99003001707030302c509020014800c584030320880c4d0520a030b4411402080b041e5015000402d05901c0f495101c040b407000322103030a0803034005d11100d0341968645c84009940349400c9419244c12840d400b5076030303641901007005071150401142e040d03c01d48140508000d034440c005c002d01c00e8283c0e102010103543c80f040c9400d8650560701d80c0c02041090281445614144d8005031000900c0c40b00495401c6541040e035045500c191040f401044e0100b0400080c40420030550000b40b448903c81413800c4c5040e1611034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 848301438 1250 848300188 848300197
    0x106180320030c0919090312240603061404020f0c1f06050603040b151305040b0a1406090a020a092606060907020615010905100f02010b0d02030a022b050601061211 72
    0x68003690ba410300e20f014180718023506044620945003c0001a40b40641c10140350242141c48406d80454600824800d209004280445005170000c400108000003040082d4110020b0041104002c1c400302d40300910421003000e405504101b5100300310038040c028004e5070a240c10550040b038040080c031002890300e070304d06a44404100e607558042c00c8103500181c2c01204184c45a82c0b094201001e1006210401400354040c000c0d418080000c40d5890350b40c4000d43e9400c5403030940c4a40c210001a5140700385800030894603a1915100c103c0130303210020012440072203160a020303245410220901d40f10204000c50f00854103c40d00002842c0444d802955484001e0404414154007508019640d000d04010b00260030000e110081c081c00001c4014003441c0e195070440010b60a00c1120b008a05002c41d4018001ea000340c0504542e081d55024006810b160007402c1b0b0b00c0d07506402404410f040180c4c49408403910460107081c055242c018001c0160500d103e89204061501c15041d8800e007140007103d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 848302688 1250 848301438 848301481
    0x6030605010e15071e051506010c11131d060103060f0b0a090f0f06080a03170115030e0705100504060f0203030c03010302040f0b03100c020f06010506030106180320030c09 75
    0x40e1350b20711aa16118050340360704a00320382c03c210051841c2080000104a40c030381017402c007010341601d6032600011240b4001240e8045c200844540d031750b1076541400341c03140c52594260080803d4800070350350340c110044c20030542400c0c1500400c1c014000c002c1c0c24064a400e458804006101242440c00040d540c0e10551080c40b003015034450754490744c4500703a0003004400710340c2e490400c42d85555440701c0381c07200310802c0102c0028034100800b05069a00022032416500d080d07003103c8075561a40740903070003401c00486d203520b00d00c1450300000d0550b40f8554100c0d030311b140715a1307910723215440c1c12409045070000d40c0d601d209640090080085500032902602c0c11603030100d80c042003180040348000010010400c0154050040559001c1c3c801443c2d000481103450580c203e8010700c641420598a5440a000d031952000082004009440c82114a440c1324070100c914030304425625541e000c0e86103031903007c00d85c04501ca0755014106140600005426080640d090b40d020300c0d000840c11481d44050780e04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 848303938 1250 848302688 848302729
    0x1101061d09070f0e0f10030b060f0d1b0f0906051c0807020904110307090207120e030f0d1e0c0f120c140f010506060c0a1e0602120106030605010e 64
    0x5408810401c00140201800358010450f992035208011400c14219655500404507002081e0710344018207034101201d81000118100340c49900400c084202004007113948058801804008540340c041e07030400b125403200410341c0300e528001d103614844406900c202d070040d2508900b0440754880c403c4a4019103401100c054120480c4e1620100703034081d82401035000a1b07500e0400080241e0303c2d0020841c00d204904441225540380c86400a030f1168180003400e0341142000900e43c28004c50403140f0240f0001c040d00d070340701442e10304140b0b0241600300c400d0006007900100c031000911142c0c42c400002241c6045000b402041c4c844042c0c0c13046106c80103241950045540100c035104400074440c040c1e1001e04021003140c00f00c0100e5880c0755403041010254030b400c002c2000d42c5807140894140d0911480074207032a90054541c00c400f5590410500400c030585500f81000501c00d100606440c0d01403005c0e10055414450020210756094200d0b0f414011012001c11142d5104501101d540b03210440 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 848305188 1250 848303938 848303941
    0x3030f08010f0b030a021b07090e0a0c0e0c07051504150516110f03070302010902040e06070c06021809040302150c0f0711120a050a03031413060209280302011101061d 73
    0x445d00240300710007000b0440c9a4501c0e08040d502c41c0481c0d068102d554609003407208140740501281c507401840c40003440e503100305008001440d5000d500e15030200d220f104c01814240300313468842c140444110404811030b0040200400c01510714031010301c03050301e02c1c0c04019610f4600305004243c0350007449a41071107400100250705860401c03441e0540b006d85d41c140c2e525040c817072802034060a0100022445a42800c040c00700080d00021701f18400d06903959443e10001160b140d50001b50700086050910b010b00400c002180d890b040d40c03040c0114070035401000c9101c1124840840321a000e0600c101002041048400c0d8810170340030740300c100c0e8001132502250b5144800140ca01940000054035900a105c9c0742c0090010218180c1000c0b80240c8040c00304004031400314031144d80071079481d010001b541001a010a6050340130b841114000b402a22489042c103012a9146a8a03149103851901f8040c062045507448540154598840b0000340941401c0c10b11040304920203a2080e580380d500c500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 848306438 1250 848305188 848305201
    0x10b121609031b1502031b0615061b06040b04110409150e0a0b04050307031404050307060309050c12010606030f1b2109050102030105092505131e03030f08010f0b03 72
    0x401c0743c00038084421103014058024401a48942046400c2c03042c0018251100c00705082c0415210311075281c1c40d00c4503000803011010032500350052546030341c64020305030b864220341c1c0040080500035805081504400e1500e4540703410340e50310b9243d48a01a0341080303010b038009600b000d10f00710254607604010550f4a0036068003450660f00311001790004020340c0502c0103011000c001440c406000f0f55804441011050103080f41e84920321816806901c441c104010745e62180e8405c5004612807400d98400c0d194000005400c254818907190003039544405c200141c0d5094450006801032440007409030340343c0403d071880b0b4005d0110300d000a100c0c000001c21480500c9024036500903a25603000c00c44005603041c901d000b0340003402502d01601d40750021495075070356240402241c00a250020348148038100741120183c009140403900280619404682a196000200400c2c9411058151550f20b5814000c28030141c0c04000e805014502d0014441d00070b43c0071000064450246600e9900d1702d505 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 848307688 1250 848306438 848306483
    0x21831022512050f1c0e06070807140d06050607060c03150b03010312021e010b0f1503040318050d030201090c061403040f0503071401050907151b051005010b12160903 73
    0x17034200305400281040920380c40c60782e51340100d0380192190100c5800390b43e404070548100009880c114080b80036030480e950224410303001020f40000c440f0000c00c1050707407103000c18003035045080701300da400d070300c2c0c05008103401c1d490310401030440030a84503502d500d0702c2c00d1074074086848180000780c00e01c240024071880850082142c041c840d9101412a401204140d144600a00c0c1e01442d6521a01103000d401503603151223001e0301c0819101043d5180740d40c9483c4d606072800604444901c1004440509c0054180d0358080483c018601035000820001414030b480c0e100c0c9405c5801440902c940305201e8084004420256613205a01000720000b5401c130303013031040c44e50154480c002c03c222075101080c45a803c06420440c007484010040b1042d0315100da14003011864080c26010002c0d41344400c44c0c07002101802079054170360080065a10b20200c5011400649400340c1000d40f02c0c05001400e00c260740390b92501c45030b00c5a1001d180c3c200350f00c00d0060007007141d00a44030240107006070340150182d0421b20b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 848308938 1250 848307688 848307697
    0x190f0b1305090709090e070b120402030f06100801060b0f0901050a03021e07060f09110f0111060406150b09031b0402090a170c04021831022512050f 65
    0x20402203140c64840f0008100c010b490158824013400d1038400d14590b00c001842c1030035546144d4880741800c249569600c40724800800507130340b500c80c0c40740c0128010b000340312290090320340c850703405003550810000f9401e45586074040c000c050750800c0003804440481d000d44001c0b03042442d16969520001c8000c402274040e414050382022141011301e0044003101c801802214403941c42440b0320a2607100010441d00c0340b00d13015029540701c1c401da0040d443c0422000141c80b005040000a50305407150152401c0c404840480d101030791450302c1a00104212244002005030b000d080349048a0a80030030748590280d009110800081c0094603081d45d52601914034054001d003a2410881d51000c009035080580c0c0c2148010703020b555a050070700d040a0007140c002a040c404d80f0065070441e1001d01c0b4002018640180c40485404075140d8858404178a824018506220250300c03041004140380182114110100c6d4101c0c13515841c5001644a12031154984014200183c03600c003555200140b9106 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 848310188 1250 848308938 848308949
    0xa0503070b25210b0d06020d06170109031404030c061209060903080411040b1c020f13152403152d14010503150a23190f0b13 55
    0xe5000c00b070301c0c0c1194403080201c8464100030a018400f40c2d44014502181c0c80314848039041111506600d02058143d0028000052080c100040540c0d85410b145c0d02d010030101d100501d651a49544814554461085c00c42c01801c0d1500ca45802c5c13850360342e04002e62962040c04207204205010782c50508407980a00100d90b0000350912074000341386402445036104032005c48203031090707034444202800e1a100740d580c0d491010346981c00302c9a01c1c00a080c40c000b0000c404990111456240030b910791a00e4103010444503031000081203011b01410b40307e80010a41e00215007550300019200c9110180380703405004609942400101c075401c46006400000b02500142c0941210741c004411402c1d044003400c1c80c160350b41245c4c074202e23901c41852403001c94000100c03a0000d034040c8045180c0043c102120300800f130004180c01201503856080f4501d00c0c00c18041c0c062640c03e080060030701810400500418030724801076440510b4106021510034103803501a60b01d031400d021030f00c42070210300d00e84000003426 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 848311438 1250 848310188 848310241
    0x3051b06070c0b09120703050d06060809030a110a0609051e011103010923070e01020606150316050408010501060f020f071a0d2301030c15082412011b020a0503070b 72
    0x10a031301f00a041c5911100c6c54658281c0707800340001d17200b8030403078005000d014040003640c6010410101214041d16080e25144503000f113254090000340b60b403144201291051001d0031003280d00b030309a001c9000b100c4c0d000e802c040e418084051960202c460440341035032600000001d068130060711a07403144003140383c01c0c032460f1041014810400d0b040903072940707049826821105255a6581130214541511000c2034080300240301190b20021110406007000681d0b1070510f040c2a50b40f40c1550a45000307070301a0011452242c4283c81c0e42c0d506000501c514503581004140840c03802d81160710380d05440c0015080194042603403901400380381c00c0054210034103007400401cac4005c8480c0a0844000784405c4039a00c2c50701d04001030001313880e607030040741c14015100c00045564080d03440d4200b107200321106c0382031409200340080304d5580039400034980c40ca142c00002c80b0301d02c900700b1001000c240c0034082c080d58000409000001c10010450b03000d076a108031052925142d0114501c18103c14411b201c5200 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 848312688 1250 848311438 848311447
    0x60c020a0203011a0415050619020f01020703050414041806231602071a030c070f0f0606091a03030f0a0908060c030403390206130303051b06070c0b0912 67
    0x4c90030781c0c1e0112015003040742c0401841220300b100402465035403080c590401004d01c90b02c6035007824400001300560042c0155004c80786210120390880e444500c0490205e100441d05006c00d0f100c0c05030300c0b0180300c400c0d5410041d0200040383d11300c0384140790380010080ca8694031801d42440b06002c000880d120304c85c109058508044080e0701c10070300c40c0c5c5040030052080034000a02d20821f00034284c8802c294211031451500c4641c0d80c90660707072185000b51501c1491081c80070000315094508540c141c001c50b400207220303090107070079000d0750000c080003210941024042d1760940d40100072144005900000c0542e82d204460064640124540c005040c502a880802840750041001140b085210750b907204402c0700d05021510600e0840310911682c1d00708205482d2540841220860742140000e05250034102507684a0f041480f45030000c4000034004030742c50a00c03c1114004403007070481400903004a150060009110328011140a003011784101c012541c404c0041c8070718895082d41e40c1e00c1c0b030b569 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 848313938 1250 848312688 848312711
    0x408040f0801050f0915010e100f030b18010b030712060605030a05030a03150e060d050106152f121c0204030b0609090c0a120305120703060f0801020a0c060c020a020301 74
    0x2000c00711414252031300d079080000d9403d0000b00c4c0900d54800e80811607041d0341d09040103080450801030560520708060000811600c078040f0300280110300c40e95900c01e4628110110892440d80100c1e58256681020703007900b03196a0100300b1009231000340c07040b02d0260141d4104500909403030f0344100e4140c040c2c001c0c04400e00170f020000f05070303010003520705009803a03040e085071482c80b08a2140b40141004080030815610780f04815820086c05280045601074450385100820010540d6507030100301814207030b0344401145240f03c009030b00d244041404501c2c00ca00e056032500c0076010384000e507000008030007918500786840c1d102c0a48a40030210b48039512840c104480709019102144114100d0380080d20369140003800c03c0d403219010b0050007540c0c3c50010043c000c0d00b0440c0d0110240b0006104541001c0481c0080300d10403191980c0114100340340040c101451040741c0c0044a180e401000718940154002207000000c0354032180015070780803030034412420013a80c50b000039855402c11490159 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 848315188 1250 848313938 848313941
    0xe0a0e1e010c1d0907110f072d0b040b0f0c1002030105040506120a03110a0b09101508070510140a030b09060406050f0f0d02030d03051f050303070b0408040f0801 71
    0x2c840c000f9111181c059002e00e260604000101000075400b8143d44009076840e4803074054002d040c0d000804884034912410866030800a194100030a81008160b00420a02c24400142c0d00072195107504201c590070708075200454400c2c1c0c0222585d03900009100d22012a841b0100d90f80740c074200c001d0702c0039101011801c201942c400e1064520450808001c41c006290a0388802e650144031402403850390200d0f1f405550356540b064500c0024001c981400f000b24a40e1901e4038031801c41071010f851144024101c020843d070b4503800710491442d076004103000700000028102c0a581003281ca5908145804d0f800311744500351802400300000f004a0750301d1349580c15800c00c3d941c01c001100d02d891320f603a5003010300c0212081e41c425580e104145101450050401300740c01c01a070880500101950903454010078900301c03004900c900040e50340d408004540c00c40c40d00034120070b509801c11543c210703c0c10b80042c3d501d001d1940050702c0056904040b03010443c0c40c1049400501e8001d0030380d40110b581d0981d4030b0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 848316438 1250 848315188 848315201
    0x1b0521010c03110a0e01030b060a0c02092208031009021909091b120603020319030206060d0f060f06050a0902070212190f052506030c02070e0a0e1e01 66
    0x2000d60800c011240064042d0080c56010f00f5221261410b00c00070f20002c0310b0b500103821400d030602d55200324801d40e9845403401070044070480d4403001190921407051014001c0d00500f5000501c030f808103024080c840ad1110b0108440d0040b042549941316000d10b64100d0580e580410b0340a0702c0010a101140b040c511415002c6070b06450320301c030300c540d03406a010598180c22810100c50103a213055860b69030103210a907030041484c5030000340442e140e0b404645840543d010030112030350100c42901c2050341c10801145d2024042e51032020700745690b9224003041010810080c5442e80706c0754985100751041c1d005400501008101c4803007942e441c1071030300003503102c0502a801111b00c460329002c40031000a01368407200c000341da003141d810001d132a001c400c03051000c0c04070340600560050a810740c00c9040924502c050900800c0c1103e1728140016080301c1d240545d1a080d504036100c1003124400900c22180c0c40607086102203405007071b0018150809850071104000301404051380c1e01a40815840ba1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 848317688 1250 848316438 848316499
    0xc220204140f0a06021015030212160f030309030b060409060501060f02070b09031c1107060e040605030c01021f0603020303041205120c1b060f07120806040c08041b05 73
    0x5641540303541d01440f80ba020280294805640606918070648125510003440881d061210809042d16a0f00103900718a80e850301d008581d00c4a1050321070039a05d042c4480c0101118056820068038591300542950103512024004c050000300082c41a107554000b107501641c4024200095a180c080141c001e41c18601100010f10801c1008a107600099048800850000b001000402c0402a9818135002d080c115401044000d170180091036030200440406001140c4410b0700854503e030510044485039403042d44030794461001100542d0b00070400c1a06000e27000250b50f602d40c40d880a900140900c3e910003501488009000103409107138841d007072045441002500c0d400500c89104030294090400e64180300d801c19580c8000001007004034061031180540314500742900d030410501c194100d40001d4445440054030052181c3d80b2100c4560b0001d41120b04003c1d80400c143c008280b00d00041000b007417400e444100e03142e00c00305100c2c0b5000030310000701100c00c1080138064048941d40d840490 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 848318938 1250 848317688 848317699
    0x3060506030307050703080714030a0c1506061b02150a030b040b0a030812190c05090f101202130e090a05210315010909020f0705060f04050c22020414 66
    0x1240c054a004800c8a00c101e80040081c40b5103815038460851507400703650b0031038410600307031010b6141e00320910141c01e00c0b48283e00c4025515041c1c0c2410305d56442e1086284075130382d1801106009580d00004001410702070401180ba07288854404a122403103140303280c99041c20045020049a40d06130006585101c064a041c46861a40c2090224038800d5010040c0703611801e02c105c4542043c00790040e0f074008110a6080062040700c072900c021112081020000101c00055840c2a41440c4ae8409510102074501d48106e0783c02c003070010194405000d036120755030f400103183c0001c400c45500e030002410102a1a150b54140141816aa500d260324112401e00500c0e2111500b11a100b164528803501001124550342e202c2860a40c0082251080380c10710a2000c0c000c0f0300440d4034400307130100321201030180ba66401c030382c18150b203404401010390a80c00072100c10030001460100b0450202002603441204100c00d205100310700c803a40c00541d196940c030104002652074004a0880903200d804c0d9803 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 848320188 1250 848318938 848318941
    0x1201061e08070609121b0f060201150503030a0c05010e01050f06030d08061827030406020c03030418090804030b100512030304030c12141c06050a08070501030f1e0501030605 76
    0x10880d842e52070314070520b8041407206104001c0078035401a106070301442481c200742004455102c4010044041d0040548040300300c80c14480c1d190244244850011080021920940792a0001e40e4a05c81e481d0300070200000316102c4002c101c001d4100f00d00010342c1e4070082c4a1803901240700b4010303071070458599201c1d205080c107a29603180a401702c0390040001500b0340c904035605180c0203019410140444020300741d0b219a001d54200005d0320081d040841078040c503a110300c1c0440c002d00c1d02000301104d91107500301300400c00c5403112607012103100d03603070b0240081a15041803e2142d60340c0240c0d80042d00700344070b000400c0800401c0503200410313a0030440f4074104000516503541d5580c08202c2d0700a02007a106c0076160041036480c9403072005018585803804061070442502380d0250042000350640e0b0703024038403d0316a003c05024550107010142c079030280031f910f08040141c0d0390001f84078032410b15503281c4620003958201c2d040302c8440c1c0140c030000d0b042ea400390200b044c010f0609101c10b40b0700f0b40c50b040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 848321438 1250 848320188 848320199
    0x90206130305060613541a0c0a03110c03070f020301050114010c15060f0311030607050702090f0907051008040c05090705030a02090f060a050304020102010f200d0f05090d090909080a030b1201061e 86
    0xc02c0f0500800d14407071007274101406988190300800a407112440c484201f804410214002000284040c40c03240f603c0c035500406500c1850b00752507068000c120b100c9104401010180d0340801108005034200440038100c0b001004054000e101541100c490706800e040080203011115800313038404030701030702140c043d641d44003c11913a82c052004021f41c4007074010040780c1d4140c0b0002480303401c013081206494249598000084107001c100d001c1c5c40c00b1481e904204000d025a09881000400313040c0e442503c9850500310090083c48014010f0805c1035010959114503210090303030540c0d04502428a0755104000c0102070002e0b0030844040b401582842400408004180117034078009034450140c400602c00c0d00500305291b048901c070002066900c00901c40206520b0150b40d0003071040d24040d00a01d00c0c2a58010480103254100b40304413030070000588006888803003101e80c08403552900140d048030700303400a04800d102e141d41e01040d44c24000042043e04048030b44241215055a0202c4202e5031007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 848322688 1250 848321438 848321483
    0x506100b0a030218091e010e0f0606220306060305011a060a113c15011202030f010f021b0a020a0909020613030506061354 54
    0x6000e40d40c0412010310440404a009401034040b108801d1880b1200c0c414413030100d00d18820441e001e040489450040f41405458001b4160140c20074203410482460074501c006404030000d0701c0c070f602179000041c0c2c84008001d10a62498130000c03003624420f61940d41e04005019082030302080d80c00b54079000e580201031031041100c451011000d40380d1810b1440e8101309492640da00c1d010600d40380280140743e0000780c06480d880065000c41c0e50f1500883c40d030081c43c5000c1c0100034a400303240f0760244c2d9000b140c4010840481e811248034080d946d401c3c55040c40401c2c1411460240c6103229820881001000329158028000312a0300b4007000c87c01e070b5851480d17035a6070300840d503000c0d41045144c40d044c8004a01d40c0c000004031800035200e2440d040900e00540010010ba43c4159400c0d00a0000c0c00075a01d03203000030301c507151002c4900f032003c41442c188070310310b100c02e0b2410046500e08034400c826518007064130904000e00f0103510790584040c11007041140e032604103800c407440d030602d80121b1160a0103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 848323938 1250 848322688 848322721
    0xb01020a03021507111c0906140405240a0906140406050304061109130606020709020304150e010b03010204081f0516050f0405130b01031d0c0d080405100c0506 70
    0x140d4020440f108844550400c40280644030b0020441d810045003a0300e0b20030409001401450241c0c0149954501c1004102ca001d40d0003100400800380c80d1680c503880203106480980f14111034515610034010454000840c02402031090608041103104240e5080b00040040f210a511000c0ba0300b00d207410121854480c034010800490014004500030039102d9100c500e085a00c50782c0c8a00d0b10100000040f4048655019122203e03281d0748180461030b070503c111402081d40990540c15400c0175911000e0004070b440c40202d040c1d03a01c0040d01e812070f05c250000000c0c103901130b00071961290cd6000302c41d04d900c3d1840c24402c10070750f0000700056000346480343c207200d280c802c0050a0105ca0361001101d5940c011044000c4090042c000810035a50b00c0210380300c1c601942400060b00d0040d1400075013990b000c0f40ca15801000030b0000205081c1001c00e82441c40003084814081351041460170304094061034000c3e68021061400b50704031030384c000340904080b50080088030f0b40ca40e2411109000e4610 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 848325188 1250 848323938 848323943
    0x3170c0c100203090f120a090e01140607030306030c12170a0507031803080315091e0c070212010212042f090c070b09031b060c040509181902040b01020a 67
    0x440001d00e603915071103a000e1600002c40c1d0b41554038128551641a240a0004540f00f1440c100000e41e011131701d8000001c0c4000700140c0c01d031032900c1c1d8542101111000c04e00ba141030b0003401d0004050b8101407103503201d00043c44c3d0044410408a444040c0b4803007800018000f116091081d2807140c1c1021201c400343d85454640340e5400c1e00d0000c03a9a81150014505901c41640c1070b0740c1c0c1c5000c00003c80341e4010754810340790820b410340c2142c4030304204510641c010342002550301c0c2c1a0701c45900186602c014951109001d00c40c03964036441d5101007480c0c00d80d4007800051035440030030a085441800007000c1d00650103000140107a10b00c01c54928020b100c07010000000340205400d11440703091805c801588130720fa0302c000905084091b1580c9000610894120f0002e400c0041e440354984181c804000a081c01040180f0907464003039080c2140f480741c0e0069501c115041000522410003140c1c1100c04203042900369a108803214850044800441d5001c0348624142002c60066520010b0350081054 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 848326438 1250 848325188 848325193
    0x1d010606030606171f0e071d010503090d0f0e0a0e070206100e01060e0d020d1406011203090b0306030106363b0a050c15030603030a270303170c0c 64
    0x102c5e1480c10450280c130b5030243c20a201d0303540200103114800c9a0903144203108a48660000b154184001540354280305892414840c1c14024400c039464009550410f5000b00c0c00c203504071054400e0141c40c00303e107a25110342d000700480c1000c6058031581d01c03814001d034040d40841d00c4d5a00d482c1c6490014074100e004210030001048010000385114401a80d10f503907003c0c02c08484141690081084402c6141060350154001120061017990810500f4018580f05189200b0580d082c0c0d401808940703180700b0420f03000408004150903a03000e50001004000a403007425001d518404c048d100070541060f10840c1c402c240440d41d4040445001e080203c2c541c142c1c07462078a10b803070001c0c80c00e050030412002a80000e44818641c1c60b000030020f0300c500f140540c0080022000ca04200b1006403103484031524111002e0003401090f80707001007901c04114490030b20110f003840c403045151032240a940c0201d418255844004280343e0408980320000255000c45182031356100310040c417a00c01c80240140c83d5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 848327688 1250 848326438 848326441
    0xa17010c2d030605040515010e030c0d0b15031c0f03020f0313031403010f140f10080a0e0d03060305100504080d09020d0501050106021c0e01020607080a1d01060603060617 75
    0x1100c11010800781903141800074000791108042021500222203e108041b0707030301840c54040d0b800603a07490005408800070b01c05d11500001240394003c0c600b10003841201914042562800401c003c4012500054103c1c0d100616500000040214010005010921117440d880e900c0d80701c0e00880c1c1c8030f840c80c944503601d151510440105070468441e4160104000c1010941e511080300c0019402021420348c60060542409000707a168400c0c103007242d100c0c580980300782d040e54458081816088519003803141d0150784013480d42002d41001e41c03051480c0c2c06141d00565007540c25034056030549014400721503c9100340c0240c4011140c0a480207000b070b240030b000e11800140c1c0c43c0c00c02c4448030310142001e036400710b1036500d076400e480c821707000400940c00c48404828000ca90a2410804540314500306c1203041c40c8100103034403040050a60410010b0b000000b41d00440c481d005044180108081004074a0301d442c5494000c010034020200064100705002440340d00c600442c6d041038079105c480710141e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 848328938 1250 848327688 848327747
    0x100509010b0c0102090a031401063305070c23100e120f01020c1b100507030f090e040b060103050106030b030316020a1206051b040311040903030b0a17010c 68
    0x1590025002c0103003941d020080a0a141c8070120701030015071044500d00c0d0800b00c4041c0c02400d442645e0030050004115811213840d0200840e448070700f221783c401d600080101060000c0740c01d0701c1160405001541c0c1404009000030310b0b5140004098280304080305420102000c0014142c90b00d072284c00080c8808240148900e40754404d51000140704003100c035589201e10b542800d907000320b5170b141c0c1c40340c0090f25109a6840c200c1c28010f01092f044407101a9480110300c05481405010360140130400c50100c0c40d01c115006200c0107014101280a843d101d10707043c82e00c0d41c3c0c030460888945001900340301c0001005802402103540130800140654100084005004803a030540e003c00d0f60700196000300002c00400400c44191010f004940100d01c9240114010809510b0703a08070429480017000f04101181310145503c2441074100c4000c200302d00c1300e0800320b024100000c0d940b43e004282d10000074240800c24503002c00209254028040b6101d0001c09a038411041110041d2018001c1c1c5040103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 848330188 1250 848328938 848328959
    0x519030b01022d0606030309030a0303050c12040803040515100e09070b03070206070314100302060d0906020d0e100603110904050124030b0603010c090b0901020a060f060e10050901 79
    0x1500300061044926440440442001048003000304800d165901102c040390381c4420b005480e48500d058005510708038941003c2907543c038426201804140c1d48001088983e4140340c11a4401a03401d8141c00407402d01d8101402c8650080c2d400b01c070b05210b900b5152110540d0b0910443c031400703480040c2e50b006071620540001002d80141607200f40d001d10000030820900b2000074600441403907000349070a142000000e81100c410701038004a0080d480c0c10000c20400d07550039032050ba5810b6849c1c1d612500c4464600002d403c600000901140c00410618417a820302d521600d096481c510441c0d130f10848680700301c000c689240c080900782c803182c1c0000440a04080280e5a00207109900020720000709843d00803080103504003020003181c044d0b01c00c10038020301c101402d0708520114001c200000e26030700060300200082c4a1206002408207100c03035181e00a0003000785043d0464001d1044518840c00d80005200a000d1000003400320400314810411404108056881c0580000402d900f13000c00e102 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 848331438 1250 848330188 848330201
    0x1416030b09010b0f16030c0203070915060c1a0702031c020c060c070507080a08090108070e0a060f02011e050406050106140909131a0f011707120302070e040c15051903 73
    0x2c070b040001c20043d000071a0b03c0301c22a962a00030380e59949002508c0c81010305021055000209003414180c4a00c120200004290f007110400e08081501812901d0080c40c0740406000302c010200c142410028626004001450820b0202c82091551a49295418100e0007200380300f8516a101e43c0000e240740070b1800051840a0068003100d0b800390303031030381c80b203180000e80341007114161400b1446070020f5070856401a00309005041c02890a20180c0c04030741c1e040c1d82445880100b0280e80041140c1038006c1d84484400c8515000302031580f40301d441644003400301980d040315014a005c1c00045d10324803401c3c0305913002c04d0480640c2d1512080d4820400c07845070181080f045044801000c8000855000703101c000004000e041c1105450003400c074049564059210a9070629950258030b441c1c40082054811303248091070340743c1c101e0f81e5070904914001032504594203150415092206000a0f4841c2c0c00484a881459903200620100102c80c0c901900d180501040750b074480d400e955500980116 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 848332688 1250 848331438 848331457
    0x304080304110a0909030305060f010c15022208120c030304081c0207030809070e01080d050d021b0708070b04030b0a05060f13152c0a0f1416030b09010b 67
    0x154024041400292120110781c40b020800381c3d1703101003108054150080c103600800c1264000b03101c035100000600410120b0030020b1020703854801e102c403089007540c1a2494203030480f900d045000c4030034503113105510050084032000e02c103512805003400c0c940e0044416420700c2d00060750075500d4941c0c800081d0780207400310b0340c140c40c10240762156943c224805814101c0c005d698003501410803107452410702c040c41e00041c00c0400345000600503011700240b92504e80c401498160b6840044103440c0d0002c0c040c0ba04040c00c43d24030300c2949610510001020360079244658280e520050b55003450303000c075209911000380020043e40c0042d41d145503550050341e1005014146030001009140014002c074200c11a682200340d5581078400c100c0c07002010039010303000480c3c40d03544001640441440003100b104100c0c0b07602580750006203a092031034106030740104990000b401150b440d4a42c0004000c001c890045990030b5400c821140702c1d00c207000f80e01482c2405843c1420700d90900c0c2084065034040c0000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 848333938 1250 848332688 848332703
    0x305060a050408042147010b070230281101030b1819230702070803040303050403060b010e01170601052b0e15070309020f04020a090608060a06050304080304 69
    0x400001c03503100c100708140c5410080c856030f210070035001ca00511703001c0000c940340d008120003241d0252441003586c1d5810346600c0e10580d0744032095480040c118a0500d00080303042c1071580c4006494407000130540e00c15913141002d48050300003080702c03c1c1070850300e400f01e40720a501c03684405d0702244258000000740780d410705d404030310805001c020a0404001046143c01c003003420040264103035401041c4109820740c41000d01c070381d031140d02e41000360501d108610030420344d0030000700301000d0080150400030019141683d886590f6800e014180d500548410f44e40e55050140f054aa5072142d4014040414140c641441000c0e810300c1d228503810000701242c0c14003008003c1c0d555004080c00008007110030111410031117a10103000701066413988601d60b02c1325880700207001320515601e00340582c07244041c84c1c0040c0e1542c0600000e07003c21103142c40c40350030600c0003901c40c2035070354401c00703c4095400b9912210180e8031584184503500c10307140304042c0060020b01c082000104c0c100021504540280030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 848335188 1250 848333938 848333999
    0x30c0312110a0c02010f030b15030c070203061302130b130f0b12070f0821030702030f0c030a030606050c030a0e0301060305030f03010f120f0b0720070305060a05040804 74
    0x1000c500c160b219607081c0c07000c40c111039150821980d000a0711801000c0500e070034080d10780c1e070b04080740c6c5607a50344c5400d2104060100c0020300c90541134040c0c0b11010b13001001c40d111030900c3c0c90203400f010f60112050380280042c501c03020200c00346009000b000b2102401c05601ca800c1003220b10002d0400040c1302071181d0b00d844142c54150303204219032070344031030b00e4000c1c2259070f2070a19404001045031f84981e0717858002040c400208841440322102180b601c0000319541d594502e0102c0c1540f20b080781c001c00003034000c505440705d1407002014003280d03005510100031850f21110160380e5401600341503a916032080000300d03503491090602d03c0b000c2001600104400380c585c1d1b1050308540100d14010400d00c80480104100406000100002d00b8540044960655940c03500ca200310714000001e00004540710100e03c4551141ca070150360820403111203049141000c08145e02c07182c01d031009546512452000c24190f851622a450040e80d002d007106280900e000342c0c2402900d040300d00542d1282d05600e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 848336438 1250 848335188 848335211
    0x80a0b03101a032116030905030a0804090e060405121303020901121b0b0f091c051b010806060301030f02280509010902070b061c020a0f0e0f04030c0312 67
    0x440800b00000c0c200c0c80001540c440515142c40d0682c0040294411405440f40f01c2807900000c5500708401c041d1010f0811100d81400d0356010b000c0d5200c140c040c49290707080d034107000b9000b02400641d0714031001030124404c80010b4507604c0505640180041d0008240c0e18600d1003194000c1248140c03101c0e40121603552500001c1048000360300801d0040c8030345c88000304000c2100c0c1000c51035803d030380019124a040040c3e80b01680144200035901e8038000032441c100b95100703e00c040c412001000c14400a48542c580203455280c00c1c17070400d01c09515624142899030042e8034203480f5020140105084d80e1031601c42100c41e40360000240d070050000d1800c0729110b501404080310034040000e11118591400c000c2c4802d0b60016402099281c0c4140002d10014800084541d007010040347c03500b201101052020b183c8158500f0000c0d405806000000b52020307941081c44115400c800e01e50b00d82e5a07552404200b0311408a40003400941100c3c0c2101c00a030007030248001e60b20051000140c1c40b481c11 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 848337688 1250 848336438 848336441
    0x5030309010b1215040b040c090c0315090b0603220515160c03020303042a060e0405060a050d030c1b1d090d14030402270a050108010606080a0b0310 65
    0x20364030198a039441d00070011a038240038090094018081e0020000030340c0d05076124501c4100908024440c0c1c8030207012a0912128040110181418a4007048002c26500d8060010001010300c40b20b22403500400040080740c03841203060140018144030f1650703803002250340c402c1121b4842034608a1300c2580c48004140304000354400900700c595000b09600700088241c46803034094604000700315149044900085e808400e498000d50f1041c155900b280d503c03004246828903d444510710740d04071040020f01c0d5688030f0080e0782c4000d02503404001c103071696818041e158400d8061a0b400403107454500d000a840346c231103800800d00800000d508645806040d01803485c4641c23010140602d017044e001103c0301100c40290f00a00814000c040401d1803010190000c440b00080e4143c01c10044000380c02d6450ba00380d50341100d1550740c11207c088901d5a2646140032058441911551a050010070f000b0720520802041da80c0580303401c9482d03928200345401a200d0b41003003581600421a8818060318036 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 848338938 1250 848337688 848337691
    0x190b09040f1b21020403081b010b100c06060f031e1a27010c1b0309150206100801020403080f0906070b0f01050112020301050d02010f0c050f010203070e03060402031018050303 77
    0x80e56144414200c03407425009804000701d42d83c0d400c074410042040001c809508803819044601c040e54a144880600c05005080602e8002c2d00119240040d044d42a4080071020319640b0500c8100f00d00764070783c00008840340803800020310b40705526001c40000813502c90030144040c46400c140c030301d4550340010b07149151020396041008910b01e00c2180030007480c81480b2a8998100c000800c41150040307401004030721081d243c113940059102005c3d0070706210701002c4010748082482802d00c81c0e454a0000e545040c00c84115190418200f00030541c200180201c808680c1c1000c0558100400e8000d110700541c401200e80ea4001c9041280500103210300c007203544981d8054424150395850080090180c940c404040345049104000506c10787c2e88881002001c1c1e902031805030340c400c4800030203444e030180f1030001400521981420400801054000b14465005a82d8071000e00c020082890343d205000e031002941a08020000d2243e04101e5000c3c1a001e84840d5004049200e0740d00e520341142e00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 848340188 1250 848338938 848338991
    0x20f010c150e07061d0a090b01020a020301020c06010317071a18190506070905212404020f0111030a0e13021303020a0f080312070302070b0c0702190b09040f 69
    0x1026041013801c1d0041c400c5440c4404420003407411005400010f040e40c0c005010308a0840c2d0750301078a0040d079200f0003046d009268050021035a40b6011800c0ca5a11b0030f00344021a06142100070b01e80041030341100f81d41e41c05038083e44610f1040794400003400140b100810968001d0050a040100318500b0403000385859071500b00d401805c2d0a904100742000d40007007810042c090342078800c010702d8680c02c2d050a503062083c004400300310194802e131401d010f60100c8a5070fa803140150035014801c84005068040d9200301d801098480b200001075640e4400706047c0314060f0014008006028001c06140300005401045010080003001d01e0800302d0b009030200010724005440c060045050101e0518050410780402c04549482c0205070359481c401d0241010303034230310760201156a890198054070402d941c000310044c1c4134602002081099000703401d0580c424032800408000d0b42008440e0101038400d051440c1e454181c04001f8000506840c42c0c0c0880c00c41d9a03201c401280506c0f20070601c1d0401c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 848341438 1250 848340188 848340193
    0xd0e150d0213060e031b0a090e06010f09090c140a09020c0d0305010914071b12030c1d0a06050a110d03061e12030e0609040f0f18020f010c150e 63
    0x10010050b29041c0c0109400c02c2c8244407420406021564002900002405006030340c0b03a1500c0c8071b60082010541c040c0d22200c00c850401241e030030810340c0842c00c94162003c0d4540c0c5084299210700301c1081d00d101c00700103801260341c80d20610510704c1d07000d140c0007242405010506155501c107d200220b0b4007503441d225164120620700d50505505015a600402d100442030001719011030803c4800c4c0c002400c00c00c14068001c0359400c00c4140c85035000700540d00b0080040100c44a0b01028025200c1201300b0301c00540383c90b0a0605103124600ac030f06000740d014105185513030504400f511079500049403123060090a07140c1000701070003040540e24200d150751703020524516080c00354815083d02d0326400c40e4070200403000e011141603140c251180c65098641403c411480e032000c252a80b01d0220400c1e0001d00b0031652441c2d98449800c5091040300f4104100412150148203410400010000075400841540c122a1641c1b10700910703640b590103950600d02c02900702c0101c0b070450350055071410054 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 848342688 1250 848341438 848341447
    0x60209010c0b0705180d170307180e10092318100902030609070810020a1710180b130507020304050a0e0403081005061e040f030b04060c110d0e150d02 66
    0x20b01004202113800d50040d1048081c04010b03a0742d0900d03180c1c0c03039402e50300c44203804000103089c14800d079500907803017225089a010081e150b60030044d0040c0700710340c4403007540780001e000158080e00c1d125040e1050443c076000c103a80b28011004824905c0b000d804050000401402c040304090103000726440310407804000289440180705140c14072000030188003050300005010000c85101041000000c2449840183c3e2100840700541c0c46225858003500301d440b5007000c104205400301c0c443c00c251510b030800c55420700700005031042a501140300d030700c1e0000d9041d80e50507030355441508007907041a602d0050341d080c1611000840d418899507445900d2546140303051000b410740003516580c00c85901e481801c20f1074240408030b03006100ba0b0300d9041d4a0003014400e001240360700b80135034001e4000001d1f8a44002c0e901d007403021542c0c0095905690061806030b10f1300c00c1c5030164000080072059503010342101b41c8010016a040021860029005280f6915040c184420900100a1044203c0e40141c89 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 848343938 1250 848342688 848342707
    0x1409040b0f04181106090117090a1202010b0f0f0f0105030a02090d0804060f0302040e010e130b090a05120703020c011101140103080307030e010b130c05040b0403050c01020f0c0904060209010c0b0705 87
    0xc0c41e0f13005044502400c01003181c049584d130b00070071110171512051034441d425114803064a02d40841400c014203030139244207400c0080f0340d040d00048481d440407103405198000d0138081106c4040809450340d441041c5103045c001650240d0b0155a00c5500408011306248040780031601440510100710b404d110000f07001d000017500600141c514070502e20b41103050608045000303c10000c103000d003001c04c8128000103044501502ca68a15859014000c2d65181c24414801561008400422916405120301c0c205040000301c040e11011505907004261060a6100645e8000c40864815916548494a6668465841d41d101e030086201345d466541e64642803a0080c11184030302900780e01a41080804a5181c0d11038402c8480c02030310f03083c000303062a00d008054074203108d16030101d0030148004c00d001060090105042801c01c1007031702603450080b0f80845050701ea030000c40101d80d0100107071000c0fa010074956800344c204080181415061914035849200740003600310340d0a00055000140300b600c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 848345188 1250 848343938 848343953
    0xa15080307051f0207110607080c011d0d08044b0201170907030318050411040806160207060f030b0607060902040e01021606020a03060e01241409040b0f0418 69
    0x400d40703c82003141800010b0b528504140045100e80348582d90100340c4100380101d02e01203035100303080400200400d40600148160641d16419030407284d00070b4541e5188102e00071041c0324491a030100d0150301e07071030030005c003000881a1144801110040b0a40e06d803103296000a1600340d12075050604000c180035440010030281c07800d40c0880e01c841c01c13002444050040000c40009490341410205c900881e507020a03000102a0381c44160300c0ba0030407210300c1d0a10115001070081c1e800c00700542c0c2495035040c3c80c441d90700300701414010050b8002881046654030841007204035814a1078041f4030500c5d1080061415002400e090b030342c0c180e46010000071498648144078050710104025130901004a140c01d114a000d000041c0903940c001520304801d41c0b10342d1201c409420780160040d00303540c44200e010402c40e8008489101c40c41c07004041c407881401440c040c9950345480034041d18003d0004e00344005042c0b40d165a40d001540003c90b6121a62580100380300b18442254114080b0150b00b00540c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 848346438 1250 848345188 848345233
    0x1030308010f1221110102040902070b0a1517070f0e09011514010c0203070509040308090607090e06040213080f030a020705060a080c0c0c060708031f0e0a1508030705 73
    0x4030b600d21101e00b00041c2138100b03150540d100350303440803102d4850394600341c461205e2980701d100254400907012840101a0340a081c4c401d0103112658059941d0341142c000301c03680107502c0c19107118444810000e0002500e0750940401081040c1d454441d0f5810481012a4054000e41e840004c0d540130402c405c0c600f485104002c40040c0c103e44011403800d8041d070405034200443d80c0c100114200d0304015905c007001130310010311010b0100c0c41d40349050700380140700e00c00580711680640155404100d105200d604010180c4c1c5580c8101c4640340c4a280400c00298401004041d803800c0740b100c00656410280045040105076001640d9245041079000303042880384d4025034402c2d001444004805079201c02d0550f403116841c40f5050ba00c03020007455a140c404840c3c1034540c13209001030b062042060144c080d50103034000b0700704146520351041114580c0003140c091804488500000505118010340210340900c01c550410540980ca421005013558494042620305500440b59a072000c5a0a9040c8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 848347688 1250 848346438 848346449
    0x7210c050405010e06040806040803071106040507170f1c021510140111120d111606022109030a110703080403060b040f050a090201030c020a0b1b1201030308010f 71
    0x401524000480181440c0640d004a504002c0480540702941c0c4038102110080c0c410101200d40e01e15203803a003810654011100c1e4030000e9604000011503100008078103005070350000c083c0040e80e0405200c071050616841012071070b44107040d044c141030780050040e02001d1907031030951180c000510801911300b000740f1100f8041503044004001c14450880c0c403000507a484c0d9800c5c0d40c0030100e200c00403617103800301014002050091102080c1c2982c940002040070591801c2c06110045010040d01094040c0d076040b1850030407140d60800c00103107158010f0559250000e200410b002544107242c041c407408540001c0c060b440081d0503000c55820103914480d940c1481c0041039510f00710b566107070311401140b01c01051140c685804100035603580d000b0700101400080204201e00e030606a000141c1a0758200760b020a00d000c1304584801e10216600078043d800189581e000c3d12010310082c10f988040704525070b00601440703280000050070040c40e00a40c0039903104203080d4140280240e1207800b88d4800d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 848348938 1250 848347688 848347691
    0x1050405150702030f03120a0b010509010804170409060602030c0c0909070920070503091806061602060403050d09090c17010e07030b060c0a030305060d050c1203070204050721 77
    0x80100d0703910074907074040e800414800705884100702d1000c41d01d021640c0149154900021a15943e00c00da4100c00c02d210710380900040c820200101d0054540d03205440040b4001512040010040b64080403604c010a00858040b8541aa9401c040c0102d80d80c0380c0008006800c002214101a00c0c1000785400c0c056045500703040c80c0c1011011184d0740c103801e1103891142a260180381000220050385484192400b41d101ca07905c090754034003251079a000408042c070845070083e8444031110200415807051034040e2915190072003116400c81c2c00b8050034000c0b68402c008000120004005218480c2d05030b07400e4544d06085d6080000400070f031080804403000300700b0a4a40300700304601040c60a0304442200480f442c8903102d01034102d016002c14841c0c0c0c3d4022100041040c0b145600040390b090a40c0640c0e03007045141c41d807004000e0411000c5101806580c89100c0c0c100c9246440034101121601e03610440789000450f601050a03504102c5030600413409410808540740c001081c1d52034074200c0d0b13032030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 848350188 1250 848348938 848348947
    0xe0603010e030a1206091503140d0f0e0402071505010815060f10031425020f0a2d08070314090a0e0c210a150f1203050d140a05060105 59
    0x600740c1d52800b400c0700c0c107010400341c0e03031007007801c040694170000c0038250586061150842d1050983c0c6019010300c01210360799011321000761180008619a8000301881e82e0ba491600b090801c112602412403a84075481503080240c82c0014005030300e52500c0108141e00032600d585414580d5040007041c40c1d800d00038100d000c082024039a141c100600501500f254441c1640083c000101d0003400c402c11002009a40301060045490900da031a401c1458402c001e0204114010340c100e85854481c0310380111070f80448200c2e0005100114060b10091250203158003108021a060300400d11800080e41c1840c0001145000d26600c91007284030007100c0d90b40c2c40c1c94003c805001c01c0b40b24807144180c030101144a000b180c444101c040854100b25001064001d43d00c00121915550420684013128107038500958050308a07540502e038400c482e666041c44510600d01082d0b100042c804c905c1c1101085810884d5809600c65403290030108004480410082d16010700300c0c2085074030142c40035051200522 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 848351438 1250 848350188 848350211
    0x1006050f06120703022107200a0c050405042105040e0c0a171503120405040b0306011503111b0d0f110d030b0607060524271315060e060301 61
    0x440360303000515131400580c1c80c10f191090100301c140d07030041d400400d003031030341030050036940700503200112a50300c414114821104a41169120308800c07004102e242491002c003d2840c150b031100303610130300a0684441030f4165440d19404e00245142060228202080900c620643e038002e003544150b021118078501243c4038070141614500e642e10542d0651901c0018601518940328020317080320290440b00d48103805d440c5460300360000e0065a00940c030b4840443d8007468005942c904031541e1b04c0e52403c2240e12004210040c0210308039040c480c4070204540a4000c0150b200c0554081c8030314050b100c4020b54002c01002d000006035420f0411103c82c00080351008041003044401c1c12500300082e01d10041c0c0b010405d0b6004039000504441d11382410030102c000503000100c0981a00e80d280e642045605d0200945040c040c007140000000c0e00415460204c6080300c4150070040d28130b00d0900c105c07034030350f25011a402031000030342110392103a07000c00541038402d82154119030120024000d041420 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 848352688 1250 848351438 848351467
    0x31602010b091602071509090b100f120605031c120c09050f180108010204030c09020703050405041a120c0a05010908060703050619030501090326010b0a030e1006050f06 74
    0x3810f020f05945512030103000450003001040c008004d0000801200c20003100040c1401920348a441805030400011400d946016030110000e4038030341c4c0f1a20a00c44809004403940c03100310503241c042a550f03040101f01c80e6003c20070381d1070f100501194000900340740c41009010001444d10140008d0505d07811342081a0401c030200c003515001d950104031707209801d0004454425859240c104449031800200b403a01e010340040c020f503405201c5207083e09540d00003000032889071a030090001030003884180801e19140e0008001c002915100341002d2035101e0002d0703640c040060380120140d12100c0c6500141c144a8030202c01423509090030b5482900d41a080d6459600040102007055503410001d40e0658881100713009071034400000b05104c41c0c480c13402034000c007180d42c1d0135404a0b01c11004c0d14244481c1081100d0088014a441d115991910003541c840e908120000814552a000e070300b004100200b1040900c03004903140814443e14040074050595030340f600f498050310003003040007960350b01da = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 848353938 1250 848352688 848352691
    0xf0909062702040203280c11070b0d02030a020c0d02010905070816170106030503120a0609020702030a14032713021e0307140a0203030a06050402180f0f0a0b031602010b09 75
    0x1502c002d0b03aa940c80030400703860b0881c440301034400c1b41030036040d21a80d1403066200c41040403003601e48405440c58208040e035620b0305841802500b441c2005039000d810003a40240d50020989070340035043c8040e08003060304060304024940c005030b5403116900f09000c02005100c004045c0c0c2c0015000c0140070003041e0b140101c490081c0c0c039030164885d400740d001c02400d40c07001d401560082c081d240c4600c070303481010818203404d9078016403140c20700d00d021400304100d10031204000d50040041030800500c1e61100300c2c000d00400052402d00050101c890502c0208240c00b20704610545440603001c0b6200401c911a07006040038400c8600c10300c0154500c860001c5c041940480c42c101c681d0b281d075101c1d1400ca6141e001c0c4000c024195102241c2500782c1600000514000c1e24902000d103e05525801031204034094a00c200c0201040400200003d04041c09400102c0c940135220a0a6036000d0001c608005402e50010708660400801c1000401c1e01161a0255103034502c020b000e00c1e070110703001448a210 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 848355188 1250 848353938 848353943
    0x1b01170402031e070f050618010c0c030b16021905032a0304240f0f03231e100614030a020d0e03040503010b010206100b0f040f09090627 60
    0x20540045400c1d903808208900e084010b8070100e6100082d03880c407140e121150361107951604444650082124900302066500c03140c10042194190821a0300460300b560300034909581681c46082c01101094081401c0f900c5404410502401d02d1141c807002032030566502c0c0b00c0c0858840e40e60034074000580100c02c480d007005202684000c0c502d17070024603250071626880d07050001c1c480024001105200c003d6484240c8c03800360303504c5c104505902c4082c0c0d12000e9480d05003000401d2040d0320710200d8001e601620040004040c181300380140c48a85041285080da4845502594410002000742465100130351203d4800b40328440c0c60b14107280540560102d40c1740203803010001c00003a040d00407950507181c00c50000e90342441061005142c4542b40c0e401400b826010b5400c0941505240d40009080e0340140b240d2804081d070649412090009904081c1000e030000e0020000080c0c5c10301e0b8214070201900031b2400c0003400d07112a10700201180c0304440e486605c40002d0903440d88640311481482030007038 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 848356438 1250 848355188 848355227
    0x9030f12050606180a1203031a091006050a0c081803070b040b09010f0c0b040b18030a05030c0703090302220b0a1d10380301081209040603080414031b01 67
    0x486000003417980d581c15080018a20700d007004902c28160b06801040c2e50481030030320015182214802e00c92900c1c4c0454240c40056241308080001902c103c006000d84005850104140c01e410355440f44180c0c00b0841c0d070307000e0341f6810f0070f0209680307818000d2000a10720340407a00d16003403410500241c2401800400b50500548a54020519000311601e04d611540100d0100441c0b4092602440c8101d060360800003024044020b11040fa4000084410f0381e0001d44030350341180d4946000781000e0344120310803010001d4034000000180c45441c00000e04200c11828040c202c0c604011084c00c0f80d6402001c1c610400307440343c0803c001003450b13601081031a48091440d005030b035510a402101c154640c0703c001d031003015101c101000d4907241c0442210105405103070b810044c003241c403000d1030b0000380190501904034112401c40007a800004140781400688007083c030581d6507c5640d820b810983c40b0708180707241e1015100080c80c050001041980c819118061091990b4000804d01000b04070118103d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 848357688 1250 848356438 848356477
    0x90a03030b0a17030a0e0f0f240309031224010302090a0812040810140c03130510020c0d03050906070c060207050601032f010c032109030f12050606 65
    0x5441e6002d0440181c08204590b059810360a20425502c3d03200e0f0005200040c0ba11030701c254180ba1030640081c01c601c00904c403091404c451000c225000541d0144d00400e00322100f00d00c2c0c08a01e01d90080d511584c404030185444500c1081009010780c4000c00300c400e005c2c0030f0082c00304903149481080307020080030300e030068880da40e10000c5165800e094119142134454510700f0340e001100c1e0002441a80c01800940c1c01007880c124500d02607a0280c4800e040720128400098502c580b420040d550046c1d0014001104003075544401c2e0a00303102030452500aa0005062500d400e0304020139400038038a450200064a08000110349415000e04400c040081d1500314005012290b0103079000c00b6000001c0d45c207196583c2c03401421507039148448044494501e10711407110501d04803601c00b441c8043c2c41d000000001650100c8032596450368141030900131080c0c00e14409214441d811415100f915241c003803403900c0c8806000c175410303504401915414030f400c000070340c8c50340303000e403200150380008225a0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 848358938 1250 848357688 848357711
    0x20a1a0f04061a1e18090307060903050f180108090d020606010809030708040b030f0f221e0f0b0c0414150910090e0a0603031b02011b05100b09090a0303 67
    0x10700051040c8661003141000c8807103130540c92040c5103002150407a4150355503140401e1000b0700700f0046a240c90319800501168001c5155a00031996030340c8a803074054949006510f0580a40e0000c0048603450041900300305180d581003404541c0016a102c0109801604040c1c005d5407400002c04440c100883d020215040c00020000d482040f640120302a0b145c64644604100d00e402c115050901d2051203408144401000b40b0864000c001803100e45050100d055542224201c0d110003c40f0030841c540030301f12801e8a21442c8011052040010745018640c1d801d101c00f5100d0040c003900740c0000304120401a086640352200c183c80d100383d80d80345040c65840a042e400c1d00580701d01d5600312448002c103603d056841140d0806440e2458011142a25680315082c200c80d850f010040201d443e5580240c03001048080c900b1409105141421009008000c50f101e03100340060111034a07807201c0d0071000007d40341d0254020558040d1214842443c054804550755650620081c0605a680c030701202c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 848360188 1250 848358938 848358971
    0x180906070f11070303031515021002070c0306020c010b100906170a0906060602160605030606030403030e07030c26062e0f060f08070305010509161b03020a1a0f0406 72
    0x40c4400d0800ea510f030036602d00b00076020301030400000c25451030004c0003203007030403440c3c0b6034400c0c031005540140b40282580d41000001d50001d034040d2603102d001100000003692030700050000c20300c1c00f400807036004106000d11906480c0c110610041c00142d203400e00c01203900c500740c45d80c814490305c400c128640301d04101c0300080c01d803940b014225904024010a8003500020480300340c0f40880040700c036080da2842d0071a080e010035074495502000400104010034441d4001c0c0540203960020b50f00215070f6513850340d4036003140742d000c55641d40c0b1382451a403c26402d011070380b407682079010162405182861481320b81c0700005030012008416010301d6a41c8803038812958025003141e40b012810981c44140140c048500195500001080c02000030749170b605c640160340c1200c1003e00b925403503440342c03c01d6003a24800412200d0410088401100403982000b5003240482d0094024080010107401e048404500e40c0c804550380c01121402e0040d00c000e603081c400d51160300702d100060304804000714620b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 848361438 1250 848360188 848360207
    0x70503040906081005010e4c06140901050a02030c0703150f05040b2e030309170c010804060e011112010512070806070806010905030d022808090f0301060f14180906070f 74
    0x480c1440b42340c1040f002004140403071090b1981e0a03541c9a2200d68446c022510030000d00c41c100c04119003400b0814017940908040e190a245a005407400c048550981d00e2500129a00c06c0c0c0b82801104110703046062244202000c0281800c8c09115614054980718a002000f0700001e0490141c02c400001c0c80200c4403984281c503841c00d440d00e20040e920b05005040b8002d078061042407052010188041c8040040c540c0c1c4031844c1030b140d000d0240e03510b8030b501008004805241d981c80d526900805100c00504c00288249903034843c1808041d41800300340030604540350742040c9190b01407142845012400a625580581a45007038030700c598404d00122001c2d0783c0d5600135605882002070100941c1d8003c50311140c510241c0c980b000d80740650101401c9000328801d406814034500b04821900c41c00c1c84e00d0b4401c4603200180011410b05c0d83d9100c0c20118110f41e070b002c5580c4001c4001c58848034070b4880f05180c40410134081c0312240d41040b161a0362200301c041c1c092414041d60403c0e0303444890040d031200c0b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 848362688 1250 848361438 848361511
    0x70f050d06091a010503060f060907110111040f08070f0602150a14040b1816030b0a0b030718050c090a05090a0b1002011406030a050a03080c070503040906081005010e 73
    0x3c03d11030081ca141100d810030a014041c03282c00341000044031514105480340c410540281410202d8984403026107451b5281c1c0c2013904655203d844403e1091101070084c001400d0041c0c0902000740382035821402d001c843d0308214095035503040100501540001c103039015014800d81c88042c1c0d254841800f00501c9191181c0301c08442000400c014400c0100601d48a003900501c8040d098400d12902c07038a403804114401c0900002d031000340081001c1004159010303402100011350085a00002450f0460326031201d504642041c0c54000003410031b000d9a504040c011012074182900640011007904450140364040c1840f000082c52040d41a041140d046a0241600d000c40f5042c68000f4081d0072100b010201c20307004d22002c9841c80c02d00280b1040c3c07082e001070150100712881e5a088499038805802021184000c1c40b45402160050000303000a0138103807000a01640303808100343c2400c14904049200707038540f4004216030760030596007903481181f088411000030814900341c0041503068544 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 848363938 1250 848362688 848362703
    0x7050403050a08030106110d09060534021e0603060d02060d29030307080307030203090a080c0a0c0e04150c0329150319110415080a0b03070f050d0609 66
    0xa0b8050080100c000d5041e101d05540d40f010b039410400720540c0c1d0321501188040003981045003001074038801c001908201501c05101c1801c181e04580480c900588015101581046000000210319002070b55500c4541c1d210040001203005600091841c00020005ea00481d4805449004c550782e40040703580d40d6900c2d08003000f084d8000c00005c41e81c415070119841c1e0444c0041a500b030241b078008140d58800f540700024525580c2c81110440103900f000d800040780384900c15152001420a10141841594220042c0b8043d055410040e0601d0204c1d44080071688112050101003511007000c2c40603103000c1a0045004100c0d410f044004000070007a900c2d01002c01c1d14403611260050301c041808034005c98400e40c8122000c040c54071075210989620b9048070038080011b1403040309800c0103400510010b48103092980e60744d42010152006060040024004020084200d015224400c812031041e001080080c0c246400180c162015014051044008044c95400c005594201c0300b00c1d0ba900040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 848365188 1250 848363938 848363953
    0x40b0c0c1c0e0a2603190e010912030e0d1506030819050f1b0c040e0c15090604031515030f26040504051e09070e010e010e0c030705040305 61
    0x203003540311140c030240000001c40d40d100d5880c46140421803401644e0420320190010b0b031180d0152107081210303c5100400380828400d401c5160710b12100300c00041e9060311f69509081104000610f2060581c00000e511950241c1001c0403e83c40101a040c0c40c5054130341c1e18004441d410200300020b010f1400c0c00c0c8050030301c1404420820420302401c2d000d6202000828002e80c0c07400e0603a282c2c028003000060458003031119030703401002d003030f045801c10721041e084d41c10444a1030041810345041d00d01462076544070300303825050f504189510101d0b10f070550014a04012101000982502c940d22010385155804d021070341211003540d010058000181c1c1d500f00090b50f480c5003103010303000ca80c0c8050303075080101004a0901803100200440d4140300b1650030b0f142608050802c4000c100280010842008500704c02180c0310040c4240750164560a00910150303251409854031110140c00090005541da0010403d420003040d94640008442481d19101d076a1a00100c400b802217a00151180c0704030030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 848366438 1250 848365188 848365213
    0x3020c0a120f02010f0e06040210050403120c02122d1e070e0c09060a110c0d0615050d02060403020f031f0209100e1503060f090f0f0717040b0c0c 64
    0x1020b0314602c65440e0001d01070810386048602c12100c940041000c580c1040c000240189055111101c503c1d138941080303420651a510340540b1008081185008281c46140c2d200c158501004c81c1000050340400410444074000f5807c10107001114483c1c0c7c100f1300203021710030703c41000e04c00c8a0040c400706000000300f85900c428140d2300d11081c4900c01c0200d04074004940313021100360881d00c02040c090401031810070f440030221089a061030380789200780110104100c19640f2003a803224610b0003044003061903d90b6206422001d445544024070039002c0754940c0380140c541200703450842f50100c40c0d028900d28510042070402d0b1180c911000c0d8215001c14018040b04603170301802c00e00c041656130000380c800c4080c003540c0340390001038629400f5207a00805289900248011517100101410030a542c2c210f207004200b21074001d6490848414400041100d41c080c1944079592100d15480c01141258280d03004601c069005800035104800300f0002654101003401229403550300c02044404000208 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 848367688 1250 848366438 848366447
    0x1f020405030f2b09050d03030204090903170915010e0a09080703031b050c030d0c110a0f060f020702061b01020f030f04030e030601260a02030105010e01061106041203020c0a12 77
    0x1890f400d01c07400180c1881d41ca401071442968000c505151140b16045040c03400700080440f0100080782055001c0001060312021405130480c854800d4540d00d94240c414007982c402130400503d0700c2d4030340d480802d03000a682000c1c40791304e04442c041d200121154a642a0120150011a002928100d4001504410154184d00410041d141030ba000e1180254001c000c6919110f42d101e51491079100303000f14489840c0d680e114651602e01401c048844c4098049002e0612100c01011350f041048028604d0034056903009000d401c0455400451070000346900240041c010310f1500f020303852115030312400c0000c003541150315400301d40e1115500c0c0c1c40d2502406040050890b0b04074000b0700b6a1000002c1401e001481c41d060b00e0410341200300040000d850240e000c1240050303d451845000078143c05601c0078410907018020420701b200656043c0980034103e0301600302411001e81c0a0410840800c0c01d619541034490755516000d80c0d0303044464a901d283c4400014050034030390041c1180f18806420 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 848368938 1250 848367688 848367703
    0x12171915051512010803031902160209070504030c050603061804050a1b21050c010e030705040f06051509010801030605040f02040f060501030c021c05031b041401120902031f020405030f 81
    0x2c401c0c03d0003107a03260407019880b40410340d21804011030070030f1107254829a40e005001400c044c50025800442c036500014610841a030750f02004c06c800250a0040c080e155603a00043c100507907051b07180d800c209002c51000c10441c4070600000080d0008601082401c1c040401455082b00c0381100300900f43c03090a01a800b0f0f441403815480300728243d2021f0155449041c1c0701603802a01a000c041600d400554401d43c404038000c0d0705000d1860041001d684e580706000c030789120b0b4800003070010304203400e0100c5803010000c000c030100c4c01440b01d0301c030685c0d110045034192503016070040f40381c0d1110315040c04400c141a1000b0b5000d41440c0c46002c4000700c540c00982151002d0b43c0c207020305582c0c0c3c41d0503a01c4011103803803114035149840c140d24180d070040e030046402c44034245034071205808400001459401c681c1010b05881d10b003e00032070442d82d101c1000c0f03003404002c41c02002510b285500090759044400c44e01d003c000380c1e6488543c0c0720003041d81524000d080180503239001d2003019448075120b088 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 848370188 1250 848368938 848368957
    0x120c0c060a14070c020109090b0d08120a05090303010305100c0c0f03120b06040e061005220f062109050c120a0b011401020304090209030a0f121719150515 68
    0x100040002e03c03052040740c950840c20b80685603011054240040300001d0030760405a50b4100c1142e048a81c00a009200106000005040000d1260903d00145030955001500002c4950b000b480144082000450703a000d580c2000c010020b00d002c110581601c8600880e01c0141071209013039111002c0c99045014032041042008081104424010802100d40501d0207040b201500150001e802404c021141da2407044a6050440c1412140c44400d0342c090402a807107501200003000401c16400d1715601d10b406019182000040680030b01c1c1e0142c3c80c410705620a842c0581c0f10308914081c401c043c00b0104c0c0101c400780025007081120003213141d40e40c106040813034280940e000000342c580d007206d10840035907605034003561034a0b140c40c0404010707400c0300c9080c1e0b9060145a90190016045101401c8043c0c4640d0050080301c802103030162440c03000031a6102c910754002d08206070551050344005c1051b5001400041c20000d4007190f02c160703480c2d904019000705000085074805945031001d04440c1c407 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 848371438 1250 848370188 848370221
    0x525030e192907090303030b0f12070e07080c190e040509250302030604020d141b03150f01051909020d020702130603080a2625080903120c0c060a 64
    0x42c18900e900500c003074101e9440c00000e282d4401072002038403036081069211002854100030300e0714040000c410352801609002d140d80315000c100926140e403020242d1003211400d1030051441c2c0803242d11041e03c40d449000304a01e2103000d189040d64005d400c0c54201003000b900400040c5044040640d888202d240d0b001c0c4519505481400d00c8940ca00d1088140d07513002c3c003c2c1c40240c4403517003071006031320804104440040c00c08242010705d140c10080c03140c036550071394001030040c0400000e0600723040b01c1180c03071030020302400204000307140c030007140c00d04640060721914401c00d000000010480e621b41c00c500c01a9000055280d0303514816009000024021034000400f05a02c42006049901c140f00c004d20f580000e01180584c1c03030040362140322803584000c80c0008000a00144454408112010021000c03400300110201150031441c242c0707400c01d0306000c41c060401c210015540e028196002e14410091130010702e0300f0307072940c041c0c0d22010512800c40300c3d542002c004940c0500f9152030011000d1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 848372688 1250 848371438 848371493
    0x106030e0a080703050307050d11090109142412040b01030c0e07080c3001061101021213020f031f0515131104120b0603010525030e19 59
    0x500c0049050919580c0c454007003031800030f403030b0f40640d41a04000c02d81014884207010084600225015443c0444e100015441c0c0d0785814400140100b200398200c00f0102182d119042d1850b203a4141c00c0c0f0030300e20141d07240f10460300e1260042c50103115032000200501101828881006554002a41642d108524000500d6111441c05040c0e05045a2140010f030f40740c00401c2d401440300300109a030302d10f000c035400000070041211070074450444c091641c0d030400794001081020b40c41601c1464842c1488000d500e0220070070300800c1d044401608844408140062050440d0f40b41011440f070542c028059800a501c8a11403c000b041e0b40034418846500b07080c002040e601640314010341c2d10500601307101c1550491900034006200101e0000307501d1104000200f20300a5020f00e42016070300c125000c13035481c603040b4103260030f44202030030b03040030910701402180c441d603144070100f204102c07289400500803c8444078a41380c2006010401040d0403a66412030502c240a012100c80c0d031410245031540 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 848373938 1250 848372688 848372711
    0x70b01030512090607030c03050729401a0a0b0307120b0603010618020a02010b06030606070803040c030b0705090301050f0105090112061508011b050306010e09071e08010603 76
    0x3180300f42042070f94800c04c100300320300c0041d02409821090320f00901c2c0032810010300c0d951300b1003410b84249600d428a0b0b000c40144000100200785241c1c044d4490b680c1c40c0601899110094070240000f4500d510400310214281c0c0c0e03941d40e8a0340c0e28000e41c00100c2401d18407029020741058107400e94441c2c29403414a030702d1901508000511901b252100c3d1105a0070031040c0e1280659490050001e50b419500c82c20005250310f080c142d1112101500080103946550156019007100c13080c5e001d03540140000e10800c001640d40c90143c500c1c06800440786a525078491034000c1c0ca038001c0c0c0c0c000803d106015010b0014056015004d0320507100240c0c000c000c1c07921201002e0013480000d01c0380d0340d48070610340010311a05841c00080d03c012841000042046100881e0030b59a203495900000c602e42e40d20306200e26007418801c0e007c5600c83c00c0b0b040207851810042e0000b80100c0d0020411801007200800bc180c00314407441d00c40e0b0b684503520812095a03210700c039000300007401c28440c07000042e0626000c44803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 848375188 1250 848373938 848373973
    0xa0306090b071409040507030212070f0e01080f01050103090c0308181305090607031e11090109211b05041404120504080a0f020d02090f0103051e21040b070b010305 72
    0x340403c51600f0203003801c2a0104000103003400420b00400c15409000c000020102070045c46d01070081c07512050610700d00c00c07400500c51541c5403080c0d03040101503018084112242c1c21024152202860040b0b215a50343c2081d400200310307a40f005040c4000001e05040002c3d00c0c0342c501c045010122600322045900a04c00340958106590000b040d4000d48007046006001c2d80c881100300c195498501c80d04444034203600b080f110030300003e05914000248005441d80e004107810054081c40c9020720107100800c81e921510101010000c1144507010080f005141000003082e004100084c41072201060150030000b054801781c40440301050300c0e503108070355640280d041e10152200400181814100d50311303800c1d5240660780040e40c011402200c00390160b11552620792190400781d10a8500d940b540c90418500046031150202c100d98400c40031910707403408162070003d020355035410800b12011005884152113244d11403400100001030f400d04014100802604990048007900c0303d403e0600841710 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 848376438 1250 848375188 848375207
    0x705030601140609040c090902040605030118051015030f020a0e010f05030105030a020103051909050a1b15030e010e01061e052403090a050607030204080615010207090b0607020a0306090b07 83
    0x3e070302100a001800b0f59041540c801150500c140c6080162207030b0b600f610404aa009800181c00580008010f10402c007041000c0e0000c0c20340818208400c3c81e14a1080c0c5018031f0305c0c01940000c11045000555a03031190b0401c80d9010180e4100b19629020170354083e003c8400b501c000782c00310b000b1140d043d000a0156055078121103025016041c401030750741c0114002c200041414819050346e03094900940404d00c9900903c51180c4000e142502d004e0800140d1025141780c42e04e00300e07481c41001d00a180080c084100c18014034203001c031394141d2400405000d02a2041f40004a40c030f003042c001103240e030b03034180d0302805c251402400100c1d6448900703021181700e40c8102d04840080f0203034148100e401d483c004591000d003200c1901c0c00e13100190707200317400d000f01540c8000c000794022405000d004170920030990000b40340c202c0c0e41500929000082d44401c914461b44000d542d80340140d0720720744c03100e4086036042540100802032039512454014018944400241d030050f8004002900403400b5000f1075 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 848377688 1250 848376438 848376479
    0x30f040302150f0601030e01060306050f010f09020c0a0f02131506140f030429070c0606060e0916020c2205010b1c09061e0b030606010203280c140705030601 69
    0x51440e43c4d10800190080c1a200f020f45000d0744d610000000850b10a10969005036055102c3c03030400d5150041301807a103500c0b50082002c40e84100140001420001400052154007851011784a05c00380001009640000c500303a06150428003c0040740200c43d24080a0341c1540d1a481040c109904c4200c40c41e004081c01031050b554100046000300d5000e8060029280580720a8101c002c0d5000e036010156809807000c0c030110f458000d282c1d040022501800025103000e20f170180071084c40600240c42d194020b0503520020f5540e640c2e00c020580300b070144500c2241c0240c5141d401c4685030500c24103000000e2003a24035240b84c40c00104a500c0054116020030003013075050782c00c0009500c6010010020300c01e0407900e455844032001c0c9900c0240007070404503403944800059030a2150181400d00600600003411904104a078003901a0464504411030810900c0d40542690500082d1a5100030000c003600102c0585007a95840100250190940b5030540c107650051340d8640300e01d4031a0b8820b0501 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 848378938 1250 848377688 848377711
    0x907020c0d1403040f0801022505031c11040b030412030905150a020405150d0501050103060b071403090306040c08070f0f0608150604060c1e020901120f0206030f04030215 75
    0x94000c505400c002d05084609102070341c0c50035984154500030745104e03034040b0165940129603502c4400c41440ba90307210701c44030074620401d0381c0c041c0d8541d81c0703e11a2100e44480401080c1605c90b000c8d1255005528180103019680da4440c0c598030351580641040ba02241d807501c203195002103680c402c1c0030380b40d0310b5035205000b0310300b4101200d03403403503003450051000c10034a60910002503590b69020300312800c142003650346980c4800203e0104240c0c0c2c0c058000c0f40c1410b090003000c114090041f011609a02d4200c00078501030300f10010390904610030110110383c07501c954014402406a41110351040759101c40803954495600c2c8104422400305100b4814599641902000342c240140002688401d500a2001120100800140380c03601b050f0080740000300010703019410405440d03d040884059a0042c00e02d01d18980c1c00111045014043c1c00381c101182c401c940c0c100440140b201028642c001c00f101d489103400e2001c410904000c4800303400600c110001c01032810241e014a601482c203d16a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 848380188 1250 848378938 848378959
    0x40909060e030a020d121b08040b0a14010603110d0603110a2405090102011d010f0e03070221190605150d0308240a090c02010b010f020a1e0f050109020907020c 70
    0x1e050b915250017010b0b20b560300d80c803203500da424400381e10f181f0800000c3c56111602c4504040c1070103103401c00010207081a03d13240040208201e1520740c10b940c1190090706c4c0200d00c0c03510f10501580ba0380690750b03180d508282044004003c100d4000422244030320141c3d4000d000740d60f1880c040e00540030052030f0000c58019049180c07805485100200380300300f0180008a402032082503841c0b0401284c1d480c041f6507965901e000ba144c000c07107010745203201107030304011814154590002074424014244001204120b2a402ca8941409104101d07441e0b01a400f103542c034104038103000000d410121500408810500034032076462030f006001c0003070b00f030b0565140300303540c0c0d2040a0051003403d05d40044c00c018144207104885035841304580400f0b82043c40c00801d072000a04000303800c0d2468141c03581c3c14042807a4070003104c140d000422400c00c036044a40e241820b241c1c801100740d008000034001c0c06041910040906001c03054112042c1c0314400d40300d80c49241d0720301a040b6203070202c0c0105983d01c6141c030b04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 848381294 1106 848380188 848380213
    0xa03020120040506070c1203120b040603080316030e03180901170a1502040b040b0c0709020405130b03030910090f05031b01030f11040909060e030a02 66
    0x812002000c458120003640128003502d8001c480c00708001c0d007800200206e1000a11000e030a00d10320340c80605000f000f18a40350110b00855062068a50031400d103441014100c9800004103829615201e01d40060282100c000104164a40b0348134002224240002d05455140c0c001110311800ca200901c030400d070b0160310a20b555455403110340030007100400c0120920b5401101e40f030f804000000c0000003030107550010b484136240800c011034951403c000a00c60340310800304035602207a44150b071105a21841c0140d0360408202552403998007441e030040c4003242d1004041d2400e111006000c20346482d0101000300c0015250701041000592800040380030f0702c03003074000d071040402006440e0408000420f401e03042680d540d681941c80c502c0ca44c40071565075a001c170415a119134039503604d8003900c44070409079000303450010301c00f614840c0081100d00c01c1d010760b00680301012614 = true := by decide +kernel

theorem cover : BRFrame.Cov 848201438 848381294 := by
  have h0 := BRFrame.cov_init 848201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 848201438 ≤ n) (h2 : n < 848381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
