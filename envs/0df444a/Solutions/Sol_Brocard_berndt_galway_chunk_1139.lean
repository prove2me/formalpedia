-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1139
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:24:36.650314+00:00
-- url     : https://prove2.me/submissions/1d42e35a-ff08-4a36-9f88-6fd018d1d677

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 204676258 ≤ n < 204856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 204677508 1250 204676258 204676261
    0x1501060f0809070612090b18010e010e06060103050405150115030501090b2404030515060a0b0a0c12030e010c09050a05040603020a050405150a060c0b130b07030c02100c0e18 76
    0x8000383c86035558010b00b001c102c80040c00c014250102d8000c00d2125401c042d402e4039030f09101441c84041044039008041541c03e1007042244100c0c148941801300b114400680041c0d01d444004501a21018209030360302c4c17059241c4043c044080e01401c2d4020444c803e45000c481400100203016550305920126140d0310f0880d42c2d00c03d03034585080001c44600c107003400e04440104e03518501004d0080b038002030030303500c42e2241d40a07903500a01c4490b8041c0b94215004480a41d131084040560310514505000060404008800080000078005402003141c100440c4501c035030140c6500319140c007415040001d0080720100441d00340544d520740170f04425170301480003601f941c002c0750310f0a24903c141400b86a4442c0020280000c1d64a01d0020b0540103001c090003984e59100202444101181030b10070704003030030125540d19800c9081034606075000c03152070190741e40c8410035030081000949640550181c0d0740c0d400140c245510480380818526101c1256820300842800a000c40c00c0e01c5401e00c0e503001341c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 204678758 1250 204677508 204677521
    0x1003110703031508011401051c030507110a0b21010603050108120702040204030614070207051f11100203010f0602161a0a090305030f070303050603011b050903030c1501060f08 77
    0x8200e030055500340c20040b0b410100b121803441c0c8240380d9848107200b5440c040c2c0a00750600c285003054102d55040340c1003000c1044147d09514114a41c4400401051f003c228080c00146c0340c007521070b50071100421440e6241c0e43ca148202d1994001d02548140b20083d181200503003500d54a102d0240110703150030805581400c400a941d9001c41c0b0140106c0d0710046038810031907071181c0489000d140c0c000c0c418042c2122500c504408468152403050260182c404040f80c24105250040c50b920100da012092143c00900e040d41c0d91082c0c07042d400c580e03000b5450038040c204858001035000b001d6515a502d6000d20313040000707090458007030b1880215040500100a070f0a9441d00e400410310702ea00042d036071401c0d000030036900a08141d000618038000070a002e0542c2d0b500c00003600d03025000b81c40c01d101c0c0341d5400b0101400c846200820101114561881003690307031140e8050084014040c08803850244030741c81c464900105c0300d44061400d0384c28801441700b16808034041207498868200710302c0904110 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 204680008 1250 204678758 204678791
    0x708071b080d05180604060203040509090a031d030309040c080615031e070504120506041707020d0b0c131202031207081903110c0105240d06090303150e061003 70
    0x10b007081c4082290115000c80a140e01e0b22514403402c40003040e85a076a43e0314940a901e0340c00134465144500d0301500000d44820b804942909419415581c8802844040c01d004070303043c000c0c41549401d8030042c0004005501e8510844400c007116031162195883c00404100141054400c00c1c1400402170003132101d040401150341d40c40c2c4070782d0b241c891070994034110220707880d0140e9442000381d40501c580c1e01c2c0901001144081c007843c060b4954002812100141c07260620a14400075040003213000c9040c08034000b07072105074000042031500d038a04801c1c80d46400100d00503400c070450810501e9829021858104000e020b849002141242407440302e403205525030003405000340540c07603400700b2001e84512a600c0311040892054441d0b4450110b1003aa0b4003c11007150801855000d400700c089008041c1101c0080d24440288900d000c201c90b0358801010b010002422002d041d142c010b001c00745c20482d60440058a61020380c20341501e03100040000960320080d000d814140b038050b800d40100100f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 204681258 1250 204680008 204680023
    0x6091103060d0521040603050106050702060d0b0136050904080301060c020105040306060b1305030c1012140103030c0b07030c08270613030e151614030708071b08 71
    0x2100c2050b0054100d0804906160a286094814141c282c80c0361543c00041c40180c002d0350b01d40c1e0380401081ea203841059a09104860300654003800600c0307254192212604600a620340614000610041c41c901d0740d545850300b00011040d200500680c6005a031400380742c503004120444090442e8109610b80f11124031042c05200300304180c9100c15400d690080d42110003e642c4200108403256a4540405403274101d6070305003130426401c2400013a98940000e08854220f0000e10080e05480f000106503040000c4180407a510380d15400b00240f91804010304034020741c02138452107101d40d001d250030601414002c010341d040c1403500300c205803842c1c0c3c80b030811688115000c00b003156119070002c03121103049000b41c1a6030315106d540104512050203640701e855030b5102c0d0316034051500080c0e04101c41000302c003022000c1c400d4140861516804c0850905e01000d01900040c130391481d8906100c0d0650b400308105a8070000002603d80400140c09036202c0381e0120203510b444c000d8180148581c40381c40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 204682508 1250 204681258 204681271
    0x1050a050603100b030c031e0106050d0e07050409050705090106051303021309150b0f01020307080f07030504080f0604172a0304050301090f02150c03070303020d0b06160606091103 79
    0x3000300015072510380d40300348030000c1c221100130789440c0d02d4103078907640300c99008031000400101a0000c2e001090300d52000c46060b0b507869102c2c40d090a4407419072000602c84a02c002c0b2440c403400000180c507403200c0c41481c6506005102420515042409210f902035040c1e101c0010007000304244800380c58101410710690354120340d41c0028003008213045020301000d2101401c0600122206044059640d00c448400407080c1d404520020392540103a8507406003440241800108025512070300d4007200007400181d109090650916803107040403441e01e482c50401d441e15502040c2400705000c10341c0c2c0804440d901c00340707519107003134403100c02504007480990807140030301511788140241c08024020345000e00380c06002044407803841c0c188400c1201100d00141d004000c84d8810800003001001101d07101c404080c02145461802c1d502100250b00c00104015980d030356403c0151240d0b5010000c00c03011190810600242c0c1060414008650b0550f211021081c640160180e2900300c40095952084 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 204683758 1250 204682508 204682519
    0x3090804180b010e0315041e170d0b040209240906120a0c02011401060c03170f0403020f0613060902030a0206030c1309060b0f031e072601050a05 64
    0x1445458825400d02494009080d03a088640e852450801c01c2d0307002c089225001d9071500145000c0d0340501d0344403803006001c0000a84441c000a000c20040c4041000640040c1c00e260108401c81e101d000e03d00f50b140c0421000c880c00010b0000340c039940c0b4095000091400c9404518080490000179010701c003151094081d0907881c044106900704c00c0381510b42d66100075141d20741d120041c4580e0310007440112040e808952404000c43c40041c81441001c41691ba1007102c081e0603400d01c0800d56800c0340c0c2d164210304024002091000312040c400c1c0385405400d040d07048000ca400c0030700d000307400d03d08441c80010070f542c840801c0040209404607044103440d0800070005030206c070760000c2800c2c07030244003010390000400424444580700420003000300048089201c0d8541d84c17280c05a20564500380302d47c4013042c0c000c0c0042803001000c03000441e0407180d48c4c1c0049000a5541103070540c24241154198080307402c1c5000c000b1300d400c2141d014004603613000302c0b54032550704007000143c100082c2e004850262 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 204685008 1250 204683758 204683771
    0xb09060307080a1d102a050d0e0d080f070215180f030703050915040b0301150302070c031209080606090c0a0903050303010e0103020f1c0201030507090509010e011508011503 76
    0x1030000d58810300c90007402c0b40c0c8158100b01c80e864129600c034040b01141d1070b506c0ca442412411400b4038201c0200180c0002e0b4401428415140c04407800d070454881c2d4401d9950310300c0d694114a00030440c904a440c131581b540045454811203030715171007100401010540d000180c2c011900b829030142c0b07030340c400c42849278141d20010409a2038545034004c00201d0389484001090024103420a01a161016048603990444001d04001da41e003802140315035940110b0500c014825000203c0254100c4c14051a0041c1031945907180c075132034030751168400c3d550440400144079005a024000f140604a040010030450500b280864000c940040802092080c04102603031110711403007500004540000c202c80e22542c403883c0000e018a400c0c40101d11981000400d0103103802d021059444408400507200c0c04090145c006401920000301448200300a4180200b8156a0440b0780e9001e40f5100d10391042ca0b60400199042041c0d00e81609818482030000400c501c61010040d504040058500030401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 204686258 1250 204685008 204685021
    0x402100c1502030612070e01030b0c0d02030717070c0201090b0705031c0509150103020f01120b0a06260f04080a17070e03010f020906090d0503040305190605010b0906030708 76
    0x2a40e001500900c26065500d44404820042d009180501c074200c070280448108040890781c0e900103032240101c40111200100301040143e503815500907041108985020540c10505040380d008803005c1002c40e400a1903a0258a005200f0307070f0380a400782c1002c91860b02142c00282005015210388060030800061203010003005009503420070b00740c0840382e01c000140c3c5000d007000d06003c650006440c85a00c2581b0b82104099011380e049075009019a4032214035500115200452403c80c0c070310301c03900d40c40c101e40c0071344440800400401096a402c2c442d850005106400c41e200c4800d0044801c00c03003001d1001d040e84505986410643c8048181d81e02d05442c8016a040c00c40c5032081180000814200300495070400210150071800b203008001000ca1803e001040f4003c01d444190070035028045052503040980100030307503d0091041302c1c1015a2541c03000d103800d010250081ea0800c0c0400d40c20700308480c42c003d003805441c4288600b8140300c2c0c0100450039a00005003101e01300500b04002c19070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 204687508 1250 204686258 204686267
    0x8010912110703410d180e0702010e0610051507030e0603091504140f0601180c030207081b10020a0f0f110a05010608120c030403060504081615060503010207020108040210 75
    0x6210310640509a8001036402c0004441d407140e030821541c00703201c001241941c1b080c01c02d102d43c00407030040310103064141006543c0b90a00103140805542d610304500303072840410070845100e5151200000d0703c0c00e00704010b0240c1c0094a448101c030303000c801e015160000b5003041c02c030400c01c0c6003500c980361a50340f605082c6150a1101c4048002856004107000c184401c0340d0840000400680403a80540c24001821741ea8210074403c10002c0303948200d00214032000c60b00800c8404c0900d183c00740c24410a80c03100200355012030900d058000e0f03d0f140e0020031100c02e002801c0420248103085007084404407004c2c0c411190540b0140c00c102c29001f82405440c01410542c0c0007004650403200c01d01c0d21403500714020b002c24002c841c0e140c071440015441040500045034010360400c8081c42c1840c1ca90358814004d00b5002e40215070705402070200884003040d0f8001e612019000c0d05d0043c00100407120440203c0301980c000c907000764010403c07000903076001550b00c1d800650507075140c41d84a00f00300c1c0448 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 204688758 1250 204687508 204687563
    0xb040b03070c080f03100e07020303070806091003050709060311010c030e130906050a1a0f060909090c060a020a020a0b03010e040f060609330e0718050a08010912110703 74
    0x4004c0d600220610004807580a82001514981070051956490b140b0040e40d0764003080344c050000901c42343c00100c1c0d40c108104450341104031501103030b03007180c1c69540c0c2074284102078200c0e007142c96a46000b00f080c0000c101c0c0c50401c040081c20300b11001e07951520000e100e25100d5113001d026019010340484010140e92140002a070401c008000030309001c924072024080c0360400c010a10362203501c17035440f85401c81e14a00c1c0008010b01144c50301000d01e09008100c1d000420010310340c0030349651300394191030f850000c10078607130541d000e84440c884610402c80303441d030780d07810801d8880340500062004c8a8540303880b41d005500701903040100e14285c075100e0061b0103140c0241940e00d09064600c503580700344050030402c81e240da4540f0002c00400d12200714024a1034803441d40d4003400300c008210603d008403014650104540d0700b00f034105845002003040001ea1b07a000805a82d507030504401805400c2012018880b5546001420010009110742e075522041c000a0702d42182c140030398992016244120 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 204690008 1250 204688758 204688777
    0x210d03181205030a0b030106050a03060e0f06040302032214041a0a060504081516120e031b0f0a02011d0a0911070311010c1704030e04060b0903070b040b03070c08 71
    0x41c00c5070a40800010081d400644003400c0c001c1c182000d1000602e0103005207000d6803009800e015205107991030300d6000d45040e01c18403181c1d02610080e1106c001d014000709100e140a40c000b0340d520100e01043c5000e41d4801010300c8103a4030b00384821700030000020404801a07108540100da0f031a008000d00c01140d50409101d5480b803084c030000651140c100c0082c00403525180195841d02c91007000100f00e4500488407821210440a070780c49049000f03510303c0b0001502c6490000314400c603016014691381c80000403c03000700343e2a0840c4403800c0d0401003a40e400d00d803034020305110301c0316600203003642e000c100310545021006201c032034a60701c4481400008090301c86061110603140540c040859020704002c0d00080e000d1101d608900805009d40900c490090342d8140b50101c1d41c03a260049007001410841c10014507040000a90b907640c021070002c6e191401c0c9070f5503540c0c030442c10185080320f1584041c20580c4140010410706100b013003680d03407120543c100003140e00784500c0c0c090071074807882288 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 204691258 1250 204690008 204690023
    0x50301050a06120e07091d03070c05060c10020f070c050d02100f0e0603011e051c0618020301051603051605040b0309030c0a0b0601080105040519090305091e210d0318 73
    0x400c80386c0394000401046000c14454240319071445610b4480c80b440304060b01d40c075409001013003642410b00003031192844800543c0d1440c075012000205a070b2003400b40c0f50070211b020a202c0300388651440c1100050504640004040903a6070114402016920004050005003060100c13014015071400007400c070300400132641e0b581c44800014128000071194125002070f68404241070400c0c3d24070111075404001c01420390601c3e039070350b48041c1c003c1c810325611110b40c8100640058900f40120b80c0116114090304400700303040c5100904446d802084481070354442111044481d400000b180d0544040d000c0c3c550741c07030391868052031441c410030039200e0311031040110160901c92255031407070142409a907440d41c40c1c1d98500400040d100b0540301d0b1140c010301c1540a0b07001c43c800342c2c08044654441d06000b0b06080c403107400140e03821950007000b50744408510400072145450f04000010f050080c2540044032410301120303964103824440e1000f03050740c540c0210341d1a801d9680110440780e11100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 204692508 1250 204691258 204691273
    0x40b040b04020a051504150228151a040f021e0309010b0a0e01090f0b060f0a03090b0901020a0306091406010f0e06071a06120d050f070c0b0702030d050301050a06120e 73
    0x14217410354130501c80e00c141031000c109000c8403144046140c1c402880e82c590400c0354800c80140e40c0d14650030f1084100c0d00b00d41e007a064000d000c82d450260524284d0792400080c000f664413400c0c001542e5203420281035403072041083d089004a400456100f46100e641c20940b2039031420f800500603c00000842d50201c112100010720484000406040c0e81c082001844960a2031003c50107a40d40c002c0460340c4110113105c4411000c981c80083c01032001607107004183e0100944628805c031105450901c02650001410703203590307406000e041c0040201060802002c0036130004240e8031303031000d40302d14100907560981000007440b46c0003d008018000380001e03907400f424a8a03110444030b10031445a1190408001041c514150f4244517000032480040c11103220329100842d038940c801c1c10b08000c030714014850140850031144904000d4074404002c0da80d0381c8103a004061900c41280701042c100002000140310390b45a03541c21004454460600400d21088492244003030601e2800000c02845803c2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 204693758 1250 204692508 204692539
    0x10219031d0f0a0e0402030f0a050c041e090501020417031305040b0d060e0d09080606100806030a17030f06120d03051e070305060109060314060f0d05070b070b010b03040b040b04020a05 81
    0x4031181c000d62081f011240c08501051505803540506039001c1d16940145e1004c0e2441e08150308828564242c0b0a034104054441110b807070222002c40310244d85503940400c00f44415206411144584100275000314104080d0b150329041d20310b040c0c040c41d03008645a181360200350316519000c15500f83e2288052100ea0400d500c401c0e9600742c0100d0341740c0000c59540303001450050101c3c240340034a80240c0100c2c51100e0301c01098030344a20103010b940c1c051059074442c5011655400130501a0100022156564200041d0602209a02038107540c4120340c552010f21110b0800075410b00d007107a6034180410380303507282521868220010454080041c0412041200c0281d02d540400d100d500240c0b9801c00b901e48824003201150300405450007903030300d1000420400c0c600304120a00d8480024103041000c42c00e503071142d00703008080e80080c00c90030300030600000b001402c0c2841c50140076888581e40c114076241c1c558801042010700090840d008500104066403200b80000c8007801c1c025200e0382c0130043c038a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 204695008 1250 204693758 204693779
    0x601030f0b0f0105030d0c02011e0c0c05010311180103060905040609300e030724021b0d0f1401060b0a0e09070801180f1a010219031d0f0a 61
    0x34031040301d0110800000035002030403040030b00d044e1100070300100464100c0781030a5420040780c240590602402d42001d20200720030030325003070030144c190741e4084003000e003883c00103000011138000506050810700d1010140000f0030549178003842c020070f41041e040003070005900030580e5070801d903031281c1054200700c188440d941049054070310401c2036003c44a003c2550b0801c1c51058884044100310b201503240d807080c0309160310600010020242c0703504603a502c40020b84500c0401d032403201220314100030000c180c2c0500c000520502c10349050420704824500240d00300030030b8100141201103020142091200102d454550440020001c10040f611000c030003e40e60401c444801c001910b016480306241030039800c0038040c0d100c0d6221040240d08140290781d420b212602c0c400e40c9907a561030064031956280c043d007018900d0b00001c3d03c062107000c40c002410089003103c41038080100c9031440001a45c86000303110b841c158054400b400d94131003000a000c0c603d0301000949d100f24101c1c0080744003c0c01 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 204696258 1250 204695008 204695033
    0xd080f28091b0303091203050912010b190503072d08100c030605060a0e06070812040b0601050a0f0e0d060f0614030a03090312030621050d0e030c040209040e060103 72
    0x50a40307854890004038111482d00b11601000380061741091042201d0381408030544001482410038a080c140c0040c0401c00c4034180700082c619903034440d00da082d0345081060300d255480310703050429241e060411001c29500e2400340704071808000c1081841601d0803110303541c00b04031190542d0003a4096038880000350386000400d59240a14505440000160f000703120300340403900050001814810b812809540d1410050b64203900200104803440c000340c501c0c0c009008039251024008118102401d00741c1004000400c403074144402009a081041d420107103105203602c451900c0ea4404100501040c119a401e50004005a0134007400032185d04841d0469410342c0d610a8900d8181d880d80000c2540c0c0d07040030a0b000c0c3c04036204584c11702c0895000255901c40802904001c11559610840c24004003820b1544c3c05150fa2800311000400100380700541014016180011580180b440060384624614251522460340098100c406480c1c94000011002c4c000341a40c4617580d40e4241000803a10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 204697508 1250 204696258 204696263
    0x50f13260106050121240305030c060a11070b0c040b0f030a050622050705070b130b16090506031009110c120708030c0309010906020309030c010e0d080f2809 69
    0x902c80089141e5105458514118011a07003190710707900c0720100c0c0d600030403540d09802c0801696101c411604207045040341c00552160009681d10000b0000b8142411000382445a0060401c20720000f14001841660380719604401355140d1500d942e1403400143c07190b03030310403048041c2c08a904e0f01d214032030501541c8030b4903103078500744107a41d1a002000903581003130440e40d22458042a140d842030950354803c42d4084258240a0f16010403521101d0620008403040c4424580450540081015021505070040e64000e03508080c4142140060b0084ca130038006d80c3d00400d0048001402210802403000050504440c20801e0b94042043c4071141c3e400340a5035a014400ca120b00c1d1000c8030301100300d50020350011021419501d4000e042c1c12240c1c805080d9035140d6403503658920110b50188001c6000301ea13041c0096035902100c058450a41d240001d07003030fa40750040c1c030100c03d0b11138208801540c00120340074221455603d010340342c200c01c00103415405c1d16100f800402c1000c191075520a00ca101e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 204698758 1250 204697508 204697511
    0xf0c020c0a08120714070317040312030522020402130f05010206090a150e0c04140a060506030402280e040b10080606010903170c0118140d050f132601 66
    0x151503195040c0e43ea00c1e60b642d0144070f81d0042040401003559070078500d500e84a4041034440007039403511030085842e604440c0d007040090000d401c01c200300d150551950701c6070b072038201488180341a206c0c911700070311200c80c0c00186c0402c03041000c0444d56030703904648041c0d080d000381450880e10b540c002071403402e80d4013545000d0320401c000f0844a01c40080d62440c0694410083d01e1429040c0707800c40041c02d641d41100140307100d8850610031035900c501480b1480d55030020f4107042c62030034256200035135200b54051802464100f040c04050303150f00a11034122103a0100300801c804901180e480c809441c0e905c801d15440310442400100030326190310138094203452140c40d4041d9150418652104000c5c3c1b14580800d0b02036208100241801c9028404206c2240c0c0290500703800010301800c0d100d495604440c182050084401000317031502184006042c0f038002400c0710f000c00100074105100340b4400040d0340c1c00100d1403640d002c494030845030240040020042145110454078481c0080f500898000c65 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 204700008 1250 204698758 204698779
    0x2206050105040c08241512070f0c02030c04050709050a030305030402040b040606020d20190501060b030103051506030c04090506040b09060c041206270308010b0301060905090a0f0c020c 81
    0x1103104002050241c080d031205d00c0004520182c444440a241d00314013600310384a031882c1804084a1009041e81101c0114511071520748200010070803080ca86102082c03003450081c58000d620001030840410005507000503440d110f07450b00b616a00302e9544140e0340075110910110400d86d005c03020350300641c405da50034012506074500b0402551064014000142e01502d1038880c458403030300c2181c402c00704918441e072942e07141504444c140400c401d41514455006945102000801d00c201001006451200c508550440d41c1d101d484601195640c41e054035240046196645e06214110310080010002c200089242c50040d4540100321401d0380c00b100d600c400905400c5020411320300c0384025807c4c042c0382ca814010350022241c4608030030b48440c0d07a142c02071000040c480c00303a203c41d2a44401900541c9107071303107001403a0060503001540040801d10042040303540112050054440455004100d035581108800091448070071496280382040c259130402900450b40080591081d5042d801a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 204701258 1250 204700008 204700031
    0x150f02030103020d020108062d0306060402130e09030405040c08041109010b25020a120210050405130b03030c0601060e0a0602060402060a0f1e020105010e06010c02010c0209220605010504 82
    0x100d020900c0041d4010024406403030041d03106258159001000401550980622118014561400e03140340c1e060b000342402042d00300d2a00300449540110102c03810362900031342c2c0304000b0f030900082c401e6600d0000c0c00d034049488590207100780d502074003000c0d00421801d003e00d88003e040240c10364056440000d400e1701c2801c0d42c00d1451180307050b41c5491b901c481c502610f528903085c0d00ca401305801c01c407030480c282100780181e86a05510000700000c0081000465560041191a116500c5220700303001c810041004283c0703540f9031818050440607070010362800d0b0304010030704600c00d52004241c103024640000c05c003140c02c100f10441001c0b0641d84080c0c0d441d22000107980d11001500c0281d4440e00030b020300c14101c1e21070240e901c0f6280300ca15046001160700e070700700040c048075501c0310405030751203a0042c00008502c4a006510403003d103880c1d42e444041341c0010f49188002e100281c001e04036400007403107030260840c2801c01c0000400d400c02042d0a40e0400c8070082c002805514400c3c0d0802003003082 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 204702508 1250 204701258 204701261
    0xe1e010501030b010c17040e0c0301050103111e0703090902190207350307020303070f0317070c03030e07360504020a0b0703200312070810180902040207150f 69
    0x1240c1c3e0180c4820350580642e0316482201c50040407901800b140400000c106418400b455138060051480101c0d10395040000140640310102c259201f88c1e601402500f00d452400c620500c0e07000500e0410781c2e0744890605048075010055000a40928000240078940d840c61991200032110b0750307420740300100d41b00c10600544217050002e482c540f02c00c0768102d115031208010300600c0c0010034812a4a000c0865004c01d0664000c8101913034654800c049405c103240d00002c0c0d245480062485c0180c1030718009001070242d0110740c3c07010b0209941c401e042c608000c810011320010b0f00028194408080441080f01040c4641403584100307001c1d40e140c1c0c00d504044901402c0d00860780140b80722615402c20340d0742121500680b4003602000300640c220b42e050316003101030203d20710404002c0e5503520340780822584490805410b080400507100104192240c2e40850502629408801078202c420480d908134040d1803c20000381d4828070001c0c4107410804d012140e0007001c116040c05100761862010f8400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 204703758 1250 204702508 204702521
    0x30a080c1b1e0105030c040905071205010b030f04030f020a0203060112050f010b01091a04050607060e012003060105130803030c0a09060206041e03170c04090b03280203070e1e01050103 81
    0x404225084100d6a003d60280c000b85501c65070034050a4101951001810140c5805884d0309002c42c00c01c030b10005c1605028002c1501402d01c41e8051499800d180c0e0710b1596044006201804010b110241c04003ca8400c2c80500d030740030b03001802c4401c0d55858002c044188003288200311410310a45441201c5010f060041c20400b140c161034241e411454500c07042c003544121a03401c5c60101007003002040542d43c100152a901c0d0064074000340703080200403002d0844064005544100d0840c0c245684248170800840354009402e00c0e00301c0e2640550780d864541000e95402046580c0404001c00c55a103003100e029050503e0740b640c0d0b134a01c82d40c0c2c803481603850b19410b40307000d0702415142e034507a84440c00040c0c00d404280e07c01c0c0b4150012021018a012040000343d91fa00070264000038100700080b20790140310301c402d0003280985150b140352070918201d1060400d800380783c212102e01002c01d650b1306010710001071a90841031004c0c0d20300f40303c90426800d115445c803512a4014000410254440d10410 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 204705008 1250 204703758 204703789
    0x80606041503051c02030715150506070c05060f04050406120201020607080f07030203040827030f03090a09050618040501050a060f0815090f030c0a050c0d080414030a080c1b 76
    0x24294050094880b900b606100b802c10002e51004007c6000000c544d000844501c00194000042c5d42c540700340d500402450503400385204040c10f0000c0008214002080c83c1214002c6402d01d55030301c0c1a03034801c61280983d80c016a4454505000001c500524804542110f4400d0b400e03166960380b0210140d52401049d510611020308001c0058812400381c2d0045030450302583c1030074100810740381843c03c0c04924500380ea044500e4010f40b072460342130801030842480c801b0005103080c44040404a0402a054071a10500c1d54403903003c41e909840f00043c090451090141c440043e00d02418005d018180541707141085a2805d54001410700382040480140c0301c010019290f41800503629510400010300407402e54001c000c00d80f162801d0800007404011080c41c080d00482c0d1003400c4c03440c100051005041c0c06409508035034030020b18000121815142e060b0759455048501e000460703d401c0f00690020104d010010f0082445607000414460141e005955580841440c60074483d031024142c000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 204706258 1250 204705008 204705013
    0x130519030f060b0303040f0b0a0329130209090403050309071a0f1317011d0d05070f05010b060d06090506010f02100c1202070303060e13050c1e0a08060604150305 71
    0x1a0000b0750702d07009100041c100404503810952106603032408071100d82d0006800620006060441c1342d014041c401910b40c8800701c101c0402c5c0d0f0701c07849049036110071107003511a071224500c1d82c1004c102175050f1844403001425207a000d242614020304594016105c44125100d000710004070382072900508040c0c400395840060030146100b11140c00e41c0c01c001e45180049c05020343c0424180040078035111008200000440c4d074451a50f0700714007601410b0000c902581201202c81c4855070003600f11000123a010052406100e880d00300980189030002c039459000500080c60301b2135502c00d40211040c0d0b428144100b04980b18040150340c07401c0347c0c03078006000da0412820f00051211580c042100307202ea0b400c09407018865855150201e070312854084000c82e41d00c040034400385000040b001c1c0c5c404030607100700c040b109090301c64640c0c0320381c807075500342c8141001621840d2007411000b26240383c0030701800c4048110b490f00300d03050302c84004441240c016894011781d1881d14080108030400c03039400001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 204707508 1250 204706258 204706283
    0x12070b0a0206010503150c1804020910080604060906260f0609150a1505100207050301090614060105070c0b0d090f0302010b032a060304030c050303100f051005030a050403031113051903 81
    0x880c000b60051a2107030380e4000d0342401580c0bc20740798003e110729580300c180e031400d109190402c1007004480c5140c104c0c0071018680f080a000800300e101e04505070700c410700740c11401c40a64030a01494040105407618040c010b5400f0320507801d40008800c0491200090f28100b19500c2184d980c003240c00e100b06024220308018020002d03800c1103040440604114130503a03041e40c1d00c450109007564081001102c240b591001d603130490100400030240c0050003481c0a501d4800c084c3c540c4440300e034040c001c800e0000000a81c0511003211070f8409590241e12164030032251901d400e010340201042035000b8080d006a18010301c0901500320f4000c0c941d000444541d4002c01079170240061500000c3c012000e00000703001d0100480c4041018500c5100784000003c81c55040c40f0300c01180c13840551006004056000700d40e1041c3c5c0d0084142da5008004110000e402da4031420210041d0840e002042070003c00000c0c200d03200d15606422200b9540c0540d03000240b0f021102c0071404c2c441035884094042c060144 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 204708758 1250 204707508 204707527
    0x50d090206190503010f0b030105010f08130209130b0901020307210207020411070c0510050316020715020706080606043002041107050c0a030b0612070b0a0206010503150c 75
    0x50042008600280c5498140340c10311a038250102e4030200b10a0100b030002c801000120b01845100018100043c209030865241c0b10018004140c800305403424405584c002400c03421189401003d580d40090401060f070414414040e460401944c0c10f550346840003000a204000500840c0e010f1042542d828107111014401007004c23400000c031650790b40c0d40800c07140f005a5501d0003400c840481c80c2a01e0750707440620f8902405401d0060303201901818000640c40d00080c1c02100f503a40c400050800c074802e280f580c2d0301c00c9060410710b400014240c100c02c40d282c008a03178002040026101d640d00d408455484007010070055006501c2100f01c864401c1a0001c224110095a208000f2200260030121a0aa400201540c0301c02c01103151058000c6452000c0c01810080143c04035016516003480342d041d5251100c0e0460000c010346e000d04500c00f00c80c482000100010001080e500c84011f803200001c0310000e484280c28071485100b4401c810ba0714600030007900106010340b00c0c0d1008585001c4406 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 204710008 1250 204708758 204708761
    0x30210030e190c050909010504020603010312210507020f031903150b0f09040506040b03060406050c13031101020f030a0512070e0d0b0703050915060d1e15061401050d 73
    0x1042040c094012401420350182c015100c401c8154850110920920705210511100c80e038002c200650982c11f100501003d0303200c940460741502e400c01c0ca28040101001000d403034003040d410501c00304080c0401c20ba4509030307040d4022400791105d60309503180c024824140c00d949014500349480c00c01445d81c0001c0596005e940050200c08185540c501a00e40c0d0b03809041c3c10313811180107091860000102004d052800d88212603000008480800c80080c8180202e5a10354008000034207096071034021803081100c2d02c1c00c0c1e410603414040049800740e100e207040210412051200c5000d403145c18005a40c0800102c241c40e010304641d0307511418a41c00c00c030300c0a000b0314054008024410004403902480d156180d01a0201e40103641c0c111840c01e01400084c200c8900904d1b0607025003004e82c195142110208050741c1141e02103d030f182c9034820754142032001c150845c0d1a50210200e00840c0c5041004802e010705a00c0d0710140f0410919603222103501c03140c4100340000c0e000940410140c050004c16 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 204711258 1250 204710008 204710021
    0x931060902070825290a090f02121905010608070e04050a111c12110705150306040605060c0f011401030c120c0b030c040f090e03040b070501090210110d0903021003 72
    0x7980030081c00c1030310307465005050700b1800c02100c4105121140c803080c0154645c402d40c222002c000104000216602c031401c08a0b8140c1000384620444180700ac00b034507040065501390f07040817816500985c036901d00720703009003010306c1030f21a00d004a80300010314900b4007001030320540d0050701a00d0306c001c00344c0e9183d0700d0b002071045003036008a868410004500100f903600194170310844050b0f40c401e1612801512014060b0186a0581c5c03281c2010310190b1910084004081c00c020510303078698440302c00080180402d600015000400402c0c03c070b040883c0000c02c1141030032040001c110310300141c801481301240900002e080c0c400f402d4010020190305401c9840420b018440040c02641c03070300b12014041c0e1050307a1840c01840041428443c140c500c218000080c20f071000e0401800d404c180200d070300c80c051441030358210240801c04c00280427003908500c0d12681d0050030340842c408540ba010b8094114110100814801d41444201007400b484450003502d400a0a03c00c01d8125030308100c002d000c2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 204712508 1250 204711258 204711307
    0x120f040e0a09051009030e030a02060d0f0e0f03040617060d081803060106020d11061e060a0801020a02010c11063714060907020706050301060509310609020708 70
    0x10b9405001e40458418810a0b92854030540301042e0070303445040040c002c00c048140749210340c02800d0007100680e00c04040366859110840049001e42000f0907480c003c0c001366220010034000c08a130040c100201100030b105445041c0c0f5019441500000c028101c10780c1100c8452f0031061004400b00400c6610b000780c40c54294042030008485042c03001701c0d0034a1130aa1201000d68030024103040c220344c04c13080c030110150411004003081d24210315118042410b00c0110440c102d01c56003c60000d4903070820410103041044000e6503643c560010003402469548203c2000807007010722404440c80c00300d080d40c0503842e004100142420391100001581a039514a014110000d102103403000b007250141c1000d00e04980011985071912205000d402c4800818010031900000e070107001650704003055a0646200d8a400c5444215017030204810744044503650300e00d00c08180c0060070204181c0b11110241d1082e08060001c590b8a0041500780d0240e0940201852070500110711071401081d00b000e030717014 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 204713758 1250 204712508 204712511
    0x110c0d05070c120f02010e18060411040b0304050c010305060d02010c03030f0b040c020a050607090e07080702030f0f07060608010b0a05060d060905090a05070e0613091b120203120f040e0a 82
    0x5030741d0180c006500d109510304485070284c0f0140c0100b07540c7c111000100d6100300795142000509040080702403007400030000c03031203243d807034220400c01d40000c01910040c0c50031401c0740355a81454103240c1d07900d084842c0302a001905200000d44d00c0d0a0814011246550685404010510300d42d0150064482884d40c1018203039100c1182c2d1a9640700d018018040c030280e00602042901410441d040c00c0004101c0001c0c03081c924410404210120041a4843c9035131400180e1a190000128198458480b1240d01120013042c91350a4041d031030700809a55104000400251380d07107106041c01e80e0f041c81c580a0b8845003100b000c0125080c941d0052012041c1040000740ba00e80707078108101104c00640d00380000f80e0100c00030504210b000c000c03420141c00e40214503480c40c40c1407c006503100009101803003000e5140c40c3d5050801441040c0115500c02d40681d00042a4492149611342e413104002030384281705002c40a41003015031070844c0e00c511101c4203985d2a060424001210000b0042c01c1003500e076 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 204715008 1250 204713758 204713783
    0x150b0a05181b04060c0308010f0302060910120504060c0f08071409040e062a030907171c0203030901060f050a030809120d120b0301023105030312040303110c0d0507 72
    0x101c1c2850060001e4255170321402021034140c100103001e400141c00000301007082c0c00c6c040c00581d43c0c4d081580d01030340003160b060740207a06159003140c5092141e86000405810403003031004020041d0824844600c150340c03501c0c420059510100c403003101c103030f07403d00115401c80680642814024014108940054008680241e00565480c90400c0465030607001d011b06501141900c40401182000ca0a500e01d643c0d0850411021840e00c0d1701c1f0b244078102750000c011241c076107030318024850400c00d140c0c2d0495803030103007400c0240039489610840b01c6d4401c075441c141000c0740170444690010309460300076001c00c031800c2c203550b0f4000d404e074400708901b507201e41c0c102090600b85004002000205030240e41f0914090075800c420426100003800d041d11907401030006929330300c00380c101614881d08540340340c540b01710f41245203101124a60811038040c000000c1816250510307105441c05948256000c01101e89001501a0780303000350030751085507030440750b01d5803103640c0b080014010301806003a400000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 204716258 1250 204715008 204715051
    0x20312012c040b070e030d020303010506070c0e07080f06010203071a040c1701090c0f0e04021509040903031a040903140304030e060c1e1b04050907080a150b0a0518 72
    0x91540458040f900014100208030b1042c3e4400c00704600c1e280d081d4001c00e50084c0c1c01c1c50181d100e0005000b140c0c0030f440d0101d0000d0500604a8040b001408020060030345410041d2008006402c200c909800480403c00460400e5100108441055400059800d000455000c41d00c2d1400b50141040c0c48158040c3c0022038a002404d0303071400600840f0000190700d111070700c3c0000c3c07440015403041d0302106484504101304950641c20300d42c4183d04403602d00590612420505040c00707041c4009800510b8420b15400f0035401d41d01014510703806208a10b5440e24800070041910780481006001070034005c001d8044451810243d46c03c0b510030304114450b4000d400c045100b40c0c20460b5104001e52024115040c05451402d455108500d0706010b45403515252000b9640008100010313409907940c1c0000501c105018030881c0054218001950903040c8503040030002403424400700401d40b031620461041914020700d802080701c0001d00400200c95a50700c0000340100000c002900c42c0c016024012070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 204717508 1250 204716258 204716339
    0x312071703130507060f0f0f09080708031c0b0f06070501182102010c020601061206030b01090221060f040b0d0f0606140604050d0b0622020901080702031201 69
    0xc110042c80211800400e2801d01e985041250352040c0240010101280c000d958043d00c6001100120309052841c802d40344012030388108903620000047c081d00202098a0101200400b10418085103100c400061403030500100ca00407041140e010b000848a0324650a02c00080d010030360244000144032611002c5040304034602050845640d00c22004602d0f00d00745041c80411158803900c0200804400c0340030195580c84180a120280030700411801008041500407002031540854020b00310350b92402d181010390800c2402d0182039404444c68070f08100700340e46c0c040c440c0d2001031400d03115840314003e001c02030000000c1c294001843e0b8040c000410500a640e034450341c0f1645002a04501d003814040007028180c1110703210351070402c4100f2407695080500b441c8980c02601101483d110b000000d102440d400c00c03400119100528023081c1445c2603406020500020780302d40c112a919410200d07241d2065401a2041040d504010b01c8203d10a44001240c60142400c490018494205441 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 204718758 1250 204717508 204717511
    0x100f03060603030f0512010e091e0601031707110112020c0604050d0206160c02190503070305010f05060f090a090203030c010f0501091401050303071b1701150e060312071703 76
    0x40e442900e5080800806034071141c00c200008161626a08080c92285204001c403810300c150f60785281070001250950f48148030365110107010b25a40040022200302c5240c81c0d8809220950307654000b1000400b0b00c2d60038200300d40006601041480c2c6400142c0010350f202100e000c1041d5040741d09010347d10700b03131108000040c0500c2c01000205628484040c0092500000034000b4024a2840a90b807600c00e8201c11200b0720f031941211700404280b1000150390b00451310368400ca40c07501c620301d400000d111065000d203846080b0051b0501c099903803101803006446010840680180b0b8039030000c0ca82e40140da20201c1c20902c014141e03450003201104003400e40c0c0082c0c14052103941e80e040100403614080c401c0c20a0b07905507900050f01589400e001a0b1079010741d00b03020b0030802c030038500424010100d508a802404d820310860b9400720100038154000c00f002d202d04d10044150310b5005c03c02c00d0036621100c0c0703c0e0310028010071022005440d842d842c0d4005c1138085076079021402c2c05040a184407000745 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 204720008 1250 204718758 204718763
    0x30307050f0f0703170a110f0304050f0601061808010b01050d020703030f0c050432060307090f060c05010c08060a0614070204060e0f0c070206090f06070609060501081e06040605100f03 81
    0x14600418003030821704622002600281a076468128040c03503040e40354065498500700b0724038280d1039a40b030b070408604240403003254000c24001e0800216280d038115580441c511a40009205415161a01d503401c0746c40042056021070003d0040558840c15038000306220351013407070040340114181202c0c00c1070781e060490b80e0000c41d1001c40c0c10f001d0340b1141c16050815098800c20149498102c240356400010a070203400e000e80320010016040c0340c0520281c070010196801c0f62684542e031513000030595004a0800c58065090203034400425109110b4180070780402040c0c54000c42c40c1141c03d40c1c642c50b1f0000040b0280301e062007003402580d81c2e4498000104480004a034540c54000d00001c0d15100c010555221040140900c40241c1c48400c1521604003040d034402c1e80e118030210008005024030b0030000d05103401d04410344100445034109604070f904c25800c9407001c076100440a8503291100d100e00c40740d0703402400054007060036504841e40103039429040b80d04094680314580390595070350704103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 204721258 1250 204720008 204720017
    0x1090b1c06060503180307020901030b060a0308030406020d0f14010b0a09080a080705060603060f060d0204141003030f2309040603210e0d0f0212010e0d0e090601020a05030307050f0f0703 82
    0x1080003010441140c004100001e002440c0703042c06543c00115080b09c1800080d0100c20050001071244c0c950210740c07005140c000b540c0c43e4503031a10346004000f84d40900c20700f0300194184568411845114001c49519550100071030010768240603a20485402c604406420030602910001300c0c92824489034410900407404a5990700c60b0703013440743ca0b01101605c094000e030b020400304405e800c6841e609a0300000200c0796144084249c0c00064050407204c1d00c541c100301c1c030340c00501050348040c521003411240b2a440d9002007910000c01074509100c010070030310f500d0060200004015003100003c1242c510010000a207060700c0e034a400320324100a466800c4414034101103441c01e240c21900c500d880180454040d450000b941c0c0c3c1d001e10140341da210090041ea100701d41c1c942d510601707410454a04044030104c0d22601100e00300100501e09414105000381c8000022540300c0d40702245003440d041d0044001c0d4515120010200c4e140e621641c14842c0b03a0400f07000b1515805170840c002c040c0c0a000340c7d04e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 204722508 1250 204721258 204721261
    0xc040e060109110f0301030807030c1e12050406050904020c071e0e01080a23010f02030a091e02060a140409110c1b010806010c02061201030503120c070201090b1c06060503 75
    0x82c4070342210710690714402c040000f80600301300b00c541c400071070b07042d61b6009074940e44071282d902c0d040d141d400a000000300343e4070311107128489031120b00b220944014001c40c0b540390024040c4400b03607020301c00c90040c1d4000907400c0103084081d050a40085c505e501908046815066590140c1514031903c0d0172400302ca0140c50404101460380302c3c4190f4058108140a001c0d040304581c0c400540400c9289a003217000c05203100766044400c2903101249100d20303100e0566917440c4c28500c1070002d054a09045030038000a060b200102004010032050060b805030500c1d02e000400c501c2500d00200009006c0d0740c0c18401c0101040315641c0d4000c0c200c1503681d50754400c1c0c030780c40e240a2136810302c51380305403091203041d036200c0c0c19140f42e81c441381c0f40d600408207083c6800e2440c3c031400401d0040c8a410404040d244806c4000410424008000c0c6482c80c400e10918200b91154200701c840c61044620190000c4c0303450400344000c652a00060031030902403e289211142031044405c15180154091380200c0e00c02310 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 204723758 1250 204722508 204722519
    0xf050708072a03050d2f0f0f0c0f0d03060f0b09031005070e0303040f0915120b0721060e180615060f0301030f1502091806030c040e0601 60
    0x940980118a5042c485100048007040700c0010512000c644481100440b1100074540643c2c00c40350b15a004c00818440361032014000b0140c50990540d17840045482400008a0044801074640e007100f00d808051411030030f803994070801c2d040354407200340b07900600440c001c2162040192081082444d100482c4881c0780446030000c030009540708000c8240204070b0540c40d40c3c1c0201c2c050441c6008114002515151001c0403a013207040240a103401d2b1000190201d50700d64143c840100319a201d260600000188090301d4a8504e040d2143c0700c4140782c62132100c4001150841c3c210740c060498645540c0f50b40d44580c030403c04402c010001c00001d680c034041400001c6081149940c80307030307032000200030310000441015541e10000302824041d40d0646542c0140d40d9623902210000321000a0352912561281400c50201000c2c0b50304135a1007444088070710302da013124005d50300c0c800801084842c0d5480902c1d070f400700c80c18005022a600d40550040311400340d9951145000003040700000700510360400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 204725008 1250 204723758 204723767
    0xe030d05010e100e061011070603140619090f0f18020f191710150915060503070818010f020405011704020d030c03181701140105031902030a0203010f0507 68
    0x240070a11802120380c4180450061499607580040090741d00f0351b89600014001c442079044034440c180c26011b20b075800948245d242d0003105c03403841100403800d150b8a0b04020032801108940d401525100203040802100e11113900c1034407010301403480400c6501114a4402c125103440305c010440b12140140023003035050a4841d0400b00d00d0980d43c0f10201c03502549200d400c008144501c1807000d50682d03129008800900c0441501c0e075880300c0510541c2500c10384480081410700500700c111f450300e02608000c100d003401e010111502916506c1c955110454200e0b00e1440040c8810502c038075080105041075400d1080300c00040072804016160f81c100ba000512000b00c4007801c040e00b11a441c2400050307910703404030b0b00485038141006803040c80e85141c01d03640c103a09103240380d00c4c4020407180001d80034840c001490b91070036030500800680800600003041171a00b8058141c240e4000b408200d00e00c141c60400b105170300d00080485180c4040d40c0d0010382580c8000c0e190f46d00543d200d806100b0a235421 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 204726258 1250 204725008 204725011
    0x31d09010e0a0902120102070302030c06100608010b0a0c120e0102010c1e110a061803090b0a020c060c010f0203040c03230604150906050906090d0306050a14040e030d05010e 76
    0x8698101040d49003038941c0440c0318010740041d2a90741c0d01c5000e072085540300804243c005107040000c1d07483e000542006500d981121240b0900b90240354002030001d0b4496124500383d03101074581c04c1060742050403064468000000364414041c504425001044150410701c0050301c040d0b0758a541103901c40c000900751003402a0380700034000c101c4024407070200035600d0180420002d2034514680000064000d24240101101404c07541c94120303070002031130020210a045500075220484400e44d2600c0e56041881050001d60050308140e14814451030200b0041241d507140800203c1e640e080118a03800f20391055508850100401d4000c10800c99081c14002103035108003881c0380701154008407940c4901c4000c000800b610b11209144880c01c0b41e541c442d1003001e070007540800491400340e024640d1042c05940082c024030900300003424040c400c0c0150000d0368005880c0f0101d803890b1000081159a404071241d42c4035448161741030605404101504408944880c041241d500d42054203503145e40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 204727508 1250 204726258 204726317
    0xb090a05010b03030c0316030203090d0b0105100503040206190e0618100201020f0301121e03260907030b0a0207051615030605010e1e060c0c010201050f1005120f0a03 73
    0x105101940c601d14002c001e903101f07580307400c00c1e1001c10801031604908500c0340000556010042c0714115060080003000300341668005d5401058040074440c007a0396500007280c009600ca070080190211440ba502003084444820b07003440c8810328440f02c0040c140360095807421140c00400700c0c00814900e4075500042d8401210300086280c2680813940d014203200501401102d03503101300c202010010110010040e013180c51500344002c14291030014070400300c2c0600086000e11540d400c140c203030210081c450043e440c000043c001c013071455456a0314040010103031180c00f642409a0800b0640c140800010240c1030070380c1304031080c140014a4841704000e400d481c00c151801c2c4003804240d030401403600314800d00700c1c1c41103c96034605883c0700f0350200c40d5480c00c0c1c01c030001041c62034154100245c41e2110314000d8009000b00d6603407002e4040303424011100320420058124041125042c030f6030600814bc4030003415503d003a510041d42e2440c219062500718005900c028031207103603074060341c2420000300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 204728758 1250 204727508 204727513
    0x20901120c0e19030b010308030702030d021318050f0621010504050a021008040510090807020a09060501090515030c0703090e0705030406060803031b13090614090709080a0305070f0b090a05010b03 86
    0x30305545172451083d90500008044803800004200311500030025101c0180c142d19066540c6c804141d07030541c50010702d02c62440d64a40c48490400e21001501600c1d2058240075140401c540c1d03188100154402011201c1000440000104103150070a00070541b20b54040d400a00d030fa0b5501e8414040500031803155141082034640900c0300055022034807041282201002284500031800e00d02c002d8460300900039440400e4401c009182c09103600004211402602c8903040070740e507a4103020700480300c0002e9039110314003000000d40545941016140b264041c1c6810349080d030325101910041e040c103548040100d20044104030400c4880d014a02c06003091a010b1401e60920007004420200420440d880848002c074045a2903803031251050014000354006200146d070340c5c1100d13500703428040c40060040101400203140c40e402098414201c0340c01400601c0c15142544080366182c1019108644038421140d082c0040f8071890461801002c021001d002142524a0b00c0340c210b9000c01c4185010742c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 204730008 1250 204728758 204728809
    0x1b0309010806100f210f052e031b120305030a150e07140d1409010f05061305060402130803090a080c0d061e180309050103060f09020901120c0e 63
    0x141e500070101d00ba2a03a603414030700034a01c5c5041c0b20040803d140e102512007213107007280000c1002440c4e0000d40c0141e04e1f104494040141e0404e1550242040034014130740e40c8250704d4200009020091105c0c010644035090007521920b03076140070603202001c0d1065001800110900c02e108902d441001c0d010000040c0c0424402c1c90712190b03164000005103014280542d800300d40084003149412500303206103040d004c1003c049031103480e1450643c19200b1114541c131b0403100c26031009691107824096140100341c0200f45420800c3c0300003506000f030800381c004da001d002c10190a00315890441c09800080090b60b02d848000052190a8006901045440e44021884002034503005482e245190704181c0100e042c110905159282c40c5041203c036001c217180c42c181c3c10810b07a403c1011a481031103684c1d904042d175a40c4004509445c2c0300d00038160b8428801408000c4c810b296130040c40d80c0f24043c100100000d440e40e142100721030100751000041511030710a031800d8940440010301005074012190b048 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 204731258 1250 204730008 204730039
    0x40c090203130602160206040f21051e030d020d02030a18020603011203051326010506090a0c030902130630020108061507080703030606032a03021b0309010806 70
    0x440341c0110b00900342540c00100c0d85214403604a0170000c454000d0001551182d0ba1040c0b654002000d10404406403201c03040c4a01248450007102a520b4022000308180801001d40004d07204280c40d07100700512040041151020060010b042c0e010b0900500607100d03e0160022415110414a01c0c01003034443c40c2e0030310041c0e4400003030b281074400c04103210300a200c00b46000d480320b01c10862105c041a03002c2b0000141c014054500000684414000ca114035000402c40703402d030b46007624040c1e0f02691070400249002c410342e1002400060900d0081032204040d0080351002032120b11f19483c2ea030b1101014814444510031140001d020030808091925600c8034030090180c80740740c020304000d030447c0030414036a2405118440074103070140d4582d4444242c43c04185660150104801090410030700050b040e02a124100f000e05100020540032218070842d18070356441004494149642800b5800c1e06a20f803002003451001048001d6a0f10304c000700014280307220042c8064402c600c2e0040d5000d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 204732508 1250 204731258 204731281
    0x12060409050d030b040603080324060a02070e19020a080601031503080f0313020a0b03040c14030a060f0e010c030e0f0d12050907030204021603080612030a05160f0b040c090203 77
    0x7196029142c00290001071300d0000700581103a81c4050a048404020301010102644a410034450885010050080601d0a008c0140a410f48000158101da0002c206110589030901d61105000e50000724020404450070100c0c0c0186031a5800900b00c082007004e20f581511809460002c0646d11100785071031a03a8110349445140c080e9140104044042780455680c0c051391010681c1c000c01850895843c0c0010130904e800c1150280c6008140d0200050056111074454034400381c05006071214800c651600c001502003491004020b540d6282402c1b032f0042c0a200700c090b03104003aa00808d801e84445800382ca014510b00f40303094a900401c21080d003181d08149003007201500600040b40075621550001e04200860744040d41140c0000f8080e0780d1aa02c3c1291046601d20a49071707000305854910034400c03c41c1c0340300b0240107903510030403441ca9013074010b5001d0440813401d122013008045a030b0751401c040840308203045480c10850707000d201c00c0054a40e4401e02a100202086007036180480b41c0c0031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 204733758 1250 204732508 204732523
    0x60c030412170307050304030e0a030b0105010c230304030201080f0f01060c0c0f09051609060210090c12060207150e0706030e010b0409080309250303081015051206040905 75
    0x880760040020308100b0000e624600380d9011951805040d1249807410000c0c00700e07441120b048001651460242030149019841d40c0c2c15a6046544500160300b40001551000300c0c28074152a4240c500c0140311030307681d6020300c0200048c00080a15260344c6903100250910704051300d408880c0d1a510104041108291791150441c1c840c2c1c074258495010a080c0982c028031a900300c40310f203c40a88001c124002c13582c102d54055540407201d00a1031101d004c0c00c403000381c0a40284401600103100050041100350417905145010340e9039443c02e85e0b99451002e0603000100402c40308150040f81d00010320448444000b21102c40c4501403054107400d410007903c40d0071038040c007c07e06641c3d80d0181858042540320070340b500360141c420440109242803840081c0c004840b152454840c84510001051010740210541140c40202550742c905564040e9050200102219020b5101c00000502003546401504c0130bc1400d40f20545d8503040c00704100180341006008074002c60418007500005100042c255 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 204735008 1250 204733758 204733769
    0x1030b0103050f130c080105011e1415180306160f09060e0d1406070207090b040b090109020304050a120c02031509150604060b0706060503060105091003080d140a0b0906060c0304 78
    0x44c1ca040540c0c0c985000c020b0800d0f00000025031070040049220042c2c040d18402d04062825000b03da203a0b20316810030240009203a05400c280c0420100f2000d501490250a21030344c04ca0000380c00810f100042442c00000f1141e4049901c10121507004064201c0c0c81c0683c542c0c0c0c0707440c1000b04a410514080e002e52007480e003c50195139180e0240e4203010007845000401c641c2042902c0790307420660070096481c1d03003500030005144e1609414000c0c1d844e05208100d10b0700e50140c6120705507071812050744c0094000a00c00e0300d41d40240840e03800021140b41e040400c00c507030303a150a841f1003403500601d0310382074061000c0b01c8c1003131201003404001070300040d04403960080980c0cad0051994807000400c014040d558400d0815000101d1300908025698000d2410368030180d0031180240c0e626001c200e40d4203819038400b4070039814540140040b5000400400021400680210b801881d800104102c0741040703a002480715a281e26000300c500c3c0c8030010a4102804484040c2000c110350b18103900c030304c41d43c8540f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 204736258 1250 204735008 204735031
    0x614060c2e060605190206060d061802180a110f090f01110601182009010c0f020901120302010c0206370c090f0807150302030711160501030b0103050f 66
    0x218070203810116550344030410801d012880d80c1d200c002c0c1803500a400605e014840d804000f0224a200080719485075400030000040c00c0075036101c0d80000c0210314400e1a41400381c902d94005078664401d0700300128000b114004040c43c00c100343e03904442620944060725202001140c0010a052060b28118031084074400c24008a9071300503940d4942c074480c8144c1c503004810000804c48002076040f051030010001c180082c0790b109001c04014040c000011070001c40501800f55a94481e1004c28109440b400c164094001582c0000e1103c50099000800c00c881b00c0c800c000c0ac040d03081c001c02a85007800e0004001d035040000c2104400030552081500c11a4080b1003d810b448030b805040444400304c250401041036582402010990540106001c2040c945000100e075140020043d0403140240d071800c0c004081d4083c118041d41c0054811420003064031b85a50440c041030094a4a00400b005803240f114031700307800075054841d49520761341414900b00c100a80c4480903920300e42d000c500c8121 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 204737508 1250 204736258 204736303
    0x90306020c030d06090c020c01020f0715090f0f031406041109090a0f080c0105091c030506040615020a29010302040207050a0c0306140c030c0a0c0804180614060c 71
    0x10301c94654010b02290190b124200500000c010360340354001030008915500303032611040e80100599031001e10000544083d40b12003010040100310014507184541e0524024079480c2e580d0951107007101e0030750495204414017103402c0080100b5850410b1a0055a901a02891a09449510b91282011041401b4043c45c00024000d8641030004c1b00d10582e210482d04901005828190581e810510343d0312400c0d86032501140511400082c8000c0003051550001d050b15031503c4201c0240a001d019183c00544a01001c40c1c200313500865044030640c198000c0652060b5401c121407020f21200f2032540300700c0304070400b5111191000b400d07410b42c1e4060b40c001d60385580c24544185025010311000d00310f03400701d5401004100c402d0300050b1900340580d1249280340ca810745031202921040d1003004004004000c1056141c0c0540351002e545402050718500b002e6a031402400c03a200ca5000c443d01181d83c13000180f04006a5001700a4801810b07180d642c10201c0020080f559040007414480d59074030240e1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 204738758 1250 204737508 204737527
    0xc2d0203090604030807060e0c1f030b0d0803040b010f05060403110d0b01080f07080c1e0a0302040f0b01110c09070c140706090501020606240a020703050706020a051002070309030602 80
    0x4100c07440a00d018010756500c40c0c0d603040206954122000848440c0e0609072280c0c90b20f030001a071203100d010024076a808900c0c11400000e0254003281440041c0340d180c080c003002c0d0740d42e904403003401c10380620506a03503480c0929000c00d8a45050304940540c44a09005000c961924400ea070150b95101d80354140b80000e160000b411283d07a810300801240b030030340021030507040209040f481c104091003250f41854464100a0b210b02c1c030800899040031a0150f000400f480046003c03103019005000007490940307a40210b0180c0344d8121042c1410707a01c031041c0f0f5400d541c0c4008519a81035010016061409200d800124000d0019055104111504805601707000e1503000c142d022203021001c03184141d40e10000900300811501c00c540c0503026500000380c240c10011804040b115a5141d0015501055285c3e03805a0b00320072035801c114450140d011001600c200400d4000e0940d64009000341040d41ca0050320b8000220000c5030700301d00501c002000241c2051903032094031382c065009601d0b90f60b041c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 204740008 1250 204738758 204738763
    0x30c050d0512042904030803150402070b091e071206022503171e01030b090a080301030b010503060106050403050309060a030f090609061d0604020405060f0a030302060702010c2d02 79
    0x41c0c0301c40b40810006000030303c51a2504001080c0c0c80700c41c82103402144080070401c40340164440074008020070000144403180440c0e81d0050584028401800e0984513151440504000c1350050340990180703070300900d52400d40c44002c403d0101d400042c107a00f424001031550034000e0040041820f0340229000481805e21582d500c2e10ba02c00980c1814018001d08005140c0c000d40000e010700000b248004c20000030903080e80f004250038000b0046420b9295540350f4040e0b60008145c220310f8001e207d030440018007100f0045000350b01070152600c00d54185802c26040910603071006050080403c8204000b49010044e1540408200c801c0c540340d10881070b058025018071b4040030301241c0361451000c10040c0c6940000074290048800304888810186203514081640c0e030041016485100010300518240c1c2000344d115802a19500703031907020b40c0c08902100010381040f80541c21450412018581c244a0414215060301c2c1025410b60300c002030288082c00640c440c018080e40c200403400c050b008 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 204741258 1250 204740008 204740023
    0x7020103091401050f0114010219170f0702120a03020d2a0308090f070513090f02030105040308090c0405151327140106060e0108090c10030b0f010306030c050d05 71
    0x801002c0389800d01507850603008140440f582c403c00d4051100100790502d142010212480068005011482c0d00781181c020103d04104c2c21540c4055040311b98031405802c4018007102248491520b454140a20402800304e907480741a4036a9403203c001030380403e60018080300f049031a800d010341201500440307401c1200310a00c8448061076648107a0041550250b1454440c054040580b42c040000c000801d84800e514424903900c1028825604a2050140c0c04030a4180c41840c4210818003c0c2d4003081c00d41e001180d040c1d0114400400300304600c1d005100305041e103142214200001e1801030440c2080d241c840941c0307801551044c41040052030541c0c09500c40e5117100c50005c041030503c101000c46813105010840d00c041c80304010500114050040c002543d0007902c4030744201d91601e0044445e910002d011408074441c80100c0304041d00c4001c0080d840c000c003941c011990b0480d0005121342011040c0c10203041603d084010004210081408025200c1c100d45509100340181803240c50500c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 204742508 1250 204741258 204741263
    0xc0304150b040908190801050901091d01060e060a0603090503030f0603010b1206100605040e0106050c0703060501180b0303071203111b06010602060906010f1a0c031305040b03031606020702010309 86
    0x5030084950910819402411440380d070030710941110305c01000201c030100421b02c00d4540050903031005200e00849601300301500125060301041e210f00702a0388609507400ba80c061504c0b40041000d1201c103080020043d006068141028000041d01d07507255941c0b4803004107901c90558141001c03491503602900b00300c031030343d42c0101041c50900c1d00c1b10805440b92825239004044045d030340c100041040c016015501211144013050020380c2c0303400d10541e100e07030190041d1004d5009042c40440081c00c070b889180e0190140c54040084903180d212401c0450b0003c40540d4401d50041c05000c00003010310b0b4801150401620b0041030000058905a115015842d8802000e81000c11810100030000902c82c2c1243c0c1d8590072500b650311010100398a8120030701039400d042d000040d083c0f04000702c200403409a40e0004091a2070040c8001c8064299000100300c04000d910f4400108032500c0c140c000c5500d4040b0480166103000d1180e940c0e50224040804000e000c141c01244510039a030003644060700994 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 204743758 1250 204742508 204742511
    0xa0605040c091508010b10121109130c0906320c011107300806130203010602210f090d06090602040806090f060610050c07050301180311060c0304150b04 67
    0x483e5400061243c0a40d802080459840d050f85880c00385022603884503212250307112003560000d009030290140107014160300749040c00700308040da5512645070801c07800c40c51210000f0300c40d695600c01401e100c03099010f04200701c44066110104106444251010000da655001b4501c00484a1302854007454048980030b520f080700a0601000039402898100c1c880c82c0e04c00e05480310b2200c91046000343e00180c04081400000064250b800307a4595038002c1c9004081402c0803042c0f042c40d0041c4d0380243c00400041c0c019144140b0364031604000348003480d00f0900c400d03003044083c0c20796442d03c0c000c1d50040c3d48a03411113003039541440041d07071001080e640c000c5010f55403151074100741350380c0b0041601c1c696090320464109109070b8101242c0e003402400e0007003101851000b0340000b2201a04140254603e50245200001d55940d00340315078402d6150381a03041c94460440e043c041d214102420022481d5046507041240b003540e00b90459a000e680801d44014850315607200070010940c410302c0701d8100c0e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 204745008 1250 204743758 204743771
    0xa0e07120e010f0b12070e0a0902090403201b0607030c0b01090212010e0402010207050906040b0307031407080313061407240b030307120f1809020a02010506060c0a0605040c09 77
    0x40c801034009104581c55144207012891040c4140081e9100741c4145110310b03048007605001f1143d05102c03190700861400c90210b10381409400203030440d401a01d0407404140c00e110340d1030001c2d10304002d009000e0440b0000e405c62020301e5004500d00c28040240c0740c4588000a0208101400f0340f5481001a402c60340403403540da1140a4800254802115641440100c10001480300007510109100f164182c0c0681500c615207002d001c4014000742540394000c1d01c6d80c18009494078108000b000450040c080e5000030342018a8030340c01d1070900d412120454004000e6588440084520281240d1881c40c0810340150035030310404280c01440030042c440c0d0892105082d4040d084d0301e004070980003050040003196030020405a907480b5140d401081c1459080c51602c459020752000200e0450905142622500740c1d0b00660701c130440741c1c110361503696020130129145542481400d91044050b1550b0380351006407900c00380d8443d200c40004081a48800c006420814500e01800090250400c1840b08 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 204746258 1250 204745008 204745031
    0x6010e01020a08041d01081207020405180109061a030c03071203180e060a090216140f0f0313050a030201020703060c050904020415021b0109211407090c0207050a0e0712 74
    0x9000c0258442d00300f179608400210f0703400760202d99a52401150b80d00e607407401c0c8a03542800f0180100815000d5000403141c001c0d04610340270700448540612642c40002c1e200e032403200ca41d801452120809020364410f0340041c0d060703140000e1000994006c0b5800c0c17842d24109280c111407004801707000100510b10940c0000720780b0660900240103135001c68044166030380b0b5603400750803070040700c0900303042202128000f4080799010b44503a5404401a003611030705424851110f11b00f000040c0c401c04a90700001e600c448000c1030342180d2340035000403140845807d1854000035641c0d41e1500028002e6070ba181e82200d0818021402c55003c640054403c0d5100e030b6660484d0010000060503c00250181c0a003080343c1c001e10040d1205420300503100d103a0b001e4200842400142c00c08540345a610f9114844038000c0ba20800000d100c0c052107800900d0760320f040c80d11030b105450381180071809541c41014248001d54070341c0d880009507020940340c0d51040d0f5424208071a030412145520a0040c5041805001c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 204747508 1250 204746258 204746279
    0x1020f0a2105040b06120703020a1d0a0218010513150c0201080a0e03040b0a02030408030d020316090506120a140f011415090603040c03060510051003050402030606010e01020a0804 79
    0x710504400c4a030340301c594101400c402d03164100c078020a25030451000038014608036440e4001000404202c4c0d021030380306d40c04200c2510071a00a817440c8030140c2211010300b00e00941d881d17801018118150708200046580880c070582400c0303418103015021a04494440c070b800712020017081c0d44880012004c030101c90140405100c603405900090591300014011011030041c2064081c03000700451609180845070456070308515026011404100000140000c003040908158250720301b0050740ca04041145204114401c1d07400d206000e04104100405d070340300415620404c4125100c0780240e6500c0c0d4002008020f201201018090860103200900220340602d5040c0c0d01029011100c4001d4941000940c0300040d48e42d8a03030300402c0142c03d03000e04000e005190454400c0b64a84501d640720390303501c000d0300d0040740c0c6140c00394458402013015107002080c0203100011400c081245091030340119887d02002044103051280c5001d40303110f203034800c2200308406500014000e40f6540c840d1407564 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 204748758 1250 204747508 204747527
    0x11a070605130b09150105130608073c12060b060703110106081501120314070f02010e0d030c02091b0c010501090c09080607030b0103020d020a030506012d03050901020f0a 75
    0x45080f860200007030880100007940c00034240250480101d81e0307280c00100481c3d1702c4a4080c00e0041600e0300c0300001e0b18001040500b01511200b14240c225102070020080d091b103081e0011844203001c15012150721a503540080300b55512200d00614440d421300f00080500010701d100798100d4400540791090651020441480d01d28640003849101c0d0b40d80c1403255a42c180054180341c4210a04c0108051180c40074500300441c07180c00c09034000d170100d40c01e0140581000c0f200341c503444003900d60f06c011980d00100c01e0302070300310880d403101d295a51610020005448824024002e11040c0c011400d104969403075178500c00c200040c0e04e65142c8000400c68040e000c02e02c20440c00c0b50031b012030030708114015184641926103000041c1417560b01d0010440c007620b00a5403190506500300024411440b1a0005215080c4075860101d240c1c01c1c80000141804a21382841c072038040e1400e0460a03522840c0401d00015a1b14600403601d0b0301d1b0b4668040c020301c1003040150b210000050340396005034100d01d124 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 204750008 1250 204748758 204748763
    0x160801020306130e071e0305010908030901050c0a1215031506030606080703020102250e04030503010e0703110d02090105090901030f12050a020a02010c08071a0907060e0603011a07060513 82
    0xd95114018124801c0d82d00d182441003840d005000d0500144d221b4142000c85500c4058191030b01da9500d444880c06c40348110402d441e188000020403241a40c24000d41d03801c81082c2d030007140340c80d10144000707109504840d1a06900e50b11403181500e80c485c5110500d0140d6000030000300c3c400440302ca940010280c41c070003110176506003070b40000d4514001c540304084a80680240401780c1c4408406581080c41c81020a080c2c6088400400c040c0099003506100b24403035201c2c544d0b030394106002c105020380000d00d04400c16080c610b51144800d00c0340203880c03603840145000b684403140000140c506029240d01d281c0c202e00c07080000402e0003156400603106034024041492002030b9103070301302d616200f00400100540c2c4525a0036005510445019080e03e0040d81c04070b04001c2c4990700c4100c02c07095400d400b20308181c80300511441c01402d2051030020441070030400c143c0e03e2050042002da010521804900300c1c00032011001104256085603540c1d42d10407001c2207249880b44c540c3c50442d0030030906 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 204751258 1250 204750008 204750019
    0x80904020c0d03200f0427020712200c060a0918140906040b0c03040611070506042a0b09030f030d02041509050916022a091f17160801020306 62
    0x7800c4c0304080004858109090543c640e14007410f02c000c030760402036000240d149000b40701c1c1d0481c02e54040361002c0c0808600c50003464120300c4070400000c0210501c1000b44007102000741190410100008155141410030f0301c41c581c9070400e003001902c41e4800f03584400180c0203495410342044105602105604441d035840140720384403424480e944900403580103108540700e5000c621584160300107036920038810800420003600c4a40c82c0c8031aa00614421580e550001c0d00388020491041e030000070030300c2001c2501c510542c0c82001c450400425200714540c1900c0018856403a490601c48140c0c1c0580c00000c0301c0c3e071040c0c17080a00000394003d11420415043c04041c5184291103100b184007166001051081540c0360316410300440d21581082109601c58890151541c1d89408100650b000e11140d00c1c0d10340400f4072060000c030101c010230205180311901d00c11201100b4001c10f04050320742c407801402040700400441780c5848035a00b0700100e4003901c0070700090711f010150000d40c401c203004d458 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 204752508 1250 204751258 204751301
    0x11100e0a1202060906011211100518030c030c04092a031a0c04150924080916030b04050a06050114130b0105090f061606020a14040f03080904020c0d03 66
    0x14101e0711180f041d40c0011032600003000402407980c08044021526000b6003419140414400006060101620f40380f03000c40c4000c40d0b0742c0c1140140059181c00b40b4001d402030204c0b8060300300065100c0000c4124103200703658070024202480008100d14480300e83d80a800d0b2107403440c40c0980041c2c00e9051008640c0c0341d10001480e80103903035001c622405842240241c0d41824100b500032440e854440b0400f40c100440c1002c00102e6850100107102c032000c0d02c119641000e074201c9401484040010500b5120f46c1c4064031604082000024a00441e0382006045105442d10f00d0054102025140c01400717403414040085021021000b840040100480304644181d4a80c4038038020b88880540039808a0307000c0c003c0300d0440c140300802d1600c4150080c4a145429620282c0c0540d0000007801a13507465408110054420340080106000341c1100007442d044c5440d00c8004503030700e0700310700000f010540301080c0c80301c0d139844640589200d0600802950040c1d243e00130001c0040210741b4890040c114102c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 204753758 1250 204752508 204752543
    0x180709061d10030201050a0f0216030305090a1d01030f051009050c01031b2f0304030b0a150b030106050d02070605091c050a1b080715020a0e090c090111100e0a 70
    0x1411441102d03410b03100e0608000100368186d60a800131023403001540103108081142a0075030a805004e10f00c00d4071810b440c0d0710288140b01740000302d5008140e0004d0712044e5030701d525070b0054911741125800108110f00c1c410342d1070000c4c101a50f004000d0440e90070644010104040400c264500c9002aa07007007000e94442545918840000120301d0045a40d541000344c4019000020400b09020759001d29026a58180c3d454074541c031541c020f54640c070707480051005980c407500170101240021070040c49400d0820300e640d0910300c8184039500510000142c903d5000300c044d0103403061907400c12020800d614041040e00e4072102160461800803043e4940c0550142c0183c003601e00b0f02130140e03150f03c0d5200302542050540309003848283c9140500344200000034030480312000f200704100401685460380c4000142c00c9506072143e007449400300d041044003200160041da1846002403030040d00705900e100c0701600748101c04041c0003905082c448540340030305c4001150903c0c244990080201c0b80c1005 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 204755008 1250 204753758 204753781
    0x100504050c0604060807030b03010e0a0813120213091704030609020a0e0c0d09110d030207060e01031e0f060b16031d0a15050c01020423030114180709061d 68
    0xd004202c017068020b40805c4042e4800e038030100b43d144016000140301c070200180140750130075800f012250082e00007500304e50180c45104074001451448070340341c0c6480180e03002a8036042148055491a170355018928140600368040f004070b40c80144101b80c2d40c544a08040e4041c200103e001e0b40901403000c400100442800302052241c161010107a080101500c0d0203c080c1075a0801620f00300000480d0a482e5a285005401d1140c801e0b0014180d49240c400040c00c0080b0900815050614003950f4907100b00d00b2004280c40c00441d0800090103403242010400200455000703070484000124100340780f555003600c00410303540070348c441415800743c80300c2c03201d84500c424041a421940740d0750300700095001c40c6d41d201d001705c85d58240503042210782a001802ca8005500c00102c0308071030054403000400c00902131343c0c406070036002400402500c0020034040710340544844c0e100f100c03805a418040105008080140640349018480280e0f41c002c1d080030b00c05450204100702c0ca101000c200d104800 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 204756258 1250 204755008 204755017
    0x4090c0e010c031b0302010b150307090807050a170a0f08030106021506060a050a0c120f08090d080c03070302070f0605070917060402010f09050301091a181c02030903100504050c06 79
    0x141c0e4132081e04955000f0454802454520220195900c50304281c02640d105030740c101c0100c18490f00c803a1a403602c40c1c0c009051001542c050501a080010b0920584c0c844081030130039102c40d60003007103c0f03018042c0c20900d060402403025089800390a402ca00f041030300c038000c5048807030030341c21540c0340c1070307807002c2a080520244d49256000504001c11000c007402400138100c1c0c0d071180d0501c02840c5040b40c9030b0700c3c40c1e81860390118002550120199810a810042c111b400851110052440980b003a001174203080d07020740341c1f041d02c1c44040001030307c8912940444103202d0340003054109540e628a403004c00b03000141d65010118040c0c101c0881e81000050103840e542c0850002043c058440d40c0042d82c0c83e00d02c00d400c80042200420001c2015142402540c5140d48501130b00105080380c0d450180306004082c114003698802c0d0184100b5440001034200303240d1820803640c1209212451050380740d4440d00040341d41600885900e003260703044d41c4d8442d40c0324602450071340f8228042c00c01080714038410f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 204757508 1250 204756258 204756263
    0x2060a021b0a06060f0503121c1401080f0601060f02060402011404050301020a030501150f09060f17010e0a0b01020f1f1413110103110301090218090c0703021605090f0a0209040204090c0e010c 84
    0x509001402d549c54000030404002d00803c43d000a1012018020582e030740c609070000c0685500050140790359100410441c0e00618851800d844200c0180710001d40f1818082d202034100035400c100c414018800c83c080354003c0500038021552a0a5244060301a0400b44100240509110302d45002c3c680181000c90091246a8400c88083e080450503280d50304444000e60401103419546011a442c803081940a45104200c0407035902d0001143d01c15958a54010344c11034001da00c1e6a5440400058190320308100500c0d4426003250995045000381781c15803489040d411102d0500100c1315007043c3c400500d60261414150030700030000150156400e64140303803100b480403c010002001d955000c7d20b5840b1801c00d50b03d80007001c1d94005240740105036207203007031140c0000305038040603010410458040070b04403001d445c281c034102c0002d61030700300200541c445c011000000f615014680c0c6c11120010b60007807045444580b580b1008000380344c2500050301081c4030b101070f121958050303501d0110403079 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 204758758 1250 204757508 204757543
    0xe01181a091c0201060f1716080c0d060b060703080103151b030c050c0a120909060308090904050a05010e031c020c0a06110717030f010b040602060a021b0a06060f0503 73
    0x15650091034020b1900e0300062030840d5600c40c40402c130340c0b01041411006118030003511018000e04a011801c21707404220b01d28034940ca40501b00241007000c5000032a000341110440400c92440c00e20074042d120400b40e581d44000006015400c0681103400903068a000b840300f402003e648d10b01c1c0c1c0b4112a43c9046076000f001000c01d46083c420b109420044138414540341040c2030000040c8014648040c00a00f03c0309401141d0300c4262990b48510303100e000303043c1c091061107024615140c5401394468003050030300841e8204000b0342402020000004090b0f8010000c000c0100f1145025480c1d030410842d0903403d02c0501c0510190007246c0c0291200f022024000c2e11824942e81e880da00186180080c050390f2010034001e607008524500e0b0040314001e01102002d03501d2800e41021040308005801000c400f942c240b03c207006141d030004919030700c405070000040e0790f00810b8042c428004140c0d40b0090f00c40c440c03000000300300031a0350807080498040c4502d10603020b84071020507850b1400e844800c415038 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 204760008 1250 204758758 204758773
    0x6050703020c040c050933070c03060b0103020f0a020f0d08091905011b050301180e06040818040507030911030613150b03070312080603060601120c02010e01181a09 72
    0x1443c060f48030603440d4410381007203441c246080700465003103050131071445072888890902401c0340c4130811650f094011022506450300411fa40c686d580500705001c06030881c0d80d82c00b42d5202990003541110b521070844101603840c1c48844400950798a40c10780c03040b859005190700c201707509000b600c40601814810b4041e20498079180664502d031390402400783d42d10340d26101503011000e2080a1000035a0070b5a40f000d41c0c03503041c086042c1c50720080d844600c0c80c4914190395504500c00200341c2c1d6170840d83c0b000c81c40b5641c6a09140842454580b0319813aa44180780005101645426a010b40f600c280f060a0061032011400300b05078480c541121680790284044001c0780c00144d03a0304041c41c45228101001030a02c450310082450300741d240c0c2040b11030014a240300c1104036080102c80e680003000310010440b500d420b100080c2a030141d008000c045c05e85840303a49648500030740001d54100340c401c0c000c010a0f43d0341011b03c0c10180503510242c3d03030f041220007041d84030000c885599201e0403191000300340c403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 204761258 1250 204760008 204760033
    0x2503030305070c08040602161a04050108040302070e010f051e011407030909050108030c070b0405210f2a040207020d020d1704030507030c050906030c04180b01031b0605070302 77
    0x1800004101c4000c0080c072000f00000079520402410140a059004000c02403564804803544a0160000c52074070007052140b00048103038000703c409842d028138061409844a28090349003110940040b40b035403007010000310360306040c109280200c8901f00d8502e00c4044107490f20388101c0900d180d0310f0b030000d80e148410b944051040e00042001c20701c06d00d4910203480d9210807400c120303902a0422211500006406946401c00700201c0019280070410649020310341000204607031040440d03a8aa110751a801402481050200c150300d882c3d0a0103642c840c4034208094034080001c00342d1500920168041c1c143c0c0381c1410320a4544080d400b0b803440c1c000c2e02050b000c10842c3c4e80c20072402c8610750008440d107000c0443e140064001036200700c00415616096240050703402816401150050381e8400404c60f0554001511120200c0181d90005980f0000c05c59041010380700100a02008031107000002000800c0c0d20803903807109281c290030342e4251500d030122202d00c00c4a10140062b8810708a0000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 204762508 1250 204761258 204761261
    0x1009060305060d021504090b0108090d0f111e0706020304030c05060c011d162102040c0e03030703110105130c140a0302040c17391e03070225030303 65
    0x2c00c804001c10140d5a802c00360300080700c0150382d44460340700110204040001418a002c4c48502000074280034066280030705500d541e88000b00081003c001c810b0840d01c46071800b8181c1944000324107030540303100302032030000c600306901c01d03a5001c1d400348541500010407600c040309550a03654800101c0f08401d01e4901080815000a0001c1c01c00355a5a00c145030800305801c01c042505e0254409007403008661880c944080a1962000b0900d002c00710034819515070610134103440d564115400600c1070386070348085640011024416400d884002079450602d60455680c19029109500070300540c3c2c2d40702102e04600403d100b0040412102c00c00600440019480351a02d511000d0044c1d0201941d9800050546200700c1884000c07400d42011107590f0b001107001c0035840354040c45420304912800d10116030540c0d000c81c0c01e1550201e00141241c44d00340700002c0f81c2548040d1140c20742100c103a10740a503a9640103554800161189112a50301d1036002d446a039680690581290360003071858070300742c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 204763758 1250 204762508 204762511
    0x103021806031f0f061706181009050c0909090102040b09060a0c06060e0f0a0c1e020a0516060807081003110102150a1a0f090a0e0a050d020105060109051009060305 72
    0x800c40c030b80742101e002c3c0b03c0c840150404000d0164100140007940b0346030340500064110304030b02e141c0102c008100981604c0310400030455850b06110010203541d0780740c4400c1c8040494001e5031026051005226585c51100c014040c203000c1101c6520300764584082c0c40d400c038400ea124036040180140300c0142d40c4d15102c1c01620042149003849010141c040d90f80000301e43d07060f00201c008555020038006008144050185d110150740800c01c11300700304c25000f4100600962801e003c001c1c1503070f40e019038140b0030300095248552010031100040081054940720314020300803040025156030005002d140318800c1e00340520109480e100c00942580ca5640081d14074140844c190300c50741c1c1d0006290714248005178492040c0c4903000985100c00c074450800d502102142030f20802c030081c0102c01c6540c0742c0e842103403c4100420b001580704000c903419801c043c100c00020742140501d00000105503010f4000e107200784070076a01c210342140c441040284049040d221034001600b03000c0b0030f0050a000b50b2106 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 204765008 1250 204763758 204763771
    0x110304170d0905101a090c130b0c07180212010e0603011e0515100509091b0309010e0c06070213150e15150f2703010c0c1101140f0313020612060f010302180603 70
    0x400f1250311900541c460b81e0014002b0b40c041d50040d8000c004001041ca5020340e00d0341d25110079440c00d1080305007880c1c02c0c1f02c1805451401c1a120300410100da50940c0705420858244d01819000c00350340100e0001400c0071200c02901d0810314030748510b107203040f2408074800d07646c98a0b02414580550203000e8000c01c0281205100d012040c000045d0000340c0c0040c40c03003503800c0e0380003050342c0d5000181d0604180000b401d082c060601031001c000140c3e140d8003001c2d0701d21707450400020308840250849c200c0180d076900030340039640c4007028802c12801400c1800f07200d01054601007100b00c0030010f11192846001d404d610a1842407003444110b200b40450030500c408031482e02e81e0702458490000b400c4403101c0c0c07105c0c00800d4103000401e0402503413101e5121080d009003441098074540c24200c0c03510348204000c00c142c6904c000700040510648001d03030400650003400e03203911101160104207000070103452031441940c1243e84c64106620030f00848603203050580c03000900c01195024409a500080c205 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 204766258 1250 204765008 204765037
    0x105030a112b060c020f19020f1503010806130f020d11090c0403051219080702030d18030816091a040b0a02060106080901110304170d0905101a090c 65
    0x8448400010042c5007540000342c069003802001985040811954000008402e6401c40581040d02e0680892644480200510024600d800728800111440281c0c908190300c00741403074207910f02460b02c4003d103050703407224070880300d554442070711545005c080d1f900c3c0101007003a0050703131000605240c2003418216224041d2400d00e205804001006003104807030340080000c003ca01002405000c21031000e039003281d00255880c0c5400005070003030384024014148180305540e0041050544204221428800340c000200040070000102030141c51341403c090700060786400c0856554944000da6603d804110b848030101c151030030300c959100340a048884500c0100c18000098440500d600801c001c1c492580546074940c1000c0300503140110161005545a25140103d0038a003c2141100d0308541c002e412030409414140d0061003d2040408050240f401d14203078404010001a26840d040c03030450052103c0d080440481c00440c05d1010419030100e000ca002c500309041900050001e0300e6161031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 204767508 1250 204766258 204766279
    0x4020f04021605030c10050906060907171509071d1203040801051302010315060c20060a08011a0702060301050922050c03070512030d0c030b03100f140105030a11 71
    0x2c0740002d0142034441900d040c1c000103981c1c1c111030024041490880d201100070007240c24170100455840c0002800c2c2802140d02d1070110324550b002d4482c2206158942d0143c04140c40c1000101c00036403114000d00f8003408804000c281924041c2c00725202c0c0070600400401c58944800402c40e180d2803601c0b54075002c0c0020000840d05607401c4c06240e10418038180041840045440010200d541102c203106042d0b1040806005403603205001044141c0c00242c6040900110b4000c455481d140e14a41644000700207402406940c022400a040741c4100c1b102c114280d0180b960640c26105004000b03500000410051266240c40582550445802c01769460340b0352203401c803440300c01600c1d141600c01e68802210a00c1078601001428081d20060300e904101c142c5c40100c2c15924000d0988100b1440c0e16540300b594014407a60209443c400c005040359040c1941d0061072008060880d080a00c060410310b20b52009800c8820403412030300041e000701941541d82d180c0c80303e4030a0f40205c480d07003c110b002 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 204768758 1250 204767508 204767527
    0x824010e240c0d02030403031202030a06050901120c0503030a0504061101020d0e1506031506010e120102030118050a02040b030c07031404030b070f020105160e1908060402210604020f0402 82
    0x40180c4510310115020075940c41c0310b04101850706000c1800c4400f107510400c81840040d80c41407130084000342462001d0b031a51600301d004006480c1c503070030584c0c110b0060400041c1d4450800c0e8083c0d44103004003201c180c00c40c0c131141495101d00c0745020020200320f08110402c0214072500440e501e03075214400041c20a562004000141c41560b1030062035075001c43e000c1c940780700220f15480e80250303046004140e494030448040d81c505d0b10052806060092003a441c8409440304100c041806008c1002155603603114000d11800055602c0698542807034200000e481d00018803c840a40702001901ea046645103048101d25600400048041040d0440c130b85408034030400281024500c90f540307100851404081c01028182405420401c580c105024802e58411081c100c0540102c1841c0c602600036010300407800311101c030203003c6081c0e00e1241e0000390f104001315403140a94801c845000c19103080038401c8a0445425a010380903402c09c0d0041001840c015401d0b00c089000a0009810041d500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 204770008 1250 204768758 204768799
    0x2f0406260c0a0f1701180b1513050912030f01140607051006090b0415090c030209120d0e030307030905011b0204090f03030f060605040504090f02030a0c060824010e 72
    0x198000034443e0010755090150564003003500c1c8005840800030001c203640f000400c41101420140980820000c0020400004075024503420f5a00003510a007803c00e580c902c090001c0a04840c2a0254090240100e405003012401c9900448608240c01510390912107001c08020b01288541d50100c4100510b00000c2e07014410180d40d10028240040e040e072902e4491801c3e6008446010311403450813040c04103500421003558251056510000380b07c0241c51000e6000b072040064582d480380c126022400200e00002c1c40c05100d001c1552000498880300003070540da1b001e0100005d0105415103410700803540f040c0409844207504c10005d80e000c8a482d0041000c4800c030b140e040da5401c0c1203d142c0800c1c103415000d11a2502d603081f40c00c0000b030f850550700500500541c081d80d03100c0c645603408a401c2c8841c40052000140c0c0003825900503031010b1500001c0c3d42d0305480b40e01e0210313454000150309040d441150201440c9411042c1c0c521503800001105c801400d0417071142d01c00e02c6440322403003141c4203 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 204771258 1250 204770008 204770029
    0x5071b0e0106050c12031e0a0b060d0b030f1501150903080a080708010f080c06030606070c081e150601050a03110a0c03140301031a04050a2f0406260c 66
    0x268580c1c136514001c0701903103030800100946101680200300184444000381201803001003040a2145810b903d401c1e0a02002c0e10352802d00d0f030380c403d0000c038500c1030aa40544c13207601892000c80c02c0303801c0102001c00080e211503240d800000201c051400400c1000c0c2010003102e8020540e1411241c07542e26640c41018603044000303020000381c100800c0012841d040000313680501b92284050100d02d29200b44265203480d0902c200380540c00210204006840e11826102e07002c0e032203d04942d010f0703207884c64103a031816086559031020b49548040c5d50f40c0350b00429480b441c00300000300f0803103d0381e4a00c0103594690280940d0740801da5500720510090b01610040c19800019503030303000c900d89040c00c0007458425880312602180100f00700400001d0000300c2c8056200c0c021b0f2205985c0780da29810700906149041c40d0260020000ca02001b000a000c0424103128000d10081d94125120a805020490b2151b005e010800880d00c501c50305500c00b4107001d42d41411a000c100c3d10380389081004240403205 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 204772508 1250 204771258 204771269
    0x16050d0302031e010b03070e03100914060705130302120c190f09140f1b03130b01090e060403120e120301090617100b0d020612061f05071b0e01 63
    0x5011050203050000c503a45070f400220035000a283c03035410003100142620016000000303100c2d8000b1550500c2e2403c0c803868803c8210380c0c8c1c0400030b0183c6824040c500e44150808417440d40240c80000700103d0080c0141e0304468801040200e13020f04550034440c0c41c0b9034003451b821031442507030001b912907581c03203002184c0700c00421009481c1924040e800d114080668202c7d81040c1e082580140c403146295040c50f6014501c08140a9641c5642c034150b260945c143c4d28800451900008000c0c41203c4455007044440c81194a032100742c1e6544a0507044590710082401160805004035020a21415001c0313281030110800040060440c0c456900c2c000036149800850b80020004201400051154800408a5600c4c5141d01410300c44443d4803544610192103001c0d58a480c0510981c407a40850324030036a000d41042c3d510500b402c089225104100d40140c850088000700d020b50115038590b40740031881e03584070030f4144003881c1e580600c0108140032440700c02c450340d1800a096000320b00024000c10 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 204773758 1250 204772508 204772511
    0x319210f0903091d1302010e031c0801050f060304030e0109052e050909040f0f06050a090210050a09030f080c060f07020d020a0b07080403020c100f02071a030c16050d03 74
    0x1c66498041c1c5a040c032607100314044540c5440c450009032041c20010703480940500501e21008a5200583c3d969071480c0b4000c1e01031040d800c20540c601c800c000c400018900d2500c5021060b039842040081c01140b80b003103640c01a0042c004940000c2c0030340403640c051941410041185901c400110382c3c42c8502e0051403280b0583d0014850050180e1000c418504400e403520a10706803203a00403811980c00900011321411420b0b0340082840b082e058001c0d0702e540c1c00842841903040254003032000e003503011400d900c00c02c03040240e45141401003040b40d05e041c111b501c0c3c1c008031034a1500d40b042c1305041c00b0800d80702c50301c0c1000a00e40151b010f106143c85600030f401e10400c1400e040800074901030b1450216410b6521004500022a118020b442d070301c40c0240c82d00010350307562490101e081c13015500380c0c15000800180c0c2038041d0380e0000d0780000704a07201d40c02c40c1d426a5a8080040440d018216108a0314030104040b40d040b0900400400700c843d200d840d820341101a5a84052500c40f00c103102c140040d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 204775008 1250 204773758 204773771
    0xf070f05280906080a0204030209061210050112030e0109081011070206030a0203010303090812030a020703020109060515040f05010e06060a0908070b03010306060e04020112020a0905130f0605030319210f 89
    0x19801004d11600003060440460801b030030760340420510600688800e20a001891448400c50307002c020303000003402c0c030b441c0500a95940d40c0d6814074640500704118081618000d4406031944202402030880c1d14820091280c250100d2403200284021050b04070300d49410004c4401580746d5a00450040b000e101c8016070703942c9036003002000c5171a180c000700071681050181408140c0340006480e0004040300005941e61500d140a0b80100845900148040c1c103000030021458142004402020401d80d001c3c0605180315854070200c0707200740505040d800404001c0740b1241040806400220a50b0810040c166229044140f80c030416500408849400100600400c0128000e800041401202d400e00909099001034261042c00c0081c4007190b07400300f08100024400c003006001804083c0008021500c00c00110004c1d290031a046071080d814040c001a030790800108403101e4076404003072840c40b2009050b044500c1d0741102c019481602c41031500607001c0704d162240100b0b071703409030304009620b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 204776258 1250 204775008 204775019
    0x50c07050604050d030b0a15031a1309020108060109030302121605060c03151c0f08040f060302070b090c1012060b04081c18050603060409050102030705070501050f070f052809 77
    0x250346206c180940141140072041000d007003c00c0c03600242c207213142400300e042442c20080e612110758080c0b15550108036443c021403204400d9200300c83c090700030b0380c401039207686540c01921102c81d070748002801a4031043c81139445800703510280007100e200d00d2045d0741c0075200f502d80500e4403206071403803020f1280c0002400303943c141441c50320181c44400c0d11400f1800381152110260070f04081320262206500c0c00715642040040001c032406865100b0050352081d0300d41d84010000c0d04480f40c121a90604100441c0d00c0840000340c407000594000c24050130402480301c1100da07042c09000d005102c40e04c0c0d10002c80d07920640005807000d002080018013140c010749036842503011402a0800c140301425a030070303490f40c0c120010f0034187d520540c1d18994903180e04004c500140807200016285520210a00428903844402803260358082c0d802404541c54411f5031080e40b050a0742d9020100f01c000070b651031440d0240029107050040d40c01c000304002c140d04000f00000201421240c00104400014042d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 204777508 1250 204776258 204776261
    0x60906011212031e021c05010905040f0215070f0f1203060501050d0e0f03070b010e07020129030c10120e010203040809010809030409020d05010f080303060108040303050c07050604050d03 82
    0x42464903181c0540e03582980b101c1d90011001d06141d010503440c3c3c0b114211410032422032040c0c0d4600b540d0119035034141650124039020400380c1c000c8034681400000a8064014000c042c050303504802804800c2e43c10b42d082008152415200d60794042c010f001c980040740840c0034800d0f02c6406031250150a0f5424981355001d07003211a0401c00741843c2c20f000703000599000701a64010501d8110006110f02c08502442c9440c0403d2040e1031a4400012100c00300900084045d04a13407416184001540783d0348402e82c2a01c03000940074a141091100c1502d0103e80f0900d5400c0240014041d211101446c03c00f0a00030f0340440c1c43e07180810180740644811980300e21901111441500085085041584e18403c0c50301c119000d0a040001c1c410100d40b804e04140100ca00405441e402159540071007007001c1d014000c00d2240981455003080001411107011049070301c07805051b59820a071355503640d01600180380140c66030084880034041c15000400411038640198041c00c010040000b04400040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 204778758 1250 204777508 204777511
    0x1e040603061a031311010201060306060f091103150906040902090901050f071103160303021b0a051002040311090406020c1b100e03061602030d0912120e0304090b0609040608060906 79
    0x1224a0801c00810140724269140740c4000d03035000d5982c005c0c00c0c142a0040303000d007030305400c090300301490010006012004540164100c500e400c9060001201d201c2c284032403800110703a428824104158800514500880f03110340c02540207000042001c010740101c1c0e0581d000312068076050b175441d03050180500c006024998404e0f414a0240d18611061078103607124050b0f0f5100804020307000c01d4420800d40681c0603244080345241005583e503104158859558050807000e88660041159104140d907040c000ca500b902e0b00b01c43e441458022002c14007a85000c024815500c1c2542400044544102445801410684404004010b401c641d0802016205c41e9240e4024401855002c07038072a200412503650107481a00c5484c0b040c90a407600703070f0071449907035451610246011026400c00c040010031f0414004155a5a0354144221140c00e04039506c2c5600d1020642c000c0c041040000e2a03034002d4003060302d0180c04075040503514004a03003911881d811000343da4108808000c83c0500401541c2e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 204780008 1250 204778758 204778799
    0x11b06021803190305210c040e0c090f0d0c0306060b071b030b061c150c0e09041e0606090e06010314030f04052709010605010f090806010b1e04060306 66
    0x4046145038a89040b0108100c0c83c0c0060901c9404180080d4100c015000c00c11640a155008040c07031800e60701c40550390740079002c0d9010310a04440408c0048a032402690301400001c1e1180000d0906041042143e44420f001100c54462141c03000c00060001c5c02510004d160000b503007034440c11945481d01c40c80c60340c4101d40085600c0c41e0342c104081500280f142d604540d043d40e0300580d20035162034125901e0f0007100003502400b02141c0300800040503a100303054a40d0131340c2ea10429901a4010408100c101355030103081ea010318490a0054251007100b158070310310406000030f43c165690b44034410b440c4c610700c2d00c01d05500504010424000c000e003100758085d10140c0614544840c21418240d00d00a90240360300039188a4085180302c0e00039121000032820481c0340003942c0c58580d00712400b070701d0356005442c0007645c12040040398601421010090b20f140b00050100b07682000414170880e0010002c2d100340d6015120f281c9804250310008001401443e600458254103050003056030a0420780701 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 204781258 1250 204780008 204780013
    0xb030717060f060f070b070f030c020d021f060e0c070212070e0a020a05161407061704060c0e06040608040201020d261b0412050c060a020304060806011b06021803 71
    0x80012542d5103048408010504840035a1140d01e144940d1883d401003800041015190009002c10150842c0c407400e032120f985e580c01e100700c24884030100e0f100c1ca030302042c03c00541d011601c0b0360030000c0d102c00c071180d510400f01000074080755204480709a00701e040d00c0c2c070400030b403002810341c3c11342c2004800c40c24114215001812441d1600074402d001c83d000500c00c141745035001c60701c031403c02e00c228212400042600100186c1c0a16810081c3d000769660031503008610482800046c1c07140550292803c81c03494018000580c2c3d076a0b01e952001c0c015003815502006840d54480762180c0d290005440a030100d0381e9034600601e418800649011a502c0c403000c1400503038005590300608014480c40907115142080c401500c5108041e42601da03038080040b0b45281c081004589034801014503084140603004503414610f40700c0a128081c405d41d004080182c1040205000290140154540080c0b0614255581e01c03654102860102101d407401c407a0756800084645001b005280c5100200078210007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 204782508 1250 204781258 204781261
    0x160f1406010e010611150c0306090106031b08061503040309080f01020403080f0a02210a0306050415030b070504030512030114030c0307091508060907080f0705010c0f02190b030717 79
    0xc0801e240c2038144507003401c11290084144c03400c01c0a00031311b44c000d540f0f100e125220f414a5919510030340c004540270f07802044602e00004000707200703014001904440440104418400040c11107060000901071608408500da84030b000100010080d84241c2c020354544140c0b604000901e82042c14900703c840240e801488144041800d1780300701d032613442d01d03100000e996000c03c00c0160f0428124120301602c00b2406c503103201e01000c80000510343c145517994108245900c8108100845000312440e203082030840c85d00b0310006a09010644c2c00001a041c018203060f030760750340c6501c2d11070303804003000406c5004401004803910301c04102d003d040701100034083ca03690490204e555a499481412103071515000408211903a0307a650901502580313055481c2454030f02000e40e07030740030603101d10401445070504c14041182d002c9940426502c0580d01d400c11600795844403440c50034800350aaa21000700054281b64594014000d4010315400784003e880c3e240002e0050010302501480700302d075401600 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 204783758 1250 204782508 204782519
    0xd030905100207062009010921060903050d020304050d031b170a060302120105010819150c2114060a0303081306150b0706390203160f140601 62
    0x1400001030001000068886041e404c068001d0920040440150045c01d8040800e01c1550301c0204004003081c0c0b506810141da551024041001c0b04001d0303403194194103400c400140e015080300c0c5100d40640f41031820b100034452444100d030b1094408588035401014404120780d018042d409020000c5034085c01c400fa0141400340c802002100095000040304c0f00040c2030300c10541c440d40140d0303005000182c1103081d8003160f6000340028003d05e04188191a10703140700e14080302c00149881d500460314100f000110442501a100741107a1400780900c0500b2554001005009981040d161001c040b03411220040074100c442405822580540c100010a101103178001c0d4a140d08100d501c150b21000842c0c42c208140202158090b03880a003580e0440081c2c80304220000d048040d0007590704204180c00c01c10340c401410051044403481e2512141425095034560550f04811000d5006803440c1c00c0100001402304450342c1001c940d40c03048440301c4424000e00486003050f9800c000004c141c82d50510 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 204785008 1250 204783758 204783763
    0x3010f0e060f1b070501050103140304080d05090d06051f14010f0c1703071d0109030c051c0606080f0105090105070c0b07030212070e040b01020c010f030e070f0603090201020d030905 80
    0xb00b030003400c0c40c18503021480a10340c2c034a04459002c2e412012644071221403400354080e110070b104c151a1505c4054410700f02080100498044504a074000e14008841620588503034208111003640003060140172000324080340103180c4039403124000016003084001441c0f008400c00e422803201c001c2c000100313644c1a40c11180c42881e481c00c90411141c4002d080c03414000b128800e984000c0c581c8800b000b07000c910340c0c01001004554141500c80d0b020038010710011213104c0454400a411883d20400410041c10b0201c0d042c41c41c00c1000c62010508612626458181c4556600c21602540b1607480003040c00030a106064202c90304400070303c61422f000c9030041c125500c06402130f007240021f802041c01c250095045507180b10312203524211038a00001c001d003001003494181170103a410710448071120740c808039070052480700c161120b21021155100c110011700c90014100110320035803802250b24003070441460000c0442d0703038010a80000f11301c00241809a180d01d06000c0c141820382180009402 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 204786258 1250 204785008 204785011
    0x1009080301051306080312090714010203032404090302030306100905030604080c0f070f06090602060420150d0c09120803010302060a030204051f020106150504050607030e090c070203010f0e06 84
    0x12607900b586240403da00b180104000d60064030361388000250800d140c2004c01c0729a2161080006a0706000d0b03681034804508607200e41d2a40c0183c10400000c1c03d41c00b0030800258006c082c011510000c01d0f10b4401003030440e0414402034003d6030003c8200710b1945000900140040454501802100c2c503120100e40c1d5214044d00040c154800420f00b0802c0d01000c0105001c5020300350220b5103141d50383d0f40000e1011000e4081ca0000610b041c1002c54081e00000d00940180d51100c1c0794810a070b0340550249e541e160040e08203a00c02c00c400800d8101c00d00d100060600d28200b41d00014607108042000341c2100f0341d6501180007213000d501d104c008141a4002c0e00d0440340c050312682e560b26100c51046000b80b2680e000540d010680c0c2103c4402006402140181c00d41250000c02c80f441d125141c1c6d0741d449600040040028404100c10700c9a402c0c00f4000d00308203807080c103150840c40246e80000c4e40d84002100c00e114500030200740d07070041d450240109108902041003c20441481c000b81d29181c060 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 204787508 1250 204786258 204786269
    0x8100b130905010b06030a060504061505070b1008030f0d0b0102070602150a020d05040605071419111c080a0b010f090504150f14030f0708191e141009080301 69
    0x9980d0010001d201c0c2c2900600e020440003020503a4038038008554034021702c250f0280d240038500c0c03c0710105402500f42c403c101d13100b035135850716801d00400e6a20584a114010030410904001c0c1a0006001d1400c10142c2480038035280004c5c0c0390390f0910801012541c4c80d1308120304640c05084d0800040d500450300041c540510880410a07542e41e141110192086946807804149001e003084244841c6a00c540d018555031f50303c0c02038202003d071219800e4050340c0e00c0d081108840c0300c07128030914007038105010b000c60321074141c4403045007900201c524201e03011441d00c08245104200303c0504007074420b00c0f443d504242403501c040c031503400c0001c02110b000e018143c040c958401c8007144c0360102c41850700080110391450302505031207100c1c03055000c52103032400d03000784074440d0f207400d03240c05c04904001130340c0903480241442d003034401c0d002c0d40c80d0080c41030076681941042401400c0520150200034181e001e408101c4017400c20881c0549010600301700301048a2801042c040055550800c1320704440 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 204788758 1250 204787508 204787511
    0x311071a09010209101d010306150c02010201090b0406150611120c011401060306140603010302030303060f0625021305090a060f1e0f150e22020303031008100b13 71
    0x59840341d0203802441000b0039030b94000d0030304184a80e131a6001c00c10340580c04800b00b40d00100c403070b0b40c00150291000b5008010080d985040c0b2081c00511802c41024802e00510020841d460540c40c4c0741c281c0b6400f5101551303c1c9803207940401c11000340444500040265140c546400042d2085254a5800e900c0b155403103694009001d100c0904250002203959805003101a10b17540d544102400400d01da00c9045110b400940c0c14454a01e400c80c01e603030403a1b230003a010b0762840d0340310010801d6042c03071201c0496005a0501c44409441044042501b4185034001e181004d410355004000c03c08201604800980d41801e0030072091090119920510581c842c0002c94450354658181d0040c0070112441084420403803400420f12000790440303d03040340000001c0102d01500c107940ca0000b0a07a000d080c10b06204440841e1228054440d0690b00140681102092101650010341158825100c410030011039140905c4441402c1c84a1400000c402d4400c2110449850224044031408892400200d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 204790008 1250 204788758 204788761
    0x507050909031303112736010b090601050403020a05040b15070606060215041e02030f0f030310090903050f2a100c0206060d030c06060e04050a030f080f0606090d1704060311071a 78
    0x1346601802d45000b000081c4601442d10b00c0310705054002c09c91030000038030840101c8086180c55005600f2103050300d8000e4540c4501178200018000a0301480301c00380d8005040d40b0f4083c907940700e400b0107405018815040451410700d0301c64001d1030024034101510540021805200001c0c0010226140404003809050100f4196000003400c01140315004081401208403640d59140d021005601c1072074884200c04000b17232a003111400301c8a602d58002c01190f01042008000510b50002c2c05044d283c01540d045280c3c0e40b00d603070032300c600745007031040b01309900c40366000c1c55410503401542041401032000701030900c2c045002a00348022110094244016074030710600384100350700081d0142415980141c418206854499901c10285405500181038108282607540c030900685015003810101c58205813100301c1000030f0740d2700600007654400b01140c441d000107903050402504245103030a001d900c40780360050290584d107c4803444201340c001000b815001942044408002001c00580c8840c44d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 204791258 1250 204790008 204790051
    0x406150f1404030b0a150801140f07050a08150402040608040605060d030f0c02030f1e0607051305040e030d0501030305030603012d021308030d150e0405070509090313031127 76
    0x180394034400c06406c001052030110b09541d05400c50340104030108031107600740d603401c1000c04000c40e00741c850200090080200851040c030070040d44d500702a5540503022191001c0c030000d01264400d500032000b054800c0200024005184030b2142d001c0c0c41525002d91080181d9001480c0c00340408100081c0b0985c0e951032402e5490802040c101800443d08840700c5480d00b0101082c05a05660f86041e10310038640044c4800d481403050702c0c0c076929a50740030501c050600703041101a03c2d50062802c820320080c4207280030300840b03004041c02140241c650340d0366400c08800b41803d4a0b4114401c0780f580c5400070481442e107030b0760340e00d030f0180858044c030041e11a4410340c1642007005060b48851741a10001c20091441c8001d80e002d400600d071710050b0000c020f50f960304131506050088501909540002208100c2410180900c1e9846070840003540d141054181d40c80c0c00010894000ba1120004c800840c03000d8206200403040000190200144800080c00f42d2030014400911116003194940f0709440b2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 204792508 1250 204791258 204791261
    0xa0b06120417040b070b1b0a17041401180606080a051e0309130f0506040501080d1d030d0207080106060509210304050603090f0d26060604050406150f1404030b0a 71
    0x180004e0740d0107a03601c5c00b1a0804510f00303c0306071a418050f00c0c003115640c1c20450100110303010980c458403025940382100c4040101c80340000c00580b9820907502803244010400c0c07040108032207800d00c920642e50320904001044410b95000b00605138840c28000e000700f00c002a10b01c4041240e5110380218910380712a0320f06502a038180c9a4010208007101502d0181540007031020b401065010845540c844040100341c4002b8803440307405400c541044170700365104281c40300c0300f151002040844503074104042407a009807000c000c0010f8001c40403d00c01d141081c002c5d040107103207d19141d030038511007a00003410380d005001c00040d0000c1c00b540e91250720209105a0700100402071025480c2c0c0760004503a41c0710448108204c0d081d006044c12016164001c010500540e0443d01e9210200d10900a031403170120310107868180d00900c188400601075030b441c0180301c050012901e00200040301d510001c1c111085001d4114107011020342d40510180c02241a58110303130b0080782280d01030321340d01031260 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 204793758 1250 204792508 204792517
    0x3060604050a03151a0612131b1e060203030c0a0908030d1a010206091911090a0204080709020415050a0c020409060209130e0d2f060a0b06120417 64
    0x40d0003054802c03000080c04100400e490955100031010312200c0001c0d546841c0a582c2422415400071060181c1c1e14901d0740c6404580c0e100d844c0c1d200302e4040707820031380320660707e818600d48079026024524001d008807480380d1040c14050502c000c10248440c00d00748081d450303010040c401c00402700c0101c2e000383c805204044000040081005903541c90f00b00c200b1060290810241c4c0f11010b0301002e042c491103510026031345100f80306480c060415404c0d840740886000c0000c0d801620041d40d2105c1038059547c42c0c02c51280036032001000160b2307581ca0103003480e040c0380e2141d01c603920700e910522080000400083c0c80c2e0342100c0031441c7c1659207030044501542d20580d001e101940041ca800001000c02c074190b2700402090004030748990304440300f444140140ca448510085941c1c01c95107040c51024001c844c014a0710300701000c810404501c05110600030000e10788528810f9020344c0521030050390b41d2103180d100410039500c6c54031302121010104410440038100918803010448001420058001640c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 204795008 1250 204793758 204793769
    0x120309100203010807091a030d110114130b071701030206030a0615030902130c0c0b07020c102606010c030e13020a0e04060f05150306060f0403050105090d0201061a03060604 76
    0x854503544c46140c01e617940c0d1164040c0f0003940c0d14003032a581c840a1071071141c0442c00e00081c02001080c91052048464030032185003d80c243d0340ba0004088540d1148004da442500c6040c0350001c5510350782070240034900080d00020038031080030b00e14045442c042e88903506581d010784200f0368985995400b50000d0a0350f500c40da07000707031828200c15410ad605030040da032035074000c80300a1001207107200b816045070205502c41c004541c0000074480000e1000d818550322a40c0750050b035500c07007c0b2101140d0803404201d0030f0b400041c0b000c00104001605c60a072221500d494103080c941d24600302c0000385c07030410741070005030501004450f220341d991369000010040105005040d900e503514014045c141c800340c010b80c148100e0801c1c4010840c1002003140c0700171600014101130907842c201d4940d13003ca510203080d40380c22a000304842c100d05241e0038000c000844c072920002840d458040c603207a080400794401201103904000d001c000c991900d07444584d0003600c18507566500d1301d4850014211380b0803075214 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 204796258 1250 204795008 204795011
    0xc070f1707060510060e0d11090403050d0c020703021503040f020a120302010b0621090106030206120114030c130e030702150301080f01020703080118230108010b03010e12030910 78
    0x1658800c0d40d000040d05007184620401e0101c0d40b0341c6903860840302000e00a00c000646407034016003091401c6000c040500d070190034000704210043e00400e01020084078141d0105400043e125080120b074402d905074811030b0300c0075100c2d150543d0b0000300640b40401550752b4110011001c2014401074100d805181a40144010012a40c0d21920081c4411145094015510700003c003001030070590304455184000c524181e4142e5010721111284040c081c080c449903650b20100800143c81e8200240492100500a00303a00d6141000010050010041c81400307508490501d810710b803255450030b000051008004980719240114940c5140603180020350f0245034605407000420728000107505890f480300c03e83d00c40040100c1c83d1343c207034860400300400081d111001004041407004500300c401140c1a4003040c2d141c2c1d100e4004600a0814900160400541004000c440405d2143d40034951056000f4031403502035501e0b40f41c80f80b42003a108072140300c00100003140b0700700c18800d0b1042c50819540 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 204797508 1250 204796258 204796283
    0x5010b0f030627270703030309140a0302011e0b130506060904020706050601030c050a050406080a0618050105030714150a020c03070602011e0912030e0106090606030b0a0e07080c070f 80
    0x50124151600703a40d140b0032581e0b08040502111110b4a14004c0311040340d001744040c2d440c5a0701200109070982043d40c2207440c90102d0350340440c0030301009291030f009a00100d180e00d4014108403851b4204156018050b103051290205a16014100c100c4072540383e100045540e00c540c00300e0498440e1207242e560180c1300007002c01c1001444d03030006001d10403c1e80c0c00c0003650a1804c0035039040c0f0450403200702180e01840204412442900b03519070200c0c480c1000306035140e0700c05216124071004014400c0e9540c44800610290900f00403050090101d50700c0e4808c03121341c0c10b000c00c4913002c032100c60b07407402c0c600080e40741c408500801410b900008003800b1a100e031035680000070300925464000c0c002a0b5020346201e415000d00c1d0154100302500100360400e0041009020350080543c41020701965403a9507002179030038038a114440060170382d03480c00b00d20240080200301d440341d00c3c1e400410007500610b051040280d484491305612050030317401c0c240c2da40c0445c01d0900c00d0a03840e80e0020301040c0101c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 204798758 1250 204797508 204797569
    0xc0a0305071202061e04021f020d030c030203060a03031812050f06070e0907030b01020a17090f03030c1c09080304142706010e060c0106060302091305010b0f0306 71
    0x402882a9030040c0c2d815500155000422a1540c8064564030314285024000c44404000d00500ca03410520091040e001c50440c104c401d1041e080c0702140038003580141d40258203e58142c018482c42c04d60301e142c00c41c5145032090003c2c40c880d0544c007016080140951401c000d0382c29498090016050007004003821000500c0d04981c0d0709c4601003090718030b003e0364002c5007195019103e20b11100100a021652598409404400602e802c000c503504600c10080c0401c0401d09440706090111042007545960b0407800e018042d01d504451403850183c0c0c000c0217002c02000d40442d514403a22011001d801c0420311410b0111146907064210f0301d031b58000041c2c00645040301d98074041c011002903d18614005400780055030550b81e800f6135104444580c2c00283d100d43c0325541c2c00180c00c3c0010f01b11b90400009240140c00c4842980001c1e01085c1c2c00140e9114501d88101c0007012803040d00024003442d81001264075403400f4003809440c2c06403010002c2641130780c98007203c10b00c03e24002002c0c2409031400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 204800008 1250 204798758 204798767
    0x10020d0221070c021026060102010b0a05030709020a0c12090617090c120102071b1d041205180301090b01090605060403021e0103060e09060406110a02100b04020c0a03 73
    0x80c10526800980300d2016a603110303611a02502c51441a21240708807100b640902c12605400c6030503c2c01c2100b90014011400c0066842080c614401658120107207415000a0b003107900340e400003481040c41c840100050760b0b00241c1c3d01c0550b1600c3c0c0c005600c85190001c16140f440d00c2c800010400b000c0601003000d0321364801074950442d41e5554990703040300e111065200103004183c4980c8a15045090740803003034140030141d4102605404d0005103401c1590b120300c99410550081d400e0240d00d1281d0800c6040500d00b6131101c0140f44900c0c11007181030a80c0c03102c08130301d0040303d41030074000d0100d01011500d90b500c0050041d098050000e100403181458002c81a01d0240103001c65146072810105540c20014159010382c1e0740900321103804c0e021205110318442d0700052076410140c641c500881e5124030801c020380540d80340b500070000c0d0b040030300d03001c8180c5017a01140c1111348414041008155070000d54841c0200c0c80d0b00c070014810b8905030105020344111254098a40f2803521502c0416610 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 204801258 1250 204800008 204800017
    0x1210209040f1707120e090618041e050307060606030509150c070204060b091002010b06040b07060906060b030f07020c0a030305090102100c090f08011109120304080601180c0305060105190210020d02 87
    0x10740d500d010000c60a50308029041200341c8d40281c00140112000c142c0308040d80350b440e005070180f4032060382c00030101500c11210303009a404881c15040030038004200655405402e02504075410107014510700f4403905036803841007201c070f0410b014804010448424281040740c2c07800760040c0c42071080d1901c408041c5041d40c8541d44c1079000b81803550240d0b03143c91040c0314003110900001c102501c0c007403400f0300700d1101e03400010050319841e0b074841c0b00c0d5000a1140c803070b01300201400c104007a00c070f05e804490101c60710b00c020a13040c1950083c10710710800707941c2c00455006481c1c1c9810415203440504004030300e40005201104140c0d464075444a2200750080f42d07140449064006414000d1f031a815580e00341c445081e0200103040007804641100e03c0c00d203c80b02030540c51442100c1c2019981c5164500c1c00c442130784281c0c0c0364a4110315040b0940128050302c42d01c0c580742c0c10240600e04003480001c1c0203206201c42c0d80035403400c00d210010490700c00d000e00c900002004e401951643c018802041c0203511 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 204802508 1250 204801258 204801293
    0x121e040b030a0e0c09070f120b040e150a14040b0703180c050a05040e060c091203070308010e011d010b0901030b180105031c090b0703110a03030501210209040f1707 72
    0x99907813280c0c0c0c0c40c6440f0405d83d108440669514130211342d8a032050395100440840004010b031210f102c80d1007510b035031280c07001003503008004180c0340b1180e4140c001020800303010a6102814038190340a440e000700d102c0d40d00720742d000041c1e01140d07136260801c9006103a044035011900d8103040c2e141042c002c2c00100c01064070811607003484555030f101c007000211417030f03000398052035003122000480c02c01c00c0b0340251090400c044c001005d00c0f1500340c0001d0841c0e212410840c0459a048014091510030205050140400082a4a10012000c5c01040c41101440303a20741c003010002c2d000038140d109403c070085c00407001c0c2c1840c030300c0001d107011402d03c0e40090040314024444d562030052040311400741050a8080b940b81c520406050055401050f4407202041c0c062000901400c0700c070038030421600101c5ca0103035500003829410034508048603400e0101560400c11498032000250741c40740e03030194110303900006000e20751456240c0b1180724403441e40125034005010400206200f0305500c030600b440d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 204803758 1250 204802508 204802513
    0x141504122402070c031403070c0801020a0306090902180703110c01020c010c080103030903080f130902030402120c0102151003020405130506060108070e010c0501060801020408010f0509121e040b030a0e 88
    0x1d0700014507200302c0c021048080e01e00a20424200040396400401c0341d0382080041c141c0349007200c2d03501c5500180180b517200b0701c1c00da076001038881e45040d4544558409007824910a208003082c640014140e4100f1001d8841140341d40004030f29503d000758031070f210110044901d241c40b20300881c6024004d40001340208055400c15048000c0d10b40300e280e909041c0d0f6810384850b40f14134110b444540e0303541c1050003540211542045040904c0400d84215002000d490340c000da560300c0d09205000700c5005051707000c409507008850b58101c90381c010600d0342d44908450741550055490454180141c80c03264000f80d0010314005c244100e17140341990b0740121a014004545454491400444003098100e07070071000910420b0f080304d015882101c031403488034000d06c004070340319031a040e82c44d00720380c4280d1001010769074034191243c0c10300070f03806219440590b40c00134007410b20103030144020318401c05111104181e110443c44054a50f1030040e100070b403240c41203454581c645014280d00400c8895811455071 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 204805008 1250 204803758 204803813
    0x306030c1202030d050703020c1807020f010c09050d03031b0c020108160c020f01050c070806090d0311030103020f03071e09050a180201030518031218060114150412 72
    0x41d415001020045a000d8000d152080507040304585035081000100c08501981034202215918601030702c00d40d030107a0001c1c000c2420700c00c2010b484d02111400000499042004040ca51500401c140c41114426103b4160003042c91900714014911841c049c0d004085000b980899507500c020107100c228400e8841480c191210b0800c207681448901d80600020080c020500050405c100e448802c0300c0e041c10f0560400304074081040c00c3c10880e410000c0158404004c1207500d020070080400082c140d410204140008102a0001407005000103801a4800c0c070741c03500540c41c00c109400042030600001c01040440100c2c00c80100c0591060700c400509005c0400c10050b01441440070340d1b200c81c039030300110650079401900903260041c032820748124600c941c04151002440101408400355401d00360a14101038104480380744000705d881150300c024014061840e000c1e4100c0c00d83c100460f074a00d261080c610302507a0030300c02d5070070210950200121400c04c1000566200202070010060420b14 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 204806258 1250 204805008 204805019
    0x10e221a09010f0e0606070204060e07081b0406021903090b0a030b030c0108090c01030504020a05060d021209160b0c1207060b01090801050c0d0b060915070c121722060306030c 77
    0xf0811600420f00a481400041501460808028072990703101030b10100e0016610600340c1c44c1c254080f42c000c00410700c00310800c902180103882601c8a0148440000d003041d0500c3c1c8000e680c0d9030a0f1128002c108200442401030500422551004242d41c1c00d102e6910b07140380304010302624034212042d00038858a155081150b0140c05501d01c0b440300c02000307080604056004501800c409003090360455002c0b400400d854840f00000c06c43d038141c0c0c0300090f0340c40c0c01000d903844000760010700c200c200c0d4020851480c0d075040300d40c00c0e0104590064044580b00c0e0107600d0014100926400c5d0110300c80400035020b810040c05410001204400f601c030908415507610225099601c00c0f1002c1288800c10010311401c44610381c0540c25110307020784050305082c4040041010f841c0840710f00709810a01250309001c01441c2d01c44031001d407590001024601d4022340d200808013811030000c0ca03954a0204880c01c0f007450300704d502040d200e042042024900d540e04006401005180800d0f94101c14107080403c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 204807508 1250 204806258 204806279
    0xc010e0d020706030519090c0e0a140a0608030a080a060e0106111005010510050a0309020a0e06100905130203130f06150f080706080702030d1e060e06010e221a0901 72
    0x421a40421031b55049500401810018072004030100c1e001d10648038003103100740c403904505200342000030002400c4010280c601c4a0213600804040c03103c0d0030302c2c80500a00d03d0200a940c0b0994050030625501d41b66071400b08081c250a410008800a444000069243e400070000c43d020000c0d40a80b10300e80555035902003a01d07000d004040e0014117104594464038410300003469028154030300014091910350000d00e90745480d600002c0211841d4041c0050fa02d403069140c18140754609004942c0c62070403010503060384203407880603410303580800080e612100c5009003006680d070155070604622140e141c0f40700241f20000401d41032007e451004600401c44440c0f850688009a004090051801c2c60403a03a001004010904500007803211250205c00390142d50003605a00c2c001c2e010004128030f1a0003160480e0740300850221384801842441e0740c11017503001e0403007005e40d44280701d002070b80300d40015504445803d078909464500c000e0860808407910241c80c9404441160850343d8620a610 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 204808758 1250 204807508 204807511
    0x210021b15040e011401031b0e041a0303070f0b09010b06030a050903130f03060c05030106170402010e12060a050c030103080a081b070b0601020111040b0405090c0c010e0d0207060305 80
    0x80c0c0d00c5480200006461070820140d50411250340501880c26848103080038410000707900c90b191000104010100719038042c080d034500c00c072889200b41c02c01c20076244010703c00040d8010540c0210382e110740d0130000c0c074081034007506901c80103000c86c1d41d40c915034540144400101442510900002c1000c9802d944060003095407841e40240f0003802c64644414140c014540900190381c140701c00c0004e1010480392405940081c0b41c401c1001c2c5403645075003080405d503100356010b602004010001406160303004070b5a100780711116100c408881d40c8070310040e00d0310060b0b0441540d210807010000100e4410005280d803003602c0f440001d100c252104400ca040c41d001c00c0c0401804072005000e4103486911444045070300a840c3c2511001d55101508080007542c8080429500c00a80c0c2041003459602402524814550002180d142c6458545264614003d50040d50b02c182c440e440400e034660b40d44c005941e8400710301e01c020040b440038084a20342da403800d00000d070050300851100050282c0a4800c05 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 204810008 1250 204808758 204808783
    0x6050c16110303070203070e0708010807060c080d0f050a0204090e010203060303030403110705061303030201050f012402010b12070312050306010203070b070c050f070501140702150f120a020403021002 88
    0x10360301404558420741c0315445440a1501840244001005031398200a603e000300f034501182070b102e0414400081c1804016000249540e0041c5802c011040d80301401d41c0c0e10540140119444070381e0440c42402924008499001d4241400180203815595500400464444480410112101000c801e090340021505079074590806d00c00980443e0207030303003801000d80d21034051314422515100011040d030400e03000e41c030824020010620425070244102a00a12042c4a020301d541c5440080343c0e50480e210b40700e410403c5035241d203c02c91030007504407920080c0004e219800c400d601c060340340e40e60140342c401500c0f40c44440f8070015400c1e0090040b00e014003010b0b0301842c50948180c0300c01200b039101402c21004c008048401c540480c9081c0081d03031000c1c290102825804e4500030004010304a0f24070804140c1c0c204002440061752110049a52940c1801119482d10300041038090a0b00071000c10b10203072140201044044c1000d80e00400c16a88200d44007083c000c0158004c903030307940d4500381e003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 204811258 1250 204810008 204810037
    0x5030a0b1b0d0507020309090a05060f1207051c02100503010614070f0f1511090d120912082106060306040b1f020f0c01080c0d0e0a0b010b0706050c 65
    0x800c5408400c0700c00100d046004080092800e01542e0b041d40403100c04543c142c00507080810985444c0c9840d03500103070008080310301803040381803c00c000303401c0d590000382e01403080881c003414a40e450024061500140310007081071850035403482540c1c025800404c82240304403c483d19041e1800d008070305070703030598003140d880c20107580d82107103104003660003410156000c100640329440010702010b44194080e1040580c03c000c8425880c280d41641c0e280c03807200603c108140a8128030382c440926090f0240e0300052a425061032a08041e1350165641e08800d03000307010b0046150500420364003c000c4500c1d4441648113445070000c110026401c16a403d0741d00200c2003010461501e0070f508032080c41180140710a112813036014546501c0282c410b215405070700b000d1200e4130500d00600c10007110f41c02c28245000c2501e0040ca000c8038034810781d0001a0019551480b14200310800c00c24503015661014981c0d485503128a4400101c1d003081008803061410000043d11101c01c9006540c01c0d44c111208 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 204812508 1250 204811258 204811261
    0xd08040212070e0603070b03240303040302060d0b03060106050901050d05040c0f0303020d09050109060c0f111201200a0917030415080a05070c050c0402180306070801030209130b040201120914060106020705030a0b 93
    0x143c1410303c130321651601d4ac1440113000110150380c400300141070446140c4800505070465006150510340141c0c0300005021090000c0501641c04c10304580d1400c034202030009840d641c074504058003440c640c002c054064054500030080680014242540200c0b0340c07640120341e990b0307a0044446100500520300020104880701c0c0000d5102d05075007910740c0c070414134010318003e4240803521402d03a5104e842210b87d1070303100449401d400c000c4014804182c44019514091780b2501c040d004202d14420740380300e03901801540304101014402d80b406000340401040c80c01100c40c0000307244850a50302c00c0306891900000c0f490b885d025000b0b1200295000c1c0240c130708006c00300100002504034003d80c0b60100c08040500f101ca641c14061944505842c1d11040550350560050001d140401480710801e202500b03181c801080e2000c202541c003560900e4030714000000e585a0002500800c98000c10000c0071440d28103a420700851168107981d000d500f11048142c0c0e55040555075011440c0c0078217200c00240 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 204813758 1250 204812508 204812551
    0x906021b0601030309231504060e030c06070807031b06090308010b0a080411010927060515090904060b031507111f050603010b09010909170c0d08040212070e0603070b03 74
    0x900b8581c0c10105042c0d400096400da00c04102c44c90307401c0c420307c0a4030800050521003035400c120002603002085d8000d103269941040030a0340742c420480c002e054000d02090b402c0030140301d8940e01600d007450800071211241c80b40391540c060600395104501003200c00f400401c41d007040d03030144e4428000581d43e1403040e48403501c035541d20200708600e0310b04000380044003007800340c0c5031500204002410707081812101c10001c4550111011600190311800900600308007a03041d5000703507006000e00b00d0381d039940c5440342c2c074140000f040420821a01030290413018100512040c2e6000d22803542034950003800c520a422207070716021100074207000a291599420751592680d80519401309000e4000100341c12550000f84003004240d2005200684a51003001000014460007001d40150380f030032410134001c01040340e107070000700d01c0003800c01c1401000a401d669504500c94a008440f88c140d442c060f8030340c0f4185242d007504486d4113000784624107002880303491103002c49114200c010801e0100b4241134 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 204815008 1250 204813758 204813779
    0x506010807021f0b120f10110403030302030601120e0604030807021c030504110409051b04020f030f0a0915140f09061906090c050304051501030302030d0902060403060906021b0601030309 82
    0x34041e0080e0181c1e101180026521241448624803004000906c03064490803030b01841c02c0c1041803a000b2050802c0c01e4208064518002d07a401d69170305050140e10ad56940004940c08100c02540100c604c1c1002c00603210704201051031070280c0d005c0c3c1d80e111401d5845003c10f903907800540014409070300303582c01420901781c8203610494200348134444002c0c21020440002d8203841c0e544109541e55040325404166400347c030141044881000d58080d410314454080c13104107804014164501e06407030000040c1c9082140c2c0c8038203500c5500c080000b080c0c1459101c1000106101c06840c080c01c0d1186000c0382000500102132441030900100800850303988401000400e20b11f0143d104a9503240c0320b01080c2d022150103043c440090700d680c2d4588a180504040d4a040780e625056a5404051801031001c02e60110480d95183c0d030302c2c000400c0e03030035451000c14058861580040c7c4500d11b0054200104107140c4c00070840079030441d050b40350031182c3c40d2107541c07146000e01c0000e012840c3c2d180d00f007083c00191f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 204816258 1250 204815008 204815053
    0x901112a1503090c0108090619050c070f12090501090b0a0c05030c0a0f03081f060e0114210603070b0a0c030c060e060603070807080325020d0312050601080702 70
    0x1d0620100c909203503240d0761068100362203c00941c0c0081c0e6545246582c4501803507805241c0100501c054140b01c0c10940c0c8510014503028040740c0c8510024960280d21000c846c03040d5807148502040000a0505640c80407005441c6400550402c4001030781c0d40c0b24014102c1520130400e1001d140180c81181500c1c7d41d491010125401e010034402461000414400348142c903001c2c000d0501c0041003442d004206103402041da50901421007000002600c6d410545001c5d07401a0505040e80706500c0016245a41d00100880b01340100003101d0025030307400181406034000f540503140e080d403111000c154980c40c183c010784071801c41c140981c0031200d10405007144c2042c081d09149540c20099200e0800f41c62400c8000e490903808802400345500f4200605001410880b000d000203905100416440384550a4415107400d010303004600400000e03c0382c1c00070241d004007085070b0322000385800b801410030001c01c00c000910b0000090f0983d4042c4409a00c143c910f5070140c0700d94210070f6001c0d0080400c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 204817508 1250 204816258 204816343
    0x1090c02300c010501030501060e0405060a090804090614090603030913150e0f0402010f05030106021f020d0509070906230904050f0105091006210b0c1201030602090111 74
    0x100e4140c841c021400100c002c00c400480d070400852250b0660401c01e0940b0f00a0b0f0240801c20000c134100000300d00003241c0d0f0b5401103035038000498108224240a01e160003983c00076244185421400550f001038080341810400e002c2d103600c82243c2c2c5000070140c6a02030f051803190003a4448000e2a8030110a521000c0c074a150f00074000c3d1400d4907180e10008018084408800314824032042c0070070340d03070028118480c08030300d45001403440d0305011000303440350b00300380b03245100013080b10340d4882400c400d4041c3ea908040008080000b80f0f0100c0b4096640c168071711641c4d0b00f551401e0310200c2c154800b0201e141540d00201002d024a208140902846100040c0240e80a025040541d4101b000038042c0d82c1c09101414004c00c0111001030b4034008a4102c2e9100c050281501c00c444400d0950f008418460540c200900b0b40a40d0780b0100c0340415403103580c112440a292100003c400c00c015a070140c090240288c1e47e1011004110a0856945010580d150055180c0407035441964641c80511203000e0f1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 204818758 1250 204817508 204817573
    0x637051c0617010c1b2102070305120a02060f04021c050c1305180f03090f01210b18010e0c03090f0106120b070e0102120f0702130e061e190902030d030c030501090c02 73
    0x1d0392030b203440b0b00300070b480310301c10180bd070340000c940b82540d0741044501d810080140e80140141010740c00141d6003c1018480b215129250010100b440014040403069884c041c00c0e041180c5029a1402c2c000c1c40115015092031095207a014804c11000680c04da090100703d005521741100502040107105501100e181009414075051508041300d0362803ca80030a601c0c1c0c0441c11290301e070100b158800384c001c0384005030ba009800400c1300c250381d0503c1a800a000c040460340c3d0341c0b0f414444070300f44200c10481000360340c20f104001500000b1412203e050300e018460842c62600c8901c01121281d280c40c5d20342e80168044100b4918000004c001403c41802d1540203501e05209035000c01c9103040c05101c00880141e5401c08070342c1440c8144001a44004c42203020740641c0542146c030b100c0d4000282401010a140100085402c020340d4000040c4d50740041c119041d800c85404010b02810f400030340300d8006070414000007440c4019005200107141640c000e4010020400e00d40000c24503141500c0c035001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 204820008 1250 204818758 204818773
    0x301060c1103030703030b0f010216030b04080f1b010b04090f170c0d08090705091605091504030501020a200a0209150637051c0617010c1b2102 63
    0x42d5000c100804169100c0c2d00c0116075070700039200b007046030f8020310090b82c150340101c4400a99200c482e0190415654801540302c180d0300d8078184212140141a1914544040000c08031001402e80ca426400c000304d20009111030550f21080c4815200b20940c024043c000f140041e2000901d4041041c1400c06ca03041e85d01c0c14003605038030891524101e44250000320719003505201c420fa0742031081e070003e000c0940700a00e00741070a010f001c0c130200c504801d03d4100000454070982d95644c0d030410006c4039802151a1b034450740caa0515074000d44c8454140c001148068a81000c400c5400f0300348141d90b6400005801100100d800740900c0c2c0300c0052010804d000d22091600350b5507034580c081c3c20108804040002080d030440c5010508100c40c20762142c08030755040d00110000e03400400c40d03100d40c181003c00019902d2000e550b00242209030070038440011105a603101e002c178154008010707182c0503500c000a445114444c01d0703400105000203405110b400c0e506903503140461440c0e130050145807040341c456 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 204821258 1250 204820008 204820043
    0x203010b0a090b090f07020c06071103010609021c0e0d051606050c04031211060c090102010b040504260f09010f0903051002030403080106030c0f14041809030318080301060c 76
    0x280d5920340068207030960f02c20344143d40d400c0030046150301c400c150411541c1814004006941d40301c54079030052140100103030311010405802c1d081501c1a5010700240800340d240c1007000e01a4000091240b41c442541962605691190103034110201d011800f03000303059185242254640e21040081e2940f150a0b5078003000100e80d8491a442902a200041d44440c1549440828000710b10100010803402e420500108400450b10315041296168915502d100340700041c1d014150b411071031907006141c58200b00c140103080060301c60f248440e9400007520040304c105550940a1207040141e070740b0080c40941c070294001c411080030040b09041c9200c000b0396a0b5500c9180c00380f40f8100014061300032091108054020080c1805440d0b241020301c4070706108000105003003c0d680303841040055034140200c0e030a0075082210302600303900040e01100c94000040201400003540100c00081c900844041d0f91280039060400c0d09502158440ca164a409812140c00cbc96040007501d12150b6031010609 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 204822508 1250 204821258 204821269
    0x10906050f07050f06150108010614090a090f0c020c0a030b01030209130c0303020c0907170610090801022101150801030809010504051c0501110a09170f031b12090a0506070203010b 79
    0x701840713180d00400700c6191100d00d48014a02c100170003410302c60301900520078660000120b4280d1900f003552940c96591480018402803025071010703c4880c6000d4030340107240070541020003109460740032150200e03801000c3c01035000d03940c030001c1d041c2540b020044c401480c20700280307508141d42c0b0420740a10800c0d511000340c036074078542c000c40159001900e8500c1034100174016036408030b21400d080040003d000308000042200420303691259134450740806003140601c07800d03409440e428000f1521400030312021841050090700c000403c480050000034072007209992484041100d581c0d06c4071a0746540e0b80c04426070400c000c4103050020034400411103484001031101480100c094189401d652402c1081c00c680b5400c1c895403120700d08014400c6440c3d040107a207001c480b00980300000440c021200c590404200e12a004c4c954000010b4080c50145030403010008610b5810a950380182c800c40d03580d003d0320803404580d0b001104030000b044a4580b11001e001d035a80050004203020010100007034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 204823758 1250 204822508 204822523
    0x1e021f02121906080106030b010308210106110f01060b160602250209070201051b18030709090b0c0a0f080702010b0a0e071d130902030f030a0503180309010906050f0705 74
    0x502480b20314510320024203081c0100e400030040f02008000c000d095840d0903aa84405001c081c1c030911000032441d9150b07401000701c0004100b1030010900e1942c6881c0002c0001d801034100e6029131190790510000e504040c81844115984402010b1400c03151000300703800011154401c1d40d05603401c2c0400c07110381001d8a0030407004200c0725058540501c05e441000f142c1d032000b404200031603160070100304280f0310820744042c580c1725020b0800d44500000d0810580d04900000d0541c050092400005d48045203400040030b9912401400c200c0f90390f030012080540c0501000003001580c0d0508807016940a0f407111504000c40b40f00108080b010136001ca90a6100c036404807101103d01c03000c00c050554040325801040500300780911865001e400064600c42500311411030b1503950780c8002046690400c5851081408001501e44840000c0b40240098000f180e0328444501c0c00d0001511490b0080110b0b00078560585032a205182000e07012545038100c50b0859081c84010804200861030404c4a003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 204825008 1250 204823758 204823771
    0xd0305190f0306060f0c080309010b0307080604050c01020a030210051005030118020a0506070b161e0e0102070e06090f150618130b030307060905030702100309031e021f0212 76
    0x1e620664001c40060840320b40790700220400c03da8802195205910804480f40581c0140180d5280d8460406550042c042c1078103841d414130415030001503010012407400e12a41c0500191501c2c58801d50040e40c4a0951110083c0140c20290301c412641c3e1442c2e000d190804420013034052015143c0d0042400c46000700340d014415000e1403010811407503d9820301000c3c0006584060034608640e4805030100f6015103a4010ba035104036000001da48111090700e0545d001e0450681040d0701c0340005170644c0d0b01c15034000d0060040f4040803c007032100605081c02020082c0c07124603281d84589180c1c41c8001e000d480903003210714041c800710300c42d5554809400c14070116155030464080d40b41c100403544a5581905031454140001c20074942c0d004001d460f842ca40011010507602030601c3e0003400c1d4855484000d50204c048040c000d641c0303a140d4482c142ca01d11031340700c50f50b050340417420b95032a01d0150380038800181e00030507010f01281e500e24480004264003040c0541400003000c440ba100c04d1003101c05 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 204826258 1250 204825008 204825017
    0x141006050a0e120c090a060506180409080a050c010b18060603060d02030f0304060e1c140c1e03060a090209011707090606080f130c060507110a090605030c040e0a020d030519 76
    0x41300780707803100581c0d03084036480c1c0b0308000d201c2c03900740801c01900810303889900041c1240000c01803511543c06c104426644103422503980d0300d00c100081c0185c1c20100b640807566181580307a14030750810701c0e001c503600216a00d801640340d035130000308040c0b907000400440c0c000110f0669000144c80c10848001c01b1017200f0091904e0b85d0900b00003c2c40040502041840340d008617007900c3c036510302c01d403901100c3d513003100d8082107150030503141d580340c950b624008940003241401d140c03512040c00b803406005401c00320b0640340a0748508072a881510007022000e54010041d20041007401041d4070201521201d071010358000603500d00d040400c80c1c0c82c5078400c00c04210040108901141c200720b405500c1254591411025441616a441050740c035000780014010000b48000a01002592a10082500a01000c400e41d26030300060054005031194600912460110800c985080c0c013605115281440040ad98250035800f00541442c90010540600c081000303d02110004c1c507901000080403a01d8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 204827508 1250 204826258 204826273
    0x1e050a0b030604110d0309150f091e0519080105091506010825031b0e04200d05070e190806010e01150e030102090406080a0204141006050a0e12 63
    0x5540251031003000510722035000181000700180000d0354200102c00251039100034050280303000d640381d600c0f07500702c5030650007020f4a41d031325039600c80d00c21130450480c6e5403031942e0241ea8121050040e603100c924280c010515100900c5a403d01d22406040d031080010040318142c0d440e80130608603081031742c9400703050b00b010031070f485a4901c0e00c00f082c0c0c10200c2860b1521b210701e011300400c401c0c41d44405601d946c5140555507080524800c0d000b2030090b0001c411048201d0b00000320280903c0003102c00e041c041e5051441d049801c0e40c5d0304608601c0b8200d920086440c0c40d104a10442c01084000c00c200706100095854026640390441c0524807200c590070009841760400e0422450704a05a0051040c08024030042c002080d090418045204440c10031140451781765000901a01a400e003290f0018a805c2001500304800244001c085000b641c0c00c101120b894550341401030001c032110500f11400800402013144150010300c0c001d0054503010024001607000950f080c0c0d01d0003010b4106034490070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 204828758 1250 204827508 204827521
    0x70c08010b120d031a091602060907120803040c030f0506190c1b140f01060611030702090106080c0c15040204150302030607180806090706090801090203030d09061e05 73
    0x41030080100c421a42d4025540c4904600c80e40e9591034100e4000301500c2c0d0000f21314540c004020940880703001044d181980c44d0501e0f018007003001d09520a40103215032400328850f05404079410301601d51410f0420590a0b0795110021903078405001118803404d13001740000800c0705d00465941043c8a98080c010501340080c0c1808200c01d0401d000059070b180060341c00c02240c000d8412454071141c101404004511410407a00d0882c0c1c0b441ca01016000b0403201416104042d84100207039100ba842d00c070358070006524403941d01c0c01100343c025005900720f07006000c4079000740841030b4040d41d80c081d140e1911034011100740c100401a85a84130164000050204514280c02001d5104030b212075408419459900083c0d1759400142c440ca0074000e1090030034001940014024010f845550100c603040e0400340411990782003039125440c001841001301180011060003808149500200250304022204604078002d250403802290920350f100e0038104000c200c6239103800c581c0d190355000200c0d45000f6 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 204830008 1250 204828758 204828761
    0x9020a020a0b1501080402120a050f03030615130e0c0c01020d1e02070507060f02190f050f0307080409110d05070f030501050d02010909020906070f0b160e09070309020102070b070c0801 81
    0x640f4500d8042140380c2204044e90340a80388946c01a011164600e04452154149082c03ea15810140c0103004410000300144800001035000f07100640d1340e515003101c00b10440300c4500410800040301046c0700c0c000c0011880c0b80c06c030315030030442c201042403170f0909030800343d401ca0788450601451142c0b11046c8941d5070021000c09040c44556034020362a1101caa540d00340c03501414064007040c00300381d1f28089040381c1300b000040c0810210540d814640c2c2418140345040303444403001102d440c410340d941000ba050001c4242c039030700d0368009081070401e410302c42e0440c040e1031005c0d00003503810400d1110008100e02c0303000c1d0f01c1c060f0f8000d4030323861040811000c008050b0352050300058041c01c85401e0b00e40050745d01032404012542003101c01a20359043d900001c0640c403900300c0c0030b408a4130b0030025109001c007407941e90340595070700c0d80380300303001e04444005a500c003190030605c0e948500d00070009103255001e50000c0d04041d02c14819554003175154801c1d081c084e007000909507010074038a401808030704000d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 204831258 1250 204830008 204830011
    0x12030c0507030e120c12010e010f020c030a08130602030403030b010f050f0703030203040f020901061214070c0b0709080616090504150605070c030b0c0d050f06012709020a020a0b 78
    0x545481458618079803400703031440b10414880c40c0962240220b0003400401801001d9034400e00a001c008214040030015001e41083e0350114425443d000100c056045a4421201c60306c0210000c1e50510a141c04181c40c10340d801842c00c01c140f4101c0c4043c000040c2c061000f1845644640c0b0001000c800706000104004131080a24040c40010024110064901002c0d501d8080d0705d032501507540e940b07602e41507030329080d20900290000e80d044000b04000d80c00c00b500305408122400c00b04106210645024940c00d400d45445011800b420000404108000170080c1d121aa508102d0b00290780c51590340e140a83c111041c2c5018031714090242881c6911062001c0100740844060065400c9a021401d14001622604081c800009020340402a081e40020025604000380741d0091400308442881a8030030b60014000038a8840044d011900c81040170b400340006940d8005071040e09005510600d07101e010240140b80d80880025240703005000030300d50750b2019030160003c03101d0b40c40e1a11703100c00d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 204832508 1250 204831258 204831281
    0xe0c1b07030201050f09060408010c031e050c16060e0715170c03060906010c06110714010507020c04050a060305071806080708030f0d090204050f010810182a031203 72
    0x4040d0041002d030fa03000068400d05120010f00641c0c6180a00c001642c81c0700c0da9018508550901d42805507041d007640c04480c0c1d0040c0b10041d0f81491a408000e0710480300300300e03002c1001000030700048440c210400c109901032840b5010000c3c0c00041d41214901c0c0c4a1158424180310f4942030f21100000d900c1990381034210380b20040701143d4102405400d04a00008005034000c3c1800000202180c0c843e40700c01c03010507000704003001500055040621264441c0809882c1e110b01c0c0e0000500c440d5051080d941700d00d10310b50103021b9100000c6c0401000c1e15007c7e060300030140d00c43d500400030030360900c4484001c1092151078807081104049140903179140c4da2145a031604441410020311101004584141c2180d000d5656159a99918100201b542190180d00303d85070004224240341c0c0c800c40c1ca0305032030700f0710304035592000c1c054034141c180c4440704200d82d020303400c5c11a488009100050f00310400b0b507800000c83c0e003404440f4000d02c90302070307660300c203407003040f000020031503407940610400c3c01070803 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 204833758 1250 204832508 204832513
    0x90f06050406051905100e0d0803010f050a03050604060902210322150c06110d020c0f0111040603050c04051c0312050f0c031504020c100605032d070e0c1b 68
    0x64044c0c00d030b0710050006108081c010b0001c181d0581405121300000800c0300300080007025401d00030309103101c8030380003402100444906010040b443d8a0f101107000100d035170000080480741d0f01c982d40c03070010301003071001240c1180741e040311041c8901d002c4180804103e106070045441d2032032010100080000c61001112034a014802801009070381e110500c080603040c10904811140c0e4070380500140f0302e1900c00d041d4880c010427241c168103400d0300202a644128006c50302151055007002d42280c2103000c6010036500100400c0041e6802900403607804900015411b090544c1c0300d010400300c02050100216076982600801e0415411165107492445021401c12142c030300408040350080c5d001d0410a0a40800300002c0c54401c50103165080580010b0010354440e00e916180399a078907403401505107490705006011031a8200000d600a208107052070700f0304400f002030454480310401501142003030240d4000481c0042c0c218206501504102007815555100d42c20300c0f818940b61010300000c943c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 204835008 1250 204833758 204833779
    0xc0a200309131a1002031201090c08060102070f050f01020a080a0203041e060f0806130903020304060f0e06070618050a110f0402091005030a140f090d050705150a06090f0605040605 79
    0x88900d08480f0307540b82e0945100c02d05030782000090b4a1402030009501207030705602d001088a03001c0e600036062440160310741880644802c801641c54440038010a0109020010100309070b140043d00083d200b10103005032140401d51f41c4503034001d5801801c519001d0381c40042d0401880c0c0c8100f01d00500b5581054000008600380080202030310854400c480421250402064080e0740f004d04550251010101c1040f014180d40b80194407070b0858855980452110032030802018000c100000313103210000d00c068501402a0388480061a11790001c0a4544081c50000e0008104006184c1100e0040c105c440c000b052110802620048010b0b980e406640140b000b0302d4a03840d9003201d207030460481d08220b074591f601e0070a028002d01441003841c084011800038006030084010010740580d0303e580a88844c0c1242c1d9000740e1360762003010390050650340607070644840d018280c00c510350807c0c64580c01180c01c65860407807000380e0340200144000380d0354039481040380e0300e031502c9031000900082d140a41c90 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 204836258 1250 204835008 204835031
    0x90804061b0305070b06060d0905070819050717010e030c0102030103020a0b0a020c21030d050f010f0317071b1502010605032e0204091404060c05120c0a20030913 71
    0x5400b500000170b00c1d0315180b901250a99499105039403800c3d2080800300240b416a00300070f030b40c92240340300b802064020309030744050383d400700f4a1180e1001e03001002813644a10744058a45a4010703911007840c195600d5401020f00d910900040c024021820300258482d411401000011000e60303000c00b0b0040001c2091301c0341641c002c6999031451800700d606020074075405141c413440b025020080ca4480c00001444840100194056401040a4012803c8036a00c0715a2103800160f076000250980e645049800c0c0151410b42c01006400d12444080f448824262801c0340480d132513402c05104c1c0006113524000085e424484c03000106002c9009182181c02520002c502d40341c1540d11010000000300f00c01e4010419404860041088270030401028040301a10383d02035005440880702036007041505410300388a181540c0440346440d183c81e041d0745840c110351507164030103003448060000b02c0360100c10322460354814060440d101406940c2e01d28860701002064111000d10440251504100b00320 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 204837508 1250 204836258 204836267
    0x70206031315020723070801020406030f060510090510020c04110703020607020c090106030209040b09010603060f0f0b18010c0507090f0e0109111504030c1d0901140604050c0706090804061b03 84
    0x868820007041c0304c1a1780c21044200341001c0d41d6400600e16980001400900719600d54000c480121819604110081d180c0d01003003c8403c040c6079032000502c221401703104e03070301c1c00c4003903950610001e004031020b407519107000c6000d9601da0b601c0c27810100800324018051640500015038014240e1000d00119815a0300140c0301c41c0c018018203040581c041041e40036510307161b00c000301039500101000d405c1e61b034488008028180f68000c1104148112000080003e03501030740500348d40f40303030300b032541025851003220303480416061215040243d04452500031a1061040c1800392520f0340c004500841c07100904010b40c2e9a1401281c02c9a140c8070b00b41c0c01045008800c3d07090a90211252103400d95500d00040540c0641e030000303009541c1c1d1200c0040c035007090614040101c60b910203940b010795101c44009088600076000c4200303481052000440381e1400764031681c0e00070941428a03003040c0071615804122181d880c41280c45500015042c0f102c00d1300104e802c2105000001e40c05182030042e0740040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 204838758 1250 204837508 204837533
    0x30609031e09180f0e060106020c24090a030807110f0a0609030f03020c10110c0103020313060e031b0a0618020303040e0601051b16170706140702060313150207 70
    0x44000a22880d441c0c0300c2c0c441c1d13070002c0c6228500110240440030f100f643c2241c40c0c042c01e01c1240c006d8414120002c03010708115000400c0800c17211008a100e1500e220328a915900c1048001e40c08800050040006440c0c44082e1a0b90740c010440c0001b1403060405202c460104150003078415800e0030300030018a82c0c1b0103602400e4950100740580070408900d4142c0ca0305004820580d44044c100c5420014181d12410080003561080c0807903121a903a0360042d800c0344400d88a00d05078050110016011802e260400400b403e046411203190455070301545000c2501c0f02826415034000c10b03d54002d200b4203001d0300b01520302c2001c03000c40e01c0100750f0009541748901e02c6001c8400300340200040720703a8011780a0326006100261520f4944804510b05500c814410050590826170401c000c500b240c13024001c0c0c21158000c10042c4040c078140102622a000d03142240188a9810040440141c8410002e140104040c04410541900324a06041e04c41e06443c00c0d200303914414040440401c9000002c1e8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 204840008 1250 204838758 204838769
    0x6050c0322051606021f020f03061002071a0c060a0b0904031b0206030c121003021e06040f1d071106040f0f14030d2009042301030609031e09 62
    0x102140791245001401c200c0d4880a902c19058402c6000490b80d070045841030381a1401c8035130b191074041408100c0d040340a01c241d0700d9412042800001c001d420480329081e5902050b004561003035507540344007588242c3d040c41c200b80341400410051451101005000c0d0004220b00080c400f610810000c43e006406c0103001600b003000040402c3c0e005042c20030708110300c0b0f0700030b8030300c41d901c2c139040c0e0102c0165440410020141401800061001d5502c5080403090b079500408990380e4a4400100d001510011411f0035800070042000141031581005480000c1160f98200100310180000309400040f00403c10001e004441620410381b140c0801c420340e02607840000c10214142c9410980e41100142c007000302a00e00d1070303c600d00c441c44000040e040e040c19140b401c1c81100308011000c2000400c1070021281d22205014511552520740c21104a071810140310501c0c610100c10101e000700030a074415181250b41e20014006c0c59840180d02da4004404449000b00c51784083d0001d00b02c2c2e2040c8a003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 204841258 1250 204840008 204840061
    0x40305090a0f080606010828020310050301090f03080912040e0a0b041505120f06180102090d0f030305010e15090406020d02040905010807300206040302090103050a06050c03 76
    0x801165407164507610203041400b8a40d08183d0f00c551003079580d08425910700307010a02200c0014034072078050682400c007580030b0900c0e0076044074030703104a8003070742004c4c007603107c0d01c1140c410120b4243c40921403501c040c2e0149120303071050f03600ca003000751050402903c8840d50f508030b240884640d96114003110200c8000e940c81300c140360750341560386004100e5102e68581c86400c00709a07010410303a03102000d06a9800703c4070a81d80000218903551340b01110900019071703420410010741032800e0708c40040303185070100001600e014510000240c490308450740c01c5982c5154001b10710141541841168090001c1c04142c2105050800040e0480e0340c0400780c0b103214800e424001010041c0540540e600321381880c205548940d101c1c0c1c041006070009000e0400c1c584a1107500045d0721541c064811039003246200840081e04240b0301c002d1100c400640c0c2641c00c03c01c01c0000200585810940074002c500900c0a807010440a2a240782a034101820f240b0300d210b02803081c0a641ca00e0400070004043c8200c04 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 204842508 1250 204841258 204841267
    0x5030c0a0e09010e06031c0210020d0605090408450307031e02040b090c162402040e070c03090603090c030b0a020301080d0804120f200d0909050f040305 67
    0xd045424226500307a49401640040c000102c5061410610f4019032085050700c4040d6007504e40407580b141c00e03424400040e442018000d40d2400f96138003c0c00425803244000c5003098440c00400d46505e0155000c682c01072001524140d01c0105e0040401080454020200c6070001c0c40c4440e41030703c802c1d1124200256440340c08d44541d80c0d00b008407000459105607000f51000781000c140f031750340000d07035801d9029a09000350f50085240003150940f080300303c510b0f51401c1150b41124103403010303c115411112491110f00328400c011089201b143c11410f0a84007503643d0b420805800c82076640503100f08180300f1b000442d0350001c1d412a180c0c40c02e444041c0b40005a440c000d052042c02d120050b80043d0580d0210001c0c07001c0d03c0100d13002903050b40c44540448044c424540303001c5400e81c8048502a0100c0d081801244a03644120600c048101040c5040440345c1c0307000c04103507064010b150201d00540d01640128200725002410380c40244600744c02040380d89817092081020040041004080202c0080d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 204843758 1250 204842508 204842527
    0x11103090904030e040c030203040f080c030f0d050a1a030607030f090c030602250c050607020d0204021b061b0417030403150f050a0903020a0b091e03070b01080601050105030c 77
    0x195250108000c0c08070109041604002d004144440c0303986000c0d0381400c5c0d808035040e004c0d00840c0d00640e805040001c03012030380d07240e000440d0411540300744980002c04c5400e0700304001c44060300c09150404000103c504054200304c08643c008100164002c0402c0500c1c40c1c03aa5010468561181e4641004600d8942c034805420080c00c003580001c0242411a0b400300c103110042c0d010b0013603840c2c1a000301011403040152850389540304103000740f1031a0781c1032081c8101d007060b030044c3c0030040c0b0240410400da4426800034080e0303044581e4905200384242c49400c40710038104400c1d5004103202ea28032350101d1402c0c440640720300c25409240d419100050752030034182810004c5030000c58106440b590f500c0090b40c500742c06402d80d440c504100500708004250b038207416100d0356401543c107800400035541c540c0d45103d074500c3c000300114428001c044400d1165400310343c1c0000c624130468055641c03900b903850561040001a0054050340c0d20100042c031440e41c10000b1640c200c100b590080d611007803c034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 204845008 1250 204843758 204843763
    0x6041a100e040b1c0b07020c0d0807030306030c0306050a05061e15070204091505090102090d030c0c050a0815090f06010b0c030f1306020c04150612180b19060308090111 74
    0x9000503030042040751103070045026145035100138074843c4640992544426404036501c45103c10403a511940d44003150000600e0b484c0240f900314401e0801048560ba251900940c28049500956034951940e0400c0300740039040c880d040d480401164002c00c032281c1c1006048c00c0c00010412280540c4104241c2c000c0301c1c44181c1a144002c0d8014014401e01104c0e2400320720701c640c000050010755013883e010911740d6006009540d612900034096202ca11320b9138a080710031800000b002c0e22100c000c0c200c041141c0d1140a4100080c2400800415400c01c00a945060a100c020003455042d00298018000c009002c100941104d0747e0192181d02c444403108560300307611034098510400980000c20300d60121641001b681103500039000d482c5403000e0f050522003540c6816a5040720202d680405028142c0144030101d04031002c074100254040d890b0044070300070904c500701503850b411000c080001603021660703003040031803200e10140503240c91903031a0100c0d409881c0c0b28906011012400a171550400c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 204846258 1250 204845008 204845021
    0xb0312210c03010b0c100e03070209010b0304051c030213060914040519020714010603030207050f0d0506070302030a09020301090602091527120d1206080f060a090203011e020306041a100e04 83
    0x8400b41085200c441c245403648d01e23400204200e02400c0910000102000d5210649104541000c0a80308550b64100c082502c032800078060000e1660074446001649404c601c0d0303501070100c54075140802828036900c400604c40e4840d1040c41241407504001840116800500b00c4440200015071039504500d07000352040320300550402190b180c100b000080c540d0010f06c41044903c02d07100c01480140590038080008540e99002e00036a10580c0868111807003a0b008540c4107069520005d4000007680c0081c1c295041044261503060300401c2d80c0d202841d00300040c084868a201100c0e29190100e07a0740059100b9030103101c007018208018944040d00c2d40360f0343d40000000d00060301c09103a82c10390003600d0f044042200100710303480e020f00894900400240e2030320284003040101003544d0391100340b0016141e902c3c1c04036059500d8440c2183c07003c00e1100c11050320040365401588030301e001000e000844009483e07110f00700c23000f0700c40c205460f101c00c0050a1b03659114980480d84600500110780609038 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 204847508 1250 204846258 204846283
    0x607111002070302061204121106040f230303010521060705090a0504050a020d0507031802060c030d05010e150a03020105070b28090c0e0601020309010807030b0312210c03010b0c 78
    0x10003c6c1d012684001d445005118511070b4482441c4405c3c0a0011500410a944010400e0f4400404070700070522140700000d84611039480392020b002c1a502d8411100141000105035900200062205282c000c00039004800e22440480f924103591200d50350ba440041d0055003403110001d61214291542c03503102001e084003602c1440390b41014544100294000d0222481c003030302c2c00f0089800c00d2b11a00819001001800000100d4800e6400b00109a030001040759581d00c41009555844a0140666030081c1983d074240002403801e0f5074510b02c11a88401500d2040308500c1041c00141e03040360a49090355045941c1030fa6942c3e520b0f501c01982104007500d40080ca60f18601941d600710b5640001d10094400d90840800984d0303031898011089059070030034056002400070007510351055030a107902000c10b1801040d6110170402080c1001e2038441d0f48103040200241408401e03d035150110000d42e40e405880d4810300d084030030400240010b0081d162048030001d050030004000300400c02e004603 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 204848758 1250 204847508 204847519
    0x318051507230d1d0601090b040b0a03111203040f060804060228170606040e0606040f18050c03060a030204110906120402090c0c0d0f140a0206010f050607111002070302 74
    0x44400b0365018680d006003102002c00b5003025820460082000580c01100124400805241c6d00f0450040e025220a5030000c0c5c11941d504200b41855841d08500d00055000312000030f20101e5181c00d0210080404103209466841003004020703103a84041c280049400d00d05c0d0070320680d1154178000e000381c17007035501584032040b00011034018030040c00703042c02c002202a151100d00c2c50250300c40c0c000f040c404450340c686c820020700007041003500c6500000da00100081c801c03460a85c4904059903000ca05400408141c800c030f07100280d481c10a8804c00382c110318041c501a00b507152500004154158500009004a0702c4900349602e1464050036100c00c030200803d41c41c3c440030070214131882220119001c1e44145d41250114040101800440d4520003100c00680084052081c0595124980d6110710003005050808410072001c2e680c00b9010040b802e9014015035454001c0100c0c92241c00d4011070310494080250300005201d401c500c0011036001d50301e4004d554020301c0141d040860079400650001c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 204850008 1250 204848758 204848807
    0x2010e0d08070b07030608010b061606181410060503061f0807120c0b0301030b1f05060309030d0b03070602101a0406120312020f030408161b03030318051507 69
    0x1224840c0421300c141003070364080010641d070f02c40c50f81c01c0e80c1c1500c02840d0058010441540c0c8202c01c1c181c80082a4020b20010031080c01d00807002010305a0a04290b40c10040d80d545680f4100f030610400921108540040c01000d0410340001d480f0340018181414005600ca800d40c0c0c050411241d43c0700074020001512495a43c980340320800710a0094111840c1c010300d0130214180740f810080da4181c030341010384441242c0d1070402600c0c40d820380f2240b480004101d484002001d54915005512402c140c002031a00c1e0f01041c071b10303d0b0955122011082c0b11b03400141c2e0501007164001600900c02d02c1c1030700040b131220314449035210035210050f06103400c2410800302203108103c004100f0201c40c805d50307a07502e0050716030740d202d02280114003261881d0142000441e0224003460003401425840041040a0b1445a0b40c3c4100900022032256005100450708005058140c07081c01104d4030000d00030665445650303142611500d86c04009104c525000c00070400d12032050300004a40d220030507070f68444 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 204851258 1250 204850008 204850013
    0x102010f020a1116060905010507050c030102070c21110114090907020c03101407031112012d030b1f0b03041b05010e0d03082e090605061602010e0d0807 67
    0x4a1242c0040c0f02052061080c1d00f00120761800c0d0322030840d44940d813050f400504002c01110981e009001c2034642e0303c10f847d00e1551580e800e2006046151185031280a0b06140180080301c1c001250385403407045480d0003149000c6990b860102c1c088078009d207800092401000d0a00e1074602451101039003102c8501c5c00c00070f0b4242c000610210b401c0c1d08404540300f003544021b51409a441241141c000000c01c8400320784154080c4c1c0051240c492003400c05400c0c14403240c401e160300d060903408001c0c94405404021540c5031072000004269180100b111140b03405c0d52240324a100e80508661300d042901d041000e030f01d40c0c0400300403003e0200549016070328281420b1001311082501c840828002c58160700107000d60003070400001c0200e028103541941d14240e01e00361204007000f00305074184c1c040c0261401c5415030b4a01d400b203110440c032040c50f01c2d05080c88501000c81d441754000b5401603008101092101d000b140845444c1582482c0410f038180303009000c41c117552681000140003e2010412408 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 204852508 1250 204851258 204851267
    0x150402040f090c1e2a0803150109090b091306020c06090f07090e06070804060b060403060f050109140a020706060b030c07020909120d1a1005071101170c03060102010f020a 75
    0x29480c0c05030707105240000340c25020000318000c1024a0045002460007403d645d000f00807919030b111000300700079010005500c41078038030ba00881da01020480a12071410040d80c0100c5002c0c058800c0d9032041081c1003507030000c036400b54406403440c6c0545103420210b60400c0504e40407500c03a600480306071101420890314071a6500e200b01c281e0396a5014031000801c200500740b0480c120045040002d16042d00c1c6c1000c103590b1100050402d4401685400f200c1015845680c000c0006600c649400202041d6038407100040328030681010701e4440c2040d5401c4c040c2c0081c210340c0c58011420300c00c01030b558191450030100515160380b140414007800700030080c0096404005e0a9880c0c026240146a9910601102c5c1c40b6202804102e42d109c1d020300c9900303407a4245034054038000402c41c10060341003210070005020441c520b0300c940300003940000e06400b000f032140c1001461305c6080c00d0100a140a0000080d140000200760b00c031a040c021002540c60380c801d4216400e0100100c10844d912102820003c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 204853758 1250 204852508 204852521
    0x12040e04051e1506040b09180f1213080105060901031b08010504080d201903140901020418050910020f07140c030f0f031902030733020a0206150402040f09 68
    0x210b441c0c01500018500c1c10980980424850020304000c0e00d41e0b40d0108107801510014030f005d01521444850030041402040b8a40c462400060b00c01c0d181d6001345851840302f01d45420820b400c0e41408107016440e142c5000060540340d0040411a002049104003090f601c0c1547c880041c07982080d0038081403006401c01010061001d401c00e1203140c0814284940038100000b8102d6140c03030800000364610405c00d0f0b040f684403040e141c082184104072200059800c401e40314044a40d600240810075082201c0302c0d01d180165001c0184401c0c81c0c004507d0780c0314003c4c00d081c1030050350006030f001e8510325072408a98800d0350006101e40203800b0042c20f60741d5070b0003106809000b4841d4103508030381080700040b01541200c641c03008601e42200704050131140130700c030100746c8154442400340b4000101c495070b808041b6a40c40340c080541c0983e0060610b0a80b10725603800a640d40b040200e90507156011500583c452151815803403501e180b0008200244151351001d42c50178190000407682105d65007001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 204855008 1250 204853758 204853783
    0x70e06060d15031101080402030c060d0f06080d02010e0d2705060703030c0e06070f06020703020a1401020a0e01110a03180b0a031a0103060e180316120206010812040e04051e 76
    0x1444c0041390054491000c2914042d51551001c290840b10b454040024055824855408902c14285c03010b03c0c01039803240e030031880554126104036200140e09100b044510041c60000301003034109038501030042001c89004094254805514020891004001d0401460b0203070003146d440d086410010010030a0071022000a92020726550180c8bc183c01510001500464010701c0e20090f980c4c0d2100962000e90b00f00c095004441900703000c035161445e140841404440096958489220001c02da9803400070f540d410300510028507206040002000880c082d490304100104154001050000805039880b058150700b00003481b4043c5c07039064000405030300c103a180310350030580c0441c01502030b035805001c1c50251804150000d01216003903003034100c0da0b40c000c405032494204080d64608066408040c155030320621041442e04c0b81d941082190f005008500240070b141940c20b0005030144242d219901d5500c00e581e01040c1840414040407001c00c1c0b9240715289901e103542440d54a5002d180000d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 204856115 1107 204855008 204855023
    0x18030203070f0311010906050715111603030b04060b0a051809160807020f030318160e100909020d0204020a051c06090e0f070e06060d1503 61
    0x601c80504080d002d00c903000342c00c604020016038074130000f07141080180c04080241c240d020086c3c6c2c0102d6401560b605090340340c14980009451020080c00090b0400181541c00b11800315010b512507201e500d05210f07441d2040c0800c4216007680c0702d8009984010447d00340c0440c031960080005a440a038480131009013000402c12101046881e0183c03082101030613440f0380d402c05800c0c1d0380301c46184020909281d2182d00151030b030102800c0c0200c900e81c15681c04402040030f200d9201c0c504445418592440c0d9244401d0000d50002d85000315080070680c00070a60b9049070182d50320407900502155440440307a403c0c0710081d4000c4225404211007404095080952004042d00d05614000040346039418181514201da45403038416100780e2115011669500c00030920408450f0303002601c4469560781804100c40f8840d800850f40080d03d40300400120b130030400c40040c2624004c0b1072 = true := by decide +kernel

theorem cover : BRFrame.Cov 204676258 204856115 := by
  have h0 := BRFrame.cov_init 204676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 204676258 ≤ n) (h2 : n < 204856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
