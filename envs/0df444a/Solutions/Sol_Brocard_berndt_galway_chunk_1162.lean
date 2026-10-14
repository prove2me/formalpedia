-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1162
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:31:51.022127+00:00
-- url     : https://prove2.me/submissions/e0bec3b3-6d0f-4ebc-8dff-bcdb927ed84f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 208812949 ≤ n < 208992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 208814199 1250 208812949 208812953
    0x50c120d0f0207051b09070e100507020414060f0d0309030818060c01020d0b0a030f02010e13180210080702031206030307080406020d030506010f0c03050d060b03010611060a05011404020c0a 83
    0x2c4020056280280020844803811000301804403521a01207805042031006001c02d070b9030020f4408048c5074045440c40c10088203503c0441c2c0f580a0302401a50040c01c111605003991390f08410140500b01c1a143d203500e0305c800500344480d60010180050014a10f81010000b0810060103410001091201c44940c0c2005100040781c54202a80000300c696000660413004940b0303100b6001840c2007510501042032860b20345100c84c281004000e0f041c031041110001d1265605c0760841c440c1403110000b08080d000c146080c1c42000d10901c812805441c1100b0740241450043d1040d40c4607801782da004600d40805445240e481e2200603282c190103120a0140f41c0015014801610181c02c142e80200111030348400e0080a03100040c225034140612010052842540700180c00380c6282c060420079511051030780c44600500c0298002040654040b0011a0999208601e06a2001641c040740d9460302e5407580314085400a2150541404400305003440078141600604011401801074508a491136 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 208815449 1250 208814199 208814201
    0xa08010e0619051005040f1103010909170f03011a0403020303070b0712050609010909080405190302131104060e12070303031e0902060304030c0c1505070b07050c120d0f 74
    0x4284000d42900403008105000c0c04810340745600c1d0308180818040c1d810410305640b0401258050580940d445000300c11001c101a0040b0340d0440340805400c0d5603603540c91505008000c0c4001c2100c06080d5100f210880c9d0304040e056035040403114131481c1c40c50b46010484044500200d501000001d4144000005a6001e20141450034043c07a05411245807ca000030030b510010301001c010030f440e08040c003065480b44152036040d1a90403100040f805942d080c6008079009541c01658041d00c0c58005489040c140350203c42181d1081d00e01030009610b403055081569a0320180c801c140c04140420024a80f00b0f0070116100100034014010701d0180c50169414150140c10075001b182d1141102003850030440c0c01200e4001c00f4007001c00c008441940091503c0c400030700040c04104001400005210f01c07105028001c2621554102c020014203202501c0354000310b605541030440740f00021417031030007075007102c001043e003c0c0900040c3d401108034922a070040104400d410340c5d501d9014280c40e00c9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 208816699 1250 208815449 208815461
    0x13308060a09021215010c030f0f0c08042903070804080a0908060709051e150304061104170c041802211204150306061209061413051c020312060a0801 66
    0x320001222030b41c501012100d414184045c00c542c100038520003039030046640450fa540b0454154904403036000c0c80e07000200e50b46140c1050203042d0348000240094899500c0404c03903030f00100e12201007500c4420030080003641c04211007a001045007a07001500242840c40101600074007030074507100c043e4441e505c541c0340c5003003181d0300004100c5403031042c4640d24002c00d00c0c000c1c0125071815850318844c24408101d21010ba451013030b0f4140c80100201d020007800da080a40c1c9a0000b035402500d441c2d4400100c40d0b900784a420116081c0a040f0010405003411300840380c082452040b1106442a540d091000d80c0318104915a4030218003051000440002d002030460820f54060464845041c5004800d901e10309804c08020305281032010414641c2090050900420b8400c0005070b9405a044c0000540318242e4a01c035140c1800381008a0700c154012082080d501480450300e040c40101c262803140c08605c04002e0160740180103c82e550400840380390b602c884003400c0d00803000d41e40d001007425a04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 208817949 1250 208816699 208816717
    0x6030a06231e01150203040e0a06170a03090e06150306030a0606081005090114061c1208150406030b1302030c03070603240311010305130209010806013308060a0902 72
    0x108481c441209002e82d500c606000d4030280c0083c1030210301c0c501d0040c3d600d100701e04c5617680135100d91000840329119a400700c4001c104800101190300d003500c082da07407122300604003100890742004d40400c88821411025100e80806081c100c03c01d806c2d2901c0125a0f000148560350610800f0141e000050f654042c803801013810701c000300b8400390381c2ca00320025518014a844401d0b891b11000a400000c51001c0d0381d0006401d880d006114001d10700b8095250f0001100540020b994414001c0416800241a4400c446044031518040b01241c00c00c42030f5061031201411f141d00240100e20301003414030000c041c4610040844010303051000c0802c1c1401c01d15031001010980d203840081120341340007620f070000303060000f84c2c03002c0d030742181d0705c005121040c028440d0400d40d860000076000c034042050854410340092a403075866a45030141e6540d20024000c61028000d251840e103040180319a403041800e41c444e194511504c159202101c44140080c411980820404c0001a40454520051105c1c0c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 208819199 1250 208817949 208817971
    0xc230c0106140f03010b0d080a1709060103031d09011e050a1e0609081005100e130507090908040b070c03080703021606050c0d12112701030506030a0623 67
    0x252104001c40300701c0c000f01481c0240d0400e41070305030980c1d5140811480c150722840c0541c8407544290112039100c101c076030307102096403030400b0b0261180000030918101c07442992003459a0300010304040301e0300c5030000643d4010845500600030341808602c0180e03151582104e10301800d540e980051990801c80e0f019022034401022800200444d402c0504003610507800d05100003494842c00c2540e130f0814072005d0030030a0381e410228107400303e102e5595000301843c040210302424480c0d6001401e000c0002c04540a1140e20000640c18546014600300c240d04062120305140c03400103140000c0e0300030700e401c0304c81c07030440e820110008621402900045000e039000386114290400003680c4801d00b40c00500c1030120501075040031034000100d124103440c6524101c04481488620407000d40807090f500071501001141441d8005552440450060302854800c0860b0989500641c202c410035a85250940c1100c1c1800340418447c2d08440070700380c00c0c02d140c1c4807440c040103200c003525407041c3d515100390 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 208820449 1250 208819199 208819229
    0x80a080a0209182a07031b230d0e010c02060c10050103080319060b0708070204090c08030a1404030203151005040515032119090b070302010b01020f010c230c0106 71
    0x421400c6018884148a03980321209200000304850190003a244000c04001c00880d25481c0c0911f40c0400381101640040b180203401200d07140419500c0c5200304550b0030b449401880a4050720403007070ac54200c034042c1c4440542c2000c41d02031004503400284641628800c4490f51441ca505c0d0707100c0c103030007940030310707401512070410345030144191800c20101410142882410f02104044d0800c58841c1940702c005165260507510201d030241c280b4000240048403003200001e207092000c401414200e1890f0b0752520030b2041d0720305003186c502841c00080d41541c08a200f02c860304c0003500595800005810010100695403c0003600b80d80003100c61210904103040b079240c0c1e43c10204455088204003100e503014004942e044c43d6000d0003240e041e1021900440754031507e0501820019002e01001642c0c2d561703078411420042c3c00380014605e00b6005201d500380c43d54614070706126081040c0071030342c1ca501c0c42200c941002e90306800c01000c44110b00400300135004101e80f09100f2a401403d0050202d129 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 208821699 1250 208820449 208820461
    0xc030d1b030504020f01050d0f05010e0a0b0307080307030528030b040501050d17090609031501080f03031003110a080a0b1611061b0c07121b03080a080a020918 70
    0x356036440c400c9001d050030304091100580c0c40c1c1c048011407034030a28029403a10008050240606030500703030306001034034140c0003144034191001800d110b0030840001344218640c0c0020706030307101242d21480d18aa0800d1281c600003900c68401000c8800d2060240d18010440e00d4682e03e1075111000c4101c0407990798200703840f050500e406000d0040004488540d407407126612107042c04503415000d0f158107000000c0c1045559070794820341b101d0f0000502224000d10058000004011080c05040d02c5441045143c610f1560004200d034403603000c004803405d40038a10b030b95584800d680c11150ba079004a000d580401c0c4240e0810400c501340b03001d61038402082c24107c2c0c00c100300003c038804690404c003920754010745280740060240e40040c06c443c80a0804081024610080c0c082d440c04079001e0300030103100040c0d03503025280715890580141c2c42c00c800041c000596449005a0b44401021600304bc001d000c1e00501803e001540651103c0d0301500d0109420005508601c1c50b1881c0c4c024503002206003d5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 208822949 1250 208821699 208821731
    0xa020c070e06011d01020c040c02010f02070c03060b1002030f09011b060c110601120f050705090c042103080604090f02060a031401051503060d0303020c0316030807091a0d020c030d 79
    0x30001c00e9511aa45000300302e00007d440b407e011102901550302e5840c0251814400d600078405296114000c64960700c2e2403420f030548401d144819164141413600841031480c2071182000507080b1500103500e04a9807600380790311500b20790f01c0581031201911895a10341d181e0f9611342000740c0f040c000020450000c55002d401c19100e064400559440480180442400c09c0140303000b0300d800001944115507545402843d25009400c041e81140c00c030701c14040102c4019021b0800c0d2a40410f421001354506100a240380c10008000f400141e40350020a40d242850703131003400024044c5100080780189500030960f140e1160790070000003640c4400d60031000409600032405070004507808002c01c0c0c03183c2006a0f540c08080c202c00d101e03100da80341e1001014000d13811681846040c130141c03034a030400d02c0c1d00010204221001a800700340f540000031001880340d00907206407446900401148004075603c41c0d40742d008800410b00181c0d0030041e62804c41c0c410000f5000c20361030b07924007140114818100366 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 208824199 1250 208822949 208822967
    0x12070201031802150c100c020307030807051c1e0c110d0c0f0615080703030c15090b0403210509010c020f0609030a0c150c180b0901080f0a020c070e0601 67
    0x280016502e90002d20041ea500407407480010b01001c0ca07280c079020440700300303410400407010807030b80f0134074000464420075004001b41c14028029152800c1a03036400b6000d8a40d84a9141c0c410b02424040302d111001c495144c1c8a000303030260b840d000c0d404026a85c5076035001c0b500300c500214081740c01542c2400700b1081c1005108a0100c0d13628140809180c1a80d50b4003e141501c0070003000640c842005403050503107c905140140740074022210781d07542d00d0401401c200703031030281625403902510410042e10b0260041140f00e540c4032042c00103039595500c00322600c041c0e620014520203881c1c0030500101420307010b0381d03001300140000020804281c06000c2c2c6850f088111240090b00100d0400c0701546021080e80c41032060743c04c2c030740100c1415240c0710b41180304941c011140076140c10440d021569001090504908114a00603420703501e0ba1031400041c011403400c1400682100c1c00036440e1000c000c2c0040c0c100c1401e182c09810041c071505d001d402c020a541002c0343d61040402080010740c0d00580d15 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 208825449 1250 208824199 208824221
    0x6080105150d0b06030c10081902031e0c0f0f0301080c1009091109060d0c0f0504050f04021e03040b091b100e0a0305010204060f0212030925081207020103 68
    0x200803000d079980046441c42c60640c2000d4000200d0320001032132518213201824115900600d0301307190046408000d0600041944d441351f00010a10300800b600089108403030091070041500c80c40d901401d8030001d084040100050300d4a0018802840d801210740d01403e82c03c0c6401a54544039030506900614000c1150303445841525621a8800c0468000c58110183c030050603010903410294180400d0602c18000ba8035007168000445003002c2960b0b034070034420801d455030341355412000480304903682c2c0078a00410740d0004c001440e8400a16241c0d00410070303a505100b01c813800142404084c4407030f400c201ca0a6440e014240100031b9201c405001303d141c17840351040303039036003108410740414103107e0b011416406020710701e107044106681e04402c1d840115403200c025580c4540b0380200400180c43c094800015110f403403501c1c1c15494400c07041d684510041c000611b60709955650818164100700c403c55144110a0b2000c18421001d10024000380d01c51148242e031a54079200040c03c9071251000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 208826699 1250 208825449 208825471
    0x111010902060319020412060902041a0919060308040e0103021305010305062412010c090503030c060a09081e0403030e0301050402010c0227040b01090e070b07080f0706050a06080105 80
    0x49200580e25441603d400920003801c10a0344002c16132041d00a00c01c0d504064000110307400300724100303c0960006071020b0f01c290360621007034089050f29003515125002c0c40c1d80c4200320000058007034407581c6a0009100c6080400310701c3c682e480d142c001c003d600c40c0e0402041c01c40b00c0d400620541c1045260003115400c401c008010315890768940380e4036160b014002c0d0004101034800035131400c140b1280036001500050190303030001d100f0079805000f4040c0ca425940882c04106001036545030200a0f6444010306c000034001c1c581da02c0c0c0030a0020a0b022100700d8000b10280003504400c1d007008903100824203580c000d0b544d1103080d0306014010903100002240310368182801c010041c2da00c03070171000d950740e03066850190891003500d450458050f50040003c46c40c560404200c20303c98001d20160407110401000c014440456000710b0700c40041d0f0240301c0c81ca94040042c0c5001600705402040e5115028500301d04180ca145e807070fa42a2102a200307045c81903269441800f501500f88100390700001150a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 208827949 1250 208826699 208826711
    0xc060a0e030a140703121505010e0102190b25050301051509011d011101150302130c020a1b230f040b01020a0609140a0b0a0e0d1407140318011101 64
    0x140240801048030f030300b244001c1003100402d8000c006503039403400c035268203204560003240720701e6082000e8802d060020303100c02c00e40d114950000c10603102400035840b01180b126115110402d2070b54002c2c0c50544030212030290f040c22907000c184c0c824000003055941036500e524100801528080e66641d800d02c2c4142080f81c140140c0c1c1019405c2000203411039403856045102c0010707140240c04041a401c55404d0cc0c410700b4040324058440d20540c2c3c402c07241c0340e006444690501c03040710701c0c4860300809a40240000c402040561104151542c008100d11140303039100c04180302620503214450f194144010b00c01d07045132905000d47d059030041500c003008031110900000791340e0b41e0000c002502c42c0e940d0300600c10034440400b02003189081404121450b072040380c50a9100c420b000c035600c0003224640070100650100100f13080c0701c91402c990b0b0f1685041d140038842c12050348028002c44080b074518102e10391510f82032018118416408a41000c0411120009090380007121100c00031649082 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 208829199 1250 208827949 208827967
    0x903050a0908070f14040915141b12090f03040e04030807030504030f0e010302040510080403110705010e09060f0a030b100605120703020702030a06020313020f0904030c0816080c060a0e03 82
    0xa13403110071501030020300300940302d0f070401040080c6010040900340c85c0d03110a06120381003040e00000030700d400d44d0079501e070700e40c0d141d110f40910303001c451035104035092040008c0b40780c2d0074120f00030035004030410b42038800030400c0101c06403840d403290b4030240f484440141000f00341600507031b0407544504117080502a500e0550f0f03000b0700c0b8440405400b0107008042d1307003845040c2d119905071409032a001c0c01260107001c82100161a80300c0403034040740000c81d5807a40380c0020034042107180898006031200c80ba010450401c00c40100001000b880e0041420000030032030f503884641c01d400446c020071109040d828236101040041c5010f402900a200c81000340039211039172a44250f03840025032034010b894203420310000341011124000900b2081c00401030200e04620640000040c81c42161100040d14480e014454106170803200a0040781d04408141d000c940c0e480000d114030310306080c904091800d50340d41c50545402000c40c21795507920074020000200400d1281a901d500c42c10011401d2038061 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 208830449 1250 208829199 208829219
    0x30e0303060109260601090b090105032e0b210d17160c08190905040c02030a1404050a030b0406060e010e0c07050102040e13030206010501080705070f11040903050a090807 75
    0x5403041c00b07010324541c0141c444035400c208135922402070034001e03100e0035603550411501070004a5074051069000300300000c0d9519000400c242031889250504212054240c5850b0020000740c0ba050242d51711045682403c0d6607c0f0241039803440c0e60b95101000107a85041d80707184c0644032000b0390600407007100c1d14007413030102084541d210072502c0b50300043c0740c481041180d5821114000a00c800d0001c1a04101c40008503d410f40211007583d94130f442d29520010401650030320b103d40380c09a042000003e984500c2441c070001112201c16841d441c2c40d6550008c00c51240c0c082d40140c231206d100c5814030040140c28004e05005008051441d10310b03504184206801a101405080c20290000b82d5581003001c20f405440040082c030105041d40c0c6040803102058124260003100140580d40000c0b407158041c1c1c003114010f02e441e035215400c100c0c40f81e0742d00508170784e100c00581702203040001c0510b4503544c50003410021803003a0349003900c400c804d060103030034103c050304184030581142406000413072034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 208831699 1250 208830449 208830467
    0x50309060a150b1b01020423060a170403021f0605120a0206090d2907080714090f0a080601060e09011403060604020306040e070305160b040305100b0307090615030e03030601 76
    0x114083c5640d400c1c940884442c4150702c000b0007066540040b0700000c1c0c04555001ca1203584141040340500310340c007501042038601c02c2d100014042603031200d20a501d5450700041c1503000d0b1107401200e00311344000c550b03440383c006080340c036070a01c075260300043c849170802107548000107407550014444509a0350008095010b00c00443d0b009001d09401142032044522101c184543c00310110303651000203400700300542d00115803045c0807a6414010030325151192904012041804451906000340041000720088a9444441e032207504040c01240084050001134024103840c0c5842a04000640134041074140c164000710300d068442540b5150382d100880e0300d59200e0400c8030016925036809002030000d04001d800e039426480740342808020842e0008114480000c03046107111a280e45554003d118840c03408000d0a0b50030187c80c8500700301458104c8402000001c041d5610381c0d031900d80c00011203841c1d41c041e0005802d08a1000b030300c9ca805200d010780c0107050001651443c6409800a40600c0e4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 208832949 1250 208831699 208831709
    0x30a0e01110405090606161a0f0f16020a06050a0e01151206051314060403020f16090207030e0310021c022109010e031c0b010f080c0307050f0a050309060a15 69
    0x90b0b0600020a07569810080764203501011443d51102002404c0200d0748030039080b10321f005230240e0000f04807640e001e0b0100720f118a201d402d03080740c140d49810458640030002103100d42540b2503d6491000102c5500550744640c80c1d040001404901c030007002400d4908170315100c0700b030040f1070030f082c0312070300c02d403508540c880f82c001e600403a160b110344000d0200c10401200203020804a800c21618240d000f2900178040c0b80030b81e08565141910301d4440313840325406034500040d2502281d04002100c2c3d42d4015140d214068100850480c081001080c00e141410f00310611440d070004454070315003002409002d80000c0140304504043d04907260080981d22907244103407910b070000003d140000250000070441d410784003965100c00781c0c0028030f204184007031a0340e83c4960628441407415403050b80d0f00101f10110766506c51b01501c814042803100e5001400c18002c0007000c000f00481c20484200030000810a603a69035524905000c5403400c0c50405010000c2d51800e044114a084425002c81000c1d16 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 208834199 1250 208832949 208832959
    0x1060f0503011208070b0702030a030e010b01050a0806030a052b0f052a1605031005060603060907030603020303030c0a110d021b0d020d0606051809070611031e030a0e01110405 77
    0x1030400c1c2004c0c03006004144009215101901c100200c1a5000c401341a801ca52a01c080c00200c400364101800d841c803d202060015200303024071405544514000d540110000d0b06a94035110a03440395800c0030012050000052030911b070350030b521080e4900c1d143c0541c543d860700016983c003d1100074800d12410382401c1010391000d02c2d00728103058000b0150340203000001101c50380706521501000040031031082d81c0c40380c0580274120700a050107002d02481507200512452171503864804202400c6030103090b12040582d102000300050b00c08000450140c0100813441d600c8014440c0c2c000c0048a040e181d9a81c0364209416007400e41e9000106040c182ea01d01c07010b5039603090594046610700b02200f002944c04440c4005040c00c0c40640e41c481e17003d0f1101a1201180c8107152405c10200040079036048000c2d078080241001290300c40c028a43c0341c2d003010303400e4070300c1e0140303030120040220b08801c20310078200301c004240005504244500201261510000d02804903c08100c9002d03002c0c2e4410343c1d00031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 208835449 1250 208834199 208834229
    0xb07020d0206042a0807050f0301110a0c081b0c09090d0f081e010b09040516080606030a1d06010906050a0b0f0309072105071d06010c020105130303020a02030601060f050301 76
    0x4011100600000b800383c542d8504c0c0419601c4040710707522401032003401d01560200140c078115040602030b01954450320b4500d2444c0041da544200d0717084a103040e00b500c000350140000303a107101c4082c001110480780480201403010040040141c0448003901403461507020003500891650000c1903404c4c40070301c07030502d01300316a00c014801c8252680c1e0035055075100b212200100c0c100b6200301c083e182019003683c04010079a619000c0c02c40009034a030248001c55100800a009807078000015a8000b030140c0022030980098070160080c1404881d01540607008100180300c2001c1c1c621810b00104011a41e41590740d11b411104601403140740700c154115407000000680d070038010890b44c4010f0546044d07000b4458803410000394100c0c0600340446842c000c0e042c00260441030303819205030f10190f001d202c4800d52203000040d00d203031440182c00c07414054203100c0201c111141d40019801540a90003030042c903106031042504040d0141c10070028001c5440009840e1688003040d42e054443c0c101b019940303 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 208836699 1250 208835449 208835483
    0x314120a09020102010b1005070c060e1c0201050d020f090f27150d0f030306050402030c0a030f11030910050f0736090c110f12070816030c0b07020d020604 68
    0xf4107403214078250000d92654020047c2c6174020003c2171910300510300e24864030380780c00b011240009440b0102c1e41c81244203401c031a04440f5411480c03040740c41414120705d07080100410310305a800a00b556010304c080840c40e07410906000c103031680b440d03104458407041800700a00409030f0140f07000c450100504242c1c0004c00614000b08804600d102c018000801032029240040108101000072030000f420200d00040b00c1c00c050094070300550291584034184044500124020410044a0034280b80c450603020500344940001358000c1e18441c1c09800800c0c1140d004d80f0a0f0391015012903c02003113113041003035166009a0304138501010200788011000b001c03000309965a1240104038103444150000110082d80f6030082d814031019807106400c550b6404051510f0741155400d42034250084a80f068010010400030b10115104d16099420150315054004082e0b20f1904220042401801c441d4140004606107507440343c1544018075604000060094980310045d00c01005000c00d5580504 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 208837949 1250 208836699 208836701
    0x901110705090721050406020310060c02010210020708160507090c02061012020d0501020a030912020c1e0118080a020103061a0f0f0c03030f15030307081b010b0603010905040314120a0902010201 85
    0x4e00940100703814030072401c1508000740203600c29147c100c100e41d0034800000d0001e024040a48000b90140c02804290114410800213540300c000100c1d00c000c42006182c0c104011102c1f40c43e0002c1c09900101482c500385200841101c00740e015079002d65000c5410010030f42c0552050409542d1383c40400300c0490070078804101c600d000c0400040c1654000302d200c22907542d0580c402d20702c160056107200e40c0d42e10501000e0741c880c10044109038110014540200b268102c00d200700402000600d00202c052190300e001d00d0510b4140d4101020036006419010195a810301034400942074900400c4030749180c012000300148112480080d484d800480d925110111020940c0c0082e2807240580c1c0d52171030103c66100302940204c5203d2110550b554151005060001c1a9010310b580030301d0300c900e840092000b4580006114040020329900da031804030181e1103c0f8041c40c02813060000c04501400d15150103403a114426200e03526030001032180009100020010340d0700103441c044001203409442c00101c4c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 208839199 1250 208837949 208837997
    0x20901021c030506150702030d030506011103040f080f0105070c03080a18080a0f03110406030e071703030a0b060a09030f020a0509011202090a0b09010e0a020d0c0509011107050907 79
    0x20300c10840482003503a42078043c1c1240303224400481d0002c14552159003030f4442d07802840d00180d0103501901c0980c4149020764066600000141040e044084c40c0f10281c0d4950f51203a0020800b148113a0001c10800c5001c020b070901c0f00480e80001d200c6803a054000405080700d1480c06801c1000c03820106240a94030f6005107544030360200461b1401a440c2460140c66220324882c0c00040d04052040b8070315407103480f03403154240458111a01c1c0c1860010100c01402d45003c4c00301090091190020314031036422003078a0046600005035440340303003030b4030040c0896440e519914064102001048480c2c1d901c041d188040d81d5001518a8100405001244400380250001c54200cac1d2840004175403030003210ba0b04444c0350f1003110001e45950718280300390113030f540f002403613500079600e000144601c40c204107407568800700041c0b0060810b004c0c009020281e40d07400701041d020510029452015583c01103214100ca0b078900000c05103649094003080504100404010821050b8281c0120382c1d802818070b0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 208840449 1250 208839199 208839223
    0x706020c030403081b01060f140112050709060f080906010314010f0c0207090c0e060712020f070f0e09010203190c0c0b010f0905090613060b0105070f0b0f0a0b0a03020402090102 78
    0xc94842e40c0728604a0055440f901c000000840c0384440c111201205006503020340301d0180040250701c0c07803d445440c8500181c00c006040c00322840903223035a85601d205040c0b04417050b0f6105003216182c1a4094003826001c1c003c0e80410a00e881045200b0600048040c1102d9011000b08203110302248101d006001070718007140385900f00225804000d600040c11007c0c1c548081d03081005250f4080c040d203140700c0100c10660020380900c0f4060110300000d080007005026030055828091a0015181c2494519040302d9a0070341950703c10b100992141c2d00503944a24500c00862460400c0040042201c0324a00040700342616002d14287c1c0c80c0c41040100c40d1143e02c0314941e400313945c41e0000d00d49072203201e00030412134a01e0040002c0b40c410b40010658001d81041110790284900d42d142d00e0050081c0c801c000d81401410410030000030414140c0075801c90140c04061024241021200c1040720042c0280403814101201c00c1c440d42e0b14090341c0e40803070368102c5005a9842200d8010b1341424017016003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 208841699 1250 208840449 208840453
    0x3030c16080a0c140c0d0204050a2c0d081e09070f03060e0607180b07110909010f051f0b1b030a0c03020c0303070c05011d1203120906010b030c0706020c 67
    0x99904141c1c000c0700c061400ca1003408081891800480da070380e62800a03400780766006d481c070030b040d034050304041e402aa045a518540420400107003a14641d40907002070080d00c00780f100e8896204007600a01040c0300c62032003440d10102904001c000761100c030001080c880842205c2e880815107540e000c00c14400105540703001018403030307070360300b45a001440c08101000c8a80903001c0041e0a691040c0380c1c880c000ba00c09820980741d10700b81a001300c00d5070000e02c01110904c49124500e0429074400d51075600c111030203800820311445512284095803405491051002d101082004007604201040010354072101241620f40140700c607030800c0440a41c0c41803065000c00180003010170344c44019202e07124080e4080b501040d00750800c2c581c0d01d20407904050460300303032200c0c18401c42d0320601c0072980c201c80c0c5030030f8070705150000000915178400034080144590310000761031070500b490200180d8400d030144054285580b5108600410781310050417020002ca00252a03005c020299040c0c1e41c40c0c07980713401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 208842949 1250 208841699 208841707
    0x3020306100314070f060518060403062712030908090a03030305042108070806041b050414190302060309100504030c03080f1302041e15050a050d0503030c1608 70
    0x200d11981c280c4680826940c0c1d4480001d44010560001030030401c41710ba40c200320003d64079014003200c0c01e42042110003008078011131800760740c1d40c40d1070144c405140a01c00020b1748442a00290404407417082803900d640403102d05040125105071141c1182c07141d0360602042c1e055103460245031a01c0356224035680b100b1046404003c2c91b90581c8000d02c2903102c0d080400100b81c074006c01c40b0f8000225402200020013641c0090281441000301c1d80d0480b10292011601c1e0681c4d070302440c14031115120741400501c010500300055121110640b10040c070030780b50040a40c6000301034002070b10050102a0040c10004045102101c04000039020103905032420003c0d410301c7e1500a0030f100d105c0d0802e50000b1080c0001c1a19541e51130221070288440560303001a6491507030900020703090b00c5500d00103844002e03c03800f0040c0c00a0040d081984403050584401ca0f040404001c1841d80340d4109a018992400301d143c00100c00008403600441a0a038042d1204103041c50507108a0070031000802c0b010000c6 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 208844199 1250 208842949 208842961
    0x606210507230a020c06030f0735060405060f01050702040b27010e0c12070c030210110c010f0905030d090c0902041202210d032a090e09060f0c090a03020306 69
    0x1c2c1003122184d81c240e5111020010400003030b0300050701c0c0c0d401e40041d50004101a00e008101c146d040410b040307500d1428428902d80303994000d41c90f200d207060390143c140c10026940741501c10070340e01c00c508840c44420002035100013000c500820400234001c55980c40300c4440e6a40700f01074068140c20403c107000514800152104e2421003e104846c1400100340c08500026031b810255200070008001140c1159501d00c1c0440701d0b2004410160305501032240e50695030341242c010f2882d448900304080c3d41c4c8103000c00c41d8608403501d5020340c0c5500e80c0b900000000040c00031040710740b14803120038081800c1d9514186071020750034541c45140218800900001d4540303240b124a040e542c02142c000d614080d0b1001d5450a041c40408880300a8210141d8115217a0195001150070200390154020364419441c09800900f0711078841d00c04100c2d01e09040006a462a140c264080ca000c00900790070b003010412804118006400c00e801c0d450b011690301100d40f51000380c0d5000b182c006041341e800382428 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 208845449 1250 208844199 208844267
    0x3101502070e06040915051e0702010e0f07030804121106070623010501140c0a02210f010605090c0d0b0411130f03050a061d06010b0307030606210507 66
    0x41c0708414402014000183d1545020b100f8805010340120701410302c580039040c8036000308002050440151500120390054030001a04c13903104803001e4000254140c42003090034a44550500e140c080d42d84112070600010f0400810b84048030f240d029403d402c1038103860441011152400000e4001d040483c0c540d042c42640d4001c00006062010f207541038104865880d0ba10041c01d0103a14041161840400003c101001c018940180100141c811124840d40000c00c586c0c103000e20b01042c810412096070b1081c0061001084007088900208141d51038a0301040000718018403076018210b012640a800c3c98907034006502d80b01000300304225004c00385811203926080b040d000d2440414040010840c024844d054000380d035080001842c00e400290765900151494401544880c220450070406106041180901801801036200d450380307022500242128003c1d030000e0304110305039280c4000d4084004448a0b8145410408180d598030814180c0c0e006210a14000084402d11051100c541e61 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 208846699 1250 208845449 208845463
    0x250c080312180d081b0c06040b09061f030b07140d05040c0b09030c04050901020f03070309020102010f0b01050306120f0a080d0b010302070c0e130f05010509010506061306030203101502 81
    0xc40001491507201c0c02c40003a41c1c4140801032100130684e048042007044980641004c0020700314450549403600d04030b026801c0250548080fa240c50140d814490141024002203034031640c0488502d03a00b50813a81d05e494140b50510002e0726071040100400c0e00948200001c01440c01c98400e81940d42e02526040d100400044805403a0f40711460004140c01c42c041d001c841c41c0900040c000d000c0c800d0f5140402c4010480942403e1103998204141e4103a0103000e0050b51003070195440020303440c140c900000e8296020b81085000300791608160401c2c1c1c0c0c0c0c00c50281c9401c041d007500d800c0c4c0995a4540c0c2189002c042c4800c050b1144200c1d201002000915801082880a100d401b1300003094140c006605070701641000034070142143c101408545949108141e0010080031025007041d40c40e16010383da408020350685131030b5101d90400110034400d02403642c000c001038807454a040c0f036181e25014521168007944c810560000007041000c950020300d00003a15a884d5140098908030a02030b43d1a00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 208847949 1250 208846699 208846711
    0x40308061002010c02120309010e0106031208010e270114010b1314101103090603013201020303070c031e0302030906130c0504022a07050301060b250c080312 69
    0x255071010300c0352a481802100400903841d0018036000900003507516907600003c0801c6000d40d40c60140c0400d0100034043c03d0011f40c002c3e40c10719200342c80300c0740c01006400160070204995400700c043c403100c01c14907286034483c460107240410610703840c00b40d000c0c0900308441c03c80c40c01e40c06080000c5030f0329607058002c0c4402d42c010b01409001c295903070007032040d00856069495120001407010118580541c10030803003d0013810a60f464038130b4250004040b6002a000711404c8040002c0071001d5224980201c9980c40c032000c10800d45d0444440003e41c4e9100c01040501000400100c1208043c0142204044da6000304401d0350701c03001492008009410445e00280316115007004902c40003212070440b040303940c010500910380c0d400c01d4140000b85d0300562200d002c01c161010070120300940b840c0708000017400d2001030104a0703e00010142920147e03080115510020400744142c008038170781c249440c4c0500e40b107600d16511a4185680c510728994490300c1c0c50700000840121070031050103d240720310 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 208849199 1250 208847949 208847959
    0x5010606030c08011d040c030c0b04050406350703140c01081f060f090e072c0906091506070b0901060608060d033905150c070b1e04030806 61
    0x620b80b1004031280c0c0800e1191503020341a5a117005412424580410742c0b0501540302504103d41d43d0360749484401c1a644240312213000450b044c001864a4000c2d2401001d48010300941c0c0d583c0d101c0d0040018211111601c0708403a0343d19958207100f400e1015600841c2c11074243c1142e203040045090700da02c1c01d403400e64001042500020300070007866a02607039074410b510030000f03014100b24060350401c1e401c84143e03003030080c2c0ca41d000a24086044806100d8260ad0b6a100c001201490800d0060389095040300c00c0380602500c0003269403104c05802da404902161111403e4481c4601406a00d1604c81c1e56600300a00091a42c01e105440e51114000c042d194002c0001c0e6542d0310341203e082c4029200305501100310400710000c280309270310300c0b200c980c42d980c0190100c001002c01d072001a0400c180b0354965444114103038050000c14001500c03c02180c49510304545031100480c0c00c0b45c422804002c11940790400400d08640500408891a5450243d440e0b01030030a0304010b000e030803042390440c2c814 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 208850449 1250 208849199 208849211
    0x5090405090d0503010603090503070c1508090c0f010e0609041d060106050703050702040917040909030305091c1b080d0b0f1509041802040624090b07020d08070f0501060603 76
    0x80d000402e001c1181c2c859540c941941d08081d0214098000c0c104162601e00c4144110703004a84a1801d02005069183d00600900001c580c081e0140364010711600306070308030301d401510507242e41d0030034813900200f40380402c0c0724214080043c4150044e07144a0380c00601c3c2001450300f0724016400d441301003500780111485c40e0381e6184121a6445207060040000c0e50078018a001400c0a401a11040d88200114082c0c10742042c1d503903006402551001c110035440d0003913001803540511425810009050251800600712860462581c24000d81d10040251040c2070111104820703010140c0940d000d00559a19011800241c001d44582d05038240714500404010707006c0d20f41070006044070481d00c1c050604040089042200404000302c40207103200c072400c507010050781d8504c54840a09001e06070180b00c0000401c40d40d18030302900e24124107010242c03500784100c003001000e40f030b10954100d07854a03500e20246003c1c81c2c10b00600e98000e20020503d000002004019003000007a500c40b55420042 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 208851699 1250 208850449 208850461
    0x82b020405010212030406140a020a11070b04061103040b0c0318041a1003020903010513120f05190e040e010608010f060e01050405070c02030a141603051b01030f0c05090405 76
    0x89224510516002da030045044078416401d140185620501849001a030f8084142d80c011103240129044c0c0d41041e070004074480996045400303e0000c24403000245803003810101e41c0751070381c4103601030082404609070b0f19080d540710030001c03503016100c03046041c4e460304001a0345554903005000501813648407000c2e0404c0c01c1c101031055041080e410002d40054000c240103019059040314200c07800c041e001c001000d000e403800d0042501907510050400401c0034070303041c80c03140c11076201e18050821003007840ca0b00b90380b0340c4942582d00c00700604401d29102460100150b4014254141c041d070400e00b040c820121010040d8001022a50901d000b440b034825003407a00c2c0102c85441c0203254240c55918018012410b160b40140d52002c12406e01c000c604200ea000039107080d80140044136065001d65a520302d00000b44074036803800d80301c8440e4801c894296602c282e02c47e03040032050b403444a0a0720708800268807a400005803206002010042c01c03511000040c00f551152040c213001b6070814000c964 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 208852949 1250 208851699 208851701
    0xd0f0f050309041b1d12011a030c0105030108060f09010b090403021005011509090213030602030f15090705040302120a02090a0b040b1206010506280e19051516082b 72
    0x3c1310420b5980320300750b4040e601d0a50003041a002003541044120b045640c00e000c091041c807002401c0e1584130740d400c190160030185041d10407400a41045810f0004103c40a00003d8a41c1c120321003c039440c042c0d030307540c5a40b00e004140d81050709074482142c5052105264001c02c50201503800c2d040c0078440daa0f01c51444000b10228202c00e440001c401060400c2520910760240c00d400c94800110340507582d0300c0d03c8203c20780c0c20a84400700020300c0030041c483c0c240d0990381d8005414070255081d004500d01600080d20300e02440c072001e8000d8290f44442c0c10001001e0008540b034035802840004207082c07409018004082158103580103900d440c010807018036100808500c1c50b200400240780503801c0405011854100c1c01c201c0c0340e0340300d010014940d00140003002c900824159030b1001d1216001400300000110340390300c09280c810a81c1400d020355164008040300c892200d4a1031aa1254004d43d480d81c01c80341000c01400070131010801000c010041c2c044285e000d921503d10010104c91418884 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 208854199 1250 208852949 208852991
    0x516030f02011d1f200618010204080105010305031207090e0a0903050c1605040605060702031015120609020a060503040f0834051c0e09061f0f030e0304060801050d0f0f05030904 78
    0x100b20340c0e2192002400e2251242c004c1f2405403000c0d0700160820381e031600e03001d094032800e800460380c1c4d40001c208138802c00300700145280c0c48440d07031501000c03992400700d498694820141064899507242e04605092501880c11512000d0750401101c0042c100010000e0034401d40e8040d451180d4200700f0002400d00c2c018003590312840d0018043c024030040f44040780d00500f800f54118034440c0000c280082c7c9a41d00950180e031860190801294050103441080300c40300e21504010b06005d030600c18480410000484004407980c400c40c0e00da0740304240b04000c100c144168400802d42943d0000b0328045030320040700034901c1d038800c23021282c400c074055000084076001e46403041c0016004000002e960b01d405d85283e50000005008541c5419110b84404c00c498500d24075140401d003090401c043d01a454800c00c2440344a510146003000c0c1045001003001d0b1061103050b10580b40361180c0c1d01400101001201200d46c415050425114641b17000d40d181d401251081d8411840c20200114500610241e2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 208855449 1250 208854199 208854257
    0x9020f1809010c0311121503070b1201050907020c300714010f050a030917070b06030d0e030a030c1401020c25050901060507031206060203070516030f02011d1f 70
    0x42e0803d8040b10031b0300c0041314014941411020414031001d1282c500784444406050080380d541c0e61000d00d03c0d00c14107105c5c010ba01c2940a0740040040262080e40400e81800d2a0800c60b003d03035040042500c039094406074084810080b0b0300c160900781013200c001a034001180c040d895641c403101e00c0d00e4010b541c010007289031040460010003202c0c0d070952007644112412841016220380d10502c01c0c0078060b00d030b04941004c0365640908018404245800c21a0241c040c50f1403920b0018088004041381d16040c001c0c0e0300030144082d90400c5010014410b904401403140207000f191542e58080890b50f560041c980941d8240100700c0c0001c004414005518040d11800313030080302507900c0d089045a003684000700c141d0070001404940040003945010b8030300140f0095005580b1012181001e85c240b0100440c211081510f01004000080510341c07503031441602400e01003601551a15a00c0d60401000d0f0880d0b4065610040713000c0f0344251000070200c1c01c020380c4d42e0040c0e0982d01d180c15091703182c0031106 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 208856699 1250 208855449 208855481
    0x212031303150204180504050105090a05070603110c0d03021c05010b18030a0209150f04022a0a06090503040f150e060306030709060b03010503161809020f1809010c03 73
    0x10700c04208000503840c52495150b400514040e616580002e1080c0102c11000519840c5c00030f000501100340a40c0d50410310b85d10140c0585212583d0700b5613501d80e9445000245078a65518102103038003001907848034040202540c1e2094484400140258400ba140710340f022038004c003004051880344a03d5050721f4250040b245842081100e480703254001c241d032154148034080910300162035040341e06028082c904030b42880404500104100d0035034004400d4000d51050054200800000030000580000441003154035180e0900341820400300600182803941032001700700c108200003004004840100c00790318640ca0712401e0010718800c03200d2a050000c3c0d580d0403501d01c186072030402540c110304018219600c0c2c659421029040e251164002180c017030780840100f01c82d040c00c1c00080030642950b00e0b0100805d05040d000c032421a035080788000717019503a10710b100840d281c0745d40c080c0c241240284400c41081c0c40c0c80f8038202440080318004a1075007009000c03950980a4007503460b90700703184c82e8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 208857949 1250 208856699 208856737
    0x70b0c0307021c15050a06080c0a030b100b04031119080303040b0c19080a0c02010b031e010609181a220606090c080916051807170112021203 62
    0xc209010f005403041c00020714040d07100d28000ba4200071101d02e0b03001501000b184a2800003543c4048030b1aa6001d0b04181c0c11035082168165105030403039083d654010542000741d2642511802e031092650440c00d052040041c1c08020b10102800c0c0a022140032610211000350703400c0003d520f45840e200b0b040466106202080005560074805030f40114400c120600380076070101820b080b49802d40d004404103c1c110f09115504800380030b002050300382c0e80000d2214175aa1800701e5a207204484210510600c1c528485c0d902c141e0a401c00c038010901002c081c404010f02e000101c0d0300310161b2800300c0745081803c0c81120b1204c075001036540300e205a0401d029060400c0190342c1c454010a107411134201d555403101041c12a1b0510070804581e225560b50030785448d02d45406480c103010314840000c60b14800e04104070780e80e00c888108000d0840304003c04403a032a4a40180d4108081c203910010700c250903000800d22080007440503032203034007c0303618120041d820f0340520b459220b141409520003110203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 208859199 1250 208857949 208857953
    0x60a0308040902090f06040f06030501230607030c21110d05030a1a0315100f080607052d0a1d0f010309020112050426090f011101090212030c070b0c0307 67
    0xe40608000400034004c1e170906088100083e9007940190025001c80c981c040c018042c540d4540315007400f41c404000f00c284400d4500c00d4100030010032440180c455071000a2000400d403241e00a000001c0e800703042105045000c4040d4128118016101c1d40000d940e11880c0604200010b107081c0100040d850700c52031a121101480082c00c683d0651401e514900c02140c0242e0301d0400c1040c03807000490f0207c10203818151864200781c00c0f523512280240074044024803950002040e4242c2040c1e035403c140c0e5891444e043c0c07c200071004140100c000c40601d0811012201240000700105547e41d0345040081c1c00d11901008400803405440e90040020108511654000e0740001b810072b005040c4208180004d410360f4099a400702c50845040304034804414405070061520180108505841c0c0d00381404040420100b542c542225070400c1040510070803401d82c00c3d4402e080c100d0300070b00b03000c949509085500c0d5403540035502c514818810000d00290300e11100003a1500c0c03c50380d03409145040380036 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 208860449 1250 208859199 208859201
    0x16080604111923090a02040602121305061312050a15062301020a140c030d03090b0604110906040602061501020c0108010905220f02010206090606011202071a0c030906060a03080409 79
    0x241400045200c0305643c80f820399a4400740c2d43d216040c454009a666800c15030001d04140700704980c1c066184050150401d10300544413800143d500c10fa403859101e8000fa040c0d000341040a603c45031813071303c0d04529101070000c04541211040d0050b5001c100c5411102e40c414100c4410348204000c462140c040b0020341100591419107518051046030b101440d0350700e1b03030054050082a2a03c2641c807001102000b41000d21084a40c2130503401e040200d549243c80d91004540014034540c401d03540c03100c44000d0070001c6001d4800201016048607181d548820029580c0c7d0400d6447d040751008803815046550310000e007102140c0c1060755241140d9103441d650801500001d041030754001b480001480380741c0c500b4842c040318180144190369104001d4000a4100000503002c0010354010030108902ea98109543d9007a1600d024001680c80155041400c00100f81c80054001445900c0c10b0042c400c440a000e54010f130303600400d0301c182d615070400308295100d17036100040210000b807004010308449 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 208861699 1250 208860449 208860479
    0x3030207050a21020708011401050f010903050f15010f0803091c0b040305040e070207060f050a030b0d0b01170604031409040e0a0605090c0109050312070302160806041119 75
    0x8650700316038240b10382da6038041d02010400c0e04401100c401d2004281201e81c10030040000701a801700030803000410b2000c019005c0014000c0b9405042d410b00040c840307920407003030480215000802d440030300070b880f20300701c1d00c880080d07076081190414500042000400c098a80d8121443c034401145440340e440241f1008911842901a00d501c114176501b000c03440342042c4a203c0e6200c1e0740d40030342d201c0c10702561503010113001d4040310441d800010306100c80c54014003c280c4a00c1c8504026031142c520740d200700e015084d5002c00503001540794100404110101510350b040e42c00e59031000c20410340e00382c05035544001c200c03000740004a00d2141003614890050007005c10381805800490511030080b280c034034002d2010303800c58240d83c1e80c804001c3c11200a04c4001c155039401d19016044a01c2c02c0002941c550030a01c17400c448100003e40c02c01018000c1103040314045041c480fa41e40300d0303507030240c1d03d4403488122010f0f2148030001d0706200c1c0c40d140180320045d4034407054480c0031100b4202501c039090160 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 208862949 1250 208861699 208861703
    0x9130e03071211030f03060405070e09010e13050106141017011211030a0b06030601090603030504030b0c0c0a0818040209220612080d06061106040b0910020f07020405060a050a0303030207 82
    0x240b042c0482802e0355061006084c01c5c04c60b8204c0360381e0b90820009000c100c0300010146400c1000700b03112403640d80d80d02000d41e41100d80741d6041d0822901c2e8010821400303c02254000d1a0350b18201000800a42c0b000b201d04410000f1500b80202c0c1484500039a19203441d8801c1c0c04110045100501c2031b4030044d10441400707030081580d40000210503010921301a61140281c403910020020403842d0b140401119014054148051111074035554024006010310b01001301a02c403003c00141541003500152006a1310041c100c44458449060588190340a0480103031101d080e0070510440d4103250080341d4000c0000b804a5240743d643e2111032011405102c1c040703c25948442c1c4c00920301c03202000211f4018003408002d5900c296404100d011160f0a522000900804075001c0130f910390080341c09a070040c0c000405003400e50311000c040b41400311859010503110301c0800d50740c40001d40038015120741351081da0108041c3d291f540400030703030030340910400f5030003890b50b8000e00002c1e10076009058414 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 208864199 1250 208862949 208862957
    0x2032a120d121512050303040c0b1c090f0501060f030c08070b041203031104170f0712030c050a020904030f020f0a1e08040302120c01080c0901052b05010b09130e030712 74
    0x591100e1001c130030704010007401d980c10f6002000303000500c14602c080e03000902c0b44900d0320385804400301c0760742100c81c000000c2c0745c8000d0b5103c1c100c1051000b0721000c2031240e603024000700300850300c0302d81e00030845003070b0b010660f0f4442c0340c01b0000c1400320300043d501042c0e8208008080c1000d20b0000c5076003c0c01d42401048040580703031642002502c03400780103000680a800301d12507200e10b001d034420782303001101c0f45c0c1c00032a40e221000c1002028010307800c2d54001501490400508241428100e20b84900d01c1c0c0c00941141000007040141948608040b0002c0000e40c00d8950200d00c61446650303544485402070944940070004207401181000b8801e400c83c4940e0002d8180340d50303500007031801c4903004a03c00309500f00502e880c0c1c030796038083c1d5a550f000540c107038440d08050b0044002040340c00b03070040d032003009002821110444808604407a0500d113000c0400d100941e119541c803065500b2187c0d030b40780190313005011000459050b010f6030030741c803105d440250b052150769103401c54880c0d50803038a44188 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 208865449 1250 208864199 208864241
    0x20d12120f05060f03010605060306040209030a0c08011d010c0906121d0304090b010503040f12090305011a040e0f0a080a0e0a1203090b030603031602032a120d12 71
    0x2000600030101d800c904110001031a00c2c16000384a0040c091640c0f09201ea4545034081c801c99482d00c040c1d940081054400507114601007000c03038500041054040c1102ca9025000500c880e0150858000e505402e020150f02402050245007a1241c2d200400007007004103000f8030610340320f451508054040884040303120f400c00d000da40240c8111407640e14903500009014001c5200301e004000c802d82c02031070300c5461481c0c01d40b42c5503d4142c51010003880d012458044070f101900c101104406950044002c04c00340c42900b18282c80707860050300d20b5025606003401e0090500000c80c048141d48130b5000601442045070b62040d00030380c0b0400440080c448199010001074840203200307000f6204105403854001900c0c00c0c0070b402d1000076485400d65100420800483d07840104c1500c2c0022203e4070001020512032001a051403402075503d1640200040240300c5000e61003003d0740c00c4070f0141d0f25401f0461070f0542c55a05c0e181c404001101099980c01d6840760011581c2c007550724039400000c0000c0c0c2d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 208866699 1250 208865449 208865477
    0x2702010f09230901060e06040603020a092c06060a0c020f0406171501080a0f020108060406090e01090201030b0301020a051603050705010c030203150406060e01030c0926060a02030103020d12 83
    0xd00450425050320034045200640e00f0f084048601510003401e0240800b005100014010300c00c07400b4690406401241382d40005001d280610b02601d0500c4800803a56413039011480d510b50001180307080340c012400400c60a0070300c501103801d04032955459003042d2040c1c0d0203101c3d022190912064215588080020307011000b00004140c0856000140001240b075a0030b001c4a8030041c4c020001c01d40000c0750102c000f800080003021195428200307840707603170341e8000001c0061005a00000c049403c00c802e103000d1070010750100c8203052003620208081030805003450300703d00450440e1408118100711414098034a2540d4003400c9200b80703070480c0b4180040d0741c1d641c00d640200c414000403d03008010f0009861004e04a481000020b980800040707242000052110380040b001e0b906041e500c140c400c1d1801c0c40342c8800e03000b40800800c424400351603e404038080040300101c1c42d42c1030140f4008240440058022681280d03001070401d00c900380e0700d8681c10014071021103000b043c40054180000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 208867949 1250 208866699 208866719
    0x60c070c030f0f0201020f0613120516050708070e0103020904061d0a03030221040b010b13050a0e0411060c070605090609180906070320091516062702010f09 69
    0x6007580c07282040f0300506001e480003920344040c4e900340e42d510790451000c00c01030100e11120f8444c10f076084000002c5000c01d41d5425500d510a95801c0300c040346402ca010b809020000030080b00301c0d4000003c403139206980751026003c000080c00021f42c018140c4003c140402c4494000701000c00b402501d00b2146904165224903181840c207045010a802080980c0c004043c1c04007494064001e00380d2808030300c1d282d5210702070100140224407030080702003500d80703a91295160721406860082d0001c0180c90b1500100d50903400125000c446540e080042e0310442e041c00000d07112543c00b050000d100d06c90902e07038151069040208095001801800104050381d03c031800800d00d1003110b1070500007428256095820072000800807003d050600c4040120000d044686401c194036000322252601c00280c006440c5007212003004032a102d02281502544815001c581e405901c109402c0050307145e80d101c1502400e94514155400c0f5548841c0c6401550082101410f00c03503261404201c000e8503065051 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 208869199 1250 208867949 208867973
    0x9040b192301140a020c2e090b033c1005010201090c0b0a02122b0e0d08060d05120d05011406030115090b040906030302010b0402032e1d04051b03060c070c03 69
    0x4610a6410900103800700000e200240140408d1a09070032482c00c10907209030318440030304040c401860360740c802c08000e10000e140e0707514822000c000881100404030080c2c03812006642d0306080c2c1180900010340c540c01440b0b50321155600c50408080d4a1403c0040a02c0307820009100081d4001c40d45411141400340300104030354189140b00051052204000603200341040e140e0b40c40c03c0c2d1608105540b40f03000003e50f200c1040c458586a0301907520440403500d00282c2410050103413090000d4416440000d2000c1c1c446518060b60800c010f80e601d8040c800061102c8442541048042005000d5203480946007600300109041c07035101ca9070ba8be0144686640958010480c09544041c00c0c01055828060004030a10450b030560960408006c044034000da00901c13003040c02ca401050015800700c812101000b000b4081c10b00a40300104c000e44100c0040450b821a038502606542c4e609120092a4212090602030300510155441100c03543c1a40d01c401d00903100580e00036000800100c0303c030380325 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 208870449 1250 208869199 208869229
    0x501060c0b100501141c090803011502060408030403050d240f0b0c2e0c020c01110307050c0105031503030315040b060c030f09040b192301140a020c 65
    0x4082416007400c02025a900241001000c000c0c041d40400040e0b03031110840180760702403015196a91141c44000c40d1000109456580c03050812206005121400b0007460484d044040c02e9101081c249034200d0300c40350220f4000304034120a002080c04248608081c02c0c4410b036910001880020209008080e003e42100ca82100d0009010504c074460340346528030014842e03003400c41d0030042d440c08184c2e182c040310440c2d00c1040440480d104481c540b11b501141054054030010041000040802500e451007561a00d000c510b200c40c1e03806883c1ca00200b100c00341e40d082401782c0801402c80d4011212540f0142070101c59000118030304529a600340002c501903005a880310428008160500042d520141d4482d413007554180441c0305000b501000715440c0b170a6003ca990350311407050000400401c103515059402c07440c0f141e44040c40203134900e181415200f030903000e4400e031001c090616079442e00344072600c0d001602c42c1c180035900c03400c0d4001400c001c00490068611002070540031415242c0c0c11849 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 208871699 1250 208870449 208870457
    0xb0a1b02220c030e1603060f11070605010504050c07020319170d0213080a0b010312120e0a02010201050c03100e1b0a021c0206040f08090d050609030901020c0a06020706050d0f050106 80
    0x40400c2d0036030580300d01d1310340010142c064081c20074880d2040382c030035110f440050243d50300c131701c0c80b8960010341d5800341d4111503a0170141901c5011a0618800804090041c0d50080f0702d4100820b6805140005440146034010010300094240c0905511b00700ba500908840c2000c1f0000160043d120780030280a44009201006131110a0240b55003000c1c41d06602c00d6038541c009100c44000300da0011207860540b500b121b05064a940240401c580d8502c51062440d1542d20b44200140404004071312059030398001d074000c0c05141c48c2d03442c5018480c4420342e210203601032801d008104001c10604450b034040b014065003c100c0f40400c08610441c1c1c0141c03000401a017090481c4d0714a40c6ca0302c0050200d091051009120a28096035450f0201854200c040c100100100710002039617250501515180d902c502a030b100c070b04003544450360341d0304042c200d140540565410302c680b5081c0044034108650351a801050300920340305060700e45038403c24840302807649480881503094020b00840c2e0003420305035a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 208872949 1250 208871699 208871711
    0x303060b0d0f11072a090212010e0f010503100905010905010207050109031704050c130e070603020a110f03031f030f0506190e0705041d0a1a010b0a1b0222 68
    0x450890309851040c280303001c0113120440104070340503c0c0d0480400340100030f0b10b841c008064508402d6000c0c0e403186852500003d241410100e040c14614100d0b10600790140b040e440307048604210810900038990964405e080e00c170b1101c5180e03000060361900840001075100c10a440b03039807d90b44525001c6c1c0d070aa4440103504101b40d4401d000304500031907014060350900341603a4090310b1f0032080724024815040c00b88040350609050b07100b0010900d00000315012941d4a06024001c3d4111810100219540c10300061040202084c42c0605420060107149903076215612413201d1581d076400d82450600030740c008000500740c40550402d0a001d800284920310381034083d1f0081c041c85150074507509042c0003000090081c00100e91f020355008840104490402403220713900b4000886254149104002e03c00e030a100d090132084201c816144950aa03a030b8803180003058610031040050f000881280d000e07104100d0100c082d8181030710040051100c80c90301c0c49050f0380403469100d042d50503030740c5203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 208874199 1250 208872949 208872971
    0x12092301020606060c0a03030b0a090207050c030f0304080a0b1308030106080411040b010c030c03053c03010e070c02060405060a181502031b011803020a05060105090c160303060b0d 79
    0x100295000100326226442c048061042d1500c4000780c6c00c1c010300f4503450329040c01a0381e403413203000006004400c40c21901c801541c18100d9940c0c1580c0c00b0305009001d06c040b4014817041c040b0403641030390080700007403451080d681c1e6021007030720005103030004100300403000c0b1000403d2a00194000d02980d510640c1d1400c19080c44150440c404e88014070461034002189a02d980001682026540500386039045941030304068a003071081910078a84108542e000151200c907410001c94402242024283c04c0c0010b03d0008007548402e0140d0700b83c01c40300c4000940c0b4540b2410a5034500b0340701070810344c201a40d500110360140c10100c0c1e4400411342c2007c0d0302d4680c00d4400e250030000c000244442e001c04007141400303504e0f07100d030802c031204d100d40004071400032070000d400240300030003103a92003080168a07007002503c40e202e0301c0b01200c1c5401110000901e5140100c6120b000f03081d080d10403441c104c05a0207031052a2142c540403002d03d40c60300781c0018074040725070140c0462001000c0101e0340581038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 208875449 1250 208874199 208874203
    0x507180c091a090117070c05100e03030610020c0a09091406061c0809030a0b06090117071715010902040f050427030207030510090b01080105070c1209230102 69
    0x1409604000494800b00410b94901d06452100c1e48041c0b0103e80d10b480c000c0048904066048150f00d004d01050244076070a6803211441002d02c5c0110140c9003548050312460050312103058142800340d1041c00031801034030b0880744246012580e40121101168002e0115407001410303801a1040ca50382c42200080c002c515407090030160034000500042c2c60700c40c1c001402e08a00c0c0c005811140c481b02c01e200c0801829408885102800404460850f4050f140c0008200811950140581c103604000502c040074941c03192881500d110117021611308100801030181c0007031410b01c5d520f208800c01d16031004000f0600703c1c0038088412000d6600d41c107009080101034410ba0101c2d010324074000741d4680302208903407071a07254012090304d0320130b402681c28200d00e000016003014005025500900060800e1035228241c1d16120322040c90217070381e8880a0500303c1c0c03c22501d400c0412501301c0031400151030691080300a4509060800030980c413140b801035654010b01c5845038100e2281c0c0b0f0100c1c29030301 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 208876699 1250 208875449 208875461
    0x1b030f0a081906091a1801090b13150306140106090506070312140a0c0504080c0607020d02030f0109150e0307060c12060b04080c060403031d150703050a030c021603030813050718 78
    0x6c3d25084440d640618500b01d41c0001403282c101d500340c1d901d000702407030f50311003490300c0c2400d0b056030b410b000c1c024a208110030344c100540710444119180034007420040c0c0c039481429040f50303207544409403074500d0402400360076480394030308034104190054240e203003c10a224401c41041406100071040c54500d100e0710445103185424000c0c400c0512040059800000b9820441c0500340c902689038103162008c101d600074000301c002c2d8980240043d109014105501c403041450048494030100300c0c0c100b0540d01159041c1c1c05010b102d400030460b460109009410400228555182401e0b501c0310052640003101c4e000d03004142c04001c0000c08201d005000c112440b01100d041381c00a1801c0d28503500034001008109000d04a40164070031031950361341c3c2d0b01c0800e550505600c1c2496403155030f4500103206900c0a46500d002c0fa01d03106158540364400544404900049811405402d0564509413080d4000511151a103803062801030300054040c0148001811441d0f00c440b1010883e034000380c26a80 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 208877949 1250 208876699 208876751
    0xf0a060c051009110910150c15060312080c070209010512070519030c080708030901120603050313030b1303200a020a0611062d06190b1b030f0a08190609 67
    0x14010300038844047c50158807001d50155041461422000b440c04402512005603403000c0d99281060020912080d0040c100411b001995214091b50b107074404400240030b902d40294000000d8401400300c0c2c05e210324200d000141007011150b4450303640380018480c880b20035040c40b002401840410412003074403041b8000d880b02d0380181148605143c401583c9000d4204142c3c104a0024040c10f80c507040d640c03040001d5074100c81501c9e501c00800c4082c88842049200894500c1c220f0b000280d0500d0451007041a250f5266580031001e10f07007546c200784d690070004142d01c903d000b4200c0c41001a500c81000c9001440b403610b41d01c5084c803520038414148040102016052224a00c40700d02806001c8240c0201280038000340740f080c1c9944004ca03c0c99502d2103c11410b40b03c80540205044039240702170f103910300b00500b02d10443d0702c0c0380f40559100d0107112258a6524824800788030240c3c01049207a0b4070000b6054200e1220000c80c0742e090595100d540403424582c0c1d1840d0140e803050b030075103041c90380354 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 208879199 1250 208877949 208877971
    0x6070906030e0f0d0f05042102130203060117060411030103050c012c0907050921010501060302041a03060301180f03090608130303050703020d0606080f060f0a060c0510091109 77
    0x3c1c02a21005132621806100102004010352003016000e000c0c40a44018020000105600030000c1c0214400c0000d2250280e201f100c0f06180706410b62001e0003100d00c01d403010303916200400a48203069425940242104d03038095110400c00417424503440c0614021800388c0000c0600422000014101140d40700108414074520607595814006100e5000c40d040019501050980e4500714102c805000e08100c00c0e034441885031800400d00030403109404081c106e0f900804c11641c3e548015022331240740300d086403040a0000203410700601c00040c5511520142c008201038a148c00060b0f0110450001240c2803000c25440034189640710f9810b10180c00d05040902c15410144071255984000340d00080c10140c845000641003842078050300d000c00c15201c02803040503220340740a0040e48044410800c401080c000003503052030000020001084080d01c2800210705150048840e088007200680b2288143d0b01d00c000e01c1c0c5014419281854003c48040d500e044042c400c1120041000d00180780c09 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 208880449 1250 208879199 208879213
    0x203030f310e0f0a14130c0b03010f18060504020f1903020f09060a021c0906020c0d0206071203091b060806010804050601121401020d05010e070c0b070309110306070906030e 76
    0xc48051030b8064200e80c0b00702c1c001a15590310030b804030282c54004caa01c22115148800d214801030902002e88401e0b210714403401d0f0301510740c643c107001da0209108205402d01a030604018010705103030038815840c1003102c00309a481c1c544001c981a45d114550b4103502c030300d0016415610b2902d82006101107601c3d80380540c07900521600b07a142c28020030440520401c400281240381b94004c212858070f0300d00c0070b88036168181c0c02da20007030200109807203120054080c85008848500d40700c01c41c03040d001d80c02060b46090005030b40700d1000c00c400b4250000c0c24145d886c021000824a403200e0400e04400d000001c01c0582c1c1000c4004040010240c129418403406000f40800504007280c42415145401d09109090005080ca1030f1400c80012035020a544001465080e0300f42c0703078214a05a90f8210780b4103003c0c0d22013190441d490350315824090400f5128401007003c4c13501ca42c1058100a01646101e200442d2400009080460984260700864500401000b80c140c15004030308000540401400503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 208881699 1250 208880449 208880459
    0x723010507060f0b10030c020c0117010b070309180204090b040b090c0c070b131502030c0307030f0309051b090a11180301090f0b04110603070e0405040203030f31 71
    0x60190200040029450320b620700301c49603e0f41e1040d01143c00040c1481082d40781000003500500c0820004030040c01511070314205035005001040f51003c000254141e06da10f0325078000110740142c075044040000c0301c0d0780000c85c104c440c00e05540c0010180c00c0140da6502e13000c1c640f42100c0000c18410300503030904803400c202e580c8042480d640301c1400d40b00b0303a554064445880b420100c0310b8000c010038605c0851808050500401041c1c2039a0300c15102c0488250110000e03a0703240141002c4080552042080d40c000070720a00030382001d00c6c0b41e801c010400203040da4902c2c3c00c1518115030010214215500a0706500d011a1841e4108000d08010448020068403032451446100040d03200780220302070002e07680c0c0f000d42c0001350080c0c120841200b400ca99107000118038505a509803100c000c035070b410f00850b2800c03204490189405448144000d444001030002520f40104266403501040c0b01301e030f09520314040142030260201c602c9049000442860f1030140b06154004e0003060b40c0d00d481401 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 208882949 1250 208881699 208881707
    0x1260307110109051e040c0903080f070f020607140105010b0a02071e030212061b0909040f170d020a1803020a1e0b040306140906060916050d020309072301 68
    0x118540c1c121200d60782111000005940301825a0310440d0044240404405200203049140f041070700c04032400d1080c00690341088648024500000e80b450404101c03018000c02180000c0c000749103d0115a1502225500068050b8100d40410f850b071036481510b82c1d45c0204203109440c050b02010a44500340004900002c0d500c0b04903018070503003140f041564540740c40b5003d0803400103642c002e00c41d69110f4041002291a81030035a540303080100b8840c000f1030b602500d00141c03079030541c001e8091340e02c541e16602c402d80c003580710101c00c1d501b0300c5c2030382c29a81048110800400e80e145a04901507699140c100e8000d02d40b00b40284c070b00101c41210b43c01800180c2c1c1e0154050700f02c440c0b18048080e0b034594482d809800c6080c1c0e920141644000003000001c01415030081d113500d601c03181d000b040554500c1c1c41240c8030041110036a034000c2c040c4000a02110001491500c40c00c0d1a02d031640c18299080d041c0c004130382c4190b0f0302d440c455000a1080012a0803403840c2c110300c0c2c000d950600150051407001030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 208884199 1250 208882949 208882957
    0x906110c0c040c1b03020f0a110306070801030305030c1b1b030d05070f1106040801060806160309112103180307060207030515041e1b080a0512090102150f012603 71
    0x4c0d014036491100078184204400e0a0020094080c0c551018031481c2c02c0c3c1e80750b45a40d00803400b81c043c0301c0001c1c0030b103806110014101d0340c040d203c1b030f40317180c2d0b5401550303029900c180420011b86070305180c4002d400108001914510308400704400611030200105842c0c183c0401031070040080410a000005004400b2242d545520080e4584d9a400500004d00c3c94000d6030040656980f80c890000b412006c00601e180c050b803803a116070720785480c1440d8220142c0303544c0311020b007410401c428001442d040046c00800001c112900282c031118512000b5411a402100c4142545ea1210852520380c80d05001443c0104821b00042002d18a503940f500e41750425081a22010340c00c5a0014003071040700502c0c51203095044008041c030700d0b450b140026034005880c003041d09290241d030020034810000917034410803a4000d0f0040070b101c0051007175211907600c0702d66040d04501500680b00803003a014030182d80a40280380c040d409542c113042d2030409440c1c94010b48804014803070700b04800d00601204803 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 208885449 1250 208884199 208884227
    0x9051902030c04050411090a1505040513030e030c060c0601090501061b110105090a03210302160b06060708040314010c0309020a0608060a0f09091b03080912010906110c0c040c 77
    0x444c807030b51141421100805400c204940000088003080b00040e1503074082060303100b540c803000014a48800c04d0008542c0100e950841e2403034404526800310307020340c04290214800400b2501d41106403000301d1010b0f00500c140c0021070307020200500a41065015240c050400c51420440c00c4540c2c0c0c0903a124189040405070551007015900107041c3d10810459000c2c44001e4410b50b00c0503502c0c9000901c102c00c0712210384030b0300c003040c0d01e0400d90b9203c1c0c000c50f040d03230035407440202e030101458032405090b40d00a402180d02013010048800024120b030060b0000b90b0107158500c0c1c5245403090041e003900c411034159030406180a24042c016998a4000410380c0c003070345041c03503040c2e40c0d04010460001454001415015095000144078002c070f4018444061080c8404030500e440c02030003003888210790000801c0c0810a201071a02da040c04c0f4000c54044800d0800030444142c0c580f21901191401c0342070901000001800c829074050410000b043c1c440305880c00c00c0b07501030710f0100030100c1e668083e80c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 208886699 1250 208885449 208885451
    0x705030c0c10050f04050c010903020102060a0c21020705060703140a020702040e0105090c1018060503040c0f080c09090609071404151e15090519080303070309051902030c04 76
    0x118041c90749081001e0000b440b030048003041642860541140c18100894045403544611542c2c0d4465510940124080b071390306800404c0c140e20313402400006030034981c01317007001c00c407440507604a200c00d80c0480c629140181c403001656a012420710a04080008002c0300506040c02c900d00c80d00342481290b903901111440340180c541c0316a1001038068144880c0d00c12840d800d0105010100d24040354614040700c0032501c5040940d00030100351600e000380411801840c003400303800c00080c2e010b98000c50303105100e000e42e110030f01e80300e071028080c6881d11f400a503015030145811082606240c19155008200c082c014840707480c01e5800c9595480c6e160041d0866551045c440d010252a1500001a04500700900300c007425210260090b941348000d07000c914500210380000345040e00308141d090b500c0c06c00e0f600c1e10411307410642071000ba560702070245100d5403c0c1690014008e002400a140142200d540104030742020f13007410340c542803c881d40c5800e000e14203040e0340d00507600000d9038001580b095034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 208887949 1250 208886699 208886707
    0x2040507030f0e0601210309090b0114040f050328030f0e0a090209040b0906030a1b09020f07060f27060b090403050304061b0f08040c05030304090b01090e0705030c 72
    0x412405090260742e04068039052040b401801540030448a040c5c81c003000d110000c50580c0e4040d02140300e840304014012840c00c0200b81f045209680107100500018107003e2601008090501d0b842d90096110044041074128144240d29040c0308032a0f06a0b00d80c24029140801450a104289440302c0c000301480080c5082c0480d03d4061041c0e0100da0400400110205640303203c2100658448901c00d44074500d0211118801e281c2408841c2c00303000c0c080e00400d0380c061550b55000c07402e51000c0302844008415a0001132044003400100055011080e4540e02d0720010f250000960310364001d0030030218108900d9420310903640040c034034840d01e52140e090040140d424800c0041684118164001036000c08100501d50000c1c02180624403d585c108884000000303203890142c0300c54003010001d0101062101102d1091000e6071700940502940740c2004d683e03400203031540d44198442d4800740d807160243c00702c41d80c00403042d10041808034800e242910b0301140c000c00601c00240321b0040008042 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 208889199 1250 208887949 208887961
    0x140c01050a0305070905060c15010506040e01030f031715120105011802090d0606120b16080a050702030c060708011d190908040b0307120f0e15060111030d05010602070e07020307020405 81
    0x380007004000c047e1610359125241640700b51100024100040c0e90000040002031314200b8004940c01ca9800e03403204003059003155101c80213003080100070390030080c21410741901101c0d00042c00d40980b0608d811a940c03510004240001005100841c60243e4035201c01044144030a40300038044455400340140d680400d0f40006000c240ca8200c06007041d0b2622001184901c1c0f2a1032810781301e401828840c14030364442a0000c1140c6104078804c000544500c0440c0c07829159802464004100b40152400d25401c00f148a1810404545500000b90010010001d4000307132400c441c40c800a0220b00f490902c0c0010184104c184540c296000f402d56462000041c480c040003618041c0c20261001c82c1d481c2040344005100c0c61030b4025800c800741c6030180811a03c0303a03a00c1806040e41c0501c019100d450602480c20308103030300042201c4d061000400f12940b080f2428402002c2c410141c81d0001303076035410490000c0c0751030140e8000c4400c0381aa030081c4054141c00000703842e0389941c121800306181e940e030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 208890449 1250 208889199 208889207
    0x702090a39080105061603030c1110050f0903120105191a04030203070f080d08091c1205010f05030a0602031021020102060f0c16060b1804140c01050a030507 69
    0x60040642203000c64408903180c0784405205a0074010341d03103000c040c3e62100d04001541c45110380719800300c03c0100300c21001900a8000c00c000d82c0150030103129040b01d03d1700f0306007054080d8103901c4c02c2c01e61780c0303041002d504200d542054100000c180110704001d07604214505100040c05035510400e046208052b0009100341c00ba0090700d4618a440e890914a54000c00150130030700080303210740188200442c401e042c1000c0c0d83d00b00e5400341c00070015901e1800040c0c5101201030320310350841c041c1a4040c04140d0041c038040d0290102c950301c00e000c1d900122550f104440041e00032010004c041c0c0d03000c00c26960001403516640390481c2006075070392908050100410f039198031035906c4040000c4540d1507024816010400203000ba0291416541ca60b034070702d000500102c07240c603203c11040c81091440c01d8040200503413180300308000240c480c3d030200019146081f9200620b40e00d080c0604120400040075103884c80840040011b0420b184010006410307409220700c1c00f400c0541d0b520000f0100f9220b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 208891699 1250 208890449 208890491
    0x7090f0e0c16051c03090309120f020a0f0e010b0903030a14040302030601030b010810152603070803160806030a06091a0106030507020f06010b09010810030b010f0302090105060702090a 81
    0x1210340085000c043d15015403210000c003c50040c2d0726294841070303900c078000c0c007829036030650561714580d41c50704154a00c860440702200c260790103824130b0604001a00c460000d28050072941c100c40c100300d85442016849410160400400d02d001403106580c80c2d00c002003507070110486402e00d0300340b403500c0120002c428002d80d230010354148110030000042c000c443c59224186c40840e4181d07000480c00104900540e0400192400140c0013408104444000c0c0ca20242d003212070845078030444011182c600b440c5070442802514001070010900002580c03000344c4000701d80941c1409055490f00760002030320b402103188003412007901c442c20f200c2003203035070140001080070801c410447d07941c4403d00200200350485c0c00c8000f41c031035450600060b40c03001070200e04844040c58420f04d0600c2260044030b10720005841031304040500e400210004060120181c06001a8100c0801c0c036480c41c010010b13038000c180c2c00030703001700410400c941c05611050105540908860f5010406800140b22100e400702 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 208892949 1250 208891699 208891717
    0x2703050f070c0b09090705070c0501140f04090c0314040f0f06110c010e010b0a051f2f101802100207080a0f020f150a11120705030a0807090f0e0c 64
    0x4080e0b200454481d400c100036100d21901a2aa003016699520040d140792203080b002811401c040c820800480d0b100741030602185285030b4034a801d00c3e04100c10000c0303036003150300468042501c58042c20070f585c1c0e0620405580d90f803d064800000d04198864114148070240083c0141c10818541418048140c0242441080300621143d03214603d080140c02081000501c40955087c02400d00c0246003100c3e2040560704010038001e90310580c6150405074101d0040c011092110030912511000c11400040510040100d461100c2c1d94040c0401420880081c08034610315140c949035504010f03040e01307203000041c0c0c103031001003108074a00800e919105d51603002200034030410040380704100b440200585014402e482ea40600e00144082003042901d154901071040c4d801d0240e0307640f4610524602c104100d0142c2525100c824a0313260102540c040c40382a145030340005544c201441d449004d07164028044d1410389200e03030400060740031000740c1e442011080306901d030100340c2c080300c1001250f410390 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 208894199 1250 208892949 208892963
    0x9030b0702030307110d120b030a0f05100e01060b0702040c030e0d1808010e150406060515030114010306030c051512090a050d080903190e12010b03012703050f07 71
    0x1103040d8600030750301da108458410005003d444035003200340c800a0704069000700761700c078201d004080d800c8082c000c0111442e5264140306204605000c6400c003807840354107901a0300502201c551200d6114180c4a500000e890640c0c5407000c10010164041d040c0c410b0356604540c0800c104007104c9049002e0850100944054000c0c07440090603507421103038452258001c0803903004556950101c940c01c031507001c2c44030116501700c0d540c1007414043c003500c280e920070701c00c100008100740c403003002c547d110301c80ea071400d410400000700500002c1045090300f40120030074030f02031042c142190350764240c800140c8541d601408071390105401040b403080c1903442200b10702c00410143e1030550a2907550b8400d082c803daa40d40030380490051150301c17905030244a950b120004601c0d00500062140070940400120400c12403440039031000c541d18007000b400e041c100c041c00460303280c2900c410182101c0080d80b200c0c07260840ca1480b180901d10745500190450b8240c203206071600c0b81c3c0c80718038800f4417031020028048 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 208895449 1250 208894199 208894201
    0x3030f0c090414100f141813080406030b2e051b030f09042403080304021c0507090e070302180619080303072003030f0a0f18050f03040605030106080709030b 69
    0x2140010304c2c2c4404507580000041c01e080d42e24030600328484100d901d010381001e80d00403224540401600300b15001504880390803803003401610b54104075002031f00024000790300c85541d41100c1c50029188080665500b5071a400d80c2025040d03810031900b01c0141d1000d011010917a5843c440004400c03420411003d4142d0b9a501074145000c0300716840740c0c01c200d100b00c0c5001071003040450b500a04401d001b200700001c448440c00c0d42c4403980c4079000208100d03801800180628040a511211490098401c100402c0600d09008009099421006851801d580300300c40400241e0380e04802050b0909041e50030f9000c0b61540c10118003400c800d0344100c1010b01c03482000051a02000008600c501015034507248150410b01040b4003d05400560741c0c0107030300030710202c0c0c0080da000258540180480c0400030f008108803003048203032020100021249058100c1c10f0003401030030700402d401528008080e505d02400c07c6400b070704600040c040c00080000c030301d0000d4156070065107a132016503040824490360f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 208896699 1250 208895449 208895461
    0x31b0a120c081e03030403050702040221040c0b0901050a030b150406020f0c0307050d02120c04180303050c090d0308090f120a020c030a080301090b0604050a030602030601020f03030f0c090414 84
    0x8100540b140c415288030364601c0c203501070780a80c0302e4280b140011001e50f180d40c9603920100d0f001d4200c40c0d8142d038425820440c14a0f00c102ca1286081c000a50503000ca40500e07103400c00300403440103075010404840042040d218030b0380e401800c44034042c42c5410000f505581850100b2040c141e00b130781d500e2490340d000801090b0190000340d0070100c889840101c4007071549160a00d600d5404520480d0f0f004334400082d02e00500d0241a0300006d80c100f903080300c0c031640304030001405403007c40c007a181c44116880000400d1650500540da403161084043c03600c1c004503100803907003101041c000a02002401d0340820702068040c0800900e26403010101d4804010039140c441150740460503c0c0e02511541d9010740a0741008140c0d0042180c001611904580c80c000150010b000b080501662002e010413000c1850341d9100b06074005180985401a01c0e89448000a0718090a00103c0d00041d8000d00c02c001c18049070781d140303941c01004e480d030250b200e00c2400003140107808286007526060030503c08001e0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 208897949 1250 208896699 208896713
    0xc060d06030b0a1d0f0601050103240609090c08060906040207300f0e030d110703050f01050708100806060409081611010f090e0c0315030708010614040209031b0a12 72
    0x144c02c0084005810a402141034400c0e940d40c619504084186c001030010421580213030300c01d0a1282a140c029500460348440c02ca1a903a002e4000c01d0101703500400510014100d880780132081da19a04001c403003402d28034000780c2e80c80070041c403991003182c00084800c1001400052165000000380b00300c00300c0b40941c0100c070516182400d0306000031f605404400107944c800c1003461000c40014003d0845c0840d8070b0070840e9400400c6c100c1180501ca2400c0000c005070042006807100d0f5800400040d45041c160320040070b440e03000d03080900a2109040c10b00a0080c0412603a41042c001c460004444c101484d054445015008103100802c001d4a480024000c0362400e4400d0b4a0003640d4601c0703000346810303003550318504074040c10b0301022000c400255070b0760214008640008841081490085c2800d000034075020a54100b0003499455800401c03903141440c40745204840112015403d000c2400040f80d5030301001488641e0301624001044d020f51544403a06003d81a162100f0301682e00310300b0460 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 208899199 1250 208897949 208897961
    0xe0106050315060403080304060b150412050105060105070312020a090f270c17040203030c061014010905100305060d0507260705010905010807030f0c0c03110a03020c060d06030b0a 79
    0x500740c0c941c04141030b128505241240c0a40354020032542c03e41c0c4880e284e200c01844069507154000c0583c08000d0350010040e000741000381000f100a1003100701610b001420b5410280c50503041c0141801014002500600b51401c0b05000c01c0d1300585030b8848a0003100e4000d40c0e640483c05000c15180b011401d1341452a1008000e0000001640d0103004c5041c0c50040b81c40380680340c0001a00c80c607106805280a0b0000c030740241c00142180d08150341d12030441c0c14004180c6004111901e800c50810490918101181011800342003c0b81c082c1d181001103010107584980380c4d0101a13403000001c11590b950f40b085000039400c40304554420340c64440c0c0d03002103448903200341100e991900c42d0405040b40003440c42c059510603510402054544001903070445005404401410386950344408400c1061040da1103080144d5602122421076082c00780045003080c1c1c1c7c1c0032040c1c110030206008603800044012040f442504c000e50f54106228030762005120741d810080143e81c007042070008103903503904a1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 208900449 1250 208899199 208899211
    0x5040f0f0e0c01050d0c05040302030607090503070806090a060e2d0709020301120b0c0d0237021b0d06110a030501080303220c031209030c1e03060e03040e01060503 72
    0x420031004046203441c2d5501480922034000391080003089000140c41d0040c00c0c3c103c115062840c2019141d40c0020b081c0f100890310300e00040c001050800862404000420080c10068041c1184d41080a0229100d50701c0d0b40000d40003030b8807185480d184800801501c10401d5035a81c120121603c03009100984503000c0e60300e0985841f82c0840421401024401c41c0d040700c180084103440c80d00580d903010030040c001071101d509400c09100b5030900e00350900041c01890007131860803d000b040d0408100301c1070b03a161103912041c0031620010504a400181c1070f01c41c1820082c640c1c82241001c0d0000f48815485040105120b0500442c44002800c034130103400c44994507282413000e0307a201caa0441d0341c0e001c1221400704214840b07071004182499107402c803601c00c4c001c1c0280495107889407500c2c0700b808255410000051440403042042c0900d6946c034501400b1980b401600f0b8503001d030703007001c4445407a0101400b0960b4400c01c104611170200100c60061408810002071507945500c0a0700ca07402c11112 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 208901699 1250 208900449 208900451
    0x110a03120c030209011b030e120d02011802280b39030f0f07060509100e07141c05070605070c080705010c0b1302040e0d020c0307081c030605040f0f 65
    0x7009014001d009490308490181e4800c992900d000400c2440903007640d406405009880143d000d0780e46460203d81c0704a03000c4002041c580b010420b0090031207540403800180086900030850050303440300c440d4182d482030103a074440c14031414070f066002c007078481d400000785140c000340701000103401a508010300443c0c2400307400c41c1c40419201205912002d003007442a40c2003003020700303450007420000d0401441800394071801e10403a40c0c1d61404983d0281d40b02e031500c0d4095030084801d0691400b070328003c401400054282c0c01d00d000f6904916140b0400242c0c0b02d50b202d03415548074041040c3c40c42e00f0840c0c21500f2562080e50ba40000f9003c1c0c0d0007803070151120300741046c021906240009440d8216070045c1c0d02e0408040c0d150b20b860381040c40c06000440840410880c01001d03958074004d9042e00012140039100006c21224003078074102035002200e000b600541c1003045100004500f1005e014040020034a5294003207008038001e011a4200e294482c0c603116180c41c410000384e104003020010050 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 208902949 1250 208901699 208901711
    0xf06060314040c2607063b01030906020f03010f0302030d0207060207090e15010b03070e0405060901140105040f0e041217150a050a171c08040f03110a0312 68
    0x1501110070030040350007410858803182c00b004101580380c9440040c0b207000d18401d0248507609603444c14010309600603400582c80d0040c0e210180034240301c00540c0d2070008410901d2800312140c2d0410025400b00040c14169900c0303c100510000f41c0444047c1d00e01100c4207a520b41e102e034186d082100f03141c001a8040d100c1e4243c0108101c0c00050040d050310001c0d00280703452490070703e111020308104c0e41c4c0c10006008601c080007e10480411660203040d5800f48591030789480400102601e1588803078620480c1401c0600100f515100403a0b4151a0805003445c64040f0141c01070707413030b0720580c2d100f15101140654001044000d04007080e00603440380d40c500c075202d000b08004560960401d084130001291030300100c1d0240e1940d5251444684000e030040074542e51312070000700300d07500daa0301148011940f151300414084080c000e804480c0818213040100d510390324802444039400620007000e100205550006260003240c14070040b0240104440d0030032014a001040d400c40c800c031040d40d00d41401 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 208904199 1250 208902949 208902971
    0xd021b01050f12161403040b1017010b040515011202070c030c08240925091401081207050703060906060e0a09030f080105010f081e0c040806011d0402040b0109090f060603 75
    0x401c00c0315292041c45d1485081d1346070b64903111004000a80410000c1e00e60b1000024603400030b0007122809504000002503040d074900c180016901c0061200548410f8000501016078000f5803c003440e1160580040c0c03030b800985081d51902070540c1000c0e148940c0e40c0000108504001018130000004020032940519041201d800480045d900d4070102d810550b041040c40400144015121110440328503200b5aa401e40c0022140c45156101c29201048014083c03401c0410010004c116418049072600d502038880701c1e19040c1c140401020070383c95442800038010b194014402414100d846800341e410f00b066010010300b090081100803c20842100600d1070190081d00e04940060b180c52014000b4514110340080006020251400303080103482841044007440d684607040c4000555070b40c60802d400140b0b8080160702101e242507002c244024084000300e480b5410960646000c00e000b1510001610510b18a8002d440628908001645074000da9007050040751510340302001400350032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 208905449 1250 208904199 208904207
    0x80f010f060e07081b19021911090c0909010906061106010803041710050c0702030610061d0310091115090d12020f0601080d0f020d021b01050f1216 65
    0x54820106500b0301440010030f9540580c200326407010148014161605141810780265084607030b8280ca6074030156080d10380d150301000039040c881100c103c0e8a400003026135616201d000c04001450080320f00001140d4661030200c2550304105005103d41d4440d0f071921015001400b0f41d1003880700203040780c05600a05000450007905075010303403000e5450030f41841c015a8601a030388000012070302c00d902d6111404540c80c4142da000380c504010407580d481081c0101071410300d01403c10025030158550130407000350000544000014209402c00c0b10220001c000303401d1400b101c442030905400c0c820094100006c0105041100d082141c10340744e41d5400c60b00785429801404041034004401c1d8642d000400d00c848024880742107144106c441c0c1e10f90340b48900e414014280e00454160b0300092101890981100070324440d00300c03d2000300304041c5104c200a644942902c2e403404503004e01d4422000a908c07807400c4518030710015003150f070b458041110f0000801d108645480d054614900d401a4007485 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 208906699 1250 208905449 208905461
    0x60902070f08030c1e0c01051e1b0408011a04150f05330703020d03090f0212010e030c0a0209070201090201050304140312130c05060405060a0305090102070c080f010f 73
    0xc070340126103426a5188040e6074005000c2c00c0703580c032042c0690040001c0c1441c100a20318000700720a52103150990711a800e562003d0500c45d0240d5140140c000886aa07020095010010310300c0c246041410113840c030b040d4815608030000c0307035080031008000403000c2c600313800c546c0b28203580401142408414200881c4814007807101c1a400d000d00400561a00602c00301d000e60844652096459002128403d00c04c10a52030240d010320202e4588203240c2c061010360003050107800c1c00e1110300259a81c141c07421281030802440340c03065045c246c040040950000003c1caa01c542181d42e5000030a080d41d54a01042c841284034484080010710418410f0041e00e500c5503060b140c150542d00e031542c0e00d18000c0400c1c0c45980c0e41c1c0c402804601c1003003181241950186640080c00c12a40310b884c01c110a41500580045011f21000c10040040b511040122150a45107203000a000e1325070310b0445019118a01002e400500700b14070101e6a0b40010843c0071242d44070300020451200001041e1058480c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 208907949 1250 208906699 208906703
    0xd1a01080c040905060301020409090c0603060906031505090a12020c0301050108030a091502010b0a06031e111b1c050325300504060204150c260d0f0b010306090207 72
    0x1c140000c000c402d030f064000301e0304400000d0000d07062940782e0b10450103ca200520941d204250650304124507a0580b046030086c3c60400c40501c03800381503454078800c05c5e0588400c10049030b5110b0004007200f01c1800324a100c3c50340700010104c0184e810800039a5103854138511440b035480e10000140280d00007040380c1d08644640c584900103803400e17405036050b0a807140f82d00c042d03548a102000361a650440b40c500039047c1610009141c140322605074144502010b041d40304a454001c614007028040070542d8070340b6332000b40302031203021404020303424500206840508002c0d004400160b054000020314480c5011080c10007140700350b00800d80300821440300300300c08650307080b0724081921f800d80c502c185904540c5800c07001c8103030040000000c40301c04540039106980e020500340200700b011804c126540b8854a0401d00c001259103d01c01e407012082501000942c14015803209134a001090311030440764150304014602c0c410460710302821060808500081c5802d401180c956036501c29200c0b209c8e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 208909199 1250 208907949 208907971
    0x80103050c01110a060203191103041a0a0603050a051c08011a0a0306050d0302010c022a04051003050303090708060c0f070b07050f0706060510080c030a09020112020d1a0108 76
    0x3941c088010b46503076040b010000c90310300500e1028000301e01c06000460140e07140b441c2e031b518058450580b840440d103140f2170300b900c04d0303400b0018040468051035900b400b03400c0c40d8440c3c01090302c0306043e100003000ba941c001011401410f151405000000c2410480032600303201c420000d183c1990304a03500f4038240110b07079a0040112074001c01d02c241c0c50140c03040c141301d410002110340e29800000c43c4010549800c80050303464040031b145141d81071051840c241c1ea1000344021054101140b0343c1400c0c44490603c1c06159203400080105c2c0d20400250b000b9038100054076030300d007440700304182c56410f80c3c01142002c0c42031130007003000c5030041e070b040790b1042a045803c10304010a568a83e250040c02070a0001081414891508a044128000c4c50080e01c2000c001565510303010034440e0400b42440540709010701441004070b210540c0c1c1c12030f42d2089803a14005202186480140e806460540d04c500c612840401c0c2ca180113072881c0d11030385021454528070076a0505e620300444080008440b005800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 208910449 1250 208909199 208909213
    0x306021803160e091501181401060c0201050c010b060f1305030303040b070302031503060a020406030f0c0921080f0406030506030a21140c0c0108011e0b0a0309060501170d08010305 79
    0x304000300e44107810030b00000c1a035150301c00019401840c44020b81011356415240e02c4641b01f40c0c40740303105015080300c038400d031070307080c1c3d032419801808180f100940a418040002044000a103080d40f00c112801c50041401d510f519070114410144d4001c0e102c54407180b81e10082c08a0249800010303a840703242d0080015009a55820049000c1e40015001e5402c83c0c01d01c1c207401009a40034041107104065030040140ca40d80703081801000e9a1716000407410391807030085a504032561003040d10050f98100c40580c0d180d0300c481d142d5026161a0080003802c0ca0350302140180c03005210344020000c076800d50f070b000c0c010381d1100003c01d80c60b40c1ea0060010214082032500b600ca024801081304030f41755032418041c2000c16250142c06c1598408070b854940ca170005d01003010350750b070000c0a0300e002d040f000c408102c034120350765250004c0381b41c04e01a01c0100300d8041003540d611442034014950955102070144019651505540d0000440856042d2240500071420307418510400704d060403203030000010440 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 208911699 1250 208910449 208910459
    0x115080606090418022e081306050c12151018090c050403050102070606030605010f0803220b070b0708061e040f020c06040f0201080a0501060e01031d0106030602180316 74
    0x2070103088014500300a0410395000941d55030485403600c0b41b003400910f100d41203d40c015040d50000c000c3c881c001c1c8901e10007440464403980d0001d242c03c690011000a041e2a00c80d0032800501456402c015004802c00402002001d600a00485a48240c40003030345049040c200b550340c505034088210440305546010404030007103030007080140f030440c1441880d0941301d8031101c0c2a43c0c080c000a81e40c05071110300c02c00800c9000e1107a14010302d22101c6210410b030522102c15140d02c9040204090078a802d50220320407542c107000c20005100c070003529a61005649800c9550140c102c0f0142d011a07102c40c0015024100244015171880e035440c44c00a00b0300034041000700500c1a80b60504a00782c1c01d000041210400700300c4140594003451008440c40e15a100041540000070980d0350581c0c203060040204540100c01911a00d6003400c0205080c41d06105980c0d01c544031480f042a07560030840000140409a40104950b400b1152081300702c0320300c5001e01da60b80c6c040c100000740c442840041040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 208912949 1250 208911699 208911701
    0xb0a0207092f041206090c050103060305030a180e01030303140c0c07171204170c0609011d011e050406140f0307200d0806130b01020c010e0604030b0c0301150806060904 74
    0x84441c65142c074182002e80b200e0302d401034513040c080b0880c0e51940d5101c40d0000c0c84603c240d045c00a11b170074a02440b0301825030b03075102d84900403054000103004004244110080c004119000a000c907240306000d103607501c0c00d00074080e1042441c41e0321480d80c0d280226083c1c0801d03404855010461000400c03c90b850b00b08003201100c00304001ca40c15000b054190039820300030701e0060000f0708141085054941c0c0082c0700c030b405c04401480c124841d4030300300803140c190398021000c143d0401502e003070320b0030f502c54090050b01c90000c861000351101c0036000d040020f0355080720160003500c0e510340d00c00b0048221501403480c40d1091200c8040344001c2440001d1050348a0700072000c1c914040c00303940e507015959110686c509401904041c1c08161400108841402c000d418084601d00b0050705000741040340c400030303444a481c01d52850401c00070807241d05450301c070b4008803802150700554480702450800d0042a140d00b0038000e0342a00c0c002988034803103592107048014000c800080c685480c3c81c4001301040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 208914199 1250 208912949 208913021
    0x605060111060106140d021308030403020a080304050108060d1e06020a0216360f0902100503040b06010f0e030f07150206040506060d21020a02010905030a050a0b0a150b0a020709 78
    0x400140d408001b00c281e030300c8d9119020001001c0890007913841d9401c1d4410401428a503401034a000c1d48140b204003c50ba034000c80c0d1a40010003940c10503a00d090908082102155152401100c0c010b40151b480c2040344690041098050a60968a66200d40d00701600c01c038402d44903007200da04112100e951b018501c0c0d000a16070508019030134140342055146076040d51008524044590b6503070045a0550800520588030380103507280079403940c600390791018100c0502070821410891101c0200072030a002e074507801124000202102c080c14942c0041c180d0f524500e024443c0506007201d40c500ca8103000160a5008035403040142455603035503014400e050003408000d83d41c10b0b101c510020101c1c2d018080c64a995075050303014200c0902c0034000584208030603440640641d124412180c081131020036a05101d56125200e5405615880035580162000c0c08004125003500e520018640d02e0b482c0040481008540a858070705940d21200c0040320980c082c2c4120030818104564040c0300e10700303000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 208915449 1250 208914199 208914217
    0x20a09210b0415150f030309060302030603030a0e03030409020d051e04051c09050603151509060720060301060c050d03020a0c1b03050f010903121a060d18060506011106010614 77
    0x640c56200c0c041504104c001c40d8002ca565184941c0b00f807041c10f60002c0e000300074100c5801c040d8a14100203000c0ba660340304400641d81004a500000002e903039050003103900600aa490a41d1240306600446005180130346491240e031022500f1070924660890510340300e80d8002e405041021114886c203803000c1150300c071003c200088240c010800d95180320246010b800c3c004545a103818800c001e000f170b0030027010344a00c1038040c20b0041c540d941d41c50074212040d13031380d00800c018928075030b05070384048900800d030050798082000b00012440580c0506000d240b180218201d40d05000201d00031313012407169442c08000903580380503100103d10122a16034250b10380c144c41180e0346e9902e848650408485048400069440b54154024150700041c5065820001142000f8031198400300300680c0000e140c40e40d005001c082440495122541d2022078617080c2164031550b06855031030701c1c1000348000c84010703011070b400c0703030301010401c0000400703a042e94143e4941503151900710b000b04c00b0f190030041c14 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 208916699 1250 208915449 208915451
    0x50109170a050303040f03020c0102072702090307030f0b070806091605070f03080106090b0f160c0902160c090207110f04061205030c01060e0c0301090207080904020a09210b0415 78
    0xc181d002603020801548a680504003110f11018a46030080c2007503001462181154407955007488003e142000f03c200d00d10902c00344038000e20446c04084003034047c1611185d8180500c103c00001d1001d00e9038502c0b042442081010100e6942031b0050700c1c0790606542d026001880100020b03800c90f1859042c10801d02242000c505140490350ba810f440c1540d110b0860006010400400c16550040c4a03080030344220074034a4180080305d10344036014054200d841400c0300f5060843e1081c04003424495001d0070030a40c00795961000c14849aa0650100b83c00f11100801000d001420030386c01c2c42900c60759507203c0e420610f042d24400400129403c0f1129180d40290b40d001e000583c08056881641420320507406076032121851401903084407965442000001d000c14100f1901e1905542203a05407031621800507103d02c8242880c51150181c000d005800c47c0c80095000e1045810886c4e01017204d450380c500c1e03402980b5019216001401802e80280402c01c0840818001880201100031200000d88 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 208917949 1250 208916699 208916713
    0x3030a0c140c03041a120a1d010209031507051902070e070516152318011803050c010617060a060501020d020a0206030c0d0908030a0509011103040209041b0807170705010917 76
    0x138608011b50000c4d039540d5030740741d40d50482c030b60a0382010b500d07050403e1405000710f00344044103011a441d08485100c4081004101c0f0010f030323105004600b904c40d4028250b8a4907440c091a179006540e072001405070380100e00c00c680000750410301c2401140c0d5a0801d001c01d6180700c0c1c43c0c0c0d995001c00b252000280400c0a620b03501100c2c06001001001100001c00c4403c00800d420036004010955181d07000d07030740c5c069042c42d00162480707020301c11030740515078140b03031280d40c1d504880e29a0b401040290810464680d1003100d60309810400165a80200c040704000c1000300c1c1d07a00016a9104214280345000d40c114541040161811034003869220202c500146d1030060721345240382c12510303042411205000080301b44550f181c0944035842e84190307110004c1018050b0040c0d50303102408024002032040b80c042000908100f903030b00640c5d0f0500c940c004025800b90f19400115210b14490060300500c04030541c891014401c0001c1e4402158810b0315202c85840c144010500200d4a0602e801124440d5007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 208919199 1250 208917949 208917967
    0x1509060b0a0f0518120a03091a1b010e16240207090b0109090e0604030908010501030f060b0111010e06091b090c07030903050a0f060605030114070305090109020303030a0c140c03041a 80
    0xc010405c005208006003000310388524000c2c0c1b40c42c000d60032452034240640100f5020311070030000c440c0c583d0200b412044c0c032034000e07200103809011003a0341c0c10240c0c0a2880180e0b182d61094003917509072036080030505440590f1301c10080501c3c2c84003c0345c20042c2d000742420030244a81e0b41c05210340c51010b161000c0b00c142c0b60b140f034005a030b42e0890220001e07800340301000207160b070140c8a90054107404000b889603501d5922406250f140355000508019650301701c55220760b0083c4421411500b1502c001d02c0480d4583c1455610ba001c2280c1c04025802449100d030141c48410590108100d00140710001c2921307602c14451554010400880030300690043c08408100c040004040c01c5100724407001c250b90051030102c2c1518110380c010740c040c0c0c9c10708842041c6080b004100c158055040e26001445540b80b0342902d01400d52180d020790140000010f104440f00541c01c2949248016241e41110520b040d0061000707200312075244540703800500c4240b0154103d005501071821088074810b00748504e213 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 208920449 1250 208919199 208919209
    0x10c0303111b060a1b050304081c1503021e2101091407080c0d03050d0e070b0a08060306011a160c05040204140301110a09050d0f061509060b0a0f0518 66
    0x80c00c0d01c02c2d45921200070045a1001802510504040c48004c1c43d03c0e010003c00151990001400c01040280e010030700184201005041c650921400c80040c4580d407049d02c503c0c0388100880c08161701501c2a400b40610510849103945020030303014100d040030303241215051040300304c0b0105040301e5540302c007481004a5902d600416404035040041c00d459490803806600c1c00314544100350181180d010b0002c0070a4010064484980552001081400c44081c0740b0b41050b8a07900010b4100802080d00107400da072140e420340c80b41405404803041c607621203c6911041640a802200c5034100704404108000c100001000c2c80b03200f03d4407055226160b100180690300a0b401c81e002c005c0c2503c0450b02c040c50240500c0c000481d2000c2c03014a0300c011082c0080060401d0b018042c042e0340040a00420440500d4409034103c0d00b000c0100040d0041213001c2c401158940b0481000600b046400310301c101200088994144240e00c841850002c2400d095071180c00c100d815200c500352403c1044a1601e46c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 208921699 1250 208920449 208920487
    0x4030f1109070f080906040b010509101e06031a06040303050a11060f04051c0806120c06040b040e1b090d1103070902042108070209060a0f030b041103010b010c030311 73
    0x540d107483d0070280c1006001010b410005082c254243d100f02c0c00d0102284505004a0560f007064840c14084d83c0d450454200415856100000401c084466003c1e1500310303806502c1920304940d014008400d0304069200c80404296055522410400040000900a80c01030813100c001d4240506460b0700d280e03801e414504200e8007890040007080c100000c101c000d000d1000581044642c101074490300c040010560100100014000c0207260f0020411403010007646000d01002071803ea038881d00c1d0980450300380c00c1480707501c03440d00019000c03400c0080f0b0200200c2300010380c1d03909a03081c0b00ba1b44041290307640088500b9a8422040c1c22100b034141c80900c070b40000b6103407819015030b83e5840c22007035030034045007686008404c0d80c0c0017810f03d0008602da41200e80264040355808c21030340b01c01c400039020318035075844a81c101200c15000400c001e6004400c03440b950180302c0001404a11320185402d81d2421516a8002600e020700c1d4400a4040d50041c8400105c1403440340c10115000c50070340341458 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 208922949 1250 208921699 208921711
    0x504150f0b030613020309060c0f0c1b100504080a03050706020706020c1c03090b190605030f010903090501031a12030f0a1119120e030102160807060f020f04030f1109 73
    0x3070001c200603890801404644164500c11030451030751510044c0551143d00103010540940400504210900300f114140c41c110000740302541c004a00740030360004240c4d8802d02d0580182c035101210580716000e0020382d800c84460343e0141401c2500380c0d408a882d60701010080b02d13510750a112020100b005031000e805404000c0d001001401c0403009040361300703411810385004040c200814500040d07420b070315203078000380701c04001e9442d1080107848002030605604240c1c0c061040e00c1c50031040b00070542000903035600a8481c190707a039481d000110300b541d42c20390541c1006203001a8140e02e0303050040c04141d0010107501030b24140084140854200c1d030040302d050700002d908400d035100c00c0e803040c403440c002c85c0004802c40c281400655a2240e001350100b400c2000e000304284218a241c13029011a1401c003000b03140d82c1d89080c00d40c546010301d174102c9081524030394540307414101250318520031540421803a230211420507103180d4416101c150441401c8480d10301c014003c80c00313910b41c3c80740c00340100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 208924199 1250 208922949 208922969
    0x51606050714030717040501061502030301030c06090f03031b0c060c020a080c01020a0f1103100f0c0309021e03070b04030b0106020f01050402010c030804050c031005090708030c06010504150f 84
    0x108040c00300810651154440360b00200c401c1050020464100e000ca0b42c400250840c0445166260f007003090040980381d00c80f40d810340c0d54a400c0d0800c2d90780840154140c9210380320072004241c65070811601110507003d03079000700c0200070302880800d005031800c040c822801108550b00d0101c41c0c0c2e480c4906451075211001040c44204603104510b040b14102002e880110000e14480c803140000075510480c1701c6014203940700b241d0502091000240041c40083c4001e4220790910827200d101070300903c45c1c007610401ca113241a80040c00a442405030340d01e8039800800c810503004652405c0003140307884850255052058801c0007601d55040d40c0988001c6000740400d9000c7d614010010342400446410920264900820000140e030489040309406805141c880100d03075071850702034139000c408a0105d80c5440740c01ea0721110a030054121034032a902c0c61064800c2c10307a4030340c00b955a9000308443c040031600200d0052040b424154006280d4402204050780041e9480c00480c60100c047d8200d00185 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 208925449 1250 208924199 208924201
    0xc100b040605090606040e0c13240e0108040201030e031218010c090f0b03190e0c0f0d0f15091202010e010b060f070204050604021c0504211d0105160605 67
    0x346424454400140000d94040a1520700803001800c144100d0140382c5400c110680802c021040d0001500e45e00c00f201e20510803600d0b200c00c00031410607126021142003c0e1100c00c052a1148180d100f00c0302c8010686481515454a03401500034141421040005100510405c5190001540c10034001c40c85c00300c024811002d054802400c1d20444960a030500c0740c0440200006440100c1c0842201e4801c88240c0e182c1c3c0780e141007418105106080f51414a08212003038035070040100f100c000b143c80c1111441600805507081c050115414134024140c0c1200b5030707000000c645040c210880c03443e41c80e08002240b01a80d81c640300b081d4588901040103039503555001d07031171800034447d03550104411204682000c1003868403244921036020028021900c4401045444c0c4858054410f001150101d901c402282d60072200018203003242c003550405651980200b966100161604800c0208e44d50090384c1d12551203001e40c0e0b80c540f00c54140c1003040402042340b004040c1c10009041d40e1040e20302180c2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 208926699 1250 208925449 208925471
    0x1309080304020915090103120309020904111002010b03031b07052809060506070602070507090f02120f070912240c030b0a0b090d0807050102070f15050f040807080c10 73
    0x44200c020140607081c000b00b40180344c0781da500341c14181120350001c1540b00c203180f44c4000b04c01a0441d26002508014003406210400540c0c0c248007c0440c0c059a103090882c2521381e00302c1c283c1e612900c0c0c40b505034104224001b00c0071828000c034814062180102c0310003076621008903044154000c80b810204a400a039024902c004551101c0105a00e02080c4a5982440001081031241c42c900070002d660010f0b01004101d01440003500078002c1201c1001684105040305000c1d5000003130001c450002540026507004c40403541501450450b9100c0c084642454030440d458868400c054658083e060480b1000580c20100c0c025401081500400e202c03c0009000d0255040c1c1c20109105100107081440702c03900c1d0605a03586000b00300d490492200ba5818440090b1003680300140207540006010300900900d441c0b0154454403420300200f900c0414105481181e0301600d1071039401c1c6900010074003103401d00002d485442c2c0200100c40c680f6038480d001510b4140c88800c101c80300c549079424805 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 208927949 1250 208926699 208926709
    0x207020102101413051005040302030c01151a0c030403082224051605120711090f0403080c0c010203040605040b0109020c030f0c070b12061309020915130908030402 72
    0x380b0041c111500340010034106441c1d11001c1d400510029034070140c51202c2040c8801040210f40550b00c3c943d04004d00d0510b070800070740720b80c402e442220141d03081072443d0b2441d40343c42c40418200c4103010010a14011100150641540000540c0d44140300130700000c40440d680354000c109240b00500e002d0601c003000c1089401c00c03040c40d0300003ca01241c403040031520340761001c0c441c081c0162a2400c203598401221034010400ea42c0c081c00340440c8200c152071081682c90000500516001e000703120798a07600d080c20400c001a00301c0d00d08a903180d0f4040850006030280d9004c2e46c0040c00080c010b400c0c501d03e00d4505007240c2040720241c50aa440c1c1040c842401a00c0b0aa1405080400001d40c82c040362040382c10340c0c03031040010303c501c810400980600d203004217101c440050104801c070203690b8548000c66010158054403010b100380c02d2625980802e40a40c07107200080f45d03000d014110960390b003225015a0041c0411550740180342c041d80301c400440d50744200d29005106140c01e544900340303401805 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 208929199 1250 208927949 208927963
    0x3010c09050d1101031508031b0f070b0c1e150601020303060a060e030a0203010501030c0e10050f011d09090d08060907320d021804050c09060c0a0203030c010207020102 74
    0x2080c02903900003030056445039907a058015070030401e044a041e0280d00100c000f418800d24510081c0e0f80c0302c10101c0d0081e03001c4024011b0503030b5001c000d207590011a061645404403109028900d0340300000800242c2280b50141c103504450b1030030307111480800a404410001c20144595442d0041e001030340310051000820780e0044420310003103080d4070701800414031444003401504180510302c07054454a0760104502c20a09038054001d101a50303481c500280815110301131480360440c444001030300290000903003c00c9450080244054080f060015a1094405407400240340d056840321400c9480340c0c000a4050004c0130000c1c2108003c18000030300c05180980010320801c0c0b614280450380c0e52000c21035845181c484a140c42d0401c1200b80444880050305210034113620202c0c1022003442c2d190301501b640380c0400c40c9496423900c07407000c000440b40c08440d0074045405c10300141c0003e060201c040c20280441404560181240c0e40029245400c60407240440b41e400150200c2156410721802c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 208930449 1250 208929199 208929221
    0xb01030c09030c1205013b0d0503010b16060c1d010804050c040e0a0f051c0201020c0d080a2304110604030507050d032d0212090319170310050301 64
    0x30480d101c0c215683c00981c2c42c0c01384180313442c8040b03903486041071040039442500708004002e0004801c0841d4a150340501001c40340085031407541d8101c0b0410124003042c12484001103984143c41d42c2c0c24916091400d4014500c2400c0300d9100d400c0304400500d0500c66100d8030003160705e88900062491200ca4070440031441d500381080114002d01c0001840090b0342883c41504803004110000d40c614900c1c5012003100001c2d1840c400c1103031010500c200825220300080c003581c00340440700f40b0700d902607080c2d20444141b41050f611407080510240e101d400025041802d4410100380c1e51403072440d86904010914001014406803410301c0204000344a0006032013905550711410503185885541e251207082c407440740111805000b42041511688016205400e804101866910803d900d00440c1d0580b02e1600003510400320303034501d60000c202c20366021039401801082c24444c10f1f00391071407400c541c0340308480c05007105441c015401c0342140130f14890f8100b040c00e04104d901e0802007600351074000e842 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 208931699 1250 208930449 208930457
    0x1060506070309050409030203130b04080c100f0804020609041112060103090203061b04150203030711010204080a022101060e090c040b01090b1605011e1b05090904110d060b01030c 79
    0x41c032400a600540968121a401c880004035410141816070a500c2101500c40040c1042240410b002c45000060300c15103d8200032500961946414030200c0100c0c016024040352080780703032400031446820400d502c248041d11960401072a0070208007034071080c0c1701c00320f071090012138061154121802c00c02d50140742403038240944150b0790003003a16001c2c05860304ca10160709a003040e9007142c0302000c640080081d08081a0f404100003030094072a0000d0f900c94001620a840c0b021a51a0500035641a40d40c0c2602501c0d4450b803942c20001084501c20071041010f000e0b040304148114203209202c0280b0040c4803904041c90004000c60a00c2c4000d4051440349140040d488116607120150341c0c2640d004403440c1d0741d038446114064a040f000c02400030b04960911440c9011101c000c15002d40500f00710a01f84506440c806030800300d5200c80400300d0000e00103100420951808802c9160860300807056801010286004608c2c41059000d041d1340701f40c0c90b6011303000e29590601c40c0340c0442c00d041c90 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 208932949 1250 208931699 208931707
    0x50c09071e020307081611010e0f1e060c0c100302270402090907021612021f090305011b110c01020709020901090e0a0f180b06011214040507030501060506 68
    0x5806031004000748040305948040e8020391140c03034020400c49089a81100541e81c80c1c0d600c06030b030180c070304c80f0a1400316075404812089a071a540158181d52068100401400101440c402400711400701c6005802d1110a00541404103840c0d0400508020800d00040c01140c0e074000305001714400807903c40e80c00c040c4100607026041c4031414800780e4bc04820501100b40026200000d40030f40078001d40340b0341c07002c2c2c242c1c14082516000903000300c01240320920b0034140c07980d80328001640107a0000103074100041c003070b400030881c0700d09181c580f00440a051102d40c13161262213807400c40c0c660300c1403003074005109044109441d4014074507019540070300008040941c01d05c40003e4540100c2e01c0b40320011a008036200700c80c0d03030056280c40c001c3c000d0b040551000f403401004601c0509807200d08003072003524000d14000c1c4445d410003100c4003a0b40240382c0d101292501c0c00112031148203256415200d030740e41c1311075116410b4028050390080d070040005000090550030314908450845d808184545d100704 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 208934199 1250 208932949 208932961
    0x3050c0301050609190c0c06050702010507020607030b060301120c080607121a011d01030e0d0c0210141209012a020601050301050105130509010605060c0a0308090706050910030b04051003050c09 85
    0x1c100700c4d658000c5c420100e18082c800788291030f040c0c00848001c0403503080504108580c2d40c150f2041384100d40a40c05c4600c0c9444000064084900c84805690894010801804000e03849100307503420912564200b800d032030b52112114184003060300c600300050b900300c00e41301015816025400342c2d07400010342c0c540b0001d00d02c00080e0485025825030045240d8842c84003070142e000e940104807481070081994280d00740107400800b09c000813207080344141419000b608289110341c0c51581083c9864060524003c900c11041c031050740001c10619240d074032800300c46194500000c080096071028030406000a00300c2a029092400503007196000744c0c035141c01007101e90384942c01c40900c400706000000d0540c40c1d12102a026120700c0d0403281d000340c000144101c41c0100000e0345138515003c0e0f5500111501c83c29a0143c49e20301d94032980c00064002d00c04e0030040c0c5015515051040100e0800140341220000414199101110000d8a0204144041060040c18000040c50b00b208680303c402e245441 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 208935449 1250 208934199 208934221
    0x201809071e2112030e060c0f030c160804060504170d0206010b0c0f010e0303010315020a0e040f140708060406060c020d1101140f0a0f030e15060a0f03050c0301050609 73
    0x9101e1200c40020310b4225072418003501000c01d52250304107803043c95100c040715010b03000d8001000008200e104800029071144d50400607105688800d102031403441e141c004000c10b564000b94401020141c1c0c10099100003050313a00240300030001602c03203540300c0f1300d40720018211101c0910051860780000000225a070b50200300f06042d600024040d940341e900b031840040c42c0c020f00251180042d86030080c424440c007400006941202e104030442c0104503c0454207900783c3c0540c9540f800070522050131a0b40501c0c06402007101200c0c41600010742c1c07400040a0815031600380c60510100710118180300c2c1904141c0240400f400c8107042802e01ca61495001c15240031078003c010300700c200d00345004409607100b0300320301e01d28010100d0500d4580c21b031018800301d194442d42c80c800100e0382e02c10040c00c250707000b4003e04a4039240720014000300c02482100214500700103100075400650a6400300d04010020b5112000c0c502034001040c0703c0f605c1c0e0040c5800c46101074409441608040d04001c410011 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 208936699 1250 208935449 208935509
    0x8030301091b0f02121317010f0b060a02060106081905180c030c0303040e04060b060301090b0f040e06040303150b0a030e06070c0c14011b030807030615090320180907 73
    0x620388000c1d95010301098600306c041c40e0b034024102601503e40200e00046054126020fa80c2c42d02000b04240c0910034204000d92140e01c0a10001d6044900108882da01580c101030380245109416840c10803d20740600031520201d540526404003c0724100d03241c60100074003012a0802ea000701000d00518000a41e00d0103940304400f110510000060200031494001412007c00a03210036101d52b180e1129102401030381c1c4007a40501020307001d100c414a840d000d0b0140002d800406440c1c20b0f00e0315241100584444d1250150b28866480b001584031915802405c2040182e0342c0014141802c0e045241407a1020308000108043c198050f00401c07002403101044598460344009401028001030710110a00590090f21900300c0019a09040e00481e82602c140415036040240c10b03158505440c2c54402d6011010004010f49414400101380c4010840100d6840c0c40e09125515a407000915404110103d047c0c170285000901034030b84010050707500a4005120002034801e1201503085d52191 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 208937949 1250 208936699 208936723
    0x5100821070602040902030403230a050301140f12070e0a02030105031c0216031a0604050408090616050d0207150801031e031b0b070e041404110a08030301091b0f02 72
    0xc4002807030000c002603035040f200140200201503480b0310b020b0034040d00309910078440004041641c5c00318600071502204541025409864403801d59003010304000315807a4482d8013075000100d213a00f00c000b81e5100c802c4601c00e0085200104500d80c03d00b01c884500042c050080324400f40184014800c80e500400d41c000740d4602581c252480c0010031204901e008813002980c010300802041c04002d0100021002e6803041c1004d26140d01034981e8400d0004640007140c026007c584d0a2280404919100c001070083c52000119186a100c003a01c5203030a2103440440c42025a0101d03804200c14541d1007200c0b0004003032030803c40843d625545861a240100c500d2800050010071000d80405000d5141c2d10003242d9001092001302c5c88a00d013180c002e00301543c40201083e20242c140540e40341600404076111412030000c8001d4a40d0790722707000302c01100c286455004e02e02c068040360a150170005035008104022010880d035190034400c01403021003200030000c0058140110280c0341e00010b001030a81 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 208939199 1250 208937949 208938013
    0x130207020d030509011709071706040c05150d050112111008070807050c010f06030605012c06010207080f0106060e0d020102061f1d0405070b070c060e0d0c0801051008 73
    0x911034012195100200003c4006c81d0401007031001c03100e000150b01c03040d170b000c0454001305101d00c109450f81d1000100e070000c00e105c40418080c442c0341007114405d0f0808007407005c6242494030760443d213419240c09130414202c0c40c00085543c2c0c1031203000c40148203102c0080d80e44840c00c040821008019a40040c941c2d030078001c840303000c644454403640460b400c10900720001c1042c2c284c03840d0104040e114030b01c0291509801c00300081600540ba520b15403070708074400c0181c80300050003040105c80440081c0b01a0540c0185103000950100601061040c1c05030301300001001c40c24404042e0a060000d62800d00518420242d41c0060f60002011034010508400c2107440c454250304082211440750028603061003000c100c4040481048065406248243c0a0b15101900c942060741c0500402d0405000f600f500030f03040000d40e014050300419480090040351088840740c40d9603210311569070141825a65690411a584481d980860003a25802c005002c603211813001540c030b11050994108508 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 208940449 1250 208939199 208939207
    0x11d0a063c031a0409081b0304060f030e0f01020307081009270501110d060603050a0207050703021009030605040c0302090f07120e0a0c03050105090f0a0213020d0e060406020405130207020d0305 85
    0x220a030403ca0583d1a08000c105101c0004545442425500040082e1070070b13480345840c039442e0b4034000c800d43d01510003070365a20f64449001902180609006405601540595443c0c15400c230705c00c1c0000d522030801900e5202440c00c15450150400c4a107070310022000380340030f5004403030b004004c0d01070320100d12494540381d1160460601c540140182080c80e8492480040c1d2080624002d40080742105c0c05618104000d90f03503410400c007a445403400062054009103014401407801e0b42842e21101000c2c64094840784d10382c0e5480c800c880c8140e40070760b000402510200214a8807807030b00b56019042400603081c03420003600140021325200d034400e9030340f07464400c07140034110304100f44220340360065401d0340e5881c1d0340d0400703d00034082a01c0700c684600810100c6601c001002545a008560140400d5100b11001c11040025000700c050906510f0f00c8152809145178204500f50083d40621070044c1d940c3d00c0e182c20014048020841980003a0044c03201e04003581e50108044115a01424003a5032 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 208941699 1250 208940449 208940471
    0x91a0301050909030d060608061e10030509330105190e1b0f0a030c02070e070509010306170d0f03151203030b1e0a051509011d0a063c03 60
    0x4c41c084d66440c005d00d00d15085000489607130003004030b40641c0e01903401c02c030740191480980c0d00107815144001d82080705400c80d544540c0c8240e20070350b40000e8541c1520142080c0310f10341c292030000d001030b400014552001c0800d0b110000c51043d0300501045812a040b00107120350301054244030700c640341d200c42c580b2001032814044001740b403085106030446280e948400c00b0201d06541c100c03182d4040087d103880c3d0041181d900024000e4161360b100038801074140c0d100381040301c03030360300107880d00d810035440310000105020317070a000740380038003900d000341041e100c910310020030300900b85000380205030811000303400d10401c1c904100151201d1021805c2c0c010074604040d4094428940c1254101051003c3e000c3c1201000e4001d0700030f90030845903145896600c000f000f036032001021121989810400ca022420b6020301c1200c01024010208603601d441882c0004580c0500c40d40454086580f0407511081500801d00304038218081800d90b4003a2559003004680c5103609014090a0507517074150303255 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 208942949 1250 208941699 208941703
    0xa0311070503071d13020105070b101a030a11030618090a0b040b0a0b2b0f02150c0115030c060f0e03070605120a1b05090402040b0415091a0301050909 66
    0x10707180190803500301968aaa180d1541c4041074020500072a04001003402c2d210880c2c01041c4407034050b5555401c080a40e140c0c03c1c1c10f80409010301c0b2440c4440c4500041e4600002c906550900040c5001600c030710b032000500007910314940a800842a0800030010341d0340e51000703a507d410484501e001165a10340310600e1802089000103080320650b9020401000071800046201e000c41c8101400340486200510003000300300071a48021401c0d0721a044215421030718480c40c15800f4800c9a02440b010b50041500110320001c402010400040c00c0c10603041300740551000680600380a0520742d01d140c0718010003000c20302035035041200b0b8664103081d60b0321034510241c2d141d40c000e059840c855503a10002d0080e0744502e01c4841d03030301c89403000114414030714404c0c0d1040c090820808802c000b1500002ca90700d6101340c281c50b41c071590030f1001080c040e601c100980060180588003400049006002a000701d415600800c80c4850048080c020301c526281580c0c11100c00384c5045201e40c90b040c0e0094 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 208944199 1250 208942949 208942963
    0x81e01051c0c090905030405030d05030c1606090f081305121b0303040902040b0316030504020307030209070309200f030303010f090504020604080a0309031103010e03120403050c0a0b0106021b030a0311 88
    0x2800d04004a500605c40f020000300203e030f00071804c4803c0354505010948050000b05d0311101489001d02115100480b54441d000b01c941c4240800140d0540e59550341c803210003003804c00e03034009102107648222003102c2ca0381d2002400f402c41d9031030018081510705603900d903400c03422041c62402800720100c0341d40341001510044c2c405c0010654955481e02d228000540044601d28518080c0c0c0350181080d9020b0711482e406250080c1c040c1a80e10b05540030700c1030301c0a0241000f010103580e04122000700700c08021303c001d00040c00405100010300007080048140603465181e2180c0c20400041002c02c3c0e0f00300c1c0c18001c454524134081150350701c030b0000840303d010b241e20142040c000d0b480c41c003041541c4126413909880c899250304e2018000f00e41418201c595010071905180c0c07003007184800001000b41d200b640326109107011403402054801303190500c0a0102e00312400d000000c01801010380511001c0402c050040c0c0ca0080d101e004000a903980602c030700007400303201c8428403042c2e91090078401d031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 208945449 1250 208944199 208944209
    0x10908030702121908030a060b040302030c0907020709021b0706030b06030403030903091503021201091808090406030215280e19261005010e040b0a0905010c081e01051c0c 75
    0x80b03404c079482030a203407019038000c444ca1903220b80b03444004146501a1010340702a60b8011b4020403031204c1a8090200a0002429450540c443c046001031843e881d0b00040032040184842d22000103440d036061441c26125412901c20305007001103a400d9500c4010a4070ba0103509450301040500e00c504059400a410f07410440c07510090180c19601903800da00108030760808100740092603030783d0f5803055044441219075041251003155409000c102250090324820303100400c00501d440c1d60b40d000078520b91080600f5501c1c0040818911490700b03000185007e90f803420700d4075045421000900404484420000c3c9106402c5d00c0c00203c0d0100d1101040c1c806000c0c108901c1c2c6104d2440c95800c4041855a25012028410000e2680c244601809a0390407104039010440381a11240d9445120060013001c00007100d54442103100410340074041d030031102d0f80b1600c2d101c0315810421000140c03c3c4040e08030120b0303c0c0c0c907400104020746407001c0c00510105600079a1a005000e80781005e0801c05540c44 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 208946699 1250 208945449 208945483
    0xc220b030a0f0b070806060418021606050f2401050a0224090d0c120507031e050306090a0b0a050f061b030901031d03030406230a140601090803070212 66
    0x11280c200500709182d907810310f006181c2c01c400c0c2da80e070b603108440e0420101d810b95000101800104814500b0000740c02c1c1441c81c0c841c01504006001c0406401d442c6800c40c00d0303991a0316901844808818401843d41040002001401c43d540705007551711056000901790303040000020322896118400e105480030040716142d4041c0700740070041c2c443c5000c0b409a410f01941d019100302080307003a0013140d501e8640d66010003500c6501481280580e00c54124a4058007400075203101c001c18010540b84a2040820540300d96403a03040001c203114614400a101e10206413030490719200d02e0707803240000012240300b100c0607619143c600f8089041801210800d0013851900074002d000902c020010745444034080c0d80400c1040d150002c1c6407010b108035040319002e500100045400724103c4e81005110146552003d80d4405110ba16041402800c50b41204c42d15503440700c284d10824429141c03500402c00740703401e6542d9801d100b079094a0b80320b1400001d1240c0c20003168540011001d200300d070207402281722 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 208947949 1250 208946699 208946713
    0x9060a0909180203071202090109090804150503150f0105070209060f0a0b120606070b0115180e0a060b04150c0c080307140c030a0c06050c0f07060302070c080c220b03 73
    0xb400102e045081c2401c0f8401e0045079030104018000722020000243c00a040c140c0303591038101094000c000c140001d03502e00d0720401000c2030f0344115444001032800240e84441c0d072440c01500342a880030032000498840c001e030130348035603051303900000780d68849030102d40c2c55403541c44241c00034080740200002250422451400062484800c00180c40034145042d0700e10b0b250340e200d030108000703841002e034000c1080c80500014440001c000d512840c07403803a030b4100620700c5281303030721202c0d06e945a07a8412800f04400d0020407507541c43e9402070400030f081c0559083e04150030098812080c80f046400130080014800e03400f03090240d0401028000c10900b420380f0740e04d20171030074503100c0d071003009413824010303c140a8902080e040000e04400107a41000f294100c03541042c01c110f519900c040e204544907c00c05501c1c10b03503040c3c12702c134200080599071001a581c031502d143c0b12020003180e034412000f58012a40140c080c1d1200351071101101e400700d0500050800785921b000081100707003045070305482074503 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 208949199 1250 208947949 208947971
    0x200a08010204051c230307080403060b030c0109080706050a0302120c043003110c090711010c0503010f050f0d0803040b010f080307050a02130603050a1514070509060a0909 75
    0x360050050714010b603491a54180c460080e141c1c4481c203004010034440c101036005c42e90b8a503e4580000c4003500340b06583c6449025202d2501d1500903400583c2c0f80c42e500c4502031158a401c200501260100b800c3c109020761500c01c8050b12400c0e039108039010710500240d080d4940b84a0350441c0c1002e40c5d50140303400681462402490150040e0007654a60440c1e10302c0120402c034000004081005c002c800042d0049540d034080301e210140582c8464a4450313241d1011180e9100030b100741c8101c105030b50b5404991f10032000320b400c0d00c13034414070789003405010001803190700400811403090301c10035100c02103940c80d40300c045090085994406000c01c00c0200a0204119441210a040b103aa0340c14a69041da110305031039441c0d05c60014000e001340d11042d0b400b001402c0c05015180c92103c01d00c40086d000395680c07a5241441c4141d04100c5440604481d81d460b50b000503c981c0c201080701101002c1185841c0360040e003188200d4404c1441000d001c42c40c40c0b5540c1c8100700030409882c200c0010b0040c0c000c09 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 208950449 1250 208949199 208949201
    0x1502120c030409060b040b0f0d090210230915030c07080406030203160504081e0c0406090e06070c030f03050901110a0c110303030606040504020f070f0c08010605030a0b04200a0801 79
    0x1802200c083c2d6007000f000086103c519015542940c0800840e0340c035000c040115201141d01041c844414941c4840340203002d03903070707040c108030b41508142c03910f02840442100740a140d49c90076108400c0b0724000d021300d03c61030f00c0780c0049000c020107030410180c2e251500440342005020b06071008000c8200090082401541600a1401403c003042c103007401d601400825079443c010f50041101c030b548084949d040704060301c0c02e980020b030680c03029a620000c454001ca030a880701508200d0b1503584814049030102c0040058590180e02440c0001c50104070380c1c1c008280001125001c410540c83d0030101c0c401c1b400a40c1302c164020400d1604d02d40e94030220303402401141d8420010341d44800e9546820141e814040100c910441300103010600c0c103400c1a081000039003003041400b6041e070050000da8001860000300070302e15401000c0202d0707a1071400f000c031030a40c0c4180d04428003d401c03882d8244001510f92920342c1d0040c1d400b108181041145040400021980c1d15040e5849903041d08006004101 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 208951699 1250 208950449 208950457
    0x11090117271002032523131703040501110309011704060209100f03140c160515010b0301030b090a02010507030e300706082401210219020a05071502120c03 68
    0x78840d90003c84040f9682511101001d0720341b660320f080d031214a888183e42100040c102c0446219080d40e64907101c0c01c0c030321965070003814200106e520000701841301e9a04043d04020304680314000f54540788903080020a4902203140c02102210400085010401d242c1c041e10310280700030300a01c005c1d900107280240704030251720a0401286c07a121244050b640003a100030301c1050100c0d440303441c081010541158440c088041a9054000c890001102c454440300c2c40b8000d20354074500079102c0d411070400f840000c2001e840e00c40303182c0c80101641c0040c5d07007081c2a00c0300b02c1e4160510701180c04e00c1d040800c3d807500c02102003002e03600800c1801d5240c621a407000f071f03a0a690520440e41c400f902d074502644d12160546001040c03a50140340043c40d81c0d030140c0d492444000601d40b404403030a40d0400d980803030062500c800030308d03600424105440c5801e0101c500d00c0d61600e20003044001802d4844a468884501541061449131305007441064000c0081d0914a41300c80b40040d40c450707000c01040c0c1c607608 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 208952949 1250 208951699 208951741
    0x16030c02040f0905060606090105130909120c0c091a0409031101050a0902031e151003030e0f0d061d1203062e030209030109061109011727100203 64
    0x2c503114000800d0303501403007030b048071a9000d030040072281c690f681000340c150002d1441504000c400c20201c180000d22508460040c56600d201082c0340d07041d4584034650a010b003003918100300b0f000801c04049100000b40404540d880c020000e00d504211041c0c00040322114042504070781000c443c0c2e810943d11424a00460001d0f600820a5803550258807094500d40710010307505900003042d62030f6480420070200e90b0b10001c0701c2190030300300a04000e00d5440000300c451301101300c0c881f4403c01c141a00005024800a800c0742c460044101007000519420a481000707401e01c1e41ea01d145041065100600315442000001254049030302800c030026507034070840d540380c0124004d200c110362403007c0b91001c1c4001c0b0079099030038098607a02541240290461000d0907459900c03403400c1c901050451003519005080c1c200c000f07903a51480300025004802241810004610180c02c004041d080354400c80381390325914104000a07425800b43e40c3c9410010307002c0c00281440041401000c62501c008658161 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 208954199 1250 208952949 208952951
    0xd05070815060405060406030e030904230a020a091202030a0803150a050f09070c0323040e090c010203160515010e0702280f0320010506030c03071a0304030516030c0204 74
    0x822a002844200d000f02c2c403800307030420700a01061100c07a002c0d130400b0220030400c0301164286402d4800003029120300c580382e8000034210381c0f0b420400041c004006903100c50710103800d51400120084c02440f2005c01d2043c103001001030203c001c1159001c0c440701000e250404a0680c0381d0030000c0e500c009401c101c1240c07900c0340305a4140011a8200030b0358952801400416a000070ba9a042c02551064a640700172810084440d4190381c4146002c50038201d03030b0714007044060303c079418050f0100074180c000e41038a000f80e01c20342e883c0f800c41e030380001100c80d05490385100440c0002945810780c070f0400c00007103d0604a10a60000c203400f26000a40c0c4d11500c6942c0c215841c1d0b034010380c0c1098003c02295a107050b484803112601c40030a48464180092904c03c1c44d04401f50100901210f0300e43c2140410384a007039440c1c10620601e890204001d15851703204601a008070b51916800600f9560300c12880700d1000302c0440000e0505005505507805d03400c020548070b0f2081010721740103180c4460b03108202e22031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 208955449 1250 208954199 208954231
    0x24010f0806040c050603060d060903050307030e010902090417040b030405100605090114060a05040e0403080703110903062205031602010f080103020d0f0206090406170c06070503030f04080d050708 86
    0x1600003501c64000c07600b00c10108001420041404056440104295001180480400009074440c403071321038491b010341d031055280c0c2020f000060560780f90503500e54007a8103040c200c5000da580e402529030001e0b84000c0c4000c1c014005004041c907400703594092040070360040104428001c010030002e0340450700380700811441392100c0070015110428012503020900320903540e150b0f820303c000245a0168981481414159103804e036401c1500c2c1128201d000507032402c00d00048540501602480300000d032012424101003201113941e98800902d111880d01c000c08010810040d000542d9a9664104003a02c2e81c559000344400780180c03030703204224001140707100791404d001c2c4250103060580381d00500210360301d607140d2241c00d185105400d0984e4041020005100140da0b07030f2041c2c400810316901c2c905e541e40003940b81c0600f07200c0d0241c0140e0141070204400320004501200b102c0c3e011034612070046042c1c481c0c0c01d000c1c01d64080d802182c10310600d0070050200c01d40d04840001c1c4900300340e0b01c408030b00b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 208956699 1250 208955449 208955459
    0xc0922030806120303190209010201020403020d0609170a0203070204150f0e0f0603030a1403060a171f0c090303081008030d0b031006080303010b07030c06060b070209070309050c090924010f 83
    0x5244812141b503034000014203111407102180740c0081c800f0132014400035051a4403500050f904000502c0308648255031074200c0c20412812000c600d0001e440d8100c207a04100d00080c000c2d403240728542d0300034860f0b961800403007000c040c1003100b140941241c000343c0010b5a1a1400076881500941d00e8241c02e002160016000b46000002c5406220780f555640c4420303229900382e407035160000ba18071039100c00455404036021018050003008600b00320014000c4013041e1030702941e03170248000901c0d00182070500000300d44c1c1e005090b5108603913251500000d29600c1550f800100203581d00300340f910b4080040e030214519855008511800800c0f420b440718141c440311510b04a1f0401c1c0b042007129013040c001002541d9210b0058060540641030a203180c10955503214201c906030b412920f00200045180d030706600702401800d0b4040403e080402400c5007503241c0d25036034107085100d00c0c0b103a545c80b0000350007a082406003050142c20b112044000106901000050540034040d07683d11900c0600c002603 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 208957949 1250 208956699 208956703
    0xc07171609090809090a0e0604080a11061509060d0501020c0c0405071e051e0705070e130c21020310090b070c1106030604110c0a06110c0c092203080612 67
    0x301041e403210150f1318141203130f0140000410000c20301e4202a03510078000c05200c0d0309220584c4282c0c481c08000f03649100e0100013400009142c40b000b002ca50000c0100503403c400003101090200e0102c5892099030786007800950003000d0840020101c0d400400c001400e12000284800c0c8040200c805100513030781c08204880881506060702c00e4032103801c50500f032103030007031008280e46806107810380c410040c0c510070300311182c1c412076049aa542c09a44108010070410811507040031080c81d41d0b1152001d5a00d800c02d0702851030003040321415808503820101500b0380c1354000215400340590b20f002c03920705091b41c001c10074580d0543c3c503042240f0010721803502c1040d039400b00750351190066100b04031280170702105400003810540c000340d944800c503654000c00006080c9284605c80207101c44450b030700d007803001e8034074140760390800080074015108443c101103062510007105490308407a075030b01c1a510640120b0340850003604e00002034051014103a00959007481450151034800a00e0102c00c001c0c0d0b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 208959199 1250 208957949 208957961
    0x6060603090a0303051f0602030c060a0b030a150b0d06090614062d06030f0108010e030406090501030504110a0f050405060607110d0317130201171b0c07171609 70
    0xd0381c1d07810816451000900030382c0440d4202941a03551844404a9000c03101c1c00130150700301201681c8049920030541600300009540444540c105208000054011a07601c030503500c1c000300301e01400700510041d001d46601403142c201c0c0042a81006801038208400201000ca005980960070806122024101c80810341e0080790068010080381c02c0794039150700340c0000c0c614074003580c07455018842e0155881d480514011200900890251b51420b00c18030708454048260541607003003840100010360704181100c080b02c0013030070045915500c62400e070307410050041009510000000c03020505120340302105094640544007081035444d400c0400c003242c080c017031004099808443c0550910b0034540280b11865105e410100c88031089001c45100b210400c6500d07400c51050b051094066692085050f40083c10003005c1c80790700d0926146944c0321503584083e15020610000f42c80804090800081008044040b40e0082c003400566606031103010841452900c800030302008110b080d80c0c3c0c8500 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 208960449 1250 208959199 208959211
    0x304051e09190b0d0230101d0715050a02100617100e0303040f1e03020604021519050c1002120703111606110d0c092408043504030506060603 62
    0x1c045001050101d502c400070103001e0703580030b41c6e28058010035042802c01070101000d4a00d2408501c0c4c403900c407102e99030300201e031400c40105da10800b41041005d51224520314441442c1c0b620b0b42e40e598104000303a1400248010380c000c254030744000000c0c43d01c0c1000252001e048010156070203001c00c002d14009541c0c03608140c80381d43e0820801f00c0c001406994510a589200391f02941c0c40c54548d40c1e48001c0d03040803400503805070b0486c1081204500c0d00c80f1511541c07055036543c86081c91405c445244803038071411000c0f824010001f505a2940e841005010b41110700b0580c299074801d0784d12035010241e00150380b5403010904101100c651407050400350f9816902c022504050340c135090f03e460700035290f03030032021440c107004001da10102c22090082200760b0b455900ca141031945042e240040801083d150110348240700e07103c0c00b062903031024803150001c3e0414643e6030080390503070010483d04000c0381c064800c00d01c028400c41e004808900a4012039000b6000e0395403d541d0007007031100d90300c000c49035 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 208961699 1250 208960449 208960459
    0x302010e0d0f02180703061d0604150b0a02070f0f0b030f0402060f0a0302090306060a060f05031e1801240b0706060905010909060513050304051e09190b0d02 69
    0x12264441c1041805100568000c020090b002100d64010451207400c03503d15100781e501e80b00811041d280c160240300e00030060b142c1c2d00505840c040c07a200d0b280c1c060103064644102d1f250f0320a00c468024001c90314000d0421090450b54070048104040d40e1225940700307091440c00c0300c40c40014140030f107915200c00c0ba02e004921603c0c5a64528003030108040c0144200d901c01b01c140409440040c00704003406100850b0b0720010391750940401054a000c2c4000d0107a440b03403400007418407030164420034111007907540d0704006440c0d031202d030785182c802c0b01020b4010003041030044c104000c0c0c0c00e00303d40f0b109142840c01d008000410201112260064604035064668401e00300204018002e800003001401d000d844000741080c0c0b5604018140c600030f80c4000c4001d0307240d103281e10a1100e0b40c851103400030300c1704020880e01c940316540d9940320b026612807a44a140c07a00000009412045844048807800030722441c0c291030500c140e007804072624001d82d588189801130891181c2041c4450903072580e00180 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 208962949 1250 208961699 208961717
    0x102071a0c040338270c0d030e030d0915020a05070509070e042906090310020703050c1912020303070e04020a020120030103171e09040b0916090807030201 68
    0x498031084103110900408003001c0b902c5a41c000c10f8004500408040201c889143d5414032040050001001740f41e1311404180244511144c00400542c0982852003600e92689141c0b05050a482c111010000160103000340d201d2070060070390000c043c50503600c7d903250416070340c514150102c1e603612b03900000134116400641c044c0440e00d0568202940408149401580304401c0c2020a05584140080c108200003000700003030311000d0724500400440041d24024242103005002a686900003040031140641c005100800d05204e01e04480d5081c000e407040700c10b401c0110b04440b0715680088000e0702d2034445440c18024151021044a01800f1503079101000b858000c0200700003503014043d0442503659032072801c0408601003400c00600400302e40340503101c1d0b165003040ba0100040300311030207150004201300b099408149504410f243d1040a810b0348034482c10b0301007002020940541a440103114041290300020301880540340d07100380e51188010f40e61403000ba940d61082d400000c2c0404d00d8070f5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 208964199 1250 208962949 208962953
    0x80105072105040c09020a02100b0f0102060a02070201200307150603020108072d080402100203030903070618020a080c1f02150a02040902030103081b120304110109170102071a0c0403 80
    0x1401c181d0f0484d00511200d01c074150b03a0004c440407031740005684400350b0451030032141e50001d00c0c8030b41e40c81d00d6025102c081d51001d4840c0000e440d0200240151a01a40461000c0035a40f09106400862030340c0c84a0306c160b01452072085950b6000f252084801d1a075030b035107411001c0781c14010f00040340c1d0b041c0c4030040700c0d840d070301020b550700718a54601d01342c0701e01c1640425001c240c2280080c1c46540c10790f122607041d0304190040c084003e451051b0b03c01903500c10024481011b070004100c40241e5040040040d01030710040c03100d01c082801074800795005030010804100d14102080c1d800702002c00300c070b0540005030007200507200b4100444002000d41c00c00e424050407c41c03580c01d466880348841100501d0151500094012030b082a002034541001c04104880344181d0103e10f002880f085000801140708168003c1d1030905c402880208040c0d90000a0291a4010311255000d000c8420415528441c411071813030003900036010a4442c69040400b141211518511290060300b030000303114030b09821a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 208965449 1250 208964199 208964201
    0x15030209100f0c02090a090b09060103080f0a090f180509070b0d1a09090307030f031a011101090b04080c07050a0b12071b0f030e0924030a08040f0801050721 69
    0x103508520140403480b01c03e0070040c2d0324581030030300ca14020080005d04120a0424080840005003240c10503406440180302040c0c0c400c09071403103138803603c1c000c03590b403000420201c1d50880c0300d07800b00608071007600e0041068102a4510ac04009440c1c40030055903031107130f055968842c000e100d0070510300401c01622032003500740e422002d46440311071130041c3c040300e0f504045000000110b80c1c00c6a6508041020001c0580c000d2104121f00c0e100d10b0240300c805400c1c120000000903049501e418896030307484a129100f02074011071703038480d049603d90f1928034045c02d000349254849807403404039008a200201e9246445070ba02800d940000800d01d0802020241510f00440e002c5c1601c07060040d43c208a8601c0c242c0030210007000c40c403810091030b10108038500a000f00708140c0f00c5a229006400c02c0014212030f05460346600819031550044504c40d40300440d081940c02c42c0003804050f8001004181a4105510f410450340000e008114940c0c0c2c0180032a00707422016141207000308518105450312800d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 208966699 1250 208965449 208965467
    0xe010207020a1e120606170a0b06061e13030c0b0a0806040b04141f0603110703080a0612030c020901140105072405070c020f01050408101d030f041503020910 69
    0x3e00d8000401d80c030b07440500000d5003105001c0f42d48589914040c05003d02c0c00c9022030100440200408030a00d841c1d9408050040040641d07004810104904600c80307825030140800f5000c080c03041e81d4400d180c6690858994850005466001b215080080c4d40f00c8010201d407444005580ca5a40544071042000040d01c02080d803d640251900220114010079805140c0508560200c05100c148078034201c140030912a84071005051800034082c00c180d49000881c0d41907940f601e801007142c0e8a2410501c010200c0d500301e00b04285050031342c01d08054022032042480c80c02280d400c401c980e41c48001c52001000055698000380f41440040c0000c1c0078800990f403103504650340703080301d0b05140c04003008881c6c0440c0c5c50f40000e44030415410650034a0809140d00003001c0ca0064940740c1080003540e03980c21f04000101e150782d0398540324041d03d004040b120401124070000d0f00e6994001a00a010315001402614054607034210081e180038080e10031100d4040010b010001d039144892029221103031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 208967949 1250 208966699 208966739
    0x90c0b03070f0c1115071704030f060903030e060c0a031521060902100e1e0108150d0510020a020610150503090a140304080f0a05071e1d06040e010207020a 68
    0xaa03103085100c0954407410741e0000c1102085c9010f0b222002c60621000c20203150b440410301c88000c1105001003648203669800c145c2d04400080b44810759464110024038a0351060051070141d03d090104004844c40180b4030800583e4090060820103101401f400300300c0e101e80c1d201c551414010024101c030b00030319400141d000d600d00144940c5a9004a29141c00c00c0302005c0c00a046c00000d1300a501e0405428404912078400c6210140312443c000703031181c80080c04e49120a80c071106000c4003944d8041d20204903945c0001620780701105040181c002c1e4105200c1c17900940125000104000f40500b000000c507500e0014050440c0d00a0a007901c8662018001082e81d00802814002184400c002c1407004080340c1c00450760303a07141c41c081e01c0c200b4009948060300c60700001c0b1480049000000e83c8019620003a041c8036070750407504100800300c80550b10011007030812407811000f011202585d10b01c81c0c1c03029581480780c0b9003c003061a080703100e031210003503100260f41000d0040c90900081e00c41288 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 208969199 1250 208967949 208967963
    0x4030e010e090f0f10030813230f0603060415031101030b090702071503020c01021c06080106050109030b09010e060a0c0806090420031207050318120307030806030c13090c0b03070f0c 80
    0x292a07803600391550307001e41c10268100e400d0300400c101d08005103100c2403190301d284609c0c50b910606a0001104a21843e0b4068814100440819525034a651040740c0071b00307841e8400c040117a642e00d40b041c20001031403100c0f0702013450a120031015061900c00c1c1d9109116a0380540303102410110403250340d4040451440030168244290006160244000c00d40e030060386034144040d2085004020644040c0e4100c07401c16410400104841c3c0d8001d844181620751180e11444281d0316155558010f0444031884607203403185070180150140c050f0700c070b80a00081030799441d0855490702c05001c1e010005131802008020800407520100780c000140180b918001030a881600400d41180501500582029030b2582c00008941000c00914141221950001c1c1c41141d0040e068003c501c0d201e0044000240c00d10103480700040c0c041e9801d101041c0c80d044020f01c030340250503590307800f50000d000301c1e0b004075041004408042007040303124090b82c1c4119065a00c03100580c00300c4408031800440403030211020 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 208970449 1250 208969199 208969231
    0x31e0204050103080c070602010b010e040b030a06050103030507050610030f030c020312041707170d050c03090402030c04060201050f0402061812010f050609070504051f050c0604030e010e090f0f 85
    0x1659503014040c003c601644181d9220899110418101000d9603c41c45c150780c0342140c04100c80c0d03003103666204400001c81d40013400c08100030100781800300090000f0300446c6454008000c15400002070607078076005504490050f99214200d9600004500024160051510356400005d100c0d0706052011351000d0143c1d03032001204510500c0301d80203a000350b000d0394809603805103034041c20440036008101102203080004034010060392181a00d00c01002080000280454101020012901c4001028004551b40d29040140b5403003a00075005140040d400c040100e5000300c900100f1900071a00149814900402e1140c107402001002c5070b107503040010400740c01e0a492b420f21034a1541e90400602094515004003045000b18000305190142304050209000d55241c405c030000380c040101102550004580c80140c4527405078403c948086d00c41c3c07408000030168050700c0c00c110141c0030b0b2a00904e100d482c1d8104120350000b241c4000c65511282c000605c40301c08141841c1d04402d00100e2603a007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 208971699 1250 208970449 208970453
    0x308031f03031e020111070f1e121215140310020d0b1c03080103060216080c0a06051b090d08091002150f0705090405180109030e0424031e 61
    0x4115841c1e0320035004604910204800d00003841c00e00c1c04003014920007001040c0c1c840540290300d0245000180403480400006801c201843c10400c041c0e99210407410b03050091440c0c011030982c090240640010f00c0100600700c1d003000740c09060380c080c850000500f80e141c20160042011651510030540c94802c00b140e208107410544010700440440220109203907420303c0c1880103405400040038039084c104881240030985c425622410740e42e0090025a40d501c801c20300450391200500050106035000500061004e40000c04061300340c4a904180304e965592440010074100d5114000d1404030308020851003482d01010b849001c0384130300509828031080c0b102060480e1030581003c400369002a81140208a061040342c1d8081110009810030b0314008100611500607540130303c1c0950b4680f000710b00900b480c605400c80320361440000300440143ca040040164055130740542c041d9241c9546145050900080341a1040e418580e03a5001442d50b070344c9843c0d060051103c503407035228a00c00700c40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 208972949 1250 208971699 208971751
    0x609040906050406232406030702060406060801020f0904050903070606030c030b0901020306010e1207030605270304080303160306030510020703030c020705030d0c02180a02071709010801030803 85
    0x6540c9004030000941454245040c2c1c048444100e894071541000394000710302a21000d200550202e090b100090140c840c443c04140c10250f110321461703110002000b00840c1d00e074009078481c40ba0307000390740501040b640c41000900300d00c034400c103043c16440700f044210003e003041c0e00665005581d03141100e243c1101500c0ba0320032603060740c00071903442c0f0060104000b8801d0400b5200e421580f0517000710700d503050003400070300041002002a400f8040702001d281035820b05000c108000d5030452418041c51604440151544030b0300c00101180215280e20140c1083d4000203039000ea0360028019407540c0c440100c010400007007803040404168503039001000044007848001c0960381041405038503801c0718503005d010786042003c41811035000c003404101c6968005020442d6000300c2c108901103401d00d0002c80c4007201300b25540c03c81a051203084c001122501d03802004420b0040a400c1d1804442e00000d2001e4480e030a0b0103400540c0c02c070010f0020401030030095412881801c40005a40301010001d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 208974199 1250 208972949 208972961
    0x910050d05270303011d061804060b030d0509030304060e06070c08010b0f1c02010e130e21040602070905131406100b160f03020a171c0e0615060904 65
    0x26201080440070100454840c01c41003182c280001c0c6056604064904260031505910a4402e8800401041e4252a60141050b40d11040e807200c81e480c0c509810300c2d0000c0d04684000e14080d22941242030303403951003401500c00e03848008000d586000c5c41c140c0c0c101c0d507110341103101035400076041000d00001a42d00d1100030080100600100f020901c0c00200018005104503141c0542d1101c40718070240302400c000e00c4407190742400c3c20043c00d4484404220b99260000a00030b0540c5014031a01115000081141010340c1e01030310300001c0303006c0d0326060303138680103030300c5400c01590001c24280f01040d070700d8204661110103002d111012010640341c1c01c03022846030840d403049030065010301c10054984690300c80a0700e4101510791400311302120102c4511000c82010708245c1d440d444003410140309206c2a110141c1000c0c2040c44803041d00849032590b4445080030003500c005007000011020075010b20801c0e42404000350003150381c0c8030140400a8084170055038408410000f090990341d5510903c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 208975449 1250 208974199 208974211
    0x121f0b0c0106060906080106390b010503071203020a0b04030512010303030203061201021905090f0a03051b0f0f0d02010c060e0309030f03090603071209020301090b04050d0c080910050d05 82
    0x40390441c9400300144c1001c2464100d00c04120801005001031500b00200481c102004400000403000d038018180c2c0c80c01c411070161190354044e111040901100c80c1d9202c0c1070b0348003101600e066958820040795840c1103100c0003000760708180f90032008501c000c4503c5601038024103040345415081d60009401e408240c0080700460f038080144201414407080100c200500d540003180b4000d400d4070420510703d18041048200100051990b803c1c1c0c550224009080d00040e046a80550b1a071a1154071048121070f4040700d910516610500d034a0b01380c4650700f00100145c1148a6102c0110501440c81c07882007050b81030000c00151000042e1075446420000c802247c05561108981c500301030800c89003081d200c005034824007141e41d055460a08a030f0300440e95081c003c141440f40d018a00180123420000b035855440c20700001d0a01c860004214403841c400d009450303034904092010740c0d0036908488041c1442c9401e01400503581041d0142d1014419917051940c1040d0120f0701000139100d0850f00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 208976699 1250 208975449 208975451
    0x204021204112d060705030a08010510030b0f060a030b090f071b0503160f05030d0504150219050d0b041b031103090d030f02040305151605121f0b0c01 66
    0x104424001628624901034104403000c0b5074074820070b18075402100c00501e61100003c10003515a03002d0b500c110403981e0b520303403120982e52100c59444018045080902c82d0131b000307002511628115912038441c1c40740062000b004181c88001c0346040c04070f1a0000034a800601d5a80c00081c80b6540c0c0b540d500178858070354480c0c900c5040c5000700004003460314103030405c1e82c4072103030034601c50000d03801000355000b01d101c5e0040203041428904103030980c8150100054a140800074070a0442c04413904105d11a80c0130362010b813a5241c07110b55481c2240304107803070030801c40401201d40c0794061040300200fa59071113980003ca10040e001c4001011586440d50002c0c10316540d40518a049406005e180400306000325044e0031071800701c00301c07500c2d415070705202da00309642c1315510f040050040e41554051034010341106c08002d000c00c100c0c550001d040ea912407814401c8004507140d2032050341250907488418407004565112102c0310007003d0160b415080340700c3ea041101144c8424000c010303160321941380340 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 208977949 1250 208976699 208976701
    0x19020d0b0f060c070302090c0712020706030b1f1d060d021905191202040b040803130519050d050106080d050304060b100e191a0c0f0a1109040f02040212 67
    0x10030020241071191156001d614140440c0503143c20200751030040304c0c0c0560b0030948a51340c41003109800e01c03651030028603441c015035482c201c15074005115070946106031400c11940404504006c4521a607403840401c12010f20495001944194481c51441301d05031060400c00310031000055403500040f200075049503010481d2080b0a10107024020b4018490030a43c3c91702401141f03007900c5111281c10750050210803813201903203c2c0164102e1f0000d2003112055a2281d131140d400984a034884107045185409080c80070405203046150b00604441c1a030031700310058946402d0002d04c2014100c00d8405550320240029119401d0194051b10142592440e55925161400e00c040700d203c100210b0050040c000b45160b066046410010220350466841c0f000300581000ca00d10040360703030481034034108800395515040401401a00b0856120b90a0f07800382c3c11402100d55940da503054024200760301d120168807090400411564001c0d000301c07010000c6440c550085001c3c1d92004c0f204a05d0b1488130700c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 208979199 1250 208977949 208977971
    0x118030905190312020307290a05220602041203020604020a0b0c060408070624050307060201110409020f0d050c030a050105061806090f090f04030207080307030c0b19020d 75
    0x10208a000d444101c4004402082d00c1444a514548500004250f421018941d1a01c14004c10a07203006e180c0c04400d40030700700c50041e081045640b113120a540c2084101c000309007041e203907004041c0b0440700080321040034500d44043d0140c0f094102025106250708010210f210401c41d034100e8480c0c1c0c0070b500202481d0500744140b08000000d984003142004042c400c001c1428808222150008d41001400b6141d104604102c030081c200c1c500040403480007550078010b201c40102c20082295805c5040c1c488155488100364241d50481458901300340e030030081880284020fa000d42101c1d50307405551070515101140340c004403501581c003054903d401008100640140b4029180035010544816007001206400659081c2e00131410500c24900821400035645565070078014145000300303411611f0070240008429007009603025001801100c001003000d900002c100c070101941030b510144101050380701c0c404210005894001c030000c0c80c0b03940c40b8503000e80d800a0300b45804c0240001450003900 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 208980449 1250 208979199 208979207
    0x180504060e06030f0312040b0601120c030e010c0207030c2c0702030d0609060503100911040c0503040501060e0402090a051e090c010e0a060c0f0c090c110f03190e12011803 75
    0x403c2078035885d0300c10001310514546034070909420030760009001c42c1907160b03040140c4c0c10102400803801c84074680f581c0b01c6281035158000110505482008000078041c40c02d0807030300c070b00342400301a1071148010001c02400003000c02c03411000482c10702e9a01c2e10303517540302c40c0d14101c1c1041d50950010f1b400480c00300103e801c81e10421005104104040008a2500b40407a44407512108002103007580c81e0400300602c55110400030118030020410081150300d000e0180c025001541d007960b4661801e800804c201201f40d03d00c034040d68005180c1807250391103030720740009884020481c00c3e249040c81031a96405050501040c041d918410203071074091045000181055400341c0b8032445103031110410002c0d079411001070440550442d8052004207118202498588034a5000d228214603001001903403035808807085440c0c0e9a008103491804004045095407405450107140020f059180846e1007035005038120106000054040c0d00d501ca004141103003140c0c515041e01003807000107c1200300305540 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 208981699 1250 208980449 208980463
    0x2091f0905010e060103050601020a0503040b120108031206120a02090f0105120c0a050d020a0b040b03040506090109120302220905011d10060806190b0702040513030f180504060e0603 80
    0x5208080216614018400c2c0c0d01e60780203132119062598400124015920034044007100680100850b03030340e0f47d50751100b1403882d80801890040e40c82a0400420300b03042c00b000700d0300640044024001c40ea00d40d801080f200354130740c44030b0003440d10072070541000507100e49502502c10041604040955850003091000da03a1038031061039003a0700b04030310328002540c540c0b036400c0c29100b060b14080c24004032031012a02081942c1c10032003048001042c000340c0c0900b240e00030742c0304070320450a0b00d40c1521290740341030070707075940c007200610110b045035404800707030300c60f0340a01a1038816aa040c4418914400303420b1001d4090340120300156200c03001070220040070b1084000360440c0c081d100616103003a1075024001c4945010b80b20410041e040032a01556407480d40e0680304602408030519039550b1034428081c2d40c403613a4200c1c011418840080c0f2280940000040e103107400d6100d100c520b80c0d0112045495401c00400c08100e6031181c039000c540d80c3c407140b00d1400030380075030940311200f810100e00305490000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 208982949 1250 208981699 208981709
    0x6080708090a02032d030f0c0708060f060f04020d1a040e0706021002031f0f031e0b0604050612010c030504050c0d0213021324090609080a0803090a02091f 68
    0x11210b0306020040c1c6001078001030b49807401c600e0b130251800310742e43c44d50305012001c1c40c1c14251002140c44030445d81d0700001031003800c0040341201c000c540c1c0e03850581e4550004071221180b01448400084143c20087e802100c6154010300044c03409080343c8044080302c01c23143d0f00c5c8880101c40028040e06041c00c0c42500920300c0b048000f01281494900029540c2074580d14002d803464021000ca03800c02000301c1078210210044d081251101d44825280c10150714a100a40301f0400d800c400c84443c2100014a045198001c0000507141d540c0000344805000c01401c7c041c0c05c64040312441d60f46020a105845113501640c1d408107850816040007880c10100c05541841a15610254030040e034035101b100c0d05403c03180d1809070311101e510306000980b0089500003542e4031100c0c80d001181c21112b041c0624484840d071100b035882929a0b404981c00740d02e901449500341e003e1821040030405003000b541d800402c2d80100c50400080d03602144a00000b030b1400251a14071a0141d1900d200220600300582 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 208984199 1250 208982949 208982953
    0x7050d140112020d020609090103150c0516080703090305030a0c0209010f05030c19211208070905060715020f0406120b030a0209090a0c0e150a18021b01060608070809 73
    0x350400d030b201c4002007002e1038024420110710741c1c68000c54442c042a200400c000501180031513a603400c22081c00074230120046086441c01800a034040d01130340036a400c0c41c3d81a8414031411900da1b0b5140880d60151100390140a02140000001441080100320801c19951000302c0171382c1c644144140c140301030700400c040e0261500d0a200310b84000640d110049030488900300c48082408907422100520741094040f400441004401c0004180d014034485100d0302c10021008000f03041202d03032900940d0104001a41c0788c0b4200110302e0f022014200c00e0740034441080910000001c5102261b00c1a4070510010001140c00c00029401c4445900c100100f1041449512482000241c40d0002084024401c0007150042071312101c081001c600040d50280c0c0d11030456031201058110243c0c200d80c440303800701500740071800b0380c105034803400d00300c038092098102820369502e03122010350400b0b0300b01550140700c00000003c0c65800d000304001440a071711492542d083c840b13001819903400410201c199 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 208985449 1250 208984199 208984201
    0x201170727081203041e03030209010905030a0c0509070e04020c01091a0403080402060708040e0a051f030b041403160303050108010501050607050c01030509011d01050f10030305030f100b0307050d14 87
    0x210106590b0405050700b180550f5a41c5c803413505078605005104000001c0d000d1020520030140c041d0300408824100740c0361008560b90315010075039030310309101d0000c0014414a408200714100b02c404260008880c0c1007240c004404040880d040742c01c016280140b0b613460303d11a40c00d01ca149e260315241e0f00b0254007094000d103410303140505480e001600090146a001506030280a003240c1550043c0400c81e50802d4281040c1080c0030180c9410b84034103190001d5841113140800300c0e418504100daa2017110f0040590751511240c128001c10800c52030540401c0000d1402808174102110001d40310b1b89000400e54149098107086480c160080d9006d05020401032012840014030034940c000c09180100381c0fa0740c0ca101d01c03800351207104044001c951480450035001c0341c064001d42c0c81156031007000807489c2d40d698461082c00c40140700c09008285d0030030125014000e451411a4840c1d10030b043c04401d59920307250388406900c04c0703034504e0029401003800350306082603025802003c1359840070328801d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 208986699 1250 208985449 208985459
    0x81c122a02060601140703030204030c0b070b010e0118050a0605120d02011a06120403120515010305060312070f050304080709051503120f1b01020403120210270201170727 75
    0x103540f09142c17011102c41e0000c1840d6040510980490700550350100e8403440c81c1d0b03903588000d09181c01c4040c2c2240e80b5440d100010a6554102c807165049460315074510294440200e048801080081c01c13410070b8a4403008082030303540328120b034119002e140300c00500c880303a0300540090071502d0042c1c20150200c40c0c4480c1012660b50902561400400242c2510b26500e50b803030300780e03481100700c0807058400e400e010420006418164510b074a194003030324144010380c0c4403010107441e20b403551b4070680280014005000030640c2d1107101034015104c1c008403858541c451280328645202903000d490407649810030001d00005200c1106034078207040e0020045030240204078840360140007510303000c2e99030104050b040001140c400d03800521100303008568980d12070600448113000e901600c00588240040f00307030f448000e485008500d044820300600043d03000030b000c4030070758140002030341001000d403903201e14210010901c6000d00c02c944c40d012516248103201d59640f08001c051360200c92010141000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 208987949 1250 208986699 208986707
    0x16091d07060c050d1d010f110f0c03010b04110301030b041401050423060f15040b060c03030a060b130902090f0301021602010917100203071e050307090b04081c122a02060601 76
    0x720490742400c00c000302e098500421503841c400e004500b1000e00c200d09142703403c41c50101d0303030448a0101750003d00c8a203100e0401d1105480d03c800b11040007103401c20040002c1080d00c003109400600c22460200b4094410360604e0950301e003603909594900c040402010140c4e0200507040c1449000800392100d860b01c0360b0031884481c40141464548441c2417060715150340c560b48045103050005000f55250403250106955076002241c125204600d072000102d52844984107a03541c900123069070540c0e06007080c820001030b40040e07503101d03080a8058080740d0aa5000e0010301030070030310100103544025850000620024055204c8000710b40c1c021510b0300c0e4400c0c0400d00c0d506414102402603075a482c3c0c89801c5a0700f41b44e418107607a80321b100c00a0904215888002180105625920440055241d4801000038400e501c0341d5481d5600858440320b10700d019080110114034141005030003449012220400d0b40e4a103401180106d00014103407030000b80381140c1c0c0000e60428802014649850700000e8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 208989199 1250 208987949 208987997
    0x80c0307301d0904170a030501090c2a0807060204030b040b0a0218010c0f060e0304080c0406061706212803020a02090405031c0606020f16091d07060c050d 68
    0xb50189020f075000030144402c032850420002c001411040e907803c0c80701d400500409081c0103401c0302070b0402c41c004a03207030700c195900e1102d100c00055000540389107840b500c03841c0c403451008444000051085002190992003d040118095031003a401840d00786411004c941e40140032540309031050100d0811409110f405180d0640203003080754081505040000c01c41194100080c0740c0c3e0f08244d0300109041012000c2e0048a403c40100c0b911049120100025a651030041100150041089024015441048540104000d400551403802071400c2222004602c3c440d104207502005032810220550005030324240c0a0211a6010300f240340c1e4002c1d246e6080c848040d10920340c6201203004c0c0304080c001c45600d00900551407480d0780c0203009801c00762040784109805801070461010480780082107425807080d541440080d1241001100d100500b074a1041c420700c2d02ca00c0c1050070701001d00f000300f00e02038103a50315500d9a51110780340040c50011594a000c1c00c00100c5082081c103401140485 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 208990449 1250 208989199 208989257
    0x19020130020702010903061a010f0e0303030a0c050d1419050411041d0307031e05180915030304031a06030d05042102031b010306090b0607080c030730 66
    0x50b03951055400101d584580320b820103441c00d40f501c076440c8800709441101c480701c40800e80703c58a141c0a0103100b585c0c00841d00500715050740080000444040280d84120001651401e0441c00c2c6188013001c0c0044035401c0d030000000303900ca00d00303000c910b03071801c0454580f0142c2d0310002d00552070256140d0300403e0280600381d01542d2034240700300da15100401c03000000030149084035110506824020301300c1c040d05001c14002002e901d2920011841082142e440144100306034060400701c4c014400c0841c00181106a0180c0300000c5815541d0b0030b0005000031401504d140500000b010940380019501800c024032a070300551681058a8200e02628120b90003103100318800790a41d243e03c01902c1d0b01c000c000f54940075901e642034044900006100c071741c034001c0c2c0e020020103031184100400c803019207494590014040c07110800141c4d280004159072510701c4286d03800c06143d543c81031014481c01040c45003207000480311010702490200303503030805000c524100d840210740c02d5101810340440904 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 208991699 1250 208990449 208990451
    0x3032307060e0109080c0601061b02030604020f060405041a0f01030b09040f0305040504060905070810060921140a0510060e0c070611030c09030c03060606040506030403030b0319020130 81
    0x100d80402e2820340c005184c1c650400504ca5440f80c0d600b20301c0707132255024012000404c02c0c1c0c910701c0310000d24030900a529258054010000c68440c1d80800c41c481d031204000780e9000004000100305501c0f43c1c000c40b8019031105000f03d200700d140e0420401c0c010f483c507400d14105407074502181d580c0c0c1d8a004105800507009061142910003600b4215540d11407500081d405c1824a000004e001030107501480c812810303035840c03412a45074066001c841c00c00622503040040e0080c101841800b2242294540c12122403190804204407a5075059003800c2085506005805c180c082c5401c1c01382c28001c89444100b1400d08120b95810441042d01d03615019180c0e20f403640000c180c0c0410000c0d03541c454040300c00c4001034903460303103000c814900c41c0d54030801820b03000c0d00900d24086400d05000031100e000d03000081c40d0b42d08250514061200541000b07000f58105900c612900045850504c515081555010300c0420506082e00000d048028101c03280007005111032260750032400701d101100015418160 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 208992805 1106 208991699 208991711
    0xc01080412111f0504050d0804050d030e010f050a0f0e0316030c02190b07210806150c060c22080a0f0611030405070303230706 56
    0x90050101001c61000100580205002080c00e5804000c03a01200300140c420304000403010f40100c3d62070307918000d00051000601101c01000c20030b0822109504060b40c5650303499080c048080c04059544c0800c40c105442908501d42d81e00715040d090010303081c03075122400141840b42910004500d44000c5c440841004800c5c1d07002600b0840c84061080040d4506540110f9201c2080341e10a15000403025007108060001020702490200c150720f031b00086c42e09000b00b4000d8070308269511645852900798940c0300041651001003941e000307020300e003110b0565039580101290030445004075010403400d09030000142c0070714104040580c0e601511302085101c0d0405034001c0074400d0b08080c0500001c2040000100301161050000103085001064041d00a03007040d01d0450342900480000c2007416400898404440350450780c0c10101d4800f450881d00d94810003a0003068103072245 = true := by decide +kernel

theorem cover : BRFrame.Cov 208812949 208992805 := by
  have h0 := BRFrame.cov_init 208812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 208812949 ≤ n) (h2 : n < 208992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
