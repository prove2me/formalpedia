-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3009
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:23:51.052135+00:00
-- url     : https://prove2.me/submissions/7320f22f-b151-425a-a4e0-39553de58b41

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 541007194 ≤ n < 541187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 541008444 1250 541007194 541007227
    0x18090b0307060e0d140609060f010303092105150a0c180b0d1b05030402180c0a0807020705030a0804030b0a2d0603170703031104060c15020405030d0206010e010b 71
    0x1414200010b50b00fa0103941d480d58404540f441d6440f101c01914a005c50f10324a445140454403011280b20f000002040d04081061407412240c040c0c413809e00b45424a0000c1c9001079a0b00e800050a268044c0040000b900400ca5460000011a078554060522050303580988080020351420042d20080c40051441e580e0000b00843e82c01050b040da5400c4a40d07800d2001e4400d04580c058003040c9815215500d940103401188214400c90300324244006108841c841100e041c2e990b0000d6142c24000c6a41540c014a0320b940c0184080c0110f6030744680d9080001d160103a03600781200c40c2400030604204010301100343d25000032408500380102e0f4007000c20000c2c1020015821260f0180300d030150301120440fa84003002071070f000000c07802010150700e04104903502128080700002e1034a001440026802403e550680b20740340e441d000c80268a0301e45598030284409880c040d82d070300b0403000030f0a0382d00300700c04503c00d039258000d400e580d0307d4040900d0380c80605074444460040300700600c8804540d080c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 541009694 1250 541008444 541008449
    0x609050f040b060c0703060f020a0801180e120409060806071b030504030b0c0403020f090402030d0c0203011d0601081009050a06020d0f09060506030d021b22090318090b0307 76
    0x40d400418400190001070141000751031250304500009480522500003103801000d5a006400030f01c0290f03003001c1502d080b8030503920044001102c05006108240c2200406020000082d80200700c81624440360f41c01e00c1d1481101c00380031140010700304070010b0341d03004140083c190040a8070642c90200009400100030741d076a0f014441c0107100400402d405081580d02070364100e00700d84040c0c50100000200c592060000784e11a09010016014502d403e0034084d104a60185c0949250b24102200303480000054804903450b54a45030a22a854440300c84405055400b40042c100c80d458507508501702100041004c4449040c68620008a140062080358143e840880140d446240b2f0441c54018440d01d60505807190800f82040c2c01d02c040e0b84c20060240404030262802c900820005980e034041d008a005904400000e24200500d04510b043c00e220115000c00f44112010a103524100c0324000000c030085119110101c2121550041c100701502c0072184c00c02c015031900c400030340e446843c3d1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 541010944 1250 541009694 541009699
    0x3020405090c071b0e1519092d140603280809030a0c03120201150b07021c1208070f120b060c0709050411090c120618071d01020601060905 61
    0x1079980108100224203940b51a801366149944940b05c183c00014403c0c16100011503079924810782806207810403111060050201c140541680390070000c402400382040003811610800400700e2080f0200300c0300810448907120300180b00c1030000e0002c0c402107c040c1049010398041ca103145422003241c07254008000c004480c00d105d4145e6807400000070b115440e1460340600540c1c140004120a407880300081c0d92280001c0c10001c0c0c0780c17840803400c8031074070190f00031240360b07500c0100207129142005008044c00504021003500300f1a2000510924901c002c0f2100608860399400c00e5900580c1c454112440346020f102d10601800c0041c940880c10309500b43c1103036900301141880da03039042103806071a0174409079020190b0300c0030458010082100c055803404500d6101e00c1d4240b501840071841007802150b42c84c00c204400e9070f01942c41000400941d0001e10080c5100c074941c0c4041c95091140c0310556600444240c0b0181c007102c991121401c0c107055500020043c4800c9402c650440e044c0c4909 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 541012194 1250 541010944 541010947
    0x3030f090a03060908070606060f050403031808010507090f0b0a0c030809011e0c020c040510030813120c06020d0206040503031f0302061b0601080309130b0105120a020405040c03020405090c 83
    0x140020000e9403280c2c00180300600c1d22000c1d03400c0200c40005040054000e900802100b961000d0655034006410f001e4400540c00300030510010b0301401c40c076040081981d8070040744a490b14811421034000750394040104400f61000c2028003d03c04540002c0c08640b4005410070a00240251440c0c0c801017000f800d101d02440000d58801b801d51180d0b034002100d111501d0110036100b036001c02800d0900344100103003c0d2000309500c81c2024081e150080d040c032800d0922442c6142c9810700c29801807801350303507995035100c80001c0100d2041d90b1440c191340600600700d0098600b4a010b46009441c460302402d40d08401704200c0461404004d481e07001910b000d00724018075100c0e501d180c840c0c4194200940c088008102116445810960082214013090403240681d803038cc41c0d8244c0d64040d0710032290b1b100340c003c0031050b030b60304958004400c1c00b00181400780c00d207a100d0601c020365090448000c034000340c0c0842c0c20032492403e0b000d01000800c0c1400c08514140c01c003c041100410001c00e04030610701d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 541013444 1250 541012194 541012207
    0x1030509010b0a03150e06010e04080a02030c030a0512011422020c01020c03070201030506030a080a210c030504120c050c09060f0603010f03020306061005120714041d090c03030f 78
    0x1020741102c25501e4000380091503881d101c1c9045400b07001c2c00d2425420b5280b800241940454000072028140d4201106140384c9558555a01e081544181045003c50006000103052803004001401840a150312500e8031807000c541c3c90a18800140e0054907907682d5403d6001e0719803291040000e4080d038040c501002c152030500301101034030034460394218561000500c4c400006000c0007a1506134400d81c2c080c01070f0303194082056035560b940b800c043c11045c0100805c40440340541c00c80d8001a05c0c8907074080c0c0315030b481098641160904400100825125130811007004143c2c0050900e81d885803c11000980103074540310b644105405006008243e070001090349561541c494030094a40101810740c2d0b0b41c0c44a03c803014444051104034028400d01c2e021445c80e02d007024904904410707690b41e090404046542030348042c24041d1004003404151400a00c948800d28000d1005c0e140b4403e006002d0a443d4544907000c0384002e0507010550010340c0c2d40021b6940200450700c41c0100e0b006116222031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 541014694 1250 541013444 541013461
    0xf0304020103151208071509020618010c0206030a150608010b0a0e210a060507031a09250512010b04050a0303230a1d121e0703050106090608210702010305 68
    0xf0884e4204042e89100c26291008010801004003141c51040c02490803a04000c3d0105007640c11961000303501c4542031000a496003280c41d482001280140360001c01399a154000c1409030307005840d42d040304c80c0c4403421079030181d40c00170902c1c00030505864415895850484009900d000b029501c40030010b00815002060b0380f242404021550300c0c22108811144210641f40c1c2c81c5405801199083c0c10140001c00c107a000340719203071500040c800408050700f891b0040100b641e500400080d142e0400711008030100040284022000ba5035032200742c3d07070710103040080640c2c410580c000d0f01c402e001040b0902140c2c13980118401120b0380350038110184055052555684d850604070540505400700d140e9a90035440603c035201e41c0070041c1a209500b00550910004030315a1100501c0c070390000130382d000d00c0d0110250000042d20800e003960300003030300c941d43d103803d40c2d00c80c4e404540c1040c1c66500078400345c1400d002e21400d078020010261010040e824a0100e10f01a00d0406414180c0d1f03200081c00c040c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 541015944 1250 541014694 541014731
    0x711163302010204080d0807080c0c19052808041a0d151809050604232b1d090c0403020907081504140a050c1207050903120f0304020103 60
    0x148101118551410040e00d00074003e400c1440b8030203003881803802c2e286045018008003030040c2c1c07640c0d490600590700c0d024666016031091150845030311034003480411281100c40c4040e03040340700e100600103100c41c0700010110054401d80480c05414035810500004050104403011900b42c00724178220348218203e562114001c0c1880b1800316420600402c5610529005003000d645d000295204050b0f1541088422200c00300401040c681c0040d01150128075580307004ca01041c4581000c2c3c58243c0d00320316050402100b4140d0f17181c00e10105940910b9648510000745001400d4606504840c0710401d400044445c3c40300450f0081300003001040b4000202c2c0c00301e070b001c0c5801805aa00c0c608150b0350080903250304403224500c803860110758075501d180c00d00590940c00450101002a43c64241c008801840050720341c01225074200301180710309900910140c440e0744151940e07511408140c040c5428180d1098a040f0002010494400d4002481003502d400980a20b0001a000c0d100d031400c6120 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 541017194 1250 541015944 541016009
    0x40903030b030d0c060c03020309191502120411090937080d0e030a14091201090309170106120803090709050112060b03010e0d1101140a05071116 64
    0x2600032890f0520100da00199024042071103400100250024140220201e000654031a100e40e0042c041d44480542060041c604403402810009401e8090500e020100d03886407945121500b980d108001c107004420410340425801503401000510f407003481c181e2034807160301c150040402d40144105048080600b440003000e441c0004042c5c616071414012216003100345105409401c000d444c080a03500841581c907012002d0700c032100d4111055a0560203500700c2c804ea6a0013010180a80c15440b009000d100b41090094450140e0f40d030034824405400d0009850800a60b07041c034000308040340e00c0070350450800350003440c06a169110010380d242014501e034000c200550602d00040b4170030300120000c0050342d01c106401c00210701424145400da814510740005103411501c040000a400340f5150b03003240700603000029040b144180c2e55801c02d1000d170340188005d41ea80c0d003000b261300e40110f1129514a0b03800002c10940380f540c0b4407002a04540c1c050080002095050383d0005000321006070328 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 541018444 1250 541017194 541017199
    0x306151e0905031f1b050f0a050706020f0405131b050a02010b0a06020d020c01080c03060d03091d0103021215071404080f0309090115021c0c0b0a0912031a040903030b 73
    0x10105028694400340b00c460400500c13503a8174050310b52042c440b01c1842e03810740003000c0d1507840c1081c2c3c2c0c1e0b5241c1c84090700f1000d2100d09004040040c0b40008807144000c04068040842d010b40383c2e41840d043c4254845141d41a1303400301d1030aa8071400000391a0305d40403504a09152880d501c044284089000d40010260203030003010358803000c0341c01d070b8010034000780c42c0c4420743c22130f22070030003031401101ca070442a0f900890070a02007003c140b01e814440f02c00c00341e01d400b90400c1030b038031940d03038040442c0f041d01c5003000f207210002400144118500032030011b80f1000039000a0a00c145592150788400201400850902000b02e08114404070801c0660f002003c3d0a010707250042d8410a02b1620707948241c003020f105400c80d00c004a02100f5140b0904041d020070780c01010a0001034604030f41c0210000803c1d4280000c5000130f400050074002d20380e218907051b100102e009000c62a200000d641901813443c103041c2080407040504002e500040380082c01100c0108200c0c003076040a400070090032440d0703074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 541019694 1250 541018444 541018453
    0xb040204180606050f060a09050f061b030c0c0409030203090d11060d020c0d030501030c03030804030519030b0a0f440303090712170a03150807060306151e090503 71
    0x209002d0030ba40304408a03a0705842100501c601801006000d200d80001480803941c0a5800d003c5410001d141e1b0282c42d001400785817400c80e83c0420080c01c00b000440180d0540e000140411101c0814040f161840a043e90184006145550040d46030300584403860301850b0f8187c00310f030a1291014208250740005030026542e100c150a03480302a60241c0420103061280c41d0804122500c00c3c403031281200c4d08107065401641c207580c0c00701c840004c05002901004030074480c0c04e0050301c04210b210481f0070340e610001442d41301c83d0180b000c0802c055002030140b09516104110000c039485107090242c5044007401101c95a0424610302c043c004643c9200030a4108002080d81000200950040000104680d204d680d140362180c0a01000c1200402e8507094400c4401e140c01c00c14060418502c00341008035103e00c101402c4ca452509135400303107c090744070201c100714060709446003002403c2404900400f0f450360500281c003001c1010580440d190f84440859911482241c81c0c40241c40002d0544 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 541020944 1250 541019694 541019741
    0x41b08060c03180a1b061d15070515010e061201090c0611030d11090a0b03040c0e090109020d0c0501120b0603070c032120160b100f08010f0c05040609030b040204 71
    0x4c180d01c1750035001e00d9001c1041800b03810702090f800624980c4008004000d078102c03c041e40f000340802d41200c0b004035454464601d452112031142400c0b14041c0041e00c200307003c146400410805402640c03082c4000c42e92501e12110040b440401d00e0000f50f9a1a052142c40311224a5800d403a5118801118440030f107000c07038a040700b2000300020140ca4408480189155031540d40b203552501c01510000c00901c2440d00400418420280c020b9100400000001d190305250b0003007051801c509030308540d0320b401180140400d603002101490386c003d03900c20030814280f6a0020810a2001606110910814010030401c1500ca283d90b80e42645050074100781c80c417819115240a4003100d1000401c550308070043301810038802c1c0685142105d1071107a07070703001c0c503060702e40b505142d0001d00b00a160102000340070405901c01e000900c002d00200d0000140605c0c4500d4520480b242c800141c3d0030020100002c000b8503500c02c2c62401078136040180000c0546440c4000382c000c083e0f100320000c2d0003c3c1e54031f11 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 541022194 1250 541020944 541020983
    0xe1e060c030d0c0f0203090d0f120c03021603021e0d051006060f0f0203160c08031c27060507030212070e0109090b0d06051509041b08060c03180a 64
    0xb030120842c030500c0502a5000c0d90500b42d0f81040c8548111005030320901c0b07121034525152103881c001c035003e800c090403140103d80340e40215041400c6654040740c1c2e4000c0c038004155040004142510f03101030f010380c003e41580e001030307820b214034410380005044500e0042640e54801d000c0c0d00546a000045510b100710f051400405003210748255400711360982100540540540618607840040d98050351820400ca0b01c0544001c40c0440700b542c08004070b45010800140400003080616503107000b82480103000005138090710b13070000100c00003401c007074043e404c00d0b504021002c945580c40300010036565202042100240240c409190781d1803541000e100b034094002d42410000042aa920704000d9114600a02500c1c820403030303e60000f4107203400c500407078bc0315806a40c00642c10110310982042d0742c800190503a07800d89003034514450001301e100300c40455004060042044d04007402d007900d015603102205000041c110310b80003540c4e2822890250b0300740003c415031640200740c4840d02080303405 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 541023444 1250 541022194 541022197
    0x1415190c0b060102281115040509100302030601030803131709010f021612020102120307030e100c050f2d0406110111070f0c0911070b010905070e1e060c03 68
    0x80554400641c0c0000c40c0041d440412540410841030b0806196007038601842203070b2005031a82610300d40160000ca070044d9841803800c011610006402944903401c160401c0344900300541803141042c9400c10130001070b100820400d044a401004a98480da21803c480c040d038940d0b0940107200074481c001c0850300c41c4628028000700c16080e82c0d118810500311a0503a07a500078062144041e01202108010074001c80d002025640e1040c815118281c14203541403403281c005507085070101e500c405845900c60b000300308920b034050190209224085024001501134481c14038003a218180000c0d551003242100c810b2602e404a8450036001d98281a804102c01c0b0f811a0181d4400a00d8004c1804800b403014007440307000c01c110348851481d0030115903403c2c0940b03801c620b0858000079001000144180980b0440c4000304c0244001c0e139980c0c1c4e0901d049107a8810507000302807200c0ca00410f02c060a9408003a641801606079801c8440c22204164002c8180481c1043c0341d2041000030a090080400320 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 541024694 1250 541023444 541023467
    0x14040201080c16080a030e03120408030702012c010b091e0c0403020303070b19060515071e0507030506011d040b19020c010b041505060307030203070c021002030702100801141519 78
    0x950411049038441f01c213507100d1284012808002011001080109181000454115045000004d42ea11404118007410703a69440d11a42c0f41540035044000c0850a000c0d81150b010100c56614051034020300b0000c0301140c0e2108054050540390008413450000000c5034043c0d60001c04407516602149012480b804048880221070005114400e00400390b40c007a0105072180103045601d42141d002026400c0c1c0c200510940d14000c0702c1d070801005031402088000c02c01e0040300500206404e508286143c0030040e80511004250b2480a000d581030101006800c01d0b07100b1000407280d01c5400c001c070244501001c0f010316140c4001090404000705506c09503000902b650180401a02100b02510360020742c46800d40141c010400562141e20a40c000e5074040c085042c00c0f0080d04150f0042940301c66106180b60269100142480541c0b4049401400781043c0b031503c2c0f00d0641c1802d4903554034413900c0c0022806031884010700294205c1d0b800c165a00044e84140416420b403890b00c0090110301c800 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 541025944 1250 541024694 541024697
    0x12100f08060612120d09020a03060e0d110309010e040207060e030a0e09090304031101200303010e0403031b050912031c0903090b090604060c05030d0f0b100314040201080c16080a 78
    0x920710284600ca010600e4940d06948140080c140b41710b00a040002e0f0003032a200301d03803010380c98901100103039032485010004400003004192183d540354018098098512003e28158170500c82c080c41ca80e40021080e05603002610b006da00c8804030b14029002c0c055003031000c0954000800c1c00c140107980603150198200089504d0398803a26490001c54403485103000140032091240e01645095002d00c0b0b13070300d41d80003021301820241c0500d2111a42150000e0300100a1108204284024162315004810055001240321090410142c001500c0b52180d154500c0c000c14540700300c032454407000c2c000c0c1e44001007255104200003100301100300080a1201085000c00d502500100c0e50614040c01c2d24000000a0040e80c941070410805582003500309000303c69510040003500403426140c012540c40c5686d002e0701250b001100e900b00600d09081740d80c070b2800c240c46c200b114130707515890640440d001902070800d600c00d625017a800050b1381c0300d4039102441883c2c464916200300a4608001c05090b20903 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 541027194 1250 541025944 541025959
    0x20d240f0c0f050c071703120103030c150c0c0b091002071103070b040303230d0e0c0306012c101d0103020405010b04080312270f1002070812100f080606 67
    0x114801038520b8065007150707840c4d5601400e82030107080c43c1148070a1080b070031003040701d0801070781044c005003800c1300360400c80000c0c5ca0410030504008010303100101c0c010780c5a50622040d00744210091000c20240b101521800700e07003011501069061119003660a8a4070b0150754440e01400c1c115540d406601e101c138000c1c13044440004000540380b040c1c40030f680c1e05558806140c01c03ca601201820100901c400b59484100f1000480012a03c100b94641c441013000c1c0c00402c800008040c00c0c280140c0c05009808402110380011410900b03100c219181510205021511403501e100c0c0c007404150011031076002001c416481540d106024507040324402c42d014040c0c0d0303807564440c80b1540924414081c2079071082c07040060100c0c6040044da880390300604250300c40340d00b941c0c101e2245902140301214a4000301070308140100c082c02022111940f20000390b02d004819910b50085208002103400d1140030714020a8000d40b0011002c030080000c021014070356603e890034542c8540099503001c0c030503800f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 541028444 1250 541027194 541027217
    0x1504050d02011e020c030f180f0a12080705010605090f010905060d020a06031802060313200a06180b07030f020d0c030f050f0f0c03090913020d240f0c 66
    0x105001c3e199101004184608070b007525000080301a40000341e51003c24003051000940ea040d14101600200018035800300410039000188004054200a0a4060115508184100070108001040e4194803000c169a0740c001070510034010700302d0703420080c2d000303178000184103601860000d0281038401c039020420458a5400030082c4410f54048002d4012052100412100c1c0c000d50000b0301c01140c0042c825100702ca941c0c0050503a500840e0b1440c03901d20011450010301c41000c40741004469448036480c541d240140000300060f14030300c5a20f0400074140c2d80c4410040d40d43c0c401070010a4219211500c8002c0361070082c20b00170b1500d140c0d10040c45500c0950444620600c500540d15405403100b144a0703a0212040701d1540c0050110400c80104010a0700d01484076401485000c0c02c0d03802958807101d6803410451120401760061500c40070070080301300960343c0e4401c000300e9154061300310203172900056078114181d40b28120a0b5506860200707821802c0e203154100c0d024040f07281d41d91222560 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 541029694 1250 541028444 541028447
    0xe0a0806100308030901200d0c0207030c0e131203020304120c0201170c090303040b03040302010606050f0d050406141630110912010207060f050408090d020103020405031504050d 78
    0x4204484081a8086030001080803c1c600401160810035100021030010365620b0015001760480d42250005600014040840d0103640f0548403507054610240c4541031450b254410030101a018408001240c480415500c0d840c060f90200c0319a031250b0390503c0c40219440140c002e4000711019034401c04050341d880c050700e1103803e08136101e41e03050312404180c1c0344070200d56410110042109003088010001c46941d40d40c04c00280000303181802ca00c7d0380e030b86498030b4000d0175540700754400f4080c0b000910802082205c4031056a0000d0b0180000183c2d9903510300b0810040e05002e014250750b80b62000030b20500c00242501060b0449803034071038140000c1c8442803900c011103581e81c2d15210554aa80382078014001c0c0d00059200824001d203c0d0420b0280c41c0003410300b4425400c2d80c3c10316907002a4410420605004569243c0c50003502003100b4a441e0311400c4061182061840c0700320071240508003168003a41c1030343c01429028040381e100e100c00012250310060155001c5d103c51107a50344000249 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 541030944 1250 541029694 541029703
    0x3010504050604110703082a04080c060406020706030b18190b12070603090c24020106060306030b07051605101a101e03020d050705180103060e13060e0d0e0a08 70
    0x706008076071485c00c0743d00e8504803105c110251403c41025010071700060200b480144a129100041c00722594451409400a1070004000c44850007044140000c2113840d4001c01e020049410b60304000c140c031030014000a005010100b4400b54190f560b41c1440400e02d050308112081e440c000200300720b02d1401030208050390000c00b42c0c03090954800c1c02c0034480c191194000720f0409100f000080c0c41c0c1034440e596804440042042000840d102d6440c961906609004d800c3c014000b90808010480c1103803a04c0010010041c4400d0900c0000100c0b41040a00341000031022600101541d5002c02d00e038210401401c200031104c020f42c009884000520f01d40b803144441d144c1819280c40b207594850b070500c0c0d040d00e03110000d40d405040c3d0174090036200400368019544500c4180d503c4031390310078109801c0c1d4040181c050381c207410185030171800e00034215895401a0070480c402c3c5000c036403090500e44240944408120701c0c0d100d000c0c1c0c0c0f03800341d503450b088180c071160f0b941b00311400140552a00d20140d41c5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 541032194 1250 541030944 541030961
    0xa030f15031e0302012013140307060f020f0a11041d06181903020c1005031e09070b1c0501080a0f0b06041d0c01110304050a09020c150c03010504050604 67
    0x403445102d0559030703480c0b0011070030300d40621900011031503055141b0600c410030b4000ba030b07507055008001a00301051040c0041ca9014040304660b61003260074100109640302c1513401508103201c001104041c016008101540036a0f100c3d004881304104036180040c4182548540c1c06e0142d0304105007004c50800f039081c2e95540c100b40b200109071658414000380701017072144010352600c0c0210010301c01d1414980c2d00040c0d0041c0603070024407a104410301484070094160340e8000400005200307200710340320880304452030001581084543c940303034814414144034403a88007140e004030000c1c944102541c5d45480700c1013544540e404001c9680d9803060551588a00403000f4003078202e40e805100001e043d1600b254005070090800513543e8030310346003003488003901e00c40781c0141d50244001080540e40300d800d44501401a201840c102882c1401150745000213000d400300c1c040d00440c0d2048088401c120f6451041e860380e988140d43c1c2403c008482280c2e00a004082c001c1e0704140020b61141031a0080845 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 541033444 1250 541032194 541032203
    0xe06010c02040b060c0703110a0b1801050f12010e0a0c0215180a050c04060b0c1c050403021002010504140c10110a06290604121520120f15010f140a030f1503 69
    0x2170554070086070b00c45560382f0580c02d414002c00f40203404105002030050b000c030a0307007180180328a5040c001240c0502800a0040c041d29003008101001c456000c10f01246034443c0c08201b000702c1c4c591310098140c041c19521800d07003034403450100c10180200082c0580500b1130a54003040481d031182040c2c08141b1030050301c1a0306900c40e18060210003140d0300c0d82d00c00d4148074500181881c2d102d90010380c80380c2998003000010b030b442c1c40c01d200a2006010520005452030801040950001000701c1c0b1044201c00c4560306101d55506c140704801014460030f0740c0d09078089404c02c4100103000074103050707020f0078030001c80300c0ea100c10a10206050407421241915845001e00100c003078160344000c903503201558800203403612024510f01040e1001d403100a40d0310000c038001e880315441440d01d802014010110749800741c5407400d1112064556910a80158007840d104e40751075405842918100500656120700000c005581c00d07084d90316a0121101c0c0d0130740032043c031007116000d20020b02102c3c28000540b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 541034694 1250 541033444 541033447
    0x23100e06061306050d0e030a0e030c190b071b090501030c0e041509050c03012c12161a19051e061201150f050315010e06010c02040b060c0703110a0b 65
    0xc44140101c000d0f090b01074107110081102803c11b000340341035030003880400b4081a050a040601460103201c181500e550035106001100000c0c14241e040b01c180e44038001c00410002262010310001381203d64000d0081c0303030018085980c40503150300400f003d200640300f0300480b41001c2603101002c91004c0c000c903084141021420740c5000b256000340540fa1044446100e42c03204036003151400e02886c444e103048060130902000c450b5088d1303641000e01740400b4400b034003c6099081e1031200c3c2c805036840018078040b000380c41c1034a4589001c03100240b0b07903c802100d1204c0304003d510100442c00c44544031070210248151b848512858400b090150f105100014040c80010028180307220300c062407a642500216090908110f04d0b0412001c80d0084942e03001001c80030b2100703003810003070f01c100c0e41d00e0302400d22220b40c035100075003400c5d01c1d000e0501410005465205820340d9516040040d400c000140012f03540c400b08800696101c5461004562021040c400c407000c0386080340729002200c450002c0325 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 541035944 1250 541034694 541034699
    0x6091302010f0504050909011a01030c0c1104090503030c07050d0c0209070e04150b0c010608070b0d0203040f02101205012702030a0204090227030102030105010c0623100e060613 78
    0x64450a002e8801c0300c040103014030000940d991612080703406541c4000c00042d010641802c900151450396810700e0506080441001856512254600000d9000112003044c0c0340701c00006406050301100203482c1740710100c20320990220320801001c84510450880b0000c402c2d4142c01d59010204080c0a54030111101c0000d5140d4099038102c040382030010400203903407200d480645e90301100b54001100c140004604010003480921480c000790003020f000b04446841d240201d18540300f8203010300d040039004400b10303040040c1c904060403a294010b202400510944c41c00030042d85518107503d054504140c00058090040701601c06e40d40b405070403105407070030888812406036101a044112040e420000002d8041c1c007840546201c5c4291a0304104004100c2c100b140000c4000f90203a10903481003004101c960b801001c007801c1103500060108001c031140a900640b00f40c2c81000307104040203039003040900340d0391010800a480c2003d901d50007c0c2c035403a003440518007440c001140c0404036154207 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 541037194 1250 541035944 541035947
    0xe0f06030103030c0311060108150f101e09020334081302010e04050c1c0e0304150318060510080102070206121b16060e0604030e060d06031703010303080609130201 72
    0x150b4810030301078180003040d8041410028a494004d074008107807034106203409081c4070040070b400360b00712f41041291102814810710355540d0750300511454041442030b290003002040c03c000e44030024082d04104548a00d44900d21903036200e24460120300841c2510948403d240c1003850401403030340a03a903025540d644a4540480d8089650300580c103020036140c6c01d1049569074042e0341d1190060504240c0c4429804c00b120020300107444056040c6400e0901c03044c41c01d07000009540448140b40560303040150300d1081a0020071080d0703225100300200340313400320501c081e50700401c0c040d401c250711618039103130b80f80321007801c0740911790000350300000410001e907407181000d05007604415103000c000c6060303040940303603040d5504c0342107602c19407140d15008005010b00c602c074840c984042c00001c1c2450b0b103025a4018590140c03e14624410900465403000c0078180f03621583c055540b120992181c000c0c40c1c15100d145400074801100044c2d00c0d01c002507500d0920f090201d01480000315a04200c50f241c0d0300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 541038444 1250 541037194 541037207
    0x20118060f0e03030a0c020d020a05210705010e0a0201090f051c020a050a06120c0804030804030c0302160305030702100906050f07050109230105070f020a061113150e0f0603010303 79
    0xc000e1007900d0302d4000c12002c0e8140300450143c626910005020300703c80802904081c07407042098150340203100a0008140089010204224244000103101d980a80255240d00680102920725860b010200e01c0c4004000b4018002e14001d8a50840c1c0c907a4441d0f0904071400301d8010385403c41c414162180ba2441c141c0c81440543e48001c011081060f110004a00300004a5100400194620840154a00e024402d040f00d11856140c15607592078262030251481c0c0011344000c04000c0051036440905201740800c0602100c04074252582541d2400e000780d50341c100440c10303880389000b81032900350240640c100c0c2e400c80342641c0791030b0304000d40c0c1c4900340c1281c0c0090368281d80b95504d0708403001c00030740c0350218502031545522080710500e6250451908440c0010b20110501c4281308400902540001c0d11100303413a4451008140c4402004d000c01860003403c080c140c1030781d000c07a0082016050f03001d06041210b21540d4912604c0c80e42d10030443c07038445841034079412040810040c001b0920412 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 541039694 1250 541038444 541038461
    0x2030106120b1828090f030509010909110d06090b010c231608060603010618020d0e0607050a0f0810060c05250f0503010203221707060204060f02011806 67
    0x4001288603200fa001a0440076804c44019410414002c00c00c0485980c00d002d003000410000402c10803c130705681c801c18a0002140040d051041c041103081c21b03680f060003600047c200c500000d201c1039042d07000c0e5003141c0d040401d461103920309100d408204100c0511a40c0c0c640c0d10140e4519612500c0c98071101c982c06050ba07a005002280c0b124500f09121080001003031144401c008050054070f480311650500f41d000e418bd6220b179041220820020242010302c00c9001c4c0020001030340c802c1e070030103c1401801d081201090f54064a001c100722107421401401c1d0490564841400404004004a580721011200070390040d0303e0034400c2c028944a20ba03074007039561040048501802500329401010181000e40d5117582c451400c0134403800c60003807814030080c0811f4000754210708140081c001c2d0800034130981c2421140c240684000e005894884d8141250707140c1c445665180c0030f05080001c1c0d03119010b00000f1920350015040014814800e440c0c00c521800b03110b0780c03d02c9483da250400f421008 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 541040944 1250 541039694 541039699
    0xf0a051005040b0301060818010912030519090b0a0c0f0503011a2b0e010216140106050607030c021504062f07090f0b090903041206090803010e1902030106120b 70
    0x82c800483c01072100b4006602800079911107040385e20b0038184904061150034600915641000c0101001605101c80b400f4a4019800c0c041242d03555801a514070141d4000c0413402c0e10304201d840307000d2103002d80713205008203600a001c0c07185c200c401400782d0f4a8540c0a11040c00680100300421440c04050036140070466429402458000e4505001c03d040905030103000345800210101074081c880d5100341111214103200941c00c1001e01c0c0c800a0012032070b440c0107015900d4040003000140c20039801003024103801041c1940740e01c0039041c01801c581004000328001c4d11189000e5802005210a40e804c40710107940f240200d00ba0880341c44907030461401042d041300d07011a50140200c01c2409804007400b0005400680f4100303500480054651004035203000c0c120780024407007154804801c480585081c00c1101d45600b083e403500d10010725180c40702030422200400085502824503188a00030003003c00c0d1610608035820710041244028400d0700041a40146102891906030300300d180d201400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 541042194 1250 541040944 541040947
    0xc030c0f04050a0b03071d03070603110c190b01060503010e131a280c0504210c0906080d14031308070609211b02060d021b060601020c0f0a051005 64
    0xca1002c60300040c42a0081d201d07200005c010082181e0348801c0d92046019071413511110100408040781e00e401c2c0c80d0044000b010b403181c0b2840d0102d44c0d10400c8503808104e10701100c076000744807140c0f40c181e4404003108039150182c89000040c414070480540e810f90f96042006e201307a032500307112002107036075102d800c407409043c0c0300147c0500840f201075184141c0c07100c02130320044044103001086a0700b0032088803420a1810100c90300ca41d81c03000035030b801d548070300041e034505402040c0d0120480302005401048401880d0003c954030301190000c2085901090403280060040c65040e18032036044905a98152001d00000e900849043c1c640d000c100d010704101842c0c00301a0702c40c0410b0354080070f801da0706405a4a1a2a0300c10700e903610681d4200340c145440180c490340f80b80240c807090158000a03200c3c9c140416428003001c80e60b4100c500c4c0d02140355201c6010f0a5413030845880d01022280e0364054062048105004c0c1408610300310f6030340009090014580c1441d00300501390000c0c0c0d55040801c40f0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 541043444 1250 541042194 541042199
    0x20102120309010e0a03120c0c0b0402092206060603050105030604150b0f0415080601050d05060f060f06071406150604030609030e09040c0f06030e062a0d091a0c030c0f04 75
    0x4091041d10112402036960700181d0004561050682d554450748c14200312000c200d001c0814074000380a6002036040310742100944408480f268504107610032400d0104100040e0000c0000701ea1200003291401d807801d10050b030360380b404c05480d40411240500424100320000100725490750000c15400801005407000a403008007140403507810b00407104018102c44018004100108206401803100f1218904040a1130748c0e010388800c00503100142800f090f502080d22950b4080d006082e810000c0c1c1000c1e1122141c3c1050003404460100307007440c41c0950008a61400e605540701c00c0c5128018050518192a66031040300403c0e0300c1c0d80c103800b04a141c4072032410381d98600c50040c0c0201e000c3c841c1105110300b07001d4150b039a1841944480241860301d100c0750350142d00864099070200741c175803044000e9998140380c2c42c4c20010400486080300d5000640d804144040da01ca0006d103030040210000380704070705016400c0d0070825100d00383c03041c0060000492001c940001010b80c0c24001d40c02504180d0b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 541044694 1250 541043444 541043471
    0x4060f021c02030103021c24060e041b050316061209020d051b0609181008030c0f0105010b04030201090509070e0604141003150b0901090b0f0406120902010212030901 73
    0x440110700e6010468000004000354948620702e46014000302e08090050303046665282d04201e6940801505c0c00040d4561541041403070303001800900407001c0c1c00c00303030745450325160b500203540c2020341d1308058942d1760208140c01d0014030100151803e020711402c85081400c1901c000380c07a034046044180e2100c0d046001030715000703030742d400003407054000b0003500e6540c0d101e0a80043c14151460f00590f018010784120390b4501d4201034080300c2c210000140c64552118501f0b20041c2034000c090188000544c0716442000001c9500c49924244020401c60b41c95001e03010780c1d84100d00c8080e00043c1c044c482880140740c96803201c0d0b00102c1c6c6007032000d80c0d8407a01d000b0a8043e04a40d000e045e0015041c2803404042c20444101a800d0000d458100030a07601ca28462103800400c0c054484a0070b03002c500c0e2042c90f405440f61202400c01e100400e901e58014886080c09640b06004040000b00c0d240759842070352070f45000d03160981c1c0e4140c02a001c0e40c2d1403500d4071203503a00000c000014641d251140540300c01c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 541045944 1250 541044694 541044727
    0x20f03041208040f0312020f06152205041407060507020d0605270a11010e030a03030c020114040c0f0506040b0901053004031b0507170a0b070207081b01050304060f02 73
    0x8504ca0a00314030100354045010b412300030001e4121405403c031208201503000800801e07025118101da6500c10354900d02c5000303551100104031180d005207410140010701007401c01000008a00900b00c5488a449a4007182e55029800c0000e40106454031240300049158000550060710b00303c5072030340078118205200f952a45803046c8000303034100b5120401070040040e40e40c042c60308203003402c5103102c404a020a83d03911140001a04041c2e880d207264050510030742080c604080d040f0850407803070030301d0b040c19444c1c000a4401c03080032601034135002403241441011344080f510104119400d00310084c0042d00c2680c032800c1701c43c0b150b0000070a072505000050304d00128407280c00707401c00c3c5640385c18540030707001042400600704400c103040003841c002030300082c1e550192042200e011f102c607580d44414034074082c01840000c00181d4101c0401c04400d600262880403602d0f014100d680a24003c40742c2d0040782031200f5402d0000e9010400140400c00390342000407801c460000051920007109000303400c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 541047194 1250 541045944 541045949
    0x5100b010c0c0b1c050108100c2708010c03091a0c0909011409060307140402090a15050d1131080105090a0311070503030307080901020403050106090912020f03041208040f 75
    0x60f11004a040445403402c1071016860320180c41c800c00032541051102a42c48c0c5101e8507026000f9200c1f800c2009441c81000810074100d100281c1200d0401200380039a880c1d2483e0040e56015880d000504095a20a020399912180c22922040400e0000c0b0000c21060303070020140d00c0000e1080000041700d85411100b0303402441002092410300307100c0360400840c02030150816110341d002ea1014019805094801038a00500720740c0107039500906404a4074030b0310240d101030304482105d8160003526402200a0081c2c21390807000b08003038119900955014010045c83e04081c06120007a0f1a40039040c43d000344c812a0241c0609036003a954201d15402e48100711502c15040d04144080410960010084e5481c204018084d000450401c00801d03920300000b09080f040000d440042915450203504403006141c10100911001d9141c0031110084c001c0c00c2c07422560a030303100c60801565480468001c0800c00c0c000050b40c6000d01d042e400041a440f007601c1503d82e250304001c000394485c002c0010800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 541048444 1250 541047194 541047209
    0x31b070f03031406030606010f1805040207050d08180304051005070f030f090f03051002210103032c0f060d061211030105010e0106050307050a090e04031806020a05100b010c0c 77
    0x80740000982d00c034a510f200a09064000c1d80601c0070305c80b16030f0b0800c609101000282c0342603a5004200710324441001d42580c0b040ea0018030003d0300d481440004030344c1843ca509036440d03403092070311080ea001d00811440c9170040a04e170000d000502c420700d0080503041c45071550380b5101e4140741c0c8079100d001091040801c100d002c9009005408010b0f600701424000514043d058000c02509e503889160716041d02c0601560603d41c00109409044a2003034201e280801c0c40c2119a8a5070312490080c01d0301d50355003c1500305440c1e2a04010010028000442c980c08016261725590702062092003100c2e046541d9441c0125180c20001c80c44400c968101e0882900484882e420b4041780d01c01e040c04c646040c0c001ca0724400390a00140842504401281e030411000d281c45651400d401504586200c0643c200d022130030322003400d11041c99409200d04440c148071801590f8045d507100401d0384d0340d80703a1041c010290f0304040c0054281d1400c1c1d902c1b002810006051440140307645546041c40031085810110 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 541049694 1250 541048444 541048451
    0x1e06020c0f07050f030303130f241118040507031b0309110d050a080706063803060d030503090c03012c0a020612090c040e0318090408031b070f0303 65
    0x66000c100308010001408162134082508010310f000c240c80c2d11000700039000b01c01c201c41c400010400e04903000e2202c0c0d40c10500038422401c1180c600c800d03a03c10a4005101c00c1d06040c42c0003248524a001c80f01e08180300c0e4006000484820b05110240c0401046801403540d10310a80910390049102c1c07418a100da0365002982d0042482c1c9210f408804040303090164685112403070010340c0000f040380c4500e4102c2412902c50030f1a1030707c1030250a45401c1045030b60705030344400d4940f2035601529200c1c44045030780b00b26449000187c05083d404100d80180e401400b0b1411240030a003e03c00640d0004582c0d400c2c3d5520022210100b03003510b0300c086842000c85c1d00c41792a00e4420aa24451400031084400540700c49070722900000d443d402402c41c090680030b511800f10f20a410100f00e00740740c405001d0801c1c0542602c14064a4070307604460080194104140055a0359281c8030038124821075200d00a141561291450380c0c0750150b01042110191100304542404143c0f0b40000c0a1414481e13075020 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 541050944 1250 541049694 541049713
    0xb090705060d1e1512080f040905180d020c010f02010b0405010605130803030613021b1219050310090b010903080d091205090f01111e0604050601050307121e06020c 72
    0xa11058443c003014882c543c41c00c800d070b00c501112070040100311a0142e10503034181c1c1d09801c002081e8800c420000340255030006e40000c0200e031a400441c800c180381440301d540a00d06650194803000c0c004040c20060304010395010f115802518a00c0751450703540700000c0c4425042010034121038003071b00900c010650100b51650921600d514000141a10310051825401e0010228011820b22040c8011190300401c200380c107401904240800d105ca200203d402046543c0b00b80e204d1588442d02c1c440d4484a410b5038245614040d00849028900d590b950404031031134039084000401d429000c0c0303410024400c50000210b000e200c0504140078207030034006424a032032300d4104041050034214100380681801030000e241da0764420001c00c0b9000f130030035104499418038000c0c02c0c10442583c1c010425052071000300130210000720a0b21442c0b0607001c441490b6225000c069030303070585103d100e40a9804400401c001003134104144080300b45444a1345950300700e0394800040ea0000600c0c50a140d015aa10 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 541052194 1250 541050944 541050971
    0x60504050903070f0816020d0c14010203070f0b0901060e1501120605060909060301110c0102030f0a0608061f0f0305030c010c08011d06060c03072316030b090705060d 73
    0x24507401101c84402549006110780d102c0b404500c0180c1c000e131982c40046008400381a00c20910030301e159000b0903044696003545070517203540d020b43c05103062800d4000c070700c030006500000c2103918483c0c0200004c004145140d9680010200c0140301d04500d5480e04800142100d45550407070203009155604041c8000250004201c001c03403010030740e009401e00030308100d01d03180c110846481b50320680304000503654100109016001d40a4a42800140010260010b10065004d0b5005440a2004400076110100d450080c0c5995024240540d0000c0011501d5410001d030254026400d8601031214203559002c5201c1d0703c815030b8001c2c0c40075000003c48142e595404c1c400c800c0241c00300d081080d6154100f0040126061141ca483ca0a607171646012920581e10345d000e5640300142031040302d556000c1460100c60b02c0d0a4150b0040400e1181544402c0a40c00840d0442004281c41c00300c0403d180355071140c00e51b50740083c100c10182c2c05100408109915468014811090440000300c0c411900607403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 541053444 1250 541052194 541052201
    0xa1b0f1a070f0f03080a090c090914030d0204050405010503030406021f060e1015031505060f130b1306030c0c113c06030405120309031323063a0e01060504 68
    0x2003075411032130f000920001a0700d07108c50030281d480448002071015403e00d40803850404110b8460482d00c0003003640e64000c2482e4000700b080c4c03034042e2014801c40e40e03600f052554030b0180d4050312003d60442003105030200c400040e641542c41c40c0250106d0380990f1807810555559040c2c80b01482002c0d8001f040c080100940500c080c1c80009180420524010713600101902c4214010031f40701c1c00e80010849104030100007922180e030039140f408110682c0d9031251079120390001580e91030703044001000182c5035000c1c0c82131082944a6446140340c00030079542c0c01c0c080100b0b40310884e602000004e410618455480004060500c000100200340034990031120080c1d41040c03600c5215440c10400c02c00002d03c04034419141c440020030154890f12003911140c1180550700342c0c1644211510000560301110701b00d81071000c100005d155101650300f209010440c1700e601e80541420440300c6030a41c00103411182198010954004150b000d045020b400d400c1c0c2c0c06500d1004d02e40ea440d59810300a074500f520 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 541054694 1250 541053444 541053451
    0x30405120d0c03050a03140f0402030d080c070f06020708120a06171c1403090309011214130825021509130e1e0a1b0f1a070f0f0308 58
    0x40205400c0c00c0a24006202c1c0da41800024200280411551103960080d00702c525202c0a0341d0341c10701d4501d03107041001d00d25002200c09074800d2144080381c0803518001c20005005202c9411400e00c0c05135070b5140c074841c41590040c21509290700b080600c01150846000e0301015984025038107490a00c01d0b10300d401d80f00b1b15001502d401e070145107003a0144030001203903284403251220882020351b007402d040d603081d25440080c407510305000080200d5100040002d100e0f04101343c8034004d14820510514003151810f41071403141c03084903000300c2e401a4089481e0840d01d03124442042c038140b8003051a00061201c50404c00300660340781015411071900494009401e421010008c0c00c00c441c42002402002e0525021150113582c0d140140c0d140500b804049150018206480c240c0c3c250001520350342c51101106880b64140d801c1e000c0513880100d03010004655162608001840c1404400f983d0710789200440c44001100b04541d1000070f90b00080802c206000380c4260040100e58140074142c03c000a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 541055944 1250 541054694 541054729
    0x100204062019030309050304050a0b0406031103010605030606390114060105070209040f0b0f070219170f04091109030708060402090f07050903062a0717030c040e09030405 75
    0x1444010000140e2402d000d602e42c0c0520b00420401c03070508044c1e040d84210b030042a0070111001c00072807240d21000c000d008403041a80c0c1001240c10910400702207010a0250500240041010414915180c1c1c0a441c5c0201c0e100c0514404091000d21a507000307004c0108205400314240341850350715028401c94006101d400d8050880307150240009103540301d010402841031091034085001e01c8100700801419540c800c01d18240e500308040e05040866003102c100006120700c8401d161517030011440c44c841c440e480401d907468000c1e0514a6142600107582180c0f109005000000f84c5003414020030009042c030000c0d1658514200040c1400c0c4922900806000c2d40b04100b4440141c881080940d8031010740500d2841545aa5004071010301c6030141d100c0e0305101d00d0f02030111522410084000c5604003415038111710b014040170745003601403c0800740549160b08402d50400814500866215040300c825515154036010104818002903d1880c0d40c0e60000c02e060042d0700b03101a00700c5102440 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 541057194 1250 541055944 541055953
    0x80706110609030306190308070303050f0a090f0611090402130302010807080f0406090c050607050c120a1703131704050306010906080319020c0301020c010e060c2502031002040620 79
    0x20003400c0f60360380320140a0f1707070045000c4211010503801c05400381c40910f5109071051f540da501c0c1c7c02c00401911090355984141e03402350b400b02c1e195102910400a00a6000d0503c070034400c40358035100700405500c0324814078101c00304181142c9996600c0200702201420301207081607030940c000100141c400a0246051100e04820b11414441c000304071b543c826406031300440c0100091401e07000c2040c079a40b00a41180002c241030080003804645070a82c480c003900e095201e28030072030b4066075503100748801034800c8021035850202c00480000071544a0350100780c2c13401203140b507960003c881109484a40d01d055000c1024800c5141c140070302801410310b80c42c02e02400e8103006045c0e03100d00c2400714040c4d100441200f90010346d0b00a00c496040040004e000710340b00d80016044501a182c1000e140425005280000701c80100c1c010a0700c42440700c417014503540e00c070364114007154284204026645881040c0007a400300909000600c0a4012541e0b950040e80d0005080c0c4204d504081040760587c00c03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 541058444 1250 541057194 541057201
    0xf120a0b2409011206021201060302031e060d021e150c0c030304050109090513061a010201143d03120f030608030a03020f040806010306090b15011d13060807061106 72
    0x211551064103690100381c4e40322180740d55281440c000e01c03860701c040d2110b1521400005140d6050345c0a188117a18520b40340d8400c25404000508074001100c0550340641c0c50b468100143c280360100310403001e00c401c014841d4150080029a80408168130b081d4030302170000c0c80146138041484145e00e9207005034010f500f0b003810400064140c140e81e001c0d021f01d03e40e81d075001440010807072500250b40c3c1c0d04000b041201400000401e0441054418100d000d50708044a150b540b1850614240c03162040c1500701c0048041040c07104a591401d04078100c48a41c051082985000914524001184580d01c0d15102d405c44031800303040c51030b190403610140344c41c00300b082040c000c0100c12118001000e150050350351140901d0541a4003071a00031110038820080040200942648089500d5004003644112603840060584c1801440002240044c000c22040d082c01d82c81c0561200060380003d05442200351405142c004540c0b440e40139120b81e5102010800a042d0400f840c4000c280c84100a00750b07604d07 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 541059694 1250 541058444 541058449
    0x703061d1b04051909030302130f0f050f0105070618020907080f010e180106030501022a1b060f07030e1201090c26030a09051309050604020f120a0b24 66
    0x100e2000c190703802151601d000510400e82071002a02e8034104540420120005042c0280290005c071403061400d0324624001c100c460007903c4034411100d03446002400c01e07041c80c3c188200d040910f60503030305004e41404040c0018809018100e6962058070030000502458010003041c40340c080d010300d0922240d07006004469a0300742d00581903c02024403800c190701c41c0358044550b5026003000300300c50351030a0b001008000064000307110481806540c505100c800d800f00750380041c2141850701469100300380f1000c511003503040c00c0c2004500105070905040b00c550030340500e5807219000304e0001300c03040f441451604d0202440440075010000070404050265141d0543c1090b030b008420465030345504000400441e400100445214141500d8030fa041e80d07e8090501911400f070a8400c094080000c1c503441c080d48140145d00703403c00014059070700c4903000d0000000384170489641012003015001075600c4200031602d2800e1041c0d0030b203029450700d82d1410598450604010300500c5a5640000195 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 541060944 1250 541059694 541059733
    0x60506030f10050619111c12060e01080d0c02030a0204090f0c0803030903092e0513060212040605031b0418050915010b131503021b0a02150d06080703061d 68
    0x5505400d00c0144006e0940c9042d1a059807215038403009a01b04c40d00341881d903441001e112610329810010320810303440c0d090280300c0c500240158181d80c0c0c081d40400d91154405d00e0103860b11800034055428840264000c41d060300c003004020b4490b600715944c603004120168204038010b020803000340d800d50410f00c41c3c0644131b1185070750040c8039136142d0307803090f0880c0034521200407000070ba00d034111101481d800018000c1d81010500d000000d4915400259003400481d0000701058a520210b2074103040144c11340b540e401c003501519064050340014880309000c00c0080001c1c0c18200000c1905602d00c041c98026188000c10540c225085903c02503030442c104188507040d01c0c0035640d2561a0421407035500c0801206501c440346800e2409501161700350150300410b40075031510061b0341400c5524680301c4d92001003203c003e40050107520701d0f00c58030308407001a2114201c1500082001070340c81c482c3e07074540b040c140c00660b0b245a55400c10703580500941d08401c900301000d4080c0040e087d9074400c1c038101 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 541062194 1250 541060944 541060987
    0x1303090902071e0c030c1707090c0c05010c0201051006030207110108090a0c27050f22061505120d080601030519050411041d120a03060506030f100506 66
    0x1607a0003061200801803101100c00310940c1c90803400e01070b0512418030341d1114103140310903a490443c5110200e00c1501140b40e00b0b11000001c0028040d052602d40000000c024400e034140030401d00d6600f0b2400602c0038000c03941c201006600121b01c2d818208561801d0710055070120003410320400c021800140140c0300c0c52600c8400b4284044144e0341d01d0a1141003240c040030007800700d401c081c40455000c1c1004400d01c42d0b040d0120350a55081984554402100c2c416142d4100b00c1c0001c0b000a242109480045143d600c901d07108007040283d980d80e0300041e00c2904140d552000351440082c081403c0c0400701c1c00821a04000402c03120f400d5003800f500501d000340409040645480001c1da0b54689202508042144910100010b01d80380c1008055848403d03800341c81a030404180f11200384042d0b100207014030381d00010706500801141d002d507860307204004e41e2013816251300300060a643c40d00099417180c1000302c2d5864140c134082005540c0704030a074100d42c2c440d40c000d000f581045103048103003540 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 541063444 1250 541062194 541062209
    0xf06030702190804140d030806040b031903170a0207030c080a03020f0712020d0f02070b0c161203020f07031709221401051507150e01020f0c06130309 66
    0x549488080d82242400d0355040d03904500c1c041001c1040401c900c1c480100101c0e40c0745210740044150b03039410062001012500900000d0b00c070004a1964903141c0d102d00c030502001012031750b00608008031014030700b04448040d0082130a80d907080c107032425841c0c10254001381c5013400310300d892166540585081d800c001c02924808000c82c001e16454000d504542c040c00040309040e8403a0081d00d00020403265500800006014110456481c14042c84200d0a5080540c0140c000f003400c0114095450701303e00390103607c0d44952041b8800e441c4007108082c0180c04030722503c103503508003824060300c2e00c1000102540907500112040003c216200c42074110001d101180365656601140010301c604061004920002004000002482c001ea40030400401e1034140442403a070340c1c1c4080100460342c800304a03026030410841c00300003520b0b8840c2400c5102c050180000e00d403141501d01400c81c1c0010390961107441b00090229400c0c9402c200c0c0541c00842e07107c2046178003a02c0d03540101583c102c0c1c400c010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 541064694 1250 541063444 541063447
    0x9090f1b0d09080f0702040f0e07150315090509070803030c04090c020c09071d0303031005040506010216060c2102070605130819290f06040e03210112020f06 69
    0x140712019500100a550f400842207602d8070101114580d40e0b0340560300c01c80c410303840c0a103803000000d0300b030060030b4032041c0074405010980c0c0f40007205000501c0c8010507030105540c902c0c0380d0303020915410381c2c00c016001d02c0398002018540852420310b0124560865207440c0d100b84100070101a042c001c44054440388400894410100d60702079190010010302e50707602c20074880070050215030008280d10806d4400da12005240c00240a143c0c4900c02540d0426404017445424056800d15800080d088007040c1b04451a444004400c02c10501090300103400207000c007000703981440840488001c40307404007014140d5200a80300c0195035986c5a00c2107174144007002c40c0e803450210140c8001001003a08506039601208285030850400765105021180442031030401c1003e070700044010100150070840720a400d8030391210020380110002c104c84d5005495096036101d042c0140040c014800c01070504035410000d010409004200581194051149030707031000e005603403048081d4031805010f58205 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 541065944 1250 541064694 541064707
    0x20d1103031f15030b090601031a04020703050f07240c08060f040e1615020c09040f050a06020703030b0f040c0903020d060b06030403020708010e0c0619030615020309090f1b 76
    0x400d1a02c440d40c48490100c1044010b890f4540d090b070440016030000301c502c4034071036590100640031103041c0c1c6c40041c02e91001802d81c08480c2402d03402840c01c20300030f00f8683d09250041ca6600000d9010400843c0ea0030315140c4000043c00c0f0240c0c1c242c000d88028079041c4040c44d11080018607020008154910071346001c40a00302945560703001c9070380c60031030100707841440380c050744c181060844610802d415040080f0302c000f060307072002c11903000c8058018002c0c03405440e1f0780c5079030003d101145c600707030b446e809818410b0002410510040058903c640c40100d4616038403001c20090741244107849001390f0800e96249440c5501c00728038001e80b581150386400310000c50a28400400b50001c400360040b80010502c0185034000407280100e540702c40007407000120000d4500e480d0141e081819030001000c2c0310400c0c218032103030f9030b425030b1113880c3c84d00090030f0399990314aa116140072121140560800140c0c2c107814100014625400324041d0103103c4075060008030407814121103079a128160601060302e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 541067194 1250 541065944 541065991
    0x150f11160f0507260307030e0607030302160b011d060108070f0c021011060a020a0903080c102a03050c030a090c0e0726160e060d050a020a020d110303 66
    0x41c503140941010848142585aa40035000000c1061258808200e044a0081c00c03030742c000110380113244d1540c2c4410480c0b003070009101840c0c01820085041c1a024030250401460004420b40d1050190f48030307012552400c20090303005407110300c1c00365140c4222401c000890360403409203038011010346411a0300c0e032044201200c0140420030003d60020052482c105825405855081010007040c1a00c9203030700c80300d030010101d2141d45d40e10000304045800420100e54800f02804800d2002d00c180c805400ca4000d0460484030010118904107402c602c9806c80d8184a004045a141e030504040090b4101030b03455200c14003004200e51011911340b00785204106903080410000d0084c0d80034501c490801ca840903155103000c095084900b41c03d00611104154101441030056925809284080d1040b00040721106036000c10180c10000030846100c1401c040e2103214403600426174010307101c60b10705000a003030640441c43ca8040241804103821144000f004403a0841907460050500c43c600142 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 541068444 1250 541067194 541067213
    0x605160203060903091203031303080c0d021309111222020303040b030a05061e01031119020304090609060b0301090b011b0303020d06170a081312150f1116 68
    0x1002500740c040d08052002d03040001002e81342495040322130b841a00980c465a0741d0b00d010403518080c0003440c07603e982d070100e802011740b583c00c01010308166140080c005c0b9030000340d900402d41038942d954501b0080041984c18403881d0501d00c0420506841c000074014030401c3c0080191621061908407490741c080641d44850ba48001070740075055a481d01d68410340e42c41300390401c8030740d42c00540c1414000b07021484c05165140484088007110410b9008100c01100100825a1800321131441003010b5070510f4081504c20010031350540c0103540d070780d052180c1001038031141e900420300706040c600e0030300c60f0200390b000341c90541d00d500c04000784881c000700c012100c40010f8503102c0c010700074640001045c5035040d0000c2c0b50801c0c11040a020045e43e506041280c0c6882d800030001c203030080e403558000128824020710804d001611281700c110340f01c04640c002174001c148210740e00007410754085005180b40c020440c0c8548407400030080fa084010048a907440b0348088049036000050040303080000011 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 541069694 1250 541068444 541068487
    0x40b0c0a0c0303021e030a080708060d050f0a0309080d090303110a0204090305040311090402090a18080301091b0504150e1306141e031009081e04050a080a05070605 72
    0x5075400011a600e09001e5114600740319160b480309a40702ea90500b483e40002140d46180c126503c99903e50b5a040b011107a241004d0480e80e4806202d40d02c0c01c1c0451420466440d04007200f0001d40750101c51883c0103022141c240c0d10042c034613004100000348098009404c2c904594140c203100c901612480c090070304003850390300300950051912540c042419844006001501d01c14142c4955913180b000800818410494000394880c81c0880020624500398000758a0198035060030f4000d181640d482030041d410980100800342c0c1c1d580300d0030602c13294801ca01c1c61001e02a041c0725240500342003541c00c50f0a070407200001800010414600c2d15110b114600016856150003000301039110900360f403c1c2004008590f1090002c00c9000d94510442044558aa01e0050003044e048080f410700502911985800b55000d04041c001035a65041001034010351030308041000b6071b500d00b01001c0007069002c580000c00940d12100901000507070004200081d1000c90602540b114100301e0b0030b500d02208030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 541070944 1250 541069694 541069703
    0xc09080a11060c25060201020705070902090303040b03010e0a14250522080606100813140a0501090515010636030c08060106050c100e03120103050d0210020f040b0c0a 73
    0x40e88251428801c80080c800d01078081d058000300d00c1d85d80000303d00741d01480c8000b4180340c00086040042e414194010401c505004c1c0c2a039040c950707654000c00058100340c0c010380e441490740007004002403c920402c0003680004a00810508203407640b40c1d615103a0340f000d1004d060b2100410241c0c070f80900151284107400ca1a0252190581d20f82d007001b1242502c5110040d00ca5034000c07a82500d04035000d0204d1104569500c0c07940c3c1d452107100341c1e0340c50500e1402d85000c2c2e608847c0c54a05d540500070300f21558052070012a480f101da00c1c040d480c1586c00c40814541404002c010f20007d80c0c458191960040594102d40d4034540c4242c145080c964501c1b402201046d215400000b0400e148a07041d0840e000032056032034aa03031b02c3c070b0140c405201d8026201c8468228903003802d140e1961384d002a0080509004403401c29006001c040f520080a0300b0a0300d0f00c1d0b01100c0d0301040c0c20390421540000e001c4c41d0b40158140805140440600c0c040d40c0111008514082002c041d168010400218201d810 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 541072194 1250 541070944 541070953
    0x2b0504090e0d140c03091306050306010608180304060503041412031f090b0607080d1103130b1b0a0e0111010c230c030d0b010509040f020d0c09080a11060c 68
    0x19945059441010b102450007046182d080020710340382d0401659901d42d03211000d146042144410080101d00301100c801056580e0070011540d501c1c01c0024034042c0a01c3e8440140a05010a540f581d250300241d1224a0394004c010a001c51517004068a8125a0003211042940c041c04281d50608800d03c0800c00112804810480d108003156040800000304008040010b42c80d90f03200010744813881e0140780c028408000040003e2803d20081c480748250f072000048d85082a103118416600941c0c1512809242030b01a5081c4160b0b0114181c20011180c9911008480d580118505001d841009014000805e070a601d40da4050480070350715540b031000801010782041e2000c0c0c146515031245031710203003d110000c2c1a00004c0d90488200b001c0f401300460078007000034059006029030b0705c0d1144c100b03c018048012161113601428a01c0000084c0244e2142022068207044034000c1a590041260380d03a403c1140b0312004c6031241d01030f038200c440302140c004840040b400303e201d003005c1c54049101d03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 541073444 1250 541072194 541072211
    0xa09050105070224180901030f1415010906050a1428030816050c010804150c0e1305090c0409230a0210020c01090906031a1f090212092b050409 63
    0x404c00000e000e94210505000e0f8003e50034420b1086c441c83c00d00004068500c40b608032000f0032180351519820340e07000c01c11034000200b46450300e194071a0030f9001d110915202d81c0c1c00c0c003007481c03e800c0d224060620b9030280d0340f03c0101c0701c00203051f040d159450a600d900445803064440390081d0f00c0c2ca409150007481c0e00d42c0e40e04404410314000691a0741c1550203001d0740c1e4602c0c54540c403030b803001e5002e243c0184900c04001c070030420410003465003d0120301442000c00ca8094030340c84810110080000d03c01001406203017003001c0f18180541900380f50321403403510311600000f9036624010304a500c002450601c00080c4030103860f140004050740694855000580302c202d055000403804800c500a907103000c44140d0300c040c110103490300c0703020060840c49190340c08002140307202180b40c0c1c04501b041500c16401180e000e2008807402e60f80100e000ca42c0c0002c2c1030181300110030103454002880f5001404e0f42500c0c08125040a0742e40d600b101892807600c001000e509206100f0b90307000c1d050a120400c42c1c1da0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 541074694 1250 541073444 541073509
    0x5040503030a170a0b0108070f03140414070626100306020f04181109090417030a020a0e0a080c010518030726010501050a050d03021c05040314030a090501050702 71
    0x740041d088001c401d802c000041c1c080c413600e0041119010043e1106901ca07180c007a0f041c0d400041440740c00040643d01e840540f0030400c03c7c1c05060186015283c0c110200405411a0f030034885160004001e000d0611340e2200b1a45910103804410450000c890f035040d214101c869201d000d02c0da201800c658004142c0c00745c40d501c40402041241e208010130612031084000e144181e5000c5951a00c4112051160f00301904060628941c040c2c4a04030304011400d8003018003409800c1036131007818069001c00c1030b045054000030021060002186d42805041c64986829610b000d1402058100000030540440b02e0b215042036801c4c020004051380e03c900d07141d20030303801d0041c18010022889808420010120901841682d040e50809402c9011050401c0c0500500030250403045045200e11210328100310b202c01d1540c0d160000d0f0f0790315603075514a0341c1000c1c054110120060107494004100e411043d5421820030400c8800038203000ea229001c600000e21400904011000d407007040e80c100b0356150 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 541075944 1250 541074694 541074707
    0x120a02011b050a11070b03010509130f080c0c01140d1d0a0f061d1b01020a050105130c0503030a0e0d080918010e0c07030e15040510050307090902030f041205040503030a 74
    0x1005195500d03502154601080c3e45d0350005031283e620034110410040c8814204102d90540c01240410b0b103e844c0c2c100ca41d102c102c411503401f025915014080391515015009200c3c5007a080024a040c00043c481c00291a02503c140110b90520a03500c201003800458188011400e80000c1001c1c0c41007041c03513007065001c018220314100c0b0981c0c9401000700a4161a4403c0b80015805078010002080408030041c0111394030107041e8150321a02c8001000a542402160700c2080102e9240c0d1010740380c0c0c600b00000f101242c0003e442a0010b004004425a000c0e03610f8000b14021201035510b11003038103040b955440b0b40701d881504441c055214042100c00521340354100c6904c840c0400b096a07030102103c05d903001e100070080025000e00080710991610f07a542c01d00910101d40114a4143c2e1040000c050100c1c0c503015a0219001004005503290030a0100004025000c005d526503d00f0300b41114031000010070080c489180d480e00d410a10780715006039006494043d08407030b0307551402407025000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 541077194 1250 541075944 541075957
    0x105040309060809103809070c05060a11071203020a020624040209041107050714030d080103030f02010e06090a06060902040f0b030c0c060411090a0e120a02011b05 72
    0x1c034144110004031144110415449002d0100c01707840101291074841000c3d201c6100c108005841881c942d41142065044002c816240c5400301c0d0300c0c0703948003018400c071544007d0918050228114107c00820008105e4682c080c0b03541c84002000c2800030000b1545001d09a009030801035402e00d8505a150075030300604402c200c0d5002c40c0e4450f60390302d0111050f0302c002042c003081d54461960b1040c9070b0402c0c1e000747c041420001c0c0042603041d4111101d5450340c1003040180c0e840d60018108100035602c5903065a1101c009401410420703203100006044c0c081c0604c001010040a10680d00c0034910030762003424075203030762016a40e8504010000c1688c0350030100c41558800e10701403001400004d144215002c070b40c0719620313444d582490718150f5507464200030320711001d2600421680d0242a020b101551050780300c0c5941c1e401041c0c0d80303014010340d990000c01c00303000b46149c00c8482e44010000110110707a0300c2d61108082ea0b03030121040484c00b6107071960500c0140d915a0984942107600500504074 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 541078444 1250 541077194 541077197
    0x4030302090120030406140d0207030507020907050c1b010c050f06191b0c020d0506070c030305010806060a03080c1501031a0f010f090209040b060d0603020301110f0d0902030115060201050403 84
    0x740d445000f48056a120b036441004103070344100010003915004030b1061440102c0c0485843c200001889140c090340d01c042011400594001000011450640c29150304000d451a01a0401c0c22406d5600d54482d0003190b80c94494003151881074080e03105402181005a00c402640c840d48032210010b0380d24442940c44004144014000c0500d1211301d02c05c0e0003100011b1008440c95400c00c0d0780964140c22171a03030a07a00300491800c4940402d508100c001d0284800c1d959401e0002e403141001021201c060f0410000307504988184405a51a041e0802c140c0f6040240542d42d03800d894015858003003c05803400076200c04800020511881000d10490030303414400400311969040ca00d1080080300b4042c007018000403010a0002070f149602500d110a800742000810380e0460740090320941212840c1091035803145014070850800307026481c840c8000c40320b05410240c0c030511404590189848654103140d8400c6280c0079175600350404010041464810340c9220f48075100280a424111020360 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 541079694 1250 541078444 541078457
    0x825061b030e0304050d0218040308250c1502130e090f01020c06010b16060e100c030513080f0909010312180609150909060f180203040b1815040303020901 68
    0x1949000b40119003420309000041c51070642480304006068403002c10a0340c00c90115030b060304421181d00c905c24000d43c000e84030308115140001401008411941c000802d0203c0d010946103407541042c08070108a078001d9520001404038000c240007030003020b00d100c00704404244001540b20f94000c801e80120300c03038420b0b541495000940d29090384100030240109030f1003040100810080d0740c010700b2102d05007120040604820703072920700950750703540e03018107040d004240d500c3c900e00744a07c900700c02c0c0441030400340200e252045031407904201d2554082c1c80180300041702c101c0c800b1a00111a40900000c025070700e2035840e800c20346512903500c1c1701c0385c000c682c0c0a01303404c440e80c1840000408950b459502e24880f03500300386400c8159a5084552401d03c00c215034085500002d60040501824604881c07000d0355240c046034180c0b140c00301c815448040d1041040c0000301b0b5110407000d030b01400c1104000d0280f502c604100c0d26103c40e0f0380b10416024245014402050361580007000f6811090340c420 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 541080944 1250 541079694 541079741
    0x2016020906040911120c0402280f121503060c02030a170412110a0b07020303090d03290d06050112020f040c0c02040f18060e120a020a082506 62
    0x120490f284188043c040005204406001c0c0c582002901c1d250705400c025120204a140301040036600104903032454410700c0c82c480312000783e40e03e80020945d805840c191020700003805e80900a0741584200001c0c0c6516011807480c07941c1c110b64000e0003107501c4801000748108608000791a50080504800024403001280225a906840c002c0c00ba030341100320f0b40f02100140d2015240c070f00752960401030600030780c0460400300b894214414031982040d0061507580ca85000c0017400d180800ba11501031500e4840151402450385085000000340c07a28101070140e052070001d6a20f1388240300091050341000008112031484c02e040b0541c261099401d00c2c41c00000d80c08001c142c5a00b400a00b00094690140304098501604178520100c48420001111407800311403400c000c410715829600213846102e000c00403c000c000791601100c0303c282d43c0c2d01340780c84050020345647e41e070f50000e04140740104203000c840400280d0020160114100721118447d50307c0c0510251602202c3c6a2075118a00f980 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 541082194 1250 541080944 541080949
    0x201060b070c060e0a03050f0f011d0c0906030138011b030c110a030609020901120213090809060304141209010504050409080c1f05070e132016020906 66
    0x41d10a03903503000502c05007030341c1001c03070450741000071001041e40001000000004180700b030060b010501c2081c009403580505240010382540d0a4980c98038114100e46a5030812101c0400ca2030725424044852a1480c0c483c81c00003409010440b09840d110981508000f21105c1d00b5400c1d010324030b1406280500500648006480310480e80300c0e5880014a04d09007440041d119102c00d021041c1f003021410003c040e040042165684030f40c0003154042c3d610b01240d4254a0440381150052003445d00051411049a01180300945200080a12244c0f0ba0640e84200113500007a50807440010f0112070301c81c641810541c3c0e015005284510013801010050615440c401d81204c1c040f0906031034107841c003841c1a045c4801424810019103495209000019000700140220040300c2d50049a2200c42c4000c1d81c58001102c00103450742e030038002071280345001ea8135007549203580480d5503480016203500e480024003640d403407003600301c44660700040d400002c480084102e811481c0252003e13460b03130342c03030805 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 541083444 1250 541082194 541082197
    0xb090f16081603020a03092123091905030a080a030c0206060102061b1201260c150a0c0212030406020714030a0807020604090614040c030216020f0a03020a080d0201060b 74
    0x4000344046520b40003141c81c280690000c2484010500c2c000801c0d00740c0f071322035180c3c6458030880007188907140400003490a0380054105084d034408503100c1514501702000000c184103401520780102a0404400c4246136240102001880301900780c5c1c0d0860254500043c0781c3e80081203120101c0c1c6030840149082c2c3c800550320b8402c10301030700203281e25150380601c081078a0000701522109001080502c01c012442c20941740202080b22620174507041c00d0000c0e002412000c240741070542e1049154600a56502c046031900302049100580d541800240455070461003501c0a504070301300e0700c031403a9010b40000060003205d103560309980302540c40701602c1041150441d46560b055000600000100f5240d20003480020305c001d140e40c2c0340c55511342c15441651191350100041c0b81100751002e0050501d4015264500d255280840ca00030350a500c036080c40e0031318100603002e5040418514180d441d009501009107030014046c0241503580c40e20075a842c40301220403001542070620001c1c80703245510 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 541084694 1250 541083444 541083451
    0x14040824041106220e07090519030f081b1621060c170702010b090f0403050706050606041206090c0f050d06020c0703060c020307030e090907050d05010b090f1608 71
    0xe00005102d1000c0c0104605500038822041d8840085070444070800d036010000c6000341501204a03001d0700c0c1c044e4015010b13050301d62086000750224107076007a01a03a1491117105507603120311031010002441c1404411070017803442c64240a403442200100200c1e0005052000f001207003035441c8800d4843c881e4005a24840c81011180d0200c8203007100010126044150040b130310746011090804001c40c080312110f410f03214000582d659907240041d0b41002100355a20500501c1c0d6a040c5013419a0f006003075124001c4080c0a6940d1240401e10b01d64964040f24010446404265800c0804e424a0001441d42100440d0907141b08a400618000c20f110454202c44c00181400b101da9001c0d29480c0203507002c50741461650061820200c002405440b421803c1c0c4082d07030045860300d91030714000d4010210a02c03594450b981400802c0342c140740004001c1e080e150140c4039540000d01c170f40745c91030141504804095110840c5010441ca28003400c85052040c00e468034400340001c686042a10901800e8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 541085944 1250 541084694 541084703
    0x6060902040b04051e18070201050a021219090510020408060a09020d031d0306040c0608060108012102010309020904052404020906120a0210030b1201020c0c0f011404082404 76
    0x2030108014528041c41125a480e00c0c00c03620040707100141000401c400c020401c042286c840d1b0106100307407581e0901c2190351050000004616001d5070010a80da041402041e501002400351010810f000c8190032111100f03034400101e94000070f48203003c502079001809603070380b284607400005220011a02440440e541c0280100007410115102111400c580801441e818000d5028068494508102991080380600c42c3e840d8031a081c0b80e40244480c10240c4034138108002c0314010b0050b40c208100c508402c100454010103041203c1c07005a0141c0503c1c48065402107000c07041005015000c6201920300d8412421061000f0341c42100140c80381c0706403000b9400c04007080000b45170303040201c00517422903046d00465071054a25400203003d49124203040300041d8442d60213101d28180f03060646458107450009605000d40c010010313a55100c81101749220364901ca1700342035031f81d010702c840b0200d050741034103941d07034454441c07109a40d114003030102164000c00c03150020000c2d801040040b805039900 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 541087194 1250 541085944 541085947
    0x2031315120b150c1c0e040b04050403020c040c0e190611070605070b041103060a0c030b0a0e1920041503110d0515030d0206040203070905040b1602120d0906060902040b 74
    0xe59044040c0d080340c0004003140c4140300d00712a10728282c1040f11740402c0c05075103940541c25044144416078a41144141c0a0b0b41440705000c0080d030003007000c1c1d201103801d880000d1110f000040c01c4076501e0800300a190446078921013500a01c0707800c039100041d5202038440c0321035078000d00c001c60340e2080d031407041e6000501c013480b290340010052116030340c200380241c00c1c80b100d2001c410b00007800d058003036580415155a40c09802001a05030240028824044450382005450490210350910f0010080c0c44040306405c808000342000e40c0c441c100e54030140c16a55440c0d100310f18030942d0340e48140107101c1e059a403846624015440303405070107591244502d00d039080081948016020348809001008000b4032800d4441c071a4030204100d08000509500406990a1a00516040a1198012044083c18a402c01010880d16422190400c0348500c00000340407942138200e05004020004802040b4002020f0907440d5880e08003c0740a07028107400c05c0b50958403c081012031089100c0d40405100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 541088444 1250 541087194 541087219
    0x510090915080d05070507090212061f022d06040c0e0f011508090c041b080c07030806010f1e030204180b011b020f0d05072c0103110102031315120b 65
    0x20480203010300610079801c560321075484c8d00c0c40c3c009a070040390030504100f03e00f504101481c80e04c0342c0300c040d00900d6122721460304405410025107030626684601d4062144903044002540342070711a8460140e03060035074074036080c54034144041e00490b204501c910300d10500401d1000c901c152005e81244c0a815610044038010740301076500e41d0b0000d000140751b01494086804a84a900800c0580320108423a084225912000034101e02009403004885040610500340081d8100690942041090030314110b43d02029004880d42c0841c911046100d05030f9184400207103130150090015503500303003001e00701e140c40d01010f50111003910300f115000490100845c2034010070800c043c07110318000362414071144500800710f40503090584040710150b0241d1410003032001190340005010604c0707901415020b80340c1070000030072101030101412403501000d00781000e038020001c84501545c41a01a1000c5a1311250380d142c800c59131710200081200b29198042c0c3d15818440e00005c1c8200811240741041d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 541089694 1250 541088444 541088447
    0xe07170c1f0807030f0e01050a1d010506150c03040801110415170103030305070507021203030406050606030411010305130f0609171e0a02010b0303030109060612050402031e070510090915080d 84
    0x100510300c01c070344591b5072569908204828001c4611480103000d0114201c030940415410240f4010403140160b4585420300c01943d8540344a0070088944007049621019011111800e52140d0350080615602e4901185800c0742d2070400b40045401829401e41208401101541d028a440c83d4207018801200c00502c0003d0081d0301043d08035803039242c51403d00400c0d90100e1603040381c0041404c40d5900c04000c0104100c05805900d501690a1707030072508508040d80c90211014156210358141354484d80050011012804031074001904810100e030000e8190604400034006c1c42c805540302080390003000001420030701110303d042d0105141c007501c07150701000f030182900080003c10855484014002e00e9a5003040958080c11201400003201803500b000030b000010390a03e40800c0c503051104010150380e021a2181660a881000100b04000340c0300302ea00b0304055401c110f9010081c00606640c4581c0b150715402611508001000f0220195486418005291148c14502d0f44140c404d5410309 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 541090944 1250 541089694 541089701
    0x7090204032109120602040315090203030a080c1c05041703060303180a0e010e070305090a020906090601090902040902210402151b060f040204180b06040e07170c1f080703 75
    0x1030580e460f01c04851611013034100c800c000e42481c1a600e00d9004038040c400d01c58080e03266010310f411090108096110765004c6900c0b070003130484013402e00100300001144034140c40100e881002d440d01c52001c044205440c000000d203410781d4160f1b000d40d407040040780310044400480f4064103005008500b4100c100f001c0450040c3c22801d0f05070807800c1c0200009001c641c800c0828080e0400080b640701925021170300030f040394030042070500103034002c49002015071660303061701e908020151040c910640e80e6000503101000243e0210050b24400180012100e940768041c0c02c00009168201d80140058403042680307002c2601c01030b520642d541100c1d031a100c0c000004003c2595007901070030304065100012800c0410440340000c01540301d200b080110324080c45010500d64032000d040d21180202e4441074801a0000c10a034082c3c1e039603045d600550541045443c00030074902c8040304030125900c1c2215110035040c000180a41c15000c0d0b0740244001000390150b804103690b880540c60381d28840d041f00030307 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 541092194 1250 541090944 541091003
    0x30318060603011a120f0d0e0319080a0503091f0204060e090103020901050607020d050109050c0a05030312150409241b020d0807090905070903200105030a33080709020403 75
    0x85d4440c0d00c4c2003241030704090114107500521500ca591141c0c00400902d824a02c030f4580040c81d80242059040003c0d510b6001e032880c50005103840c42e1a6541e00031002d00c0d141c00700c502e0140418540c03258205141140d0000c000b52200c0c3e661b80c003040c409580a0101c941000c0c00700a600211150051000b070034084013031b0000c140000c10141504019848d22801c43d500810103540d2500400c0300d010560400c070340024010b003425001103180c6840026001404000501005c981c141140e4a140c0c0c199a41d80220840503000160f498010140881500700701195100d13000d11141040c003040c06901c041c4268000025a503000342140c0d2103013130000c40e030f0060000c14802c28441c03220804503114000d0b22910348a03c4060703e0304801d040c00c2d030400301d41c00003034064241c054000d1044501d03e0303645d1110507a0381100746140d0206509000d07000c42c1c034203901c618040500d40c030400080440d8501c039418140d0100c405840070b4a0066458100700410703441076000203440050008900c8034811002d912030b0f00c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 541093444 1250 541092194 541092229
    0xd09050612041a09070603060e06060714030f0c01020405150708030106032409020315030304351504060b0108060f01110a0204020a0c1b06020726030318060603011a 72
    0x61200c0030846100d00001c0aa84d002a135600240083c07040d641c040c4180c00c0a040c0b514000440c51400b180007400034401c51a006100b60921804409442da04005984441c58441c43d15500c640c4440d00c124001e4200b41f14040c41808040318115020b00035001f202c2c2803903000046245036a09040d000c1d805000261040c20409031540b4400f11560b00200121016011001c130150383c900b003c2001c0603000400c958850f1003500200401c103c140c3c4000e00840075034209805804444022080903c4d41c107407640c09000460141c0c80c20300c0407074480c44000702d03c03c0d8420102000700280c0e03000111211b0800722805904a00700d160303d500d2a60040c2d060b407400c0c8520b0030880322800300c1c1e0350200b01640c001500702c4021519000d5104100216000702d410351404500403a008189000f0b40290340360410700c01c20700300064a20880305e038921002c40060310712010714101c9a6a003869403035544c110444103400002c81c050440400e03041e1606010344030303484258916051002844c0030810507800030b691994103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 541094694 1250 541093444 541093463
    0x1704032016060c030e0f0907140c03040e0402181b0702061306121103100b0c10110301050108160816020708010603080c01180312051e04060c020d0905061204 69
    0x1c0140155059000540300540e14202d00714820b15000d441c240701001d0342c51040c0440c0b0f456003510707140d400740507074400305900d080c0c0852420082044100d200e40320646c2d07028040041d000c102121f28240c15070090744250388a00b104401d06c10386405420090343c0502c1001c138820104503501d4604800b515499000424552900ca5214a10901941c01d54032500c003046030400c6408015060b440349103071841c06c0c20809840d5141800c2d407440840b003607019000c0300100c0030881c5000504100300ca08001c0b4230414080101c01e41c0007d00340042e4000348107041c001584800050f4801010f010f1101c10403280f902d8620f0a916012825261010b0303424009045200d20385c000206010b09002d440011402500096a140070101c5540d00351a42980f040c4c3c0d4050440145a00007507100e1003096804c2114440024503440300d00402e10250401c0282ca480100084188002e10140744d00a00000c5200e4003203410400c0c2191040d60041018031a20f640001c05001c0503200100500000f58410300c60344564 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 541095944 1250 541094694 541094713
    0x15080604061409030a080a02070f0209070824030a020904052e06050d0317040f0b07080f0109062d05031608060f0f1305070302030d0f17040320 63
    0x55250100440e8281d400c180c9480d007451503110000c0c041504100180040c42c41d0009024001d004524064024030819500041c10428058907081e01242541d00078924044c42c1071925001301803000949030280a076262203c00f801030600c501c06a1450310016000d441e02510503000c0208560700104155414051406580032003044102c92100c0300c6602072040d140f08031074036001c40403590a90001d5001c1c03422200110003281d0440d13041c10000210a410100d1552140750002c01e41205060041031110306906005540750400300b0a07105861206c80600240e0740d4006c0003090312200d2080c6041100384990000800184658442400c00b41c0c4e10166400e5a965001c41e1920800c040340d24030b00542c1c003001b40600324081c000e40d900700004041c19603060410f0860050450350140c5014156a042c0001d0003c00c0418041400210340040654200d1010700801805000d025241d15001402d0304240040410f80c40d508903001e50341507036a03104c01e082c001c0710502c3c8135211114480054480c00002d0b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 541097194 1250 541095944 541095959
    0x311010e060301091d03031005060d0b150d05091f090302030c16030c0e0f0c0703171906060306082805030a200c031c0c200907081915 59
    0x70b50007801c039032000091082c401c6104805444071100416440d8000b0024007040c610082c0740c000540313801715011070b5180c00b80c1007468000c04540e081503400c24180e0100c086040c3d0103801801841180d0030301071065543d5000195202c3c408204286907000b140c000d4040c05d0342080e400001320354030a0040b60326190031080ca861500413230320142c074084124448240b0070800c840c1d400e4401401c1c903841400c864146619901440d4034000c0105042420100300c00d0103162094045055051111071710300c0e030a0600c010751341c0000444034000d001c2d80d0300340301c40014030034070034030910701118488400703000380b444420b02d00342030300c04c8607416643c640c2c03441e145040200300c1c00d0000346181021921400780502020080070b0124191020585158001d00e840d01d03c00e85010880b03040c08214005030360300d0040130503015074040c0d10f010300150190502c16441001c00033503400d0000d070110308036200780140d41c0703442040b1001401110049841c9141d02e4003001011860b4000d5810044200c1c0c84000c100e40f40e03c903 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 541098444 1250 541097194 541097197
    0x1050f010918081c1a01020c061e071a0a0b030106080a030e0906040204030b0901020c06070e090f0703060f09020c0c061e070c1d060108070503091e0106080d0f02100203100311010e06 80
    0x5801601201c1c0103205c0c0c031a40e010800c02054103010303240c840c10600300d4412569001c841d400c03a640c2d0407038001082800c206018003508214201d0802c0403120303041c14075000006005840205029610b010004030700088000b441c440100d9040e07903100c84862103203041c41215600501065001502400301100160210391280d02c590440030005866640c41003440303140410151580003803290030034101107140c4038158880e0b40404e403002801816110380008a0041c0300644c00b002c8542944000400c94483c0d0744c0082000c41c150500f1265101051010000c40d0300c50403501e5901b0004054038841424101c0c4007030003410340246607460441d81e070381d01018419606007000c0341e0640c001c203040102e15a00004e6032600301c80f80e4a485401c0d4600101c0a9503a00b031121166001c002420b2a400c003014003d40080000d002c161040d00d0017000d5101000d000304003001c00e407101600070450600718802c42031090f2807080411403100000076285403204500c80078081d02d0141006866040300999450740e00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 541099694 1250 541098444 541098461
    0x1527090804170d090509070504060507022d0a0b0c030712030f09080c0f0c010e0609032409060708040201020705010c05160f09060812030f060d060c0201050f010918081c 74
    0x4029203c4068002c200400e06013081d00443c0c86450b000c424000b845078410b040d80c042e6941801c00c150f0300c0545000113554411006802007541c104888000401044403501d411800000c1d180030744c009464243e1446103008a00f0190b0565009014540200301c0d414142c000c5a135a6003400150300d429824200251200801c0654440000041c914030b00c901c00c01166042c0c8580d04c028210a083c0360000030008502031182c0c900c14038000c2801d1080b587d00b80003c0301c195410800901c0c240000c0c8184000c14081159002c00b18001d04002520361402590068462507051f805400118181801901c141141480641e800e2050ba001c201e80e0403660711400c0c000d0311126060002c8103281201c01ca098604a801c02c0441e078000080300300070056410182c9412040d03081400c91540d0b251404550f1034502c90401400460402c100c003400c00c0c0e0103500841c05860300f810590036a0b80c0704c1c2c4840c400e94110000d4075100c9121050002c0c085032070710025152150b846540e00c403904414521303482c16a00001c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 541100944 1250 541099694 541099739
    0x3050d030207020a060302070b042004060e040c0f080607080a02041502100c0309030512060303070b042906030a060f0b040e011e0525050f030405011527090804 70
    0x2508509528101c80f000006025a14065203801d10756622700744a01c0b0050401404030340c4100150f4103d4440e4075509455440c054000c0000c1903a0314030941c50403400352819140ea0680080115411800d600180c041e203240300010805921890703022a2446070080443e81303407076070a11003c20a500b4403a5466904ca01d20b41c000c00701ca02401560301d003140c18811450381410300e0410301c400040d400109455111045201c005541d07070311000030074210b10542200800c106c212504100400c0648001d00d40c00b00c10500001d0489003d034504015883c0050750102c2d810780c445683c03a0001070301d0741c21105c541c10409c040031414112180c08681520030800310340300c0c1a512200c0c8852021004032212a180c030422609000301c0c2408041c101d421134a5103400600102c01c8400000100e00903001c83d0460300c80c0401042c1d40789414145603000340b030410114030085e80e084074005004080e162040c1c91044084c107034640085072030764003107000300300204003219115014000007907484000c2c0c500902405c0b94 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 541102194 1250 541100944 541100947
    0x1c02070b130206070f1103101505040e030d05040c080d210b040b090a020703020c03070506040501051e0304120e010315050d020a030b04080924070b0c07060504060b041104082503050d0302 82
    0x30380426048c5142c00551000c1640781100141101c1c00044102c0c2c00c4071002d036000206400000c0360582140710790f00c10040d50728140014441000041e8083c403003102d4141d42034802400b0b80f4001140e240180c0300740f510001d03469840409000711107500480c10410001c100103608002c0501040c02c0d024100c1c0c02d00300c039940c080361070b006044e010300c0001da5100003103020344250340c10500002c2c100c0c0500c1c024181006404945113009035428420101c039035040e01e40310b5490349040d181030307440c09038078107480c000241c007203001032013294003c2c00385090040c19035040d04215400c100034052101280c00e4140c2c0c0c06041c18a001000c03903407000c2d803240291700410b4003a070340364440300c11b104c00f6422108020050180758500744202c0000e1a00b41d51703100d42c2c0a56007038080d45900c61a8041409000806060355207810117000803c41c00b03070700c100300110094400384141e05d111074500000340250301c21507000b83c0007800741c4410300c04900132401140030b80d003940004254480d150985411441c1c0009000b2030390 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 541103444 1250 541102194 541102223
    0x304170a150519050105030304120311010218010e030d08010e0604020f120601142803111912150306051e01080105060910060f140f0f1c02070b130206070f 68
    0x803070083c00e080c605622101400294540404070b56a44103600c9041d2030041425101402c1512422244c1070340d1101400070354440312458400200d5070b40c00b00606001c20381000d11a0340724200826100c50152254a806000742e03e041d204000c0a000142580d0f802942088060000c013096805000e10300400d03a69040340e49000000904a440e2040322450081070610a20800f007950001c6040740c0340c0c17204807446a205c0c3e101c1c026000b402c80701c0f0295600581c00701c1c883e00d13142818500000045100e0b0b4600c00003d80c0d604241d803c544090030301c1d00182140b0b1106101180664100e940c00030300103103c4070b8803180c8800010510f00400e03000081d01d80d460f8000e01072039291890440350003602641d078107901c9500d04940940711030301000780303c024006a0300c20b25103420001400d0b1445030b1000303812956204229005d020051340208040700384103d41c03170080d900c0c511481c4255001264010301c0b01c0c80b5501d604155170203c1c54a0300c000c90780040100034140014072541150041d83c1e1080344907020415 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 541104694 1250 541103444 541103461
    0xc02030c10030219080f04030e03010603081603020105010510390f210e091015020f060a0c05030601080a0609022703160b09010203190207060207170304170a1505 71
    0x18008884a01704860402403181d05000149030641099041c24080540c2a035840844d0140c00c0660010304102808184040050103074002e035101c4d1403090f4001c100c640c0e245d504200404003149001c0c1c0021b04540c001280510383c0f0002051100605603440504602020425485810000d412204124405506c0c0c0c1084002135465025120680e0f4170078070148499001010015200300d450310407058000400e01c1c41c1048003450001c4d010810030b001107501e02e020b000e2359075680382050010500c180d070001004400c4610420b0300e030900c69925039103140c440303100450303c120024180c481d4140c1c0d07500c000540384590348028001c5902448108450341001d401818540c41d0841d030072402a08074090303c0c810000400a03110030f4541010304e003520782c4a0180102d14500440724503a4a100b0041040c0924640008038103045592590881c2c1515487d05025809941c602221401c1c65106210a11080400c9041e10780300c04501811039100108076110f81290b95540061900c0e140d03665014041ca10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 541105944 1250 541104694 541104727
    0x703141b061501051c0b0d060e0c01051e0a020f10050f070e0d020111030d0509011b0c1a1305010f060f120f020d060b1210200304030c02030c100302 65
    0x6600c400300e00b00e4400c0c1000190403032207002a28004030a00403030050b41c0d84655030100c042d030a40a080c00c0301c08400703460088000c0c11310111815161048100702441903100b202100c411070303500000c0311090a03640c0181a82e40e000280e100c2c0650082d0350203041c0c1080704200038070b1f10004042c00454a401c0c0007004544080780589200204804520b914104e80c0710030000f003006981c20720305a494011607480c0c80f400e5008400e40081d6180c00e080c140300030318805400900b0707400104031003901e844900b887c00381c40c005a030040003172014040524a0602e0345420004641c006808075407072548203210307a6803030300b1102044d184005c1c06a9030441440301d06000640e54006c1c1508455801c1181060389031180003080e00200244030300d120303072141020440160441d486640000c1c02003034111014525a680742c2c1d071032202c000240380c500b144080135120040b01c2d4800c11202400d1051540d2507a8034100c0d120300c0003280c00c0e41c0621914075590081d0716034030082084a25155070040c4c0b02c5104041c0c55994 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 541107194 1250 541105944 541105951
    0x1f020303150607210905040e070f050118030f050a060f0e060108010e12160c0f1a1801270f090f05072106050409060902010315060e01050703141b06 65
    0x15010070701c406000035102e040e6600d004495012840400f0340c0c1d81201701c58441c100d400c0785810a0801e01c40c40d050010000d0340b0780540300120b142d0a040c0740c40307000468070030714000c0304200c200b52608801c0003c5105450070301c0304103000350203481c0e40c03d0045e111041a80d035006070800c0b03007503030b10400a460178409000079070151400400903c0b0301d000d0384520300d42e1030240800c1780c0482000044c0e14000c00040308141001e0175401000d81ca406a03031039a8150480c1c1c0681710b8405043c2d40c0356a507605001c012000c6460f182900a4000c04000c1044011a01d079000c25190700c0035403040109802c1e42527051080340b0000c0000681c0f0000c0c940c180b024080598804240d21407a02c0c2c2402d0030b00807120342010702c0c00c00403c0b122080151050b4901e100174082d101960100380c00030719055080301803050940000003024000e0301d09028211018a00b120680c0c2e1512401c0f000912f10350241120b580301d580205a00d80c00391a001a4560605140c1c82103913101c407114040500e01c850410038070140c00d100c040d92 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 541108444 1250 541107194 541107199
    0x71a010e060d03050a140712030b090a0b150c011d0f0f0111030a1509020a0f110c0f01030507020a0614040203010c09060e040903140711041104061202091f02030315 72
    0x1075440e810f66025000e4015200f801d020f000c01c5008180c0408034142c20717217580b05e030814950708540c50041c4003d4001d00703442040c54051a202000210985d2003070003a40803001018007160444003030705000441c00c0d0040282087c0325501d480c0c040d0809078481d800b8041850002001e8800c10340101030940c40d00450103113840742c99040035070344460074491300207581d4490042000030500c0540f00100d0840c9608540010340c0c0e040c804190030313a005500038160f04d410303012a10f48030329280390060503a540d1814040034560080b00384403040080d52181d000030350481c845004a44c501c0c03407541e81d0902500c40074402008003c4201c3c013080306615007401380c3c0c071a00c4820f00341400464100f007801010390380030207025130065449030000e4003058031804542600303981c850102c0e42c9520240c40c01c113502c601c0c00e1000a120328140421348110488050842c0c08880d4180c0f00c0c021190100454000a50000080c1030303448036a40070f0f50004040c5c20414542e010b8040e50155a5070303d4048469644d40d40d00c05840390 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 541109694 1250 541108444 541108459
    0x170105181501050405130209070806010207091407030f021303060902040b1207030f050a12051b012706020702060412050d090f0306020d1b020307020f0d170c0102071a010e06 76
    0x80d0341e807040900303040d1402a100410715070388901c00d4030749440300190003d42140c1c400d400c0248450780024031500451090307081e41c0146589026140643e80c40f441c0d0b03010b1011200e0041203095000c2c0d4031510400350422000f60030809050740c05ca00c1b010039030b44140d82c41b6403a110b00c0c0c8210301e010b105034200ca880c1161a18210317081e6101803550791041e404010038140d18100b061051100401c0b503404080d500081900d140b441c0400010142c1c0c0188480040c580b120703403101380c28500e040c014640c150300d0200500141802c8550003d06050320b9902c2914059403c02c140005038590070010705c01382c001c1c80c00d04c3c40e0100c1c0500d062850b005040701e8640400c40110028010a1803030b02c1c00c0c000700da41020707000d620f0b0403803562004020714407a8502e10640c039046002c2c80d16590084054a0614000c0f03c40c244030048070f40910907600d2a4080051164181c0c1c0c07042c0ca1060000030250025408502c001410140c51340c0e6040c0402126010b0010a41d4500004114100b00d40a500707601c81803d0303074401c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 541110944 1250 541109694 541109713
    0x13051f1d0a020d05010e030313110a081b010e0301020a0c02090c131406090406080c120c0d030f050705061f0902090310051b040b0304050715050d0207020a17010518 72
    0x49071194807112000388288446010076090007025001102001200c0054a65904080c402c61801c010010b5049400c3c080d103036060541c40c6001816a800c40d540d40015007085e60841e1703a903191a180410241c0d040c005894040c0c082500d0902c06400368032603a4580e0300c1c04100c0b5004010012600401181040408011400710304c0c134180304000889440700007415240204c100080d0f0345001d14503600f030708245041800189a1000908000742030340645039008114140400c0c036890b4100007a9450308800b07110407400000b0702c0380200603000003107454000e08100d41035031254204a0169900100e21041c1e100042c600440e09000344028a0050011440c3c51044c501194a4406041410106039500c03000035640f00114449a07800d8020022450396641d2a40304151054000351800c1c2c803603100c0c003100421441c814105280403003031030313491326420000250814400b940c40b15008907080314a20344000341035000741482201d003001010000c1290f1501c44600c4030b0300600689003c001d43d0100303202 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 541112194 1250 541110944 541111001
    0x304081e0307020103270b0402100903020102070519081213120b060906120106270b0a030821070e18010b040504020d060b191e050f0313051f 62
    0x2c40c0d07262a420b08001c90385103048113030060820300d2600340703c1a800c030480103101080800d55041d44114030880e9000c004003584003084858000a02001f03000d6407080e0824001d52401041e50008400d12894035100e250322030101b9400d080301c60b14030b10a11000801c0c0804a00c01e1004610040d08500d2880041480c0a0311001c05100f0090001800b4042a002107000c1d034450140b15804003881c40c0003800741d180d03078110120300c00300d1007000300942d07207000f07209041c0808180c0204c030310040c8000d102c0010242540c482c0c4003140d00c441e00f104020a5046c0301ca00d99505220300c0c440c8520290307215180b100c0343c42d40500070b15000210000707502030300c258010320880f42000c2c180c034140e80041d1401038640e101210914000c2c01c0a400c429140c01c004104a07035074640c0c102c1e004168082d5a136840c490420b110808102c00c00108c801003000c07800c140701c41c1b08c2410706c0101940d40110740d00303204410352695444d401d00b000b0000c0c2c0340c00c1c80c1202280c009610f842190048040c242001400144500c00c80100e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 541113444 1250 541112194 541112197
    0x806010c0809062101120b01080c030c01080a020c06040c05123705030f190302040e06010e2404290f030c0f04080106030c15080402101b050304081e03 66
    0x180039200e102c3c04078401080c0c2e008901c03900f02401c0a0740c00c441c01940c42c0c140c11030010406c0c40703040f19050070040000c12524404550ba15070940b020b401044004101c1006641107400248501510b0303500b03003c81640d82c01c0070884030f4003c4c1d026a0041161704d051034107128a000303291a01000ca0f5000404012000200610400340710340b601840010710004c546810b10310198804004d05030344000f2403103e030a64000c100a003881040c1d0001d00780c04021000c0c0c180c080e801b03244200702d0301038440000113071154010550f10801a90080ca52102801030440b400018110841000b495507800b0805020700004007480001c803c21805003070700d0741d00c40115020a0392180c040740102c81c0780702201068401406a05070b401100d40030200b10307291034464010a008003828481668903803070340c4500040744d4081c0b412120030703024580e560031a55940c41d001c0c04ad440521801e076004014801e0f065140441c030b80040140d07030f684500701444e6141d19254a4501c0c01540140c62101c0d03143d20030142100500000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 541114694 1250 541113444 541113457
    0x308070e01020f03130f05090c07030309020a0e1f080a020604030f0627030906030203060906040b0a050301090809210706030c091503051e1605030c070206070b04030806010c08 77
    0x54004000c140d0000100c0c107005808003444001d110110f441d403461341004802ca000d592114065000b0300703503244c04100444c1c00a6441002c0b1810411441020034840e80100142500183c100714003290b0b02d40d0b0344500000211303000341c020034a40c924880140c0e80089503800410010008000f1080c031a000226a840707207100003080c0c01c0281462204009050b009802404d1460700c00030060600e6440c03242000e90059821400540e0543d40030030068020301c25a40544005090251203a0743d10b014000144080c80c24640d00000b40e160000e95a5424004c1071011842032480588401400c800e0002d110000326510740c07000ca4441d0003401c002e01c0002d90344c0440f852032802042c910700c0c2c2c95007030700c4c0d0604a800000310950a02e1789842c58076019040795008019051407400481100c48450420344416904402302c42454904015075501c00c1024680020240300b60301c0c9400265400144554040c6030105e0380b44610108010505070000350ba513a100070300707081c00c0c030040d0b601d03543e40d129512448 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 541115944 1250 541114694 541114697
    0x706050309100905061f1406070201030e030f180406142407060e060a0912050d11070b071413051c021801050a050f03060115050d0203070804060e0307030807 69
    0x100004a070031504100c06401e0060b503820411451120b4280740391038080481c0c5454625090080142c20802950109402c0310a24441440c0319075443d0200000c603400000300b0380c1015118a0701e241d503445c086c0010700d0b03407540006d125940c1c0d80702c1c050280f0f500440d0881e050311840c5480320811260000c10804c2000b85800c0301c101a982c41042c142c030802011959405106041c0410460200001c590250f60705100600c01c503140c07556500c080d00281c0d501c00000509201f00f84290445550288019100c0100520400310300410b2805184840f608401d500385c501c0d840c4c260070f1000072508a241550508101050140740c080c010001015245943c81901d0180844200200e03000401c406801d1401d0350041c040041000143c0c044c0d4040c22080c09842e1180c161000b0000c0c0524242c000603811680140c0a01802d07880c0c40542d101d04030110701120f080c0300c01046081524420392000750310441a5444420290a2034284070381112604820011264410020840801c6d04140002d500c50706a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 541117194 1250 541115944 541115947
    0x3220219240c08040302040b15030415050f040f0204150e152d0f0d14010603020102160302130b010507080d020a030c030e03070f0212151e1e0a0204180b1f02070605 72
    0x40d00402c000d43e01d1202d649c00e007040b001c014842005500c051170309603e44001003e01107a02c5101c0c0500e5162401d80d4002c01058200090500504140d00010b201c00d08100c070381031039140c0d11200d80300041002c960301c1003451012880c115040c41c00c031003804103501491a14003165038100c1503001e0094400d520052182c0a0b0030782c452442d03660300e8034028680c1e03404000319051104510003e0301a00c080d00049016004650142c0c01034094003c100d011030760024104600050060f1222000300444141181040000c0081e80b02045802c0c00034070fa180c0d00d060005944103801280241100c480c64140300401d0b0034001d5141244600005407161075410000c6040484141d100003018403100081d254480d014142c0e24411031071010000c1480b80c52805880030342042103a0760031942040032240700c0b4841d01007000380382079561520940b039813004007940014500364a1750036446400100351900e14081c0d45541d007800e100c0c107200c12000e45200031040200f5540c0e00700032010f034498070350b03000380c5041000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 541118444 1250 541117194 541117211
    0x130f0e0117160e1501050c0a11040e070b030a0c03090809010f030b090a020703080c070b0f07090e3108041e050604031208070503220219240c0804030204 67
    0x8003880421402e0034119020525141d031441c26004040045665140114100484107030f154002d50499401581030009080711000301d41c0c60444518050882c55006076071fa00c12100714410822018000d031210402041d00c0303141134a004010303100280c40d070600b01420aa0b0550020341c0480030380d5040f55003400d06101c061092502213005003072044003503a01484643c10300035007160550007032003202c0c041d84e0b4180703860383e580111041c54071481c90014140d18019001400508401c200590008214584210056650b00c0140041c100070b50701c420303605030794409015403c032213031420100b148030310ba107014452202900c0d05121b50145110f1030715400c91400f45010710f500c500308808003416000302034545803a281c0c2040050340f202c1c0e0403c080800e150f0400b05405034041c40949214004c40360090f8117001d803404140c0c0001540c000103c0c0c000c2203108041100c1d54000c101c0c1805000c00d055001c200380344081d032001c000c1d41a44511000d1007104805030000c20750710000c0760306498055502148000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 541119694 1250 541118444 541118489
    0x6030106030905160609050f010212030609060a0810050f0105090f0f0910090804080705120c0d020d150b15040f12170403080706110405010503152103130f0e01 70
    0x4485140c620400d0351005800b085486e00403200c4004c1d01c0040d0340441c50356410200681e9554810250300c40d40c0c01061000076868038000d40794641c0944060b100b080c444d66034242c990b1915004892114220792100c00304140084948a814011f1608075000700450070881c100400a40d0083c150b048800034003000541000b00402501c0200c2d0400f5100301725520741c6091501050b041070040403801d000b0b040000660307251000007072182401c0d000140100e6404941040002c209100d82242c10100c10184000410150034402260310001d1001285605075441004402c0201c410180c031103200a01080c030455020822101c241c03611024083c691290710f007003261910304107450007860500c00040c088204440d0101412000344108014040440303000381d05991401603001c0c0760300049041c030019850714010082460f100c0405004070384410410f60982c010842c5030484018a030b800050170414602c190119440281385045008406600b03101c181c040d100c406108044810460880309030740d04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 541120944 1250 541119694 541119703
    0x715050c1603081047120703060f0e0907051e010c0213110c06090a030c08030402120d0c0209101a130b0a0305071101050c251406220206030106030905 66
    0x9000811714015062000c21011080714085845803461800400540ca25442c0c9145246491030b07100300b40c3d0b410085661000c44c0c40c81c100800302d800f09900c0c2c03000011003070090724030380005d450311408444070380c03a0032030101c2d01d080c0310382d0b00090007001c00300b104a403803103032022103100c40000904e452046224203000050351402c9090303a00c5299443c11841c0300244040c0c3c0c00902e02c02010303070280c50341540c42000f560344503450324202801140b001c850030400a0b20340302c01075900901c002d00e0080b1540040c1145440c1000c0e031221400480d030710381014015071511019045c0e009421805449020313041461080b8960742a50300f48041307403808602d200510010007800c00103040408002921a82603420040280000b6283c02020407506c0828074603418060003118443c20b00008002d150401128540c0c2425041280b1005a10300030285407001070a800c6030302101103900c100400b80380c10707d0800301e000610f80b01820070510081c04010300050f101d103001d07681112418180002c45030490309119082 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 541122194 1250 541120944 541120949
    0xb0a0309080307090617010803030a020307030221072d050331030f0c030e060a0201020d06080114160206012c07090e0a11030a090f05030715050c16030810 68
    0xc05801100f0850f482c2d520003840011a50950b80b50042e104c0a0103601c080c50703c0c00e00a09009400c00c0001607085d030b03150b030002c40c1c1045071407900504d82032001d244402c0424461100300030160300402032040e0700f580320581091120350306101b441d0a20001801880710860382e030a407c01c0c014007100081003a15020800841c006600410260b1900034440501108000e1042240412043c10300d1001c0540b14120189210380c0c142c03103400c06960324004101903500410b5000c01159020801c6034280041409000001c12010380003142c035072114a941c080d00e060080081079520314030b207001c4c1c18840c0d00160b0141119081c100c2c0841e100d40f034416a040480e4803541d0005000c1d10f50b02804100c0707034232016680444000c1d42500f0300d15160440c000d800d03100503003900d6804030701c148081284061554440c007000c0b4419136020402c404160307202810764210304019141c80f00c80e840d8014080c00726000c0c0d113512000201c8018542950700c2000d08100c8041f010140800c80e0803c0003c62203401c1000c0f2001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 541123444 1250 541122194 541122203
    0xe13020d0602030603010c081306050405120a1d0f010203040b1c0e0f1005070c0b060a0f0e012108070f1704170708070503070605070606051005090301050702060403090b0a0309 77
    0x505150324248000a58000d44009010758a40b50f01c01080c6071280c0d07545070203070700d01c91203900120301c2e90b8640c00c000c1c150141050b50a4050340002154044050f00104801011a12140c2c24239100603a115802011940e640d0b001c1e50150340c0400060380d01204440648035031010aa132260702c1481190601404080d883d01c02514110600c03005090010341d6003106207480e8104c0396602808c01441d4251030080c1c1d01440456001224040001d0000070340943c41100a0400015165540b00c0600e102e000b41d406010595801d000501c200210410028001d44101c0201030b51030003039a8900019124002c400340110040c83c0d0310b8000c0249542402402c15020011140c45c1d903114107414080e01441c08a584c0300d44113031440005c0b001004201e40d03048807401405000083c1c60141d090f503240d4002c8908680c640d0340c4000202d481c1d506c2c00c1d441e0070010360303640c0e801d0f4507049580103040c00c680000d8200c00035940203000304000643e011302040140c40300745003030b00e03100c000307024083c0c020f407242d174400a0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 541124694 1250 541123444 541123459
    0x1218040c0908010c0915050c032701080703020c030a05070303020c01060b04170c0a06030b0a0e040b061e09061201200c0132070908190302011d03040e1302 68
    0x1064154003031068030a82c1c151900820034041540e00c20b03100d20b00e0502c110821001e4100c00d02061034020303006080749000c0c00707050b00c0c6000a0036070506640e20852150500e42c0c0480d94203042e09581c400c980640c8584103050451821400d00303480da94901806014508001d0009001e501300340c442e4050750315484019000b0300085445a1801c0e0701784d0040e02404403101036544014800030b20001d6031408410024040240050a1071812406441c00c4c042164002c65181400603000c0341c1c84034210300c41e03402604403146604101041040c100f4110309103900140d15048150b0303441c2d840c1070030380d500b01c8002c4030030210380d4102042050250046424191166100002d52800c50412400030b02c9100c0b9511f0007040803107003c4a181010425200c0da83c052000880e450501002d40303411001d8120569040800859a0394010107160100c0c084132922104040d810100070140c090007642c080a00401c00c100c0081b1281d00915540d014034411050300f420208049040520821b0102502940280400b03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 541125944 1250 541124694 541124711
    0x908010e010c03151d0c160302010225020f0d061506050c12030403050d0b0a0902031509162309032401060219060f1d10050c030108121804 61
    0xd034000d052000310b03034000c43e00309aa03000703909032030b0381390300b81510300c0084040c40d5080b042061140e80c038401402c080806c07600f0025100d0350f002c141e050403030391072080e40050303070310aa18140007100c80d10848043c4200344945c0c00500051380c6a003540401c0c03031020340da0111002060304240028000301c80319910700303114821004c518281d02c14014040c01c4092000c980c140c0520b60040c101c60703c011503010700050024002c6c2000181141c00c00d60351401c0081030401656242c001070412030740150392600130504035413031424645c11720785600c592000c121019188001c5030440064140724580c003095214017141d003080c0a0b1001e56409803800035101030b040b110f12980002080d2140100c00129083c0303024042d0001503a107200280421040c0014a00c511584400303581302c01c061f1030001003010490384c4440d852102610305109401c0c4d050000001403800800c801504401c40d007014041030200a41000140314401700007501141d00d2003134211850355203d5000d00720165000aa01d8282e03c1410722102 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 541127194 1250 541125944 541125971
    0xc15030c070f21090b040e0105100203090301060902030708100e0c090303070c0f030b090f032506290405221a07080a050601030c0c20120f010c26040201090801 70
    0x8a503c0070300142c40f004169510741040e0084c80c01184103080b10544000014801420302014014045085004585c1840180350000b802e4030a9600148000c3d980403041160f03250303102d0b032312540103500d010100d009141444188035400000602c0d600640f600066412a141c90800c00c56180310307001668201c0b019129080c000c110012813006032104070451005c40e02d003c1001c14030a0070a102c81008510701801030781c5002058098001100c025441c603807008011501a0080140e54036900001c3c070800d141e424181080300415200c07041c012403800b410495000c0c1f02c28003e4000d00e02020501920b22041e14008074030b41440982c49920300d01031414080c1598100e194a4000c048080c010300c46030f0fa40a00440845850420351030000b01c00c40784003030106841c00704089004101840c0d4140351000700c0f001c00c0d085e0000d43d0301c00702503034403032030842e1800c0d4001c0c8584461680585044035080f079a6250110900810325448001c114610022a0440e0b0049461600520001c40203000501c5100f44 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 541128444 1250 541127194 541127243
    0x30103020f1806010c080c06151e0d0b0a0603020d0b16030c05030711010e01090c1706071d03010b280e01050a0e31050c15030c070f 58
    0x403030081c9103603500e6014518041e02c00c01c075242d400c2c0c035200809a603841e004440720601c00400740d565110400c000e40d1444c1c002d006461003400c030403400d200020310610600031600100510586100340c0407006d2080c6039240e003000c6506980021005030a52550380380c200c000c000640c80258441032082048040104c0314400610030000c0b883c0d025004030740e4036415401c1e5504038102c940011400c000040101d400382282c0300025101000018074a80440d000324211071001d41c090f20856000390b810481100e0f00402c0035181095000604414180303001d02400030701c02c4d82c10540c8850501e0f00031304560f4030250b218880a1100400d4002c0b030b2071030101043c0d8010100d01c04a85d92000300a004165802c200e04414100d0b04083c0c905150b40d840c01b0707085a280000500071009030340c0c0068041c0b030402404040c000f07405041401440750111b41e850407610749220b502c0114000c07004851002c400d078400f00d054075400000a6400c82e0b80d1003041c90700c0006002c0b4a40300600000c20210f50440c00c440200 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 541129694 1250 541128444 541128449
    0x50d020d060e10080106030b0402120115080307150e12160204052401090e2a07030918060621091401050a0b03010209030c01030e0a05060c13060c03120c05070b0a020301 74
    0x856180f0059251601d290907034216010140c8904080c10101d401401c040d001000c2115403d0000202c48154000346040f02c40207501c195482c1e403000c111041030080c142542c889040d9050385c10420440c200c0b584549481c0d05900e55092540040b42c80d07080c0201c850340550300d03070354020003c200390714244403803a4040a40000104048141c03142c00d0a555002e8581c0c0b0041d6106c4800440d001e5a600ea4036a5188000e6070700450171a5039100000c106000303030030140131494402e444541c426410404120001000740070400100f905081c030401c20582c01ca641016458060308001010303088901c407030400341a035400000c01c0c400801d03c4a00350320106500450040d902104240400c0011400301801d078000d6443c060341c10342020140085540c0a544441c160880c44002d5542d0750085031101410b0140032501c1c102001c90004120701100849078842c406084103040c0600b019241d40c400804500301c0e404c01e00310301c507603808060070742d07034091019140590b90010080d00c9516114041c00d000e0742007072 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 541130944 1250 541129694 541129711
    0x50a120503150603132a0914071b080a110d17090a080f130b0a050d060b1207030b04111b0601060c080706090609060203040f02150c0d050d020d060e 65
    0x490100302c4516105044034021404a805c0210f003400c40d440c1c5583c003805860320f03005903001101809407880103440c4603c0050000f0070300000da484070064401082d400c000c2007042041616600030220441d20041c1c192034517004001c0a07225034075038a0540340120040c0303100d840341c860301009180d4140d2040c0d2804200d50201c0d00c1d440c454a440700345a544190004009022210a01036112558582e8002d0249212840241d45c245030740c548441e4465405a64140f0000e0000a00e0322982c400c90b0042c0740040c408011000d00c7c041407000303203a00484015201008050326500b80464032ba0f911381003e443c10f40102800d135138408150803060700c4405000c180e018103018950000070181d00501400380364036004515546489032540d00e807070091084801c00c0710103541e2660341030003080442c07018521540c410b9080418009243c0104500c050b010300b503919101c0000c100e0920268000325071030810081c0360424940314036003511250040c2c01032140e41c8000703601e032600c001071400c8000846070049103007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 541132194 1250 541130944 541130971
    0x180e0102030702100b031510080d09030b04110a05030304120b060303090a1a0f13180b060406030b0109080a080421050a02270903090114030f13050a120503 68
    0x10012800e03070000702c4451001d82c03c10000c036020351165405c20612044010b041d81c9004005060b110354811054035005800c1400400500c01007004000c14804003205003007500c6501d18599400300d011a0040c00140b000d00542c1c402040781c4c0300c1902c00340140000805580d203413500c4200304a00035103000e0055400340a01c1c00804e4060401100704d90081c44007802006616081071142c8040c01e002a00b04000750b07500300120b81203801d0103009040c403071005030b002c102154580001c011942241410102400e4175201e0a19520340d5540211000c80c1c25034240410038114840060300c100480f03a00015560080b000e44004108403403005100b40c80399085090010001155002820300a0440040241c1d128606a074094074001d41542c40001040a1400d201c20554000b821b421101303607007180b00c0c1d40c00481c0191056030402c810140c80d10746480300394114035083d56141c4a10b100a040070700c21980134000c01040c041d041c0099280e2940004174103015140202e402401540b0480c0e201e0000000f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 541133444 1250 541132194 541132211
    0x5010803090f041103040f14060c040614130e0a0f091a010f121707120206040c17030904020c15252609191a0f01060c030c0501021318 59
    0x4040c800e6004001d0b0300304c0b141e4110f640750303504d450401c00c0b204d10564902c202d400080d040c220b41004154402c00c0003158880c3c0361403a1000144c0050000c04030ba80d441101440011250210600c001c812a04004114081d540368281060b0040c6070007644854824100390207041400704c01050880401140140441d8503a42c400a1400c9004180107080001102c540c4120104403000303c00c191001c41c40302c00a1501d089969015407446050742c2c0e04025030055000c000c10300c400501c00350700824dd0008955002c01c00325400f02d8580c400c00680502c44d40c0d000c500104c0e60002009060111004846000328030300746414600b88104c491600c40441344158020002c0c0c0506c241e266900603450058000307100360325020500c2c0d504400402c14949440784c0014028000c0510a1007000c0c90b002c0c00c450701c0f002c0794800717918600100c000c0c00020440c1034040100040750b4402038201c0115013500d4601e041d5001803078020701a214204001c085407000131404601030b81e10941000d440c01840004004005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 541134694 1250 541133444 541133449
    0x40807080607020d110c0909061b090609040f02091512060d0b07030b010e150a02121e0f0906070b2401021b0301021209010903020709090f0f0203030d05010803090f 72
    0x20212107000c0103800040d040c4001c136018540a4602883c18419914403003400000720f000313004c0480b40c0c01d049a001a05120280c840c035020320200c1241e803580c0038600b682d00404108140318186203240610f64030000c070300140f03a203036047e20313039401000389002c44140e5240e0107038069812010320001003281c1c03200880c10503e002021b1000480d805004412960b541e58420750007400c42800031810300c9548880b062840c1e5940c0600105c10b061003481300d440303400d07109000b490301030b0f00c1e603400c854000200030031581c40718001510000c100d01d204403245d940e03440d400c043d0740f103000d03846201350032010100e40d0400f003011454216102c1e04d00742030210200201d58100100340901e0062031405030b003068200250101040f440d03804c1010001c0e0000d0f1800b0624800c0b4030100710708599100e05a5502d40e4488200356040c800e0200400007000b050000c0b81c1642c43e01d02103810910802050001030200810454800b4000e403040c134252814108215a56544190b88035442094030510414030034084188a1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 541135944 1250 541134694 541134703
    0xa0908030706140a06180c030209100201021e03010503060126010e0a020112150312030b031606021507080c070611180a0503010e280203070f0915060e100e10030204080708 75
    0x82d1944c404042d400701b0f5101001c0d0040081011940415408002100c01a10b5482014000055960006076128008a03160845021506140a05170000c200400942e5000103020f030640d15000e4400c40d03450300b201da8003000d01c014582260190750030003121091240c1d010443d404410b000380c0f5042411070301c64044000b150b1107100c1d9a8440c1c481440c0c1400866040c04113030301c0e40081800d0010300700842e5000640b410b0b03001d14108226502c440710a00ca203a07070510412402c20010b500340ca0990900e10400f4041d003000900400189001190b000140070294000030074044907a00d030380d50350308000c10800314017a0300e00a144c0c1c007500185500040e64203052240410340079001d0050f000b41220300d45000b001c42104038410b41414800d520100150345c091044d14000d00c121905560b406180c1200001510812468421607030300c0010200031a40e0003041c45410a1310446480b80010b9180c0001c3e201402041071103600608925000040540c05500900075507130084101c4030595039400030250744 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 541137194 1250 541135944 541135949
    0x6050a092c07050f0403050703110f06040e04240f11090d0201260106050703030b101b02131e181a04050109080a08040b09060105150a0908030706140a06 67
    0x41c016510070050100069100d40750415498604145082c4581c000c900d0650006e030402d42c0c468201d400e0400030040107110321612010709440f80c0c92483da04000203001801248118800c015032240001c3c01c0144640015520800100701200301480c181350302c0008040c070929503026546081e824164880c1030506644074164010b00714000c2810070740c01160f0078001940180d01602982e01460050094403203001d01a001954600e070300c8240d64200201500c0c290229580244000c0b5451240a544a094104a10b603480e004214019403840800c0000c900021100c541c80d191101c03000b04150721908007203140c05040014400b0806d0030380f56140c2e2860010008112180519440c2140110113200302e80c0140a400002151290b58450f080158010f00d80e0000050440c0d08000403c1507402c01c0c01e0308041188002c1030103604180206044c0d000c150524417070b44070042014101c007445130300c007032003e054280241c0740c403007030140b03005c8015041210041c03000c10380c0800000c1d09586103100c0c8808 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 541138444 1250 541137194 541137239
    0x3090815190209040b0d05030702180402030c0d080904050a0c02070812090909070b1c0f0c080c03060a050409111503160509060f070c0f060201020c0c0f0d050706050a09 74
    0x101c100450744060025400035284640003916004c03125542d42c1c60030081134060380078001560b07881c40c40780304001c4804000200c40d203800d02004244000768030300181100340d42d1003d843c45283c8503032900740000c0c540161a03c2a078082e050101b0003c40143d95048845e002c4090f4080380d0082e501c0c1d40308542c44201c0261800103005040c4840ca082c2e02e48802d2054103d2441803d966100307481e07640174032903540402a41da00e90040403250180082603880303620f400c15070707103081081007545008001f0f01ba9140980103500f8141c0c0480490141c0e5211381c20a001480c00420412010101d450200d10740462403003060311a00310b10709d10003404589501203901c1051034400402d103c6804d800e0948541e040207003442d4100b0414000000302d89071150091103071501540c60462450b1400070900c0d00103582e41c03c108216401407081c1c03581c4050000c0d810b10034001c22207050301c20400e160f000c1489480184005003030b40c803400000040c00c64204c0028011000079585d445007854450158001110007a1138518 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 541139694 1250 541138444 541138471
    0x52208071a070f0c0513061406092d04181b0e073b030714031b12033001050a0b0325030609050a0c17070c06020703090815 54
    0x3070f8101294010391803080940000c01a2140c003c10b070350395540404e140300c065840100b44078690000824455031542120090324044020011401c00000e01000341e1703402c0101a18580788040c0e00f017420b03144420107881042040500d0603403219070301320000243c0300c10090b95030b9000c056150340303545001d0f54048000d214194513400c02c00c640691840403411001110141ea070408002d15207080d030604840e04500c10981704e80b460800d4105102039024004204100394900c240b51004698903004d2007041d61500184082c990100e0350b80400c00301c81e104140000a09500c4206a00c101d1080b101e00c21422401c100e44968240342c01e01c50280101317540300c0961981080582400300c01103901050120340c42c4900d051858065403410000840100441d4036a401885511450301c41c151340208030304010300c410381d1105400742c06000081e6041042c00030590005103014020b1031b0031600342e5803002e0119541d11850074001d00c1c4001d6030160003054056082c3c101c000d0480e10309464010703481c0d8540c00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 541140944 1250 541139694 541139707
    0x110712030e430b0403080a0c0503030403090806180c04021c3201080c220c0f032315121b0a050d15020a030e0a050615010507051507052208071a 63
    0x1b03483c1a002540560304009000d0440e00004000340041e50065200761640000300c0d04100c182410450010400c120a0100391400c03a90500009090b54109405881c0140d803a11040c0d064548545452001c4e440d1034100013104a481400c481080c040d034000d2004100300c0c0300c076100029482a020f105002581d030080e20010711918000d0000c40400c4c0d11044c4800108040107000000d41c0c0b549034048001c14072401518026030f030540500440da004010b20202004c00e0039919032111000502084c1940d2078501c006429034440c070000e000203143c0d54048603a0080d410400b030180f0030030220b2442c0500600080007032142442158400701d41d50042c50203041e4400419614025008194072034100360700d039243d2481402003408012034082c0508080c208628205100704240c8041036903050400c1010810381020540115417000014000400d05029889a041c22215401003c441e04010364104195550600d0742c40e000c1011526048291002c0540d1507406020342121906d40d00c091400400c100c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 541142194 1250 541140944 541140953
    0x90601170d05030a0f09150501080f010b0a03120201110d02030403140406020c0f06090d0b06030f16172a120d1710150909110712030e430b0403 63
    0x5005c0c0b99611600004013810142c80b030b0403542c2a014030065610b40d8850040c07107644414010054640d00c0e050090040c5204032010541010301ca00c030180240c0241d42c60760010a2003900003580e100f604099003611440081002c1001754000e681c01c03008540300d2407103001546007082c03c2c0c41c1291040d4000d000703082c02030b4045c40000d20583d040554003010410250340701e569680450f00c001c0707002d40d41c0701c01d0918047c1c080c10f01d001041c01001549500c680c2442c5601181d8094600c01e441448038a0341802c10800005441c0c4840c0c44c030088107070138010312402d4101c0c51204c03d5501d295812142400020680159203880d40e502c1554400010300401124543c00c0c00d4040e5207410020800c4034a40456030380303441c0e603010300c213944e585000542580d0013002010180c0c010603400c1c1110600c4503103044074540e650b44015202c40d041b80141612a10f40102d0440103010084d09450100c0c03840b04c0c6804040000d10400706080101141c20034030030300700c03012062017220385e4040e03d1060b20424034143c115100c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 541143444 1250 541142194 541142201
    0xe0a051605092811030903040302040605040608120a05040e011203031b02062716081b030c010f0c0209040303150905010b0d0e030f0d0b01170f0a0c090509090601170d05030a 76
    0x1500c040103440d0080d1321400c0101e42c004502c13414404010b5500c0d10b0443c4100b00c295000766001070701c11810300c0018807404102140c03100040580c040b20940e905100ca5069446004a500070031000b00401d000041381d1742840044401d6a100c3e5404002c0380441081c1504808080041100181d00c1840091030340d82e010240151411701c4220150540301d1403000c0e00e4904140415401c440c00e440c240c0400501030100b019044805003c80840000c2000d50003196a40a0040760b0074100320901c5e0401000b140103640090190342c01030b00750189031400b0309000d4098044410325016030f10f0b5001c000600d2488612485050341d10f10303914149002c2103400070401400801c80d240700180010041b00b0007580c1040010004403070280804a42c2c0c0c1c4245001400d109000c10380040c455030304504000300c150000203203a621038010440002c0000030001d044954a000f5000550404601000d00c200044000b601504941050380103141d401d081900701e036110781c3e40204801c0410000e0000c00e008080030381 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 541144694 1250 541143444 541143511
    0x303040b1f1a07060c110a0809061204060b01080601032309010605030a03020f0607080103030e10090b0a020606040e0a02030d0518100c03030b0f031504060e0a05160509 74
    0x200c02904494690030740064140c1c0003420003210810020fa0081006003c1c09a0030303c110f51800c00c100466160030f40c0c1030300e0b014a90700040200a00086829503603035444142c403566402c407075401d151031400d4a0070400818511603c0760200e081d02001641303c2d07102c1d0241ca2030800741c400420249a003c0d60191404400c06410000995251800400d050b1810429210035a0284d0f0040a522020551107070800c0350281030801009410001800031070382002914040ca141a01c101c0514483c0364003c440c0c407403950b0490001c03000c0010f40d40b10b42945c001115801001c003264200149110340031140d41e203501121009401d60410059030100500a00c080c00499050b54000581c440f90310002400080c51128000007140e003030840e410906925101d004810401980e500843d0070303085000a03591520310710b000b801d9101203c001400c020558100342c204003094021110302c0c06681c0790440c0c031142151181c524414900000049a24000000500550700b509040c0f088010740d00d110340742c038030020 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 541145944 1250 541144694 541144741
    0x62003060a0b0f0705061006111c0509010c06110c100216150608060408070308060f0a050d020d0b04080a02060a020901080a0b0303070c090b0111071a03070c0c03080702120303040b 79
    0x6016070340c0442e42c10b0101c0d5101f1203051850781000c50600c24003a2002150544800450f4000c03140342c0c10101040b0700030345d4243e605042c013903102c0720401c0040b01c0340548190000c0041c1e04295460300001d2400300581080340c0d488c0140d902c1d149014030302c01c00301d00500801040b41c04502001c100424212100400c1e16842e0140c086481501d41884a241220556048803030707903800940d00c01030591180f0a5500454121400401245000005600314840e802083c3c41070ba42e402105045695000220030640da000c5c0e43c0001e80d2030141001c1085821116240c00540100170004480804500c216203134a501619a81390b2610342c40c40010051a9001015405100402114000c50a6609040c000740800c0e4404241560171200040101840c41c4140d0303040e03401401c052001c4880c0410004060070500c0d1081e4581e81c950408445680d01c048000c2c1991001ca1000300038000c13420020700a0780c0c000c1c0c0d9201e4a2503490704846540344030444028011056140100384140300c4110f42c181c03405000f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 541147194 1250 541145944 541145947
    0xc05040506060c12070c0501081b0d0f110a080106170a1a0d060c1409010921021305040b010b0405060313050f0d020f070801020c070909020402070f062003060a0b0f 72
    0x1070078540b071500c180b181c090380d13203040003040040c200007100c494034003e00300030b10b001020b90030401c440208102c0300c82c01d401015800854540d0802d545584000051940759900f0f001554a0070b03000b00c00c0d41d100008005c0020104000421f945d40107100002098505419509841d9110302c880b60003003403040050740d400410310222586a1780c641500f08901809190001021544000c3c0904400b083ca810100f071440c05114100b2240c2c0c010007050104c440002e64954110903d5040010750b0341060402984809021580350b664461544018441c500c82c9655801da662030b1800d8060600503441026448981000003500c081980031170b041410f4410001c0724403164251441504190f0f5007000040181d02014092115140070441107004001610013145412082c5c000b4580320340c0079001d005074007900d0b0b007926004c6460300e50441d81195040044880c01601c41e140c80805403490404002503001210409201d0103050011a4010a4002c140038107040c03504c00f01090380c2d040300c540c1c1600c0c00380 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 541148444 1250 541147194 541147207
    0x1602010c020a0603020c0d0320160209180105070c020a0303031509020c0a0506060d1101110f0a03050c0d0e1f0306080f030a11071211040914010b0312070c0504050606 73
    0xa94500b040042c02c01030301c0140c1c071025004103031407404490351049010982051f55503000881001101021102d00c60040f81d500e40c410482154a00b2040c42c00a400c0202082045003090340c1014456049580100134030183c0c0b039000c0c00f111a04465000039500450180c5c0420000f03010764442c0690520010744001000d607030380209030480c6c000e021040310a4200004040030407405101d59648008104c901c0c9545651580724005c08588a00324181031001d0200c2d00d11b06050300300001081400140308448541ca0b583c513000b06150090f0b40e02074950310075500400401030040e084155408000b510380312820900080b84040b1941d40200302c070605503038050110740b5001c2444588242c820007001540e5890300440000c182d09440c200c10880c54010342c4040c003440e199841c101c0d021503000402c400040d9070b04800240200101400207103803000181d00000d48210640208440306c1c022020359440b02c1102e0040324082c4944900140545c0400d00144054a01507000a420180c00f9042608204 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 541149694 1250 541148444 541148449
    0x90601080715260106180b030c030103060c020a0b070f0e09091209041811010f050c0d0f050d020a2a0b0c030a020903030408100f140a0c0302090a0e0109060602070b1602010c02 77
    0x207400c0c1c00c104000341520076001b01205c9501c40c050014064002c5507442e41c984100244880e020600004104540b02c00e024104141700300064410960402241110ba0800120181c0782030200f040c400302003031b06272181c80c0c0140b030a940004d2084559201600d020b248124140c0c000b0342c4690030490b403041e070306d0301c0512891f05201101a00d80b07102d001e2900690303070024000751088809030421000c1000402051403c00408198075101c44807030700341407088101d590415201800382d44401d591907440030450840055200b03080400451401101c0c120a001292000000322003ca00190810200034007103205c24182d400250f601907030188005003400310302c000090455000d40d01940340f41d0300003520703103018010700c6c81114140c1f21020b030304224080c11815481103680c40140f034610100d566546030002e0500a80407104c00e404010070000700e00b616551081c1c104002801541c4049181c51404944580000b91110680d13410820550611400030200200710054480807810003a4110001e80141c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 541150944 1250 541149694 541149767
    0x2191b0308030a060504020406140706140a0b01030b010e18090f010903122d0b011206120308310305040e1312090f050d080403050a0803090601080715 66
    0x851041071455540d0902d42c40e10016100d41d44c000307910592040104100880c3c00034000e5804803019289a52900c410341032107001400b03210a1003580c3e0a0b00700c1000703c02c00a0f0b50040d40050400d885c10001e41ca008401140d40a100c520748581000c0c6181d00181c0304400c10321006d81c0003c81c0001c45a0a00800700c0131800e54480000850100300c2d0b03429003607803d10440c022a900320071140c0b440d5032251004054140c10400d0803a4184030340c3d41d145109007450b40f00c0c9108410803407144006004141d6140909042c88041c00c03026030000ea51200130544a5980c003d905958503000000c0c44200e00200341c4138207a09800c09011800d00c10104000118941c20f200d9607846101807c803005040c0095090242508040c0081e200410440c14014403400706402078100079a02c0c2a6410601c481e0f140c40d2903e640d1069410140c15441080300c00000c001034400114818a80501030380c081c2e0341c0c1c40c41c1c2c6540d0f90507140500c044c10008582000b284922507103103400c582100800c1d4000000740b1000c0340824 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 541152194 1250 541150944 541150949
    0x60f0703050c120c030708030c09040606020601060e04150501080903190c0b180d0809071d04020a0509090703020d060912080f15010c080a020a1a09070902030702191b 73
    0x100d00d001c56400c848250601040d80c406420310101458803040c950300c107899100d1841b00414035200071010030342c0540490305944e444c52015000b001a69101e000181d0346450912a20300082c1000c3c0c511071250600f8040c14064003a05041200100d0800c00150341c884801080360095200a111101407100340120701c003080c030519103032050098031a080c04107529030000c0c0a629041d88001b0040e20400000a80043c4212607151241c10307a00d404c00c555062034240d41c8006503044427940709007101c150414103540154401c03540390302d0042e03640042c4503800707800f2202c4000a8000c2c0e0030410242c00d000c8103d90045205040005001049556608059041800c488001400c4000308240202604c0b1a00d4204a03884a001c1d039030301d10741000802814030351300002c020040c04540002c41c1ca000700700b5600351b942d206440000e8800d86105190100c1801c50304e5002c103200d200d00c0011012818803c5038026200b0360b001d402c0848400c418121020715001c1d00b1940f40c20702d4401c50804200304841c0c0400b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 541153444 1250 541152194 541152197
    0x2010201140c0c060609090a060506060c1006080105010501141c0b0604082113061b1a0403121b03020304020a05060d0b01030605030c24090d15050f0f0114060f0703 72
    0x2114510715030f08038034029006128900075140003060004a406c0000c108400b130782c0c0720030045550342e40c010100d0350301d0050300301e44009481030f4143c4404640c129046070007135845040c002c01850fa80c82c401102c1d00305603080c11080404081060502c444e0941058910551001401003280c0c840c100100b41180d00a501040441d080440001080d184200b003448261405d100c0050405614040c5030b0060b80301e030f21407507090120b010000d074118012100440034607504105403850b2990703c002c0c40d00d44078408540480000f2001c10540c40c0c1003c036882403034604401d012510f034001c0c119500c150020351028100341c1c4d00c070034a070400041e0b540e582d030010400610f200f0008151003201d42c0c00541591201e070006440f9400c940b1440b012621180c41c2000f402d0b01c925000040c0344905102400648190a14981c1144000d0380000a2020440b03400b0f044020225041099035140c00e032481c8526803d880b01c1005080300340041102d200320030003200490000404041c41c101c0740b817070a11925407000c00101e0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 541154694 1250 541153444 541153447
    0xa05030901140108190f0f0605041b03081905120103050115120b0a020a09080f0604120519030b03010f0623030f0303070302070f1a090607050913050402010201140c 72
    0x404402806409520403080c0140c1e005541044d00301c0d600c40d40c0c81034611000304001e40c503110901c402c40f402085610782099507140661040c0c103104000d05022039003528044a01140d0108a0360481034603400ca03500442e030300f420200c9004040c900001c8041251041020900c4000024030b001074425000f944a6400020000b521024403a51818564018403a14009001c08404541140181e55000b108130800503074841c0c0e550410b440c003a45541081d40d083c458240741052078440011114092800b034801d102a0b60b101000484480c400c0441341e02405a03400c4d44080181d009801c007548524008001103956031480709a2011509140d1150151840780c0055040300d50b243c00404541502c1a4007400c10701802144039a42e0344405040442090b41c005511002d0004038004500101e0380084032030401401c000c0990b0846900766a03240f0710303014040210f0703201d900540480d0300c000c40140c48100800c52920b5044002d01c4000c2007a4155500c0c2e458000c64071443c034445500c614803c54000303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 541155944 1250 541154694 541154701
    0x607030e010e07050f0f12070e09060f130311100c020307061a010212031905040b061e21010e0102031e010617150406150203042427030203030a0503 65
    0x803030944486044038000b54100340424000b58850301d481c0244908103582c41340004c08a0000304410545a500c28140c0c0e00900c9408504011803004581c028020303035040760340c1d03030f1205910361a00c1c00c0305a81c010380640b60345080d880083d0081c7d4030070611031384900c1a20b4084030109184401c1c0c0340313030454040040c0c0000400d0001c00066200381c1480d02840860b07224211f1903000040c0d030b40e08181618416034030000c00000c00400001072156079070040c481e0706000c50f04140c900b04003002c205032026807240b1089002e1066120302d15104404814009091407803021550994612044040000c01c010395200c0007000e5014009000442c010070131240500c0b851003559440442c100d0042c6c00400c10813075540800445502201c0c200c680087e001d080c1d800003a481240000c3c0240f25540c071001c5c9034040c40031a0503141d60080050f00c01c8964444c1c03554030005420842c4c9400d80b0003114100702041d4517818034a5206501e0f03000c0c81c00040421000003010381c40350000f81c0b03580c10401d4003000180000082 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 541157194 1250 541155944 541155971
    0x23010c020f12010606021203090601061d1f1106040b0a090c030b090304030312050f070f11060a0e0114090a060c020a0c24080412050f0f040f05040606020d090614070203060703 77
    0x7c90394001110b161407401d5003440f07400a0b8440c0c006104000030480a0541e04260503100b00b032114848c400107200b00e49900a91507003161001c0b0f0303c0d9980d80410400d1580742100203001ca40c15106684c402c1c509401c85d0784840c2004d005101c0c440c4180c8004c4a480000310000721303901508d50289040320b008540311840d40c81c0081040c1d003940d1142030001d00340b10601c02100c000d5881160000c82c05d050404c0301e4403194004807800c000d01c3c5000e01c0a40707d032106011801c551940800094081c08000b407008040448004403044419550022240e0104280e04080ba0159100e422141c074148103491240035681c0b200d400948007900000e01c020841c40705d4124031522107000c0540181c06060000442c603007a12165914500c031012b18060104c0000c040180b86010403c4402c890b030402111900c540e1145d0300d14038034035481d028240c003d51034a030b0f0200b009800003420101c0d00d816561400d802d02c2c2007403c01c0310002001046020413601c14060000103070703001d2005600c550f070250740025910403003c14 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 541158444 1250 541157194 541157203
    0x30a0c081615050a031407030608010e0a03050708030a1d06091603110904031b0f020415180905010209040e0c010801050906061806040b0705030a0923010c020f1201060602 75
    0x80389410a160307000c0420080c14107180c56600a1600e0821644400001c401075001d00100199040c14201c10000c01c0161505580901c042d1031001008000284249800c0f90380c50f07140150103800325005004c40c000054407000115403065401401003580b0134200c0c10040804040004c2c644190000410442d01c00004c0200350417002e440d84c502001545036488100c4d0f204032044a041c01845c1e00030000c0c0500d8090004140e1000450010140550007410002c00b4141800320880c03085003001442403a02180400145c140c80b5618100044001f144071204024855288d00301c1c5d080d50248203031001650342e4031402201040c008040c1c05d4a48080c5d00061a800b8140c00041c40b4010b40700511855450744010340b400f0386410042c2e150300040a20015121b400b99501400c030a82000a100b8200300c3d010010307064001c0c160304d95130b817610746840940d60006d02ca00461072111203000c00b008442d40c81903050001c000c0c000360081c0c1802c040500031421020b555250420345a44414042119550420 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 541159694 1250 541158444 541158463
    0x20f0a0815060d0308010302010804030e120307020a0e0f13050106090c03020c0c0108071b03020a230f0c0f0f06070611030126100c050f0415110a030c1b05030a0c08 72
    0x2280410f180d11542e4000c1e00b9010113000190410030040000380806005e4030b192810b0001c000c00d502c00f10641c25061550f25800443c08a020781c0c0207240000701469001c41c064000c0a98411841440d5a030a481c000d04042000041d111507407503130400100c08659205e07075001c852465401690355100404045d140801e0340c854641002440406c0049040d8800142006002403842009410001d410100e24040c1e03040340c042c01c115a58840040c880c0d809c041c42141d800441410303140e10042d4002c8040e16406903020003504001c1d0310b26a107080c2d25000342101091003005003090300300b00243d1181c00880301e000c0f40e44c0369844030010045c01450044808114018816500d40309000000c14102d501c480100180c0c42c0f24a072121034080c6007501410549240300d04402040c0e0b01d841da54041030200b0005240034201041820350740c00c11500740410b401000581544400c42c0c500183c0d922080f1800100a0111038803135004008622540c06016609920740603036004070b049410008418108240311 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 541160944 1250 541159694 541159699
    0x15010e010503040f080c0102040506030a0207060b182a0c0a020f0d15020705071a0a3506042304050c2d010e060406081b0c0c0d020f0a081506 62
    0x307000b08000034203851004e94020b58414001034075080050151400b901654000617444130000c4200580d05500d43d01a04e4900d001d1007051180c1c90060003403210f660118000707101c0012110b400201c090101c481031040d880f01a2510010000d0038449845858003d0f000c880d50b980c010001c1c00c802c1d85404c400345c400700c14040301c40b00440c2007c3d64400c000c00e0049031003805000e40114141b400d014040c45450001c0203458141840c00091002c400ca2a51000300c20784003140000d074114107090800d403030304100003414411507001d41001510090154200800b89a4450744031044181c0d40728401c94071500c240c3c0a000040c0b61801c051402c1404c111802c031800b40105540c20400d50000e250f00a181031595889006007009210b510040380c07030b9445400210b0304450005400201c02d94000803d6100c2d581038a26405e100078000d45d40b01c054480e00483c01800d600010622003546414041c007a1000c2c4010600003601000c003011a04001036580b02c2c02d40c0d03410040c100c0c1460708103006040c0e407001d000c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 541162194 1250 541160944 541160947
    0x308011e03060b06090301230f0601050904020c070315020a120b0102120a030605040501030f121706041a0301090809100903170715050103200306041101210515010e0105 74
    0x1400c04004065900c0d200c040c01c40d540b950700d104019200e0740112100380030007600a025040c08c045505164200070071502108024840001e210110084241809660141c0d2198500104002040060340107a102c2c82c4240c0500e00c0c0000000760025080a20140c80f011702580341c8042d6880540880190500403001e20b0038404100010307039010518070740d20044d985010b51075444c1090128003c040b2508100d4009250100100c1031140c0284d581e000540b14040705008031003020740849003132218029803041042020041001c0d8a480e801044c0080310f0300041d581640d0700a0300203429181c08403819202200c00140c00202030426a0303440c000307805203080c554400e914503981d00305400492200c0500e1086c02003404402c004d21814044031b0081c03240c0c0240440c1d6101c1c1805800c600081003109400c0424855062980c00c0115086204540290900030b084495a006680183c46a5003283c110b01ca400d110030500025441180e00541d031192108da081d000802c0050704090084180d5070522a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 541163444 1250 541162194 541162229
    0x63c0109050f01081e0a02310509060315101a0a05120a23010e011e03120e091303201b0a0f080604021306050102030d230f04030801 58
    0x100c2c0035480c02e5814007864009581e50b114600e1201078010380e07001008240c0000c2c1809510100768014040581030344c0401180c1c004e441801c00d2000c80107040c007140074075042400300310302d00d0140d03109036008201906441d5421148243c1036802a030442e000c4000442c01c400a10844030866800100d007041681c840303152402e0400040c02c1400307400d18604207400260006105000c1c2600400400c10070a8040c400306402000c0040d1059070034011540e110980c08000900300c0702540042922800071000c5a07101411500c074101c0d0b82401110003814001c094a103040d10b0380f92050070b20b03c6440701c880015070103006894000c141682800d07880300302110140c82c1101c58038000c603d8151282440c1021a104400724021514104a0350b208406c00700041c24001007801021540500c210310132030b640413242803005038000840e4014060350780140c0c07007885400e80d84c0040da4400368844100c22003241c04400403a0214018034070454560041c41005400d0008054000043e41d0240000320404800d404 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 541164694 1250 541163444 541163449
    0x1050f03060a021305151210050f011101092a150504051002070504021b0610031122051e0f092d0706020a1707020105090108063c010905 60
    0x107001a080d01001640010301c81d4414086220240003880003500640c1860500344031203195400c058031100c2c9850440e000100c501100c1c042003010b6a9004007886c5c0c42d4207003d0011500d950099110403155940c450200010034011b0158507000109009107014030f040c0d0b08814062f904980c0e100628202258001d070a8081c0c00c1015602925401c1d03c0c00000500c105104030f1511402c0e43c025604584005071220140d40c3c40c8558004074610b4004440c400e8850b110152914411880b02a20803000e9403241505480c100000340443c60f1012800c014000a000b240e0003281c03c1562203200e14800010039000c40c416000d42c0990010800c84800d80900d40304d4119500d40c12074a000308510035031255040500c0a001d28100340100c1914100c0b0348071034861030069683d241241040c0d030320007043d850b8a13501284480072214081d506035a4141003690b003c0040d155200b010b030002e50300c4940d04040c045581c00b0f0f242d111907409942c0e114000c4c0000303040d1040c0c11014107072820300d0401c114040140100d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 541165944 1250 541164694 541164703
    0x4080f1c17090a060f0b0a0609080312070207030c060507110117010603021b071706101401051c0f0b041a06070f080909070801030c0b09030c01120612080c0601050f03 73
    0x1c640c001000c10040d81c40c07440c0745040403c00800200500d24049160301030381c0e495808803030b4a000035202c03040301c0c6031a20000e4071104510710440a141d4410800100c40c4220819920b80010083c01200d46d525200d41d20440550310a4025000260300850840d0610580d5081c880600c1800c0c2807080419541046510805405002d0001856000a2501e11070502c0082054520a66605484420b0749410664021558541025001d803044201040d9030440d00d1412404551070940201d0000e00f00a00555898010102e0b12106054840c60460001424001c16030b8402d10f0400008001d90305c034040204641d6961b50000219000802c980320301e4076490112612540c2010044003061383d43e1529800601c1200c1c04141c1140e446800d10041d103810440883c140c130300c207440184015455200d20003250046840c1b00c4d0b8150300803070b21409554004d495004100070b10700400f203901503c0d03854828041000c100111000c000001c1c43c0100f00906002c00d50150008454040c084c00b01c2d800080c2e030b40e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 541167194 1250 541165944 541165967
    0x60b0c210a020a02010819060b03060a0503030a0c06050603120406030b0307060905030d03050c09030102071a0a0b0913020102070b041415070807021219120e01020c06161704080f1c 79
    0x60002403c007054401c2446d642c0c407c825003500c04180800c0341c9450540c05c0703603002550464000d0fa0000000b1601c1d25021050710211762042e500c0015074040c03074a511018040241180d501400b462003081841480c03200100041c04c040e032030104400b44400c040c03500d4004075500070303c03c002c1100c40520a65802182c803540a00d0326140100d03142d1100300380106940b158641c1c40381e15610000300307442000b03449107001c1c008255400c1e1008a030b80d43c1402072025601c1d648a02917001084800040e0013004070b52030440c1c49030042c07045034002521043d6201507503000c0d800c4600c2281c12102007400782c0c5014440540e0f2120003100c8181040e00f00e03035894520b4003d854000f482048c0d00e41d0f0070185030b80c00f001840c03050407502d20f13040045400e90501c003005c0e5408000309400900400c13003030062540002001140402c000d800b541c03501448441d81c0000c4154008121450038544108500f9014102d029002624030b0340c01030050695581011071801032095000d80c2d201180c41c0c40030400f02d4000180141 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 541168444 1250 541167194 541167197
    0xc0f080405100c02010b0a06080105090c04080d080a0207020405090c0a0602030705030a0f02030708040e0f06040212150402040527011d0a02070f0818041d1b0103060b0c210a020a0201 80
    0xd810fa40004240e0142400c95425600400250307400180075602c403d103141221002c1d542c83c0020749810714421a503108a00401c40507070702501103540310520482c4034070b42c80402d4000041c00d0826075400201504d82c2030b509040030f5400003030110f52900e007680d03001000b007829000440c0f60000d141c0d00c07140c40e401001211024000d540124201c10790090086403c071030b80c014502a625915115006503040c8103540c041d1105001d07200003001410140300300c0d41d100e0f0303103524001c00780e54420015049040280c0d20f071a8009400b4400002c46466000c3c3c0480c85810611000707003610803403513841060410592044100e0b9205d884150003049183c40c2d000c2d00031812420140e500c0c10107040444502181d10801000301c1c6000036041d8881c03000e0071151000b00c1c030481d014080204081d410a80404c05081000c041c0e0b0030640744070318207846002059a18000605010805a5544071341b0b0f50240c12501254200750882c004c404040d808851854200e00c60145015003022034004c4000e50303c8000900090 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 541169694 1250 541168444 541168451
    0x30a020601140307180509070609141302130e06130605090c03100f062303060a090b031c0519080c0702060703030e0d050a080a0902062b020a030c0f08040510 69
    0x102c0c0d5442c10310848018080d0030000c61141c50200354424024881100c1c43d90301c5028540001c510b90f4824001c0c2411110305071081e03144410514204008502c0e4001d030171851603400c01a6440f0286c15981d407130000e0880a5242c0041d10303051081c40f9250821801d90705805184c4801480281c2e2020041900610400c0415407203641d03144580f01c4100660300402103242e01440002921680700969009a40081c0e81c80d10100030340400001d0b15000035240203500200c2e501c424409100d00794803281e8640c5000f0211241414000180d4200c140c0d0705d01b0030000a0000200c05201c11401e00301c040c06102c2900c0d040304136241550780c000c0b2600540d0700003442248001020418144aa08000b08081008040d10f50f0380140e0900a0880d520054020f008140750034001036171a0a50710802c0d1380380b80c001d0b000c645003a6203124120443d0215034446030822880704494842c03501240b01401003031006840c001510940600050080c140948078001000754071010400003500110711003090103244480413 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 541170944 1250 541169694 541169729
    0x606090f0920160807061a03340515120903070309090b01050d050f0901110c0a081b03160b06091b1312120305010e01030c0b180d050109020909030a020601 68
    0x408012611403c0504460000f081c41c8041c01070355888564140040112115440d5001080c10f0b140c60220f0a81e40c1160240042d119043d8100300500b0400e00010300e041d440e0544900000e5103440620018101c01140401c40004a295101140b0b80110b0319a00035810641c00303503002007610545010b240035103a1070f8840300c0e0795a4040c00c00d0340c03490300344144103004520b800001c40032400811250201ea41d801e00c107a004200803018100d85c1217120080141000c0d60041d103882d0714a0384402401c408140310400d400e85074650500240045805500c0d129603c4101814010384008014000034480d005480920112030711a49000c421614001002034691981e003c128a04603955808030110035400c0c8045010007180911411401c1c21035281002141d0300d4a07010803060710240002040d050b0245801e000c0c5103040c8010705162030a0300100110f0b03c01d042c02007503c00301c21020841e0fa5070345a80d43c110452820212443d40101000e0055080c400b120000960354101841200000314008001c0d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 541172194 1250 541170944 541170967
    0x30115183002030f0c04110702210f030c0604051e0c0d060e07030624060f050d0b10020a060e01050c09040b0d020303070c03030e0d0209040b190606090f0920 69
    0xc01e41e9081c1c0080c19a1003490a0394001034a48250401d010300c01c910300000c0300c55182d141015909a5a000f0740010300080c1140740170501840d804041055a11030840a0707008000100000c1600d0309901000e0b00d81c1d402c252030044d02c0c0c190001051600d0064090640043c0d240c00500100342803001c40b0714606181850420074010711008d0014015801503500110501a981e008030f4421001e590903a900c0c055488555841070100d4003600c00003501e90132210300b07031610940240c00f2070020b03800d000801c2156400000c4840200900820240c0c22080c0c0100034003510b0300c100d50802c1e5a801c000c1c0036619040c10f8411103407061800440c4a50f42d5051140d00c240c84001900704101d0707025049980e203040394100591084114481100050300c5c800707400c2d085041c2441100f1807154050b2440300b80f81c40790b03910307034201c107000414809450001c6240b40c03081c08000c2c06850010041c5840302c080c40c0d810444450b145100c0d0f070f04031149440c00d100b042c214941c1410703071b881c604000071010b01344c503440c40510f03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 541173444 1250 541172194 541172279
    0x7120b0115080a05100f080106061b03021e03090a320907030e010e03180a08070303020303040f29160e060a050c340602060601020d0807020705040203011518 69
    0x2151542c6c1d128160049280601513002c0760903666151241078030f5002107031441100b040706800040041c0c114940000e0034031460031800c840040040700790780c2006c80303030004106001c3e400d03800006102c001d00c0d01518160f41952848984c150003141c0042101c01d01c2e400b0030f041d804041d0001d0200b41d41c80541e44003118082d072200485401180c25a999241000f00c121110262441c0b01c1d840f0301841071000401c40c800152007412254140c010354150b43d00c603203071030a0005440344141c4100210380e0700c80c40c1176a01120450010084821100d60500f8620814604120220320650500048101c042c0b07180d960b55080d96407000b264a4140c0e80c0b80840026079007005503806024210740c42c0700d122503020303030b0110030b005c4201d0304480101000c1135503440c0c0c00c07a0b45900540f403072405600002800c02005214103183c561145003401102c40d1290b0321800b04040364002d07440084446103d10410200c41e81c000c00c02081110409104e08600781000904a400545695006512104001c80c02c4401046d1031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 541174694 1250 541173444 541173449
    0x7050c01050f0c060a09020a150c0b060a05120105042009190e0709020405010e09061f0302040b0c16081c03020d0b1215060625021207120b0115080a0510 67
    0x10a40d00c0b2170074134030f1410000c2d1075040e00c1240700c0e0a0480000c6089600c2d2340c0c800690400740c1d664554001800c0c1c50394400700381e0141c42503800c1103800c41c0108181d00c44144640d210318042000203820715190800040f007407407420392080440d590444941c0944d9804001b84d8103d0794220b452408400c682d641c0000a0408800f0040036001e0010000745000d515400390013152030a807a980ea0f000480b02c20440e4100046038256803003d9880e00c540a0320362030120300c542c010860300303006141940710781c0903e4454004580304401540003030f100d403610f540e074951010020f0900c90003c0828015881191881c0c44c40c102145040640c081000d022400441d0000c0e402d82c2d2001d400d01c00400c0440d82100c3e20764412000f0030980c3d02811020039a03506000c0c04031000020010407100031324550b0542c604040074080001e980c0841c075459000c504040034050310004040c0301d4014126004103280c09078003040141c0c4010030b02101c001d059034049030005c1d1317000d0b80002003442c00121940e030b4004145a050198 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 541175944 1250 541174694 541174717
    0x120c07030c0e0f0703060501050313020a0302040612061112130302250303181a180913030813050604061e05090d0201060906050d020d0201121a040b0607050c01050f 72
    0x80000007003a0b04000d520a000d00c22010b05440a5500e013001502650180c1c8582c034000313030080001440c0c03070243d04801c1040c28402810044030681d00d800003000e54a15400540b003030800c5401e09420000b8038402e8200660074449941e0801c08424060403c001c07005240030342100006000008062085c40294901580500c10050708040081005a5542c07280411808030341c001400912a003c0350310a0400c940d4140164605004082d5402480e60800c88003502c40c160200750342000c43d46d421b0a000d10906d00c0060250030500c880c1270040c1200409000f40000c0540c020080c40400d5020411a038060703048440842ca92000444c50046900306100e1071610514200900c001c00d10049066503058159034000d0124546516084040f11028401c0941c08003100009500500f80015040341250050400c1e01d116403800ca485400e440c0344424003000840700201c4980070345040c2c880d00c8030700362054031107504081b61a031300c0c1950f80f480032310068188907010680c000f04000000c222070104409 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 541177194 1250 541175944 541175963
    0x60b03030c250608040507032d0609111504032d060c0806010e031c030603080d06181404030806030102190924050301060f0c1709041a03120c0703 64
    0x105100040b003200440405990a202c0140040c1461040312418026a0440082d1010a20750303551801c035146600c0c0fa50307007010003040c52000e501010880080c0c21602800c0c02280d014140d19012a1902c21507940343c1c40b41c4c200b954280710310000401074030f09036a48801c10709010120781c0306e05000c0c448101070380d00106241400c10010842d0507040086c600c40b103501e44a03a0b54941c0c1c0015620f0300c441155003509580090031280c0002c0418660003415040d60800145054a984515405070312090040040c16101c0804000c4846c2e80d415041051820a40c04c009081800d501202062000340002d420085490041400b9960a5041711201203804001c0445030f03642000242115003203110b411f0114551450101082d201c80f103060b0780000d03190761030501c2c503828601d055a00704480c1c40b00c1000c10200d003803040e001400b0038500c3c110a04a14070396588a064107010842a201340f100300100d059030b505094805a2070020307451100c080c0011040c1d4a44044809591034142d8550025052101 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 541178444 1250 541177194 541177213
    0x5090703020d060e0c09010c21020a03320a0e06031003020103110a080f070e090f0f0a0908040b070201051c0516080601080c1605160602070504060b07060b03030c 71
    0x1015402030024142c1c980e4188603c9aa0310190600128200c5044105035010480c69426610820002c4c0c81c8a21441010034099030859503907000d96071100c3c03480d0160303120b00e00090034550000b029203d50201d280c54040284c0c5298003400a0690302030801170154400715241884602400343c041d102c0c000506519100d20301a640e000107041c2c180320a80c046498280344c0394034250040115525298240c03110a0a0344a08144400e1440300820510030462900b0100110f60358043d80d16000f480840d214900c141810880b031039243c00d0183c07124184500e081c12803400660201d007030720f08a8a0b00307103590740c640c0410300042c1e030705204000207200200550007201d01d0f081955448075010744030500c0c0d0a1540380c10741c002550320400c15505075001c51820000910b55420a40041c58039200d1000d004d06c01e082c055503264500004602c080448100b0400d040c0f00050341040000c0041000b10303000d0041a2a0000c034040900c02d00388058401500c52200207040d0b101007044525440460084408005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 541179694 1250 541178444 541178447
    0x1061209080d05101d010b030103021012020304200f0a0905072001020301062309041112040b04030e0307060503220c0f06090e24010905151209011407030c09050907 72
    0x38000d00980c030b240c0c03612017680c1440d803485101090584545c080801d186908617020403090703a44010108040281d260b20011680c40c0c0303070025500582c821800e01980006007075065107011400281c59004842c0c21641801344e0ba58000c1001c202d80100400080d01d0f11001c0c821508001c840c00000d03071400100041e01c942e03046c1503000314101da00568404043c000511440140300d0420a9a100318410a000f618206c3c070f0607620552014850009a034640000420040702e020800c071429a501c5c4603400030007043c5500030200d410902000c502034486d6500340709001e0220f010240840e4119080c02060b1180d503800c0000342400950000304030201c5650721100171412042a015a400145010360b00050740110300d130700180202c6030812020b400c1008000800743c810341c0802c1007810420040000a62030325201c40c901003041801c04e0311030303507a404401040c1d01644080c10407030300c81e07250401d079041c003545c00861150412101e00d40840c0c0305914030011503103101c1c0d94012950080011f0140302d04107 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 541180944 1250 541179694 541179721
    0xf07030c1a03060a06080a02090d0503090306010e0c04090504050c0916030b0103110d0b0a0e0a0b031e0705121501090603120e06090103020f0c0303010905190501061209080d05 77
    0x5039044407000020a16030044615140019907a050f000910fa00083c07140034092180603901c410384e9800141012060000582c0d6101c2e0104180d1721504006200115407d00303201040c05040c040b282001e00f82800c484410075841366100392507070241d84101050400406002c0311640e40c0c0020080e80583c100504240c400080004c04400801d1504040001d1540203004d91312440f1a5445858244a85120040081d062210400d80e03c00d0b0403034004245244400315607070061406144c002a08082e0b00203042c81d10b0b100c2c44000304950b150040401da111000034002c0b081d50b4040d43c0c4041c0c4c0c1c4992101103490800740c03150710f03c405aa80030010841e1a0107902c520300700ca00540102b4407007c240e4600f901c0041c0d501c4003160300103008020010f07195019030001c0c28400440b0312458a0900108101410364100f0b030002c001c026142d906110280020701d03000322058000003000c2005501d4031001a04044880b08100c2005864192035400e0120210a9400c0c041300190140305514022314000d805 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 541182194 1250 541180944 541180949
    0x90e07080f06040b0412050d0e010605100503010302060405040c110105011413021201061d03061e1612050c0702270c090a0b090301061e150e0f01110f07030c 69
    0x1034428607884103290803001541a02642d00103c0380d1441d51903a845440a50103403152103000d015040010b500c1a43c10381c414000d418152100008055080c0300070403051810a10303085040080500051000d03a80741d50403a07003150012a0300180d4409681c20665190008081c0d50000d54a0b09000048910100020501d8080c0440d0b0007030058148001c070380c1c00c03800b400e41745d40550010034005000c401d01070b201108076014400b445001d0b0252050000b4036240f01100c581000c000441c0c203410500c0201c60f0305540250290750094188014400c00030708c21002c140706002c1803500d5a0215030100340040407240140d8024140c8041c1150f1aa285600340718050541801c510074030740065428401c00080d12010b51004055081c860302d055491819a00304582803076042d580d4501c0060034642444207500c8946402c03803900143c138030349008030746125070f00072610041c0f1901010400e10f07503481c04081d4400c03000c24244a084001c5c0e000b451403801d0414a1588401e202d16417000c0180324070b25844008 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 541183444 1250 541182194 541182209
    0xe12011103010f0f090c0206060409020a2610020403020306151804200316030813080f0d020d05130e15030111071103070605030720060a0603060e07051e0a090e07 71
    0x310b90710b041d104101d9081e1b03900c000058014101003a000e1500750083d07143d030b5000600c502e00c001e89811500c10b81060010f0500681380b06541e06810300310003030000081840c0141d004600741842e40d000300c3d88540c001001003045020b81ca24046250355884041d00d2030303149101019545103081d140405102c0141c880900607911b014099110700e18002070a0030305403000031000c2d912a481d40d900c10025030400004401207181802010807455002c2252035083b26558004280310403040070060709080d4103a0301c15080190401101840400e00d040140171201305903580c0055580d040800041031400c0d01c0c103281d0650920b100180c403004501d015028290050f4001c115412a00e001c06550b204a4814100800c4d424000696094014628024135015a00da6404080b407852290b41c00c011084880e442c90a5035044140f052042611640410350829002001d11070b082500055400100f001c1c0000311444418141446441d852074210040140303c0d0300780040e540c114152a01c0d4180341c007030f085 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 541184694 1250 541183444 541183469
    0x30708040303171510031e09020901150f080c13061d030105010e130510090b0f09030c0a1b260f07061e0915030c09150e12011103010f 59
    0x250071030030040071503006a1003525a1041d01c01c81600740900000c045c490b150a2554440c50241601d5070900080210591118001355804c403038810054001410307040250440411110006225000070b80035980031071500703213030500d5501d103a01c0d03c84912881c00300d18100070900d50f0000e1400e0b0411402060b0b605881c015a2000000505042c2254424804c0d0798407603802c0004904806801c0c1104034580b8020b0003030720449910840d5200a590358100300b01c0e1400f19640402050700101041280c00c0303118100510300c0c08245d00340380d554400072620050249820040700826104481c0c8445000344003810b00304a00e4034032090b198011000d48000410540180210b02030302c40000f241030030944a203619440c0840040b00c02101c411814801c0901c1401203500c0c010440c00006542c11500304003030b50307000c01c1c8803001c6200201f80700c8455002003015044c0300d0100e034026401ca0758050403420240d648206082520192a0140c00d2026410510501c004004100d00308140e0040c4150b45800360100c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 541185944 1250 541184694 541184717
    0x606013f0c0c050703020402070201030e06101401050a0f120e01110309010b030102040510030f11032d07020d030e01110a1205130209040212211b12040e0c0c030708040303 75
    0x5860101404900070f0080d04021814001850954050f01d48140185000078410031899403403480c00406403403100e49441c1a40081043c0035548c0384d4407103a5032080c44c00d60b04100031008060403c0c81410401004d11010001415248079154440201c00c480f800007401010421000520540c0c0243c1d40742001d035007004503600d0f00d82814001c9404442c00513100d1030043d00c000074120020406d162400540d2600d030118400344d8203d0401540c0180c00801015a00f8250380303641047d101e4042c00e00c00100a9034000300319001e41c012402200d011110f080105062901400c000e00510323200702c03500300c14003010819400c995849003001c5401445600100010b849160940055441c100c40c0250300194141c0060014100340480149070b07040c502c00c545410420320718440c1415902c60038a0a0541e001ca07601d0903886410b00d908040424100140541d07103182d80740c10b503081c07050f40914146c44a070803010800201140089841600c20724080e80c1e201c10702d51802c0c03600c80d40544010b0340041d80101c83c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 541187050 1106 541185944 541185947
    0x10509092e050a0b011e0207030c0b0a0207080c0d030e0d0506010b0306210a0803180303070201200a2c06040b03040605010e090606013f0c 61
    0xa0781e981507036000c03200c100d03000100620011802c245101c03034580d801c0280b40745000c0c0c40726102030b0001103040003a0720300207065100030000b606a400c00248030441601070b2000581a034241c41e42d05907a484210380c0c801d250200c5a521040e051241d10003e8000c0c2e28152201401821040110359540c0310306040900c00d07481a00300c2e4a0001c100300c098030300b003403021030481403070000b6940703250802c006140c1c0c0b4440300c0c10040c410b560000c0440c0507002410651034091032081e04480c0c3ea803a1690000b8003801e1700030030348405200a820054001c3c4240780030703104510015620300c50302e02c180c00a22010b00a113a075000d4290f400180554800b901c908000340080d048100ba9a5524107142c64801d0441d00140c0c0890600944103050001d07c0c05c0c04180e6035041402481c00041042e901e21580b40742705080c941021018889900301001c42c0899000c5011840c4900c200300b06080c030a020 = true := by decide +kernel

theorem cover : BRFrame.Cov 541007194 541187050 := by
  have h0 := BRFrame.cov_init 541007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 541007194 ≤ n) (h2 : n < 541187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
