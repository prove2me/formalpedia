-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1063
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:04:40.285097+00:00
-- url     : https://prove2.me/submissions/8714f029-9bcb-4458-b8f6-40f6e1fd30ae

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 191007194 ≤ n < 191187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 191008444 1250 191007194 191007199
    0x210f050f0d0f0504030f06050c090a1211090112030c0c0801060602010218060405060415020304090203041109010506030606041a0c120706060603060b12041109130b060414010b0f04091406 82
    0x8215510742c0c046416100354400501810841240100042c1c3d50f5080039400400b004542030504a0500004080c040306510000700030308641d030745c3d9003000381007003840548203030448500031650b150244181a183d4074550050400c41d07a081c40004000c407001c03d180203400108000c00a9944404c8064001c6d8800524aa0601072141504685242140440d0103844000e013065082514285802c03d09125080043c41980400e02000ca0003424900c069031003a40a040541034240001c0305005e5011010b03002940120030800802200740c0720241220202e4201480c0403d06e4900c0c4454018503000d8107600951030b005410303003d241d4009040c0039004c520b0190808101282e52800d040c0c003101c4562192203c003020500147c1c410001c1e1201403a8041d0203010300044030300000b400182c00d008129000085003c00700301040500500c42c20300c40c1e0002c0203540821004010703012100c00000148246118200000381103882e490392003040e2001444041000d0180c0440c2400400010340304407203850 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 191009694 1250 191008444 191008457
    0x4080106170a021207090f061404060302030d0e01030e0307030c050d080106021f0b09090d020d0e0d0b1e0408090f011d0913050609060105030d09210f050f0d 69
    0x28080c2000180401c1d0200e5440007000320303440903802c0c025034140e401c4046680c0d0191440c0000c0d05152805607008001e6007420000d40d807801d15404034034440e0403501c1c0601542c43c107502480180c03000500e0741801216400c0802805858078012030103444602e240003076901000c40d10004043d04010b184540da486442901c500c03031254041202c21b414240b00d40da0050f401035803030041c1400c1110191094442c4028042204c580c6a40410410744064130041030382d5116880c4448820384c180504d1100403100d24280e003410300883c0024030a01c8400c200a4101c40185d000329000c0741e80c00c0300c2080300c441407074038852180c98203050180f1f02e43c11074500c50307000340d440c2c500c030340030701c4d0b01c54950300c4800c20300001304443d0040c0341010302001041c001d10607007188145101c1940410401c000d13039807060b05080011705196040100345400c4c0351036000110207020a88005001c103480c0540000090b120202010012550f01e0820b40300d10340030301c600500740c0c0c020300112201641c0041105200310300182c9518 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 191010944 1250 191009694 191009699
    0x302030312060a0e100506070c05030d2c0d30080a0506010f08070305090f07030f1506050d0b070c0c0e06010f1103090d02191d0901050708070c0c030605010b04080106 73
    0x82100110444051741d1204d50700f4070034009440c0c1140501282406112518039054813900400c2c9019400d00c608808604d0340130002200075402103164507540c1c6c90035000c50281c4900340110307128500000d0001c01ca1151142147c80700300c0d001c0c1c0401280000740310300c14245a11040090034110003910002c04503801d090000702c030703540103c107400c008044940c6e9031900c5503500201203008000281480c5240e0045880b00c00c140c80b410800c880196000c2c032101238504400d442d01c040c00c4c051620007a0116070401c50100550b80c0e0301e02e11001c1080e046211040540c2e100c4d00c084450319061309004250710060071001c07401c5401000b20502c0341d1020f0b00c2e03480c888860000d040d600c00c03540e401c602240e94400c00a80c0028200010004082c61001d030406c0305003810410034151802c8150090521003600180019581e501c4541d0950402c030654000c00007420142001044804000c00c80014460b601001ea01001a0f04c40690000d58209000304100e5842d183c20443d5a44640710300c50070340d82480c102 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 191012194 1250 191010944 191010959
    0xb010f0504020a12021308030a0f0e0a0b16080909011512050c091c05030d0507080a020f0406031802040504051011040509070c0305041502010c1d0a0611070302030312060a 75
    0x3110606403c64403a42da62804c0c80105001030361040b01c000d0034800c40c1e106c0010b49680c007000036180020103511a94907841d4031701d100404055445121500c1229040d00c10400c0c0702c000011100d14070b84054502c82000e030641099800d9201356070400380c0050101000040070017102e510085401501da84071003040c4c0c24240f204090380c80c141c0b46105c1c0087d00b08100d42041c94031b040150880c0324590b000d0320f211030307041d141c0300d056810240c80c2051403501ca0003044100360380038540a0740900d03119411801c01c84012070300b043d40d01482c0110014542c0c1d0300c0a002010003000e040c800b40941c020410b001c03514140c6016521034032a03100c1522480e081000b018216619101610140c443c0a042c0191030760381c6001c00c460a400c0c8034803c2d814840d0800c00800c05582031500c50110000c150000720fa0003100d80c40042c1403024101c01c4030b00c0b4404011181e082070780c0d1440003030100c440c14a403d00241d8074015085003042c1041d4002036044c032001030039070044400c032000d00748240401c031200aa110703a117024 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 191013444 1250 191012194 191012197
    0x30c0e06070b0609060f06030408041a0705061b2809050f0f09220516050d1a040c080a0302060604110406021203040c09060b03060306070216090b1305040b010f050402 73
    0x8004010411800000f91141480f0402d20f500a0300100922005429000480c0440d07109403015100303e60001400e200c0b14203903e0303240465200150f4480e107840b0294849603210030f40917080f60000700d410101040f80c00564000d0b6207014903020700102100501d0703a05031041d0301840c12044003142a28000003003e107840c500c091081e044c00303404404184004401c00c03a205c0c100030840000e282e0001014041d0880071460000158400c1c0c00600061001c8108400106050340c03000740b203440c00550b984001004421050f8290a041280c1240d036111b91904a55005441d001030b0060b21820740401d09040c1c0c0000e01c02d01844d000e4404102c100400e141410540c4239034010000960301580000b13191501010003503501500800750000b45030344074a10042601d945900210301c0403808028402c00345001d00c038840c1c00120a00091200c905c480c21091203a040310b22030000307a2550741c0ba810310725071140d42d0803140c001e000110821041ca0189011600c401081c0108a0310000589010031681484d10 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 191014694 1250 191013444 191013457
    0x105010203070b062b1716140a020310022208030906180402040e040506250c050109120908070801050f011a090d0302030c191101050a050c060106030c0e06 68
    0xd0246107004016100e02001c080c0113000c0e00d400c00c0c010ba900c08042403010b1408500c0c140c0314041c141078040035081c04100e05051220000100c07004100d418183c0751a0102141c1a945c8400d004100b03080b0300400304d0070400704020281d0940680d0890241000c0e10354001d125080c10f9040d10114010b80d003803411514030b4076020b1050030768402c102ca0700c403514100c4003504280c002520b09114000c01400414240d070010380c40301940d8052070003400100503040c000c00364044c900c20340c403001d081707034404402e0403042d8008403480a000401d0105401e201c5c0039041111100d401401d8170000e082500c02c0107004040d10b00c0750340c06c40d00620740b020805550601540b070240010360b2800e000399003407007405915011004050040e509042084038255180c1410fa00112030003500036580f50214031000300e0410480c044813612070001d050018000903c02d058896040e10217103041610384202e900c0650b054807903030088010a00c200400046d0341617240c0c01002d00c6207210360b1010040b040860900c009401b590 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 191015944 1250 191014694 191014697
    0x2120f061e101a0f0c07090612020a06030c031104080a0b01080d02031801120f09020a1502030301090f090c1205121c2a03050f090f0303040311120c01090b090303010501 74
    0x4400401c61600c3c14400320490040322504140381200c1805580895030055031010b0468020010421400c28240f05240c010002e402d40b4080f20030343c13940083d000700080d014038024982e50745802401c41d40309038480082c3d003004501d020798441e15007010507580c6458030000c95100b51088000b19a0180104110b8040401ea4004500701b1404807010b03000c01903415281410007170401c411035280001e902aa80400401e12000568801d590040c01042d6500390040004510203901d0b0000d01c43d03002003100d04444041c000040e1985034014410050038460380c0c00303090305c140e01a01090700c074481c115030010140b103041110b844548240b0000c1c000e0150ba070003141c9151950708001030003040d07600000103a40c0d568070012480e00944d00703280e40789144481c030500044c0d0f0300d6040181505a1070b4000340c0202c0041c0c0100650099030756803694a1000500c01420400400d1302e00e0901c020802c02d280385200d801030f800c0c0d140c880c03070740109000f41003081381600d083c128000442c078003c00220449040c4c078410f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 191017194 1250 191015944 191015971
    0x9040c051c06170f03191701030303020c0c060a020705040203040f0b04030906020115060905060a0c05030f0a09080705030703080c010f06061706010c050d14090a0f0e0f010605031302120f061e 84
    0x40c0c2110340c000903446d07142c01d41402405002c8121115001d8507060203984681c40050701c402c3c058090a01d84000c0044440c0280d80801a00030a1500084e4031030487d181220003590b26911072030b14400e04500300a00030405032100e170501080640004248064884a07802000180404107900692409602c01d40c0080340700800d003400b040c182080102446030b41d0b0f080299050340e80faa04c0d01c0c07440e80880e10b03950b001100410720541c00c90340408180c005082260040c4807403800c10b80040e84905035448000c10060b00020b080201f16401c0d000182c03155015881009050303620400500050000ea0024500d20944800140c1030360090b54402c41c41e0f5040340c02060070700d8401070b040d909070880d10145181c600042c8160b8401d5910341912402400103c0d10030034405140c00c60110b1745080c0a00415020a0000e005000c120352020641ea40020000e400509500150022a00143e000c07840800107000301041000b10580011f4034500946102624440410340100e0b0081e444d0002c2c0e9612114028 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 191018444 1250 191017194 191017207
    0x150b0d020603130f03020f0c04050c0a050901020f030408060708180d03020c0109020405010f03020a150509010c020a05060a09030b010f0501211104090504150504030509040c051c06170f03 82
    0x1400006507034010364420003c1005038041d00c130800d540d070400c9411401640400f81c80140204207104015040300250303001d00c218103001302154030354080ca600c10002c00c10049500c1c0340c0d81c1e10030850811410300d0b560940769129181d22166484100c00c546080c082040d01d0f0100e20401c0c80c1c154401008800080501104880704804a010b5807111000301a40d6407903507503900c09170380c1c0c91240a0081c01c2222040140c2c0d85584140421100e080e4003900701d598007200080046034004045407250f03502464010150a010303c0018000e01880d0480d17600220045801041142c001500380f055038000e00d80311145a80e5040144843c40440c00303214000b62188040c1c1d5035861003055451801e9100390700100340c80820075050680c941060b40b0840001d9128002c0c03006206107140342e034030101c020300d409000350724290718007605511919004a004c2d540d0740503c0125603101d2419242141d0764484c4c402200010b80c42d213032000d020380b4001d09032038102503030859138400c0d8002032004041c1e620308042e508040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 191019694 1250 191018444 191018449
    0x2042306180f1e090c09031b010504090f0207170f0d0905030c0a1b0602070b120411040f140a18140709020318150103031d060c10020304150b0d02 64
    0x2006600c0307500b00034480d1075250180e4a0200501c280360082200e0b080f040303081c0c000c210035418054460601c0503c100007075081a1408196208071400b4a007040f026001c20600480d818896903203c456543e181c182c4c2c51944481c03030380062101c2405001031020740807032102c4d480e4445c820110102c0400000f040340881c8400541c0040c08594016411303203080c000c0151500b814020343e071030100c0350349452403000348031074018100217005091b1078401441514204402e4666a100f490055103014801400160400000225140700c1b410094070500080415021144c0902101190300800c82079010018003d064184106103070100c103440c510782c00c80b0050300e40301030a2150501c3c2085501401d400070900100030700065000c3c008090303d40000c2800c0e1003555040144100c10310700c80b0b403040c1004001080d0300943c00d6860303500b00130901042c800d6071800508644074008041c034090243d80048500801c05030b00cd14803850245400008400d00b1108034011a0101c00b1b18950002c8d40155110160 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 191020944 1250 191019694 191019727
    0xd0902030703020301020c010c140403050606060c03160c0603110f0d020903160b03010e160206070e190306020304030813050d050f0720040f0c1e1403070302042306 72
    0x1800035055a03289500d07900801d007aa40700c1c895502443c2e44441480780d50030352080f440c40b821201c04000710300740b5041da51030544600001e411180b0a1401254510720388106004884035105800360280000c0c40d03d02e00140c0688841c4640300201b0316000b00c14410f904084200c2d81c00d14116080700c1d140c092a0308500c0b00039003000c0303d0590940b2030408110350380c1c2c29200d140c00c003600a044a441d2030b0762502404003040040140001d01c1d400e070704501440c0c0c2a8000507002d40042046c204403000d56141c00205008595001c0c0c40b10080668050000a1140c144d00450046001e81c0c3d5034400c1d5500c5250302034100c4414a401001540440ea01d0403005215201030301480c86011129498198141ca513000d8101107281c2c1341c030044151040ca15100c0ca8507200f00b8004820318141403103654522075014008482221704840112804240070090300d21494440e401003440080b100d0f00d80c100300303e00400075001400345005407961440340d038401c000c2c01c03c001400100d006000303074945140100900040c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 191022194 1250 191020944 191020961
    0x19050a0f061d0708211803190f0212070605030708070504050915090106020c0105090405060a09090f03030e0a0807080c1c020a0318051f0203070c170c04050c0d 70
    0x495622104250342d40d003400c802c44401e0400c0002019654240092a41000c05050202e440d050b142410892090f101c441070f14070049000412424401e20480403908201e03450442d485e8a4448002410805c40381c11002c007002c3c0e00030765021040001d22800e895a0740210300901010036030a1001842c2c0c6441803002c158000344624016085c195a040805c803207040a640742910100c00701c1c483d52540c1044880d45006107a90300c02001e04400705400a807540c4140b0a1082c02070740c859000a1503a04e400340e41e42c004085d03030038041140002c50705144014502c03041040300000e0030000340e0141103800060480026801c500341078540300c010740d690001c0b54041007081c4194002c1c4d030080c10b103083d0000742c0c101c0050807903006007012100728a0300400c030801007043d80600d6185002d081c0010b0322600e41c013601c0e903000f45018511034900074406a244dc001c1c40002080c0c40030020000c0781c00340041c22a01400b43c05041104c14a100c000d0400050395000c0720303000a00d6005201e00100710a998000424 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 191023444 1250 191022194 191022203
    0x14030903090a03210f1e03061a0304020a091a060702010c0c03120e060f0f031003060e21030f07080c0d020d050105091003030203030601030c030204080303090a030219050a0f 76
    0x10308030141c00824a03a142e01e52058070f81a03000302d600c00001590b9030700088495903620b8101d0170b0600c1740c80e01800e07500a03030300b085405c600502d40205005000340d11080140c0810710700c0382561b1080707030501c0c0003030380c4115400c0f03028200582c0006820300c190b000785103282c80382403035008000c2003810a100300c54112610071303810007a030b905680000c1600b0131224000366016070760166450544501c0948400105d01a0a0044608000c029100c85004050f50401c6d080111071654a4440d550100c0c04030b0001e03000507068520704020301240c0c5500140c0c1040c40300c504020352442d400700e01c4503c0d4603404111a40d401c034028100004030128411448944c0c022940309171079041c240320311148070403600f00038a100507441d542e0740184600e00d010100d855010041c4401640c089080d40e600945902000e0b100c1414941c4175401000c0040c000c0d01500c0c06004004112520b901d060310009987c4d801e980300c1507025001d07480c00f400e0b0320800c01401040040d0801c004180c1c140c81580d031581d5100c0345460544 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 191024694 1250 191023444 191023447
    0xb0a0203040f1a091c090302040c110304091a041406040b0105190e0f03060105031b0312070605040209011a2a06090a03082d0a0f0608010f060b04030314030903 70
    0x8001103918001000640d20400b0014161502e020580d141010101781d000c48010031902c581002c40d0701000e080140ca90681e404581c2c0a0400b00558180301c88003041c004d240400f00d0040f40c0c0d941141e02c00d41d4045881005074450140074070a0104503414544035216550680e030009109007055040303a00024810314041e03241c45921502ea81490000300e42140000740d000c801c4c12680c1c54031401140d00c14904401814095241c030340000d0361400440c0c010b401c082518079422400b0740e030900c401c40b440d0036900d5410755101000d00d0104d00416084404030300c602d011038000300350321011100400c1e03803d410a0a003803914603d41207102d6038040340b01c000050440c82e14180d03d90402d0500c0107e0050b8040310007031050b0101860046e00141005010601080e0303000c050103039001d5130041407d215240b0050725105500d81815900140003240c401824081c01e203d000102c2c40c405510508002075440c508001d00c0344c94134500e45a034811440060005540b102036204040d8a030002543c003c41c82c142100d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 191025944 1250 191024694 191024723
    0xd05070519090605100f080a0b130e16050303090609060702041a011101021204030309030c0516090e1501061808070303031a040c0f080601030608060f04030207060c0b0a020304 77
    0x403290104010107521141007080308010051050043c24090a13040300e0744514940d402e5070080046071291a11000c03c00118041a51a442d941c03041054a0015114884001c8043c01d14005426001c8035944148101244061400c28000344082034510040141d4980080350301001910303007025043e81d80c070060030880b00340142c7d00d074841c038603004958007105500c03040d00d40c2c00034010440911340322180d64010003000102440320b841c1d56034403581c035060000300b5440c139050842c2c0070010994020038912036007403031084840020300183d04540c121b890910070082d04003005522148400d94251500d852a001400114010250340c081d41070391031400c6000b80d50b180789103440e043c440c4e031043c0e0101e036841c0600507507910309c12520f012080c010343c2c2c2800440d1407060300603c005480000c0d8010888203802140700e6a201c3c1c0c01000042c25500216040750034100c42011030507006680440141c0f261010000781140981c010403003581c5c100c0294403083c0d42d0106460040d500050040f54002d01d5540304 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 191027194 1250 191025944 191025949
    0x15080109020a050d0f0e160e01030f06092009090a03082a0a0e0301050604090b04020f12010c020c0a050123070606031a0f01050603130303020711090c03240607020d050705 75
    0xb040c0c601700c459035000c2104112240e0307003810075407203040c3da940300c5003030040900c61000020502411a44e002403000401c3c2481d05181e4002e01d40c03414000c1128044136500b1880015408000440c004215048001c90700c0c3d1504481c0d545090020040c08240300d82c0c005610503409102180d99541a00745c11002d0500c048003030112a80805070700c1c0c01180404010729000d06092050503405501900e0402c56580d2580310017004400090000784103092560452100782c4a0020011011060000900c1140a82180a5222044c2d5200075010302c20f9450001525072007400410020340101c10400c80c1200485540c49041d4440c40c0103039002910f84100000050044040301c000345112115814103040c00a0303410746800d41039006621444040c018000d0f1400a07403054810580e042c20010f95803040d9140044402c031001489030344c4a10100204a01c01003100c1c002c5102c0d48583c0c610340e101711081c0b0143e81500550741c46464000c00103000c1d000041c180000d81e04202800b540459800b56540d000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 191028444 1250 191027194 191027201
    0xd020f1207060215060d03120507021609090201080a0b090f090c1806040f1413031e08162303190c090810020702060307200601030501020a0915080109020a050d 70
    0x2103005910440900c6079103041305040a4200500700c41c03070000303103901d84c80c014998100200300c0300901e9550700200795003500811103c0c41100a2200c43c403000e5a490103144010403042e101030340031509200001d40b0207141c0f4840d40b128484000c201c0e80c80c030307100c5c010390f0f0742d1414000300b94600600c110b4468a02a81d1100b2f04400410640c040c40c0b812441e1801c14001a114a800c2d900b20071418412610011201b015003680c0c4005c0c1c10102402044441c14111080710a481c0c04400d002c01c0e40c2101e8401030307070041c0f01d540b1940402149000c82c40032a0800c079080b4480b2800c118009035521501c00c0c000008074021a008440d05007a18103032100030351030000b118804500280440c4030030401b000018020b20424200c110090801c505184041e0081007042c40300078141c00400800f0202d018150301460340501c034034844035080320283e40c0c603480d001e8000c0d8021400c400104150740c400007001c00c0c070b1550001400c4090f5895585070703440d10703890b00040e400800e82c2c030041c00b90138002114101c50500c03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 191029694 1250 191028444 191028449
    0xb0a0308180d0f230604061a06030912160c1508070507080d09080705100e0c0105070c090509030c030304051617030d09030e030a05151503030301061103070606030b04060c02010501050d020f1207 85
    0x2040040c101d062000c1069255041e00c8022780110003c1c020403031f10000118034080300100d92030343c140d0f8030000f0503c1130301490ba101c0c100400e003401040005c20403109101c01d01c1e848040302d03124220f898980f000d060310306000380c520090022100f0402c0580c0d12a081e00070140007480b807105030341401d6241e51402e06003072960b1000b288040c0d640c1c09281c00380a04201058800d842801d11900d000c1440c1c0700c41000202034050034294a89410105107610b404000b00d610404d0240162034403414645082c0d80c45120044500bd01c420806d50049013140400302c00001d007000c200000c62500407004000e02c09050081d40c150241f28010110313240613102400007804a44c404d5000d0302902c075800381d02040029014003030108a49400fa46000261400400c590550f14075061a010204002ca000740c038611030365600400c89401c01c7c0b400400c21505040550042d84500c4060005911608040342200d00c00d04c02c25a006c1d40d490380c1100582400b884109003104081d11003c292195004400d00d0054941d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 191030944 1250 191029694 191029703
    0x50d020c0604020a300c030f03050c0c01050405010804110103090b0a2306010c080c0f1207062d0f0204080d050910080103030f11010b0a0308180d0f230604 68
    0xd01c1004210324005403154040d11542d00982401480d940c14009444115104009412050403284050054010702c80008542c81441d00380210114a00108540c2000031440380034032070712542c8800c44d800b907400d94094500681d6402035a981d5070301c400c80444040103811341419603d0f0408000300340301e104040d204a0361220b01003402490701c0f810f200b40c4a107244034245d50140f0708041c07001c0e680c2e04c40300e8110340341c0c1c204080325190b0034694221800c1802c5d1541c01001441544015424000c207403000d4001c00340900002c204000418445240100c503490840d6103100810941c40c0d400070b195481903081d50700300d1900500f01074542c070106240511441c22100403a50114680c001c0f4074080340004003265540c98000c1c080e514564010300100c60580c0c41030140074000e0910100d0880035445400095802031a400d511940d904003810560300403000e1a00b45c2c0c072285000061030500040c060030090b840f0340d00c000d031142c090711001d21000545804007120044030100154808080081c5401203014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 191032194 1250 191030944 191030953
    0x40903050903070e010b04140112020a0807110d080a020c0f0a0f11030a0309050904020609210609011820090406020306100311310620120703030c050d020c 68
    0x3034200340c0703800181e44c00f11882242490060080c9031010080e00d0407506103020207541501c0039801a240c200f1054140700c0c4040c80810302c40c1d00b141d03000030360900800f000d403261181d855034502400d44482007000d01e40007150708a00860140c510641c001c06003400000d0503285000589642141020b100520540f210f00c4160103000038802c1c4000911544c020407401411740c1c8043d80d0f40a04050303200c0c8189440344008500080554460908030b408003440248007041d1740910542804900a5501c5008090310450000558170841403242000d141c040030f00356142040c1c5551110000400d03002d640c60b030002d00c001c2c4080316407160118a4003c622401d03025899107000760034010b680d11808036079020941030907001803040c20120104c525000b00c805001c0007000910800750080403038041066100d2414410018045030702008008a00c151414210a00c001d841010343c2d4030007140d84980000e58082140800083c003c2c2e10600003000141860307400c18000d0b031460012a0061008650903801 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 191033444 1250 191032194 191032207
    0x708070f080105060f01021f09080d050406050c1314030304030501020c0a05010b010201060e15120d12050a090b16090e0408070203011b2a0f0c050915010807030c03020904090305 78
    0x742805101c0d480f101c10340c1c40d440e5001500340001e41d0313400035280070807002c4a403585050010b4540c0e0030041603075411007019a40d6940720290074000704001c0340c0c1924130b0303403a2502107000d200061049420f8440f01e0180c0c000700e46e00f0320401d00070703900b40c00503202e915200800001001650030f002030041046c0c0075010f400d007601503003070850950360f01803a01411a40b42801c184221500d0200c20781e0090f51414011170000d40c1900803482e000281e6000c0c2460b0700c1100401d4480a60001b203401c0e41d4880e1a0050065494400401041c0c9211a8008120209843c0001c0065088011a140c081080d14200e203d26075034003541c1ca06401e05440c251042d2400003900c50550900b4000c03c10800481c2600504540d103240c001002e4200340c20308414002001c40a0a40e0b522204811058090304009010881c200c00d14000422440301d1250038050911017000542c0e45149000c0840314100607103420039160b0322040110018800001014103050f070074000180141c507203114640301c440c400d807619665000d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 191034694 1250 191033444 191033459
    0xb060f03010f051e010603020a050d0c050c1b0f0a030b0f040c1226130504020901030f061706130305030c07020109180e060606040b090607062702041109010f08090708070f 75
    0x1813058000710705150041004414246e03003d000c8a940f0545c4103c001200514808122480c0c4614a01c1c60b074144100d00301a401c0403004020103032400070485d04402c03aa003024040c011000d51500c00a40441d943c00000740300010086030b200c0c1c1c040d02c0340019000c00e0f03840b80184074948410346c80a0b100480000c0d90440c0c0740b00d4507000c2c034409281c0b200c1e03413a0605d800d0140c030300f5a0310207500038180a641c020a60b12540d0f40070ba0804910720303107001c06c01d004454641c0d4001c00320259115030202d4a10402002c0f5802001c0082c0d104d8035560503507140c4c5d01d95176a80e085000b141d880010120304118180f000000c440c0204030a00c0000024840082554001c100c171091908001a22452240004220821a440454003260308520701600e066854500d03904025008183d50380000301605661a2040c070040010000c0c94140e9108841c1000051020488941c45005950784540440c910303200400d915409003480f80c0d8846c0d1404100c0c0c265603206c0c5800c6040c007003a90720071840c500b9518020b00180 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 191035944 1250 191034694 191034751
    0x7020106030312090209070c05101d01060501032310090f0203060909060601020a0201140903061003030306090204050906040b0406170f0c15041a0705010c0906080703090b060f03010f05 81
    0xc40043c00b09012140481c0c000400c02c250162001003802000551035041100a00202c0f0f41104e80345d0042050a002c0d00381c85040c400c0e031041c25811540390210200b002e41c024426005c0c140b1640030031201003000707900c00b030b10450000380038287c681c1014403000641522034050900d112426181c056101e0600c0300902c401c184024000400d01c0d0807071001c000e0280d81c0050310110742902442d10114202810130b90909030300c030705404160580a020104040c0c2c070700141f0810100c900c00d5a0421100d556084108201e0085005069104001c40c001c1201c518054003d0982030b11300801c0025800e6688003800c82c0c0c4143d2080181d03094024107482c40102c0c005110750600000c043d40c4680040c03000003030180710b512883c02070000c145c0807040240e501710041800d64102c9a40480208024140d400000e4203400340ba100e01800640310340e0000d20124440e006400300580c1c00540a00a612007008101c01005030f281e0098240d9a50b1008030010381047c0a0613000e01034180c0b403105110f00c0c02048a810 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 191037194 1250 191035944 191035967
    0xb0901060f2c01121401080703140c0f100e181f08060406020a020708060736170c0d1101080705070c030b04030903080a0f030515010c0807080c0303070201060303 71
    0x71126401000e0b008000e40c141110481d9a0910340b40300700741c0c1d0620010f00202a1030b541000c030480003900118246e1400a025000e42c1d0041b40e102c44415403000700c641c1c0e94000c00500d9500301d40c0340c0003500040d08000e60300703c501c90494200140d08202c0400071503010000c56000c00c80501c6910244110343c081c4014000141c054001031080c101c1c10704001580c2c2c0d4501410041c0440ea00044244003d0301c28031001026200c510306039003441c14006801480c00240d502e48817042c903102228203100603400764482890002501c0034012903441e081e040e25502d2903030008940113019240c9010029034584544c0343e00f076485018800600280500014031820009040c042800307410040303500442c882d00494030450b607110603005481da0f20361404a0f5106503d80c0024600c80c00480c0c05050150400340e5030980482545d401c0001e9998203030080c501190004407140032403c6c0d103261740d01103083c00303004008250048142900e05180400c900345160700c211a0700c13005035910b02003401010351240c401000c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 191038444 1250 191037194 191037227
    0x1050f0406060212030c070804080d0206010501030b0904060c2001091109010b1603020316030e030c101d0409020d0503030f01060806060a050a0c080c0c01140f0316030b0901060f 78
    0x8000d0600b14081d42d20114060a281c182801200242821034020121390b0602d500590702500d5035590b603002c81e0340d940001102000f50144900104640d480b82c4100304040c10018180340c21615942c03a00302c010700c601d4000102700112840a00307c540030120785505c02e194104000550018641030034210040307a400307903d101d1042d2200410602c00c043c401e031100441d100e10402d060190310328003680f540c451030f5594141890a40482d009040c2c0028441d00848415800d54141c4c50060b010400000008601500810310b0a410200d600035501c03d00b0140d800d026100095110752a000a100c450400d04211030350fa05c00000c104421004420450051141d400c1010850a1180c00540e0501600c0310420804c01c022030380710314092041c144107241c981c0114845a0381c001d894151030701c8048050711140466480640410038541070000c440207816a400c00504646a82000841203031348085604101505d170151003006565058040f4001c08040e03c2d4485018011800a02141e070b00348817120 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 191039694 1250 191038444 191038451
    0x2060c0c030f0a0c02030a0605010806091f0b030c0316080706020102070c0905060613090c02010c05030610111006060f0912030909050a06211a0103110f060c1501050f04 74
    0x5011010000c140d4070700d880020085500c4882004080f100c881c0c850601950611940b01d000050000c1ca80c012410380301722f030058603402d030f4480c4041c60780e0320107401081d603040c40c42c03046070020b0765000d0380301d03c034105d400806039100d254550380060726045402100d88640c41c004041006110020000c4030010b0807180002d608000035034550f420146d41910440305843e40b5000020051303074800040341c0d03c2100c5070111180310f907110031495000745115141180550700c0c0c9104080017070700410a483c81520300408924801100c054200c0d41181c0b8403403012214032600341c44600c20762040c000c00000d004a43e44070395050328010001005540c00383d0000040c20708110404000c60341c410b80c0901503801b10300001c131b002e441c1d50307000d00004c0c40154040c601280c61400042805079014103070608141c00b5100820380f02d4840100205510401c2c40001e1800b0022201c041e00b90038140941403030554020456130811900c2c0c0c10f61420300000641c800c6c000201c0100510862901c16003540324130707c083e87c040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 191040944 1250 191039694 191039707
    0x100501080903030f070e1905041109150a032315010804030815010207090204030503130603060f0312020309041416020d09330f0e09060a0b09011e020d02060c 69
    0x7241ca03440040d024082d0000641c0029114034000d15010301e075030402a0175070f40902d8096054100052060040621883c1001f00e602c030040c9204d000e407000101c000785440c160505240d42e010090b8040c841c118185601c8203640c0c1c11034080c40002c0b20f000c51400c2d01c401c98900d03207101d1452034070306110443c6040c058102c1c02d200c040707540724a0300d542c054070068508101501660040c0e2900266a001400c81c4c1d00004000c020044040090700b5010030790310725586000e4540c1010f1f400d854460080c03003840b289241003000412001e03e03e1503203900c900c1c01600e00e0000b210022400351200114140d0641aa941c184241070707510019660020001d840a40048800310030000c01840b2580302d1481900c801e035035a40c0100ca560f50f442000c285907281141200154190040e002e20000074040001c0b030070141403003105007418140b5134850b01c40182010505420304201e03401c19080200310701d04124958146c1d840c1940305c80c60b80710342d94006400800500c47c1c900d1700203142c120024220a05843e050046 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 191042194 1250 191040944 191040961
    0xb030106030f0624060314090a0203210708070b01031203110301060e0a0b0a0201060e070f020d03020a050702040c08010504110702030a120c0501020f031b03280605090a0510050108 79
    0x2852450f8421030218203100841c40c59401c03124200300400100001003c00620941c01d0351100303601d55464500311160350f49810340c880d1580e810352406034068010320410082e06081000481c0203807007802c801c0f400e1000d6611882c41e60740010700d0403100b092401c401803040c88402c103048803184005103418407011002c1d4841c00d62501043c03040006000c0c2040240321070f030b82c5082001d0b028040000400f0784405003900700a010300441d11600c0c203a1002d400105001c0c0b4412054015400e8050f0000c042d4505c03c0c3ca400c0700258022404038007081014414400141c2d10f03409516070b60300e82075446000c0e6504000c01c00c0100d80d8001d240620307001c2704102540042e200441c040c0b2481c1c2d040f42c503403100c0c11008981070720700d071219140c028070552001410b2060b00504001440c050300900d122442d91103004014030b80703a0310041c2e484260f065408903440038220945001c0340c007101c1442c403020402d20b54440206a9250040e90060403840c1c0752001c0080d600e085a00040c0100002d1070a10803500f8210745 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 191043444 1250 191042194 191042213
    0xd0207021503280e01051e07020f1f021902010903020601091505060c0f1c0207060504081506040609020a03021b0c0a03060b04021e0703030f0209060409020c070816090b03010603 78
    0x24030700401d501d143e03250b0b0a0031290b40a4082206094002d10291505003030a4444594030760160003c0501d00004c00c0c051440010054002e45000d0700a045040c8404103021136000e80f500003414039502080300b508140f00ca00e0410110301c04603000801c0030745546c6006402e04105030003008016241902a40c0c200d00e80f44640021580d003603d8190b6286d0340f14070405e0800c201c00042c16402c0c42800061103151464240b01c01203200d40b51300340c034589529900110788504c2544200b1032640e2001d4003148545100c40b5809030012070050001480983d1843c0c0e100a98119070075210109602144000580072441c0900c001c0f20906005006c2c50298240080d400d05464000580b00c0b6545001094a83c1c4556040302c900e00c1315401c6e900e2011104c5038030b109295100400850010f810050003211514980c000d07902c9415000349440c0c00e040c206080d1000a400070700e1013040d54031906074002400b040500c0600c0300b03652401b4100c240941009818416030f16145031190103a0314169040021401901 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 191044694 1250 191043444 191043481
    0xb0f01050310170609070519090518010c03020901030617120a0c0602160302010b0a0602060c0c030f030a0b150711130b0406150e01020a0f02091b0d0207021503 70
    0x2031480d12611612901020100340b500000507802e04a45011906900001c80f00e00c41e052081c200c55146849006002150700e0300c1603004c1100d040c81c0002d000141d00d075000b65a101441c04084c51002041442190035110070b4280040407035800200e0042c2ea5070301d80071b00f401030900798210f198044142091656256103102d601c2910301030200f0354461280c8035200c61250140c00a00540d258407101d00c604100c004d00300300481c055883e241c1c2c1d40880d8108440f91504072103d64029002e50380d074400d4582c4459000055151b03250004000c070240d10f07000380c2c010314064a90210000752119410060000044a00700320184583e014046100016420070301060b0b0140103484002e010803a1843e608041e10400528030b621609191001c910780d10250300440c3c9070b08841d036800c159400030b0740c01681c40c6c142001d009403582e035401c0c2e80c25000d410a9141c02d40c020800b50392061b00c60384220200101c2c0d8000c03900b8102c0e030a070006864010751500091010083c820010b000c0c0c42c6041c99440640d8112068 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 191045944 1250 191044694 191044697
    0x616110606130c0203070f08030f060103090c030201110a1b05180411130b04050a1a0402040b091c0507080a05061005030c1e060406030b1807080c090a050d05010c02010f0b0f01 77
    0xb43c2c0c1c184041403081c801d4440301070388090b05521a800c24a80240540c000302c0701040343c2c3c03400a00140c1079611a002d05c580d0070350405500f00301c41d4195001140c291405007045074503072240510703400004500c5c1407800c441c0c0c5004107140b04a1070400c800c010015039003007440c042c0b48000bc0c0501c4003040e10040d411000e208100c4540d4840144206440040c013980c1d10f68540c007914040c200188070110f900800e0714a55550301159640407980104402ca003d035008000541105210311701c0745060a85105190111211001c110b0700f10b1545e40b54608000c580185030700d60481a1040208034003080155000748910000f805c130182070401107079940020565443c4121083d55206164100e456050001010045c0040796180e072584d10103070281c40480c407064082e0700040c3c0001c41e4044043720590040071582c0e1400982d4a80d035001c52141c1d00036011036039009a017003400141035950311000365074803032148c1e001003980c2403801406130031a99481d4215440c5400d21074601d40c540c2c0c0348078200321b400c0c0d001d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 191047194 1250 191045944 191045951
    0x3021201090b0324070305060102010615030510080a080a020c0f09070507060e0f01060303090e07021f0e07120209100521010209030a08070c080a0b0c07060b03061611060613 76
    0x411001078604042820003082c100b00b50440c10503504c41c0d0204503441108985c4003070040340c071078500490884516114414403246a44c1c241004184280c0025401551031014000c2c626114200d44d814244001c070b08495202c1c00007130801e1100c1d014001c6200464003212500440300818011138a2010000d21100c2000300c000764070760810006a000c62000f001a104550f10790305d5200f41039000f0002800b058010407441e48000074120600040030b8804c03450b59025240c14038172101c01080c0034001c400415035540d20f4481003c0038850400000340241090594140c1500840c01407103608800900306000184145c1020300458945481c500c40d16a00d00c4150071045030790001c243d0090084a400c150f25000302004403040c000d006025050160294078648102a91110710301c0d59280203800c002c16290b00500001e00743d0b80d00d40094442c007800b0304c4c070201d18902100e00003828104220b60048029046450181605034024242c1d032104042d500240030798200309001903040000501d0090003540c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 191048444 1250 191047194 191047211
    0x10090201110f070501091205420a0e0d14030c0705120702030106150816030e0105190606020109051c0903020d05070306050a05010315240807090c0302120109 69
    0x2107082915411152841569850050295100d84840703040c4a0140003031320038030b00072403004610460003210300e5010000b01810888089032070f0f00c64194000404640c02c0080b090103078181c5002c1c0e00c100e0000c41028440e51464005803a030100c49440d00070402c0c1340d108080c0c0000c1c41c2d400039011000c118a000380c0c5601d83e62108020301c00da00c2001c8008096000d40d0343d58401030140311001d0490306100b280203100454903400036001000f44161031000180140011425040504150b81c0f1102034034980407500328034030f802c03079400d451080c2c07801840940401d10801902070b20344912005401d4902c000e00c10340d0b90070344400755902c1c440c400580070a171803502c128032640e00400c911001164050100301e6180c44904205407105040e10040d1421030804001600c000c19034811203059a0317204014100c5e0f400c43c5165a00104440c00802d0800c0d000c0301e100c124403507582011040101031840080041c80d007009201000d68032120708540130701d4010b100c0150300c840c9000d41d4a06490702200001014038 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 191049694 1250 191048444 191048447
    0x5210c0903010e030702120115030b0c0d020a080a110c030912101b02160e045001020901090b0a031e050106021506090c0901030207060c02030403051005060310090201 73
    0x3103110030302907140d0f10301244802c58400c0480035100c158021034410021281c85030380c1c68282c1e400c0c0580303e801700810010500004800a14641d04007d0542c4210304158981c4031481c1264041d2590703901203004a002c101c04500d160086651085640c0180340c1082051000a07640f8001c0700145403080d52500e504c031108480401403a0300c5d54204200c14000c22110898043d0341e014083c1030350005000380b201034a02d0391100c0074403008589030101d07074a280343c0d0340d40c49140305106c1d507201d4400c4840065030641d100341160b0710b0002c48d101d01080c040e40c040c00b20080e071012124400703178540c040b640107109a40c1f0703a80c0c11113249800c54020448142e680c1841200c02c9004021301c214000c1e09a07407070a00b600110180d640300506861441d000c82d240404841003400200c101161120303413000100f00003d484030b0500020b00109001070501600340b40540c1d82d201c0546078543c1c0c81500607400410700b0130520904002d031880ca0000032100b003009091850100781ca841248081c1d4084544403000c090459 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 191050944 1250 191049694 191049697
    0x4020a050c06010603020307090803040e06040b0409020904030e0a0f0503103317060f04200612160c080706051e10050901150203070f0201020c090f0702070605210c 72
    0x1000100542c0c0e007940e16040701900070340056980c0350004814541c04101040004129020740380d0142041c403484d902c0c0704c01c0002420300340384850340044d2941c54260050b10741140c2280a03521030b440b8042180c600034140000341e800c070780c41a5205824440200025200490140400581d0040104803182001c0b1003414040c10b00b9800d40c6410750001002c0010003054981d05d05461082008000c05408100780ca03076103c20550f00e081c141d190030b0011a001a08034088809105c040c803440c584414002d00c0022030941140007030846c05552502007002c164403110305500044000d040800301035100740c880c0c1c60640210180201440e950340c0c0070070322071001909203e806c250b28024000e864a81f0000c2460140998490680901300080c00807804020841d582c007110b101c55070046007804e5094403404c110006504090341940500605020240c803045542031160000018020880c02d00e02c000901d061410f43c4040c08115040c46602e0140c1d14008602c0c0904980e611b50f00d01d0b0b5100c20710341d600d03103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 191052194 1250 191050944 191050957
    0x160e06040213091a060702061b0705040f02090913050d1206090207050d030b1005070204050c2208210a08090c121b060403170a12180b100f0504020a05 66
    0x681082c1500041e40c3d54032504240c203914001c1400c00307188000102846402d0144010007075000b58240040100001e440e984011100c80140444071340969510110b400c9640c1c203079041610a80004907805641043c03030209421110f101d640550700007007178494644030750103400d03d00204501c24040e40b201c40b40c140c00450250500c00c00c00c550355015468100d50b60888040c101000c41c1c149240c0c0e051915010407a04280c105a8403114941a00d0750300300002458010303e03a81c4650820b01021141618044104031a8604104140c0502d030406080340d00c1c3c002c0d00c85000c03248a428a4100c296151040207841c4580f04508114015880b090401c41c10400500d100580005d4420b0f00c9610700740c0c0002d52001c01c4c8040ca40320203280d41c0c501041c40100d104901026100052040300752008480003c01484070f45800d1034141e08100f8203000083c01c1d0340007211134060f00214041480184202031204c1900120121143e9901c1464810320120200041c44dc41d446181d0114a962019025404803a01d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 191053444 1250 191052194 191052217
    0x1e0303230c070608070f0914061c060b041a04030809060a02011d010222120803070207030b0c07020f010e010903110d0605041b05031203010b1b100c020f160e060402 72
    0x4200742c80b044010312507130342200d0b10400505031012500a20340208840ba058483d03c041c0f009400c04407030140012a8000b080c180e001c01c2224200510100051180001500e4944a41d40d03480d80b0740380643c03018403060b0807070401d450410042080014140002c440c5000d1040d43e1441c0c4419170000240d00412030420804443c403155094104d100b203040d0b000f040d8601c40c07094029101075031001e4045168409002d15500c0d10103101111001c550000301542c2c4c007038860310440d04140c0c1c80e9903540c0c80d000780030703960000020000b290039021450800000d8207000001e1030b008400d03007161000280703a980d0b240b00c081d0000315400811003058031050224403245401c0030040c000c50030b007854000b4400a04950f09034400240d001c0105181c60040745600a0014200e5007506507400c0550074a0f01e030303000031420002440300348043d041089050007001408140b8a0b400a000030300740348041d050100e8100f0400716a08005008a41314403207961281c00e85a031f00e508501d0b9550340d800410020f05c2001c82c11031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 191054694 1250 191053444 191053453
    0x120b0a110304121b0f14160602030a0f0f080f0a020c030a0c061503050304090b0a0f1203030506010e031216140a110105070c0b07060b040f061e0303230c 67
    0x20b200929154082c020019982e00307101602c4681300989251303440c10010400c900300c82c54100030561602d003140f95002c0c5407058a841e140304d65080b80981d00940d00039400b40e080400c1707800c8440d0b0000c040c0340c01c141685c1400e0303520310b00d180c200030440c5000400c1d4012000c21380e40803d1290b1150350580d8000a81c5038222503a41101000242c03025090080817074003181008000c200350a450740301c2c1402c4a40c40320003036090a0500840c000038241c007030f007403a401841401380010740d0282d044a000003012704c000c5a403c1c00c1d250782001001d654000381810f0500c649414101e106480000320420178007a140c59540c0c8503c03003001c0302c3d000c2072007102c400703401c00d820400d0b84a103200c80803907029002e0344200700c02034105a4402c019103180c01002000707844a00c00b90b800b003040b00f848800500055200300800502c6101c2c0700c1c00942214892846695219500c180611a00410b4490162550000e030040720f002c0349190341c020700c000c000c51400c01d00001300c1c04460030100562015100b45120400588 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 191055944 1250 191054694 191054701
    0xc0709020307110c0d2f0604060504030501050a0902150901090306020c1606020a02030c210f0c010908010605090a020703180b1c0903080f0c0c06150a0b0301120b0a1103 74
    0x140f100c1043c00020b59203014000851100340303030a0540c451401e500800f0210505c5080d034611403400640f40780c600d000f40d81d80c0c000a803079603241e0700240041c242c10f44030903407205c0c214140b80e403c603203004004c80c1e485480e14000d1005070390354508207054031307000e000919624001d00b070049170310720b0448d840244114000b003804007028001213003100b000c0103001da010501d07070b80e00d01d0104e03034902025a0194140d00040c500b210075041440000e1085045200024120145512003502e07040309541100481c0e08540320b05007480d03a1150707003100103018010091003514244400a508488045c009900c41580060b03007100701401201d0113940f02e00c2c01d20641c540c4a0f80d44502038250360001603101c0d803081142400c002007044610650078215095601c00282b60780f94400c100b44031354080d00190a0f0315050091a41e00241004004d101349424025003800240340d4040c4411005950814204a04d0a0005102441511101200301c0d27070000801c40300c5454480213031001f0540301c00046050200001003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 191057194 1250 191055944 191055947
    0x19031719200f041a030c0f0901030e0a050109020109050a1802031308070b01030302060c03010308070b0402030f0106030309080f0102040e150109090c2c010c031107050a060807030e0d050307050c0709020307 90
    0x6001154200050035074842ea014130000f0f1036210407201140c2c001c006109205000c2403ca02803d08290181000a460081c200f2080d181c1240224120b030b060307460700d03a00011075034081c1e008401002e00b500c0d180f040605000c0d801c010b809030441e540700110350220010301203424003c0402140341c2c00c40c0080b44d480c0400d0400c488202024001603001d40318100c0420b01008100045078102d981200c0c032603003859034a958182403090043c0c0140d0b0f042c4908143d500103c6000e100e070500451094441071491441e0078082402c06854942d039924903407042c070080041081c210702295003c0f01800400343e802003440016180060782d83c0000154034070300795507000400d0b00030103015440582c855913440207598110b20460040c0e42d608001e80001c209044080000303000b0b08082d02c1648100301030365002e0b600c030300215040c0700e8654800e0001a1001003444a00c68051141c1e404005100f0080d100e4002c003d28060081c0c40098480703403c0040000f05500418018800f02d400380c5440c00c0c00b55035900b44a81c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 191058444 1250 191057194 191057197
    0x40911120319020304060c0609030e060f07060b0306040803060d081309020c0f0705010f0f030b060706050106081012020d02210106080724050f0c19031719200f 70
    0x250b454020080320503100940000190380450b0215620744c89400b0b02c5988140c060044500211306025216035500c44696401d805800c03480400d00610b03484461a0411900b529110f07101c2a0098004205100214120b08101c0703a00ca10169001c03804500d03d8a09840244204481001001c6502d50049880c1116170000c00100526100b21500ca80f441d082558580070030340310f650b0209620f0301410702a5070240380d140c888100d440c01d0018080740e04078089072195006090442d81c59581740010710015800500c506d4002d003514000c1e9032105c3c103020280b000401a808003070310802c50201034004654818101c0b0141782504448406180c1000d10003901900c80380c01400da490141c0c00c40411043c0c00c000e001c004011442c600c05850900c110800d1319a58071072465130202610411a0401101040000720031780a8a19503d1125211609004040300000b041940320503000700c090000464110407004c43d0162086000a04008000c60382c0c2010404e80c4005101018082810300c100c1e400c040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 191059694 1250 191058444 191058457
    0x1209010204060807110a0b130515040b070c0f02010e0d05010212010e060114030f091c050d060e0403051206010e0406060206090708010204080613060204090f0213230409111203 77
    0x8031003d001d0340301ca42054440e6500d00e00f10700960380c0800d6112006c5846130310040e0b080145070641441140b00e649a036810304a081480001d031035132020a11041100045003d54041c0d07072443d002c001d0790300955505540e42a0544083e041000c0d03042ca80d501c0d0f0b528090300205056200c00215600e441c00c03004412519424400d0804080104000440c15405514a001c07003040001c0390703615503076801c1c4409074510009040f400b101d105014075022460071041c002603501105865558488001c230a4401c1914bc680c4c2154840c40109814040000e80207801d440170000c2d1442c89060710350350a40100d5034240f010f50250351141c244940043d19580202d202030146c00c0715816550480c1e1502c02c1c107420f0388941e00c1780000c66800303140001d002101d00103003203844c58841c0e00058039044d03548981d00151184010304144540d8001681e01801c800d001101c0000c0400000c3c0c0c944224104801482e842d680d102c1850240791a80c00f480b08100700b6032540c00c0c1d08030005100c03451540301c51551a81da50040e0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 191060944 1250 191059694 191059697
    0x10203120f04140c03030403031110020f030a05070c08090d0303240501030b1008190e1006051201050609010b070501060302030a030818070f0b07031e030b030114040b0105060f120901020406 83
    0x181c181c0d0f024940d0114070384404c40009001540b174149180d50403280c1801c46008003c49008030b91004d4012903150008107840c000984075652281000d4403c0d004840000c0d200c2010300a11400700c80000720490103598404800311516200c002107800c0c240c01600d010007254071a2200300d84980c41020008010400f500d0081ea4104690801c400074040544090b01090011821400005104548128052082c03840c2400c000c200d850300d00d070040389042c140b5003030f414100d92103c1d02448207042222102e0f90310200b01c0002e00c41d90034004003041c000a0103001c0d0540c0180d00040c1181030080942214004581c06012545a1402420000c6c0851415200890551218a1407900c440c40004100c1d058458003800001030602d0413000f00100d40c04403a084092029138420182485d8603410500d10308400c6440c0415040e0403001058211398404400070740e0340751141c2c1030101094440440c98107689090b04e19954510b54040c0e4110180544803520380800405400c105250301c064000e0400c90f51103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 191062194 1250 191060944 191060963
    0x90c090504050c030105090910020301060f260f07031503080315090408091003320903040807140409120c0204050c03010503100b19030c0807060504051c02010203120f04 74
    0x251001c22081e01e0060303d200700d524406200501403490940405e0b600418a00d007141d183c240c00014017400c0c0d8000b640070324041500e080d201002c1e107402510508200b032451420850070340c140000040c81801c054184001740300e85000080e14140241c1c40075043c1c030198882d8082e025a00d240405c8180d00c21941398905050310281d43d00b40b414501c1e66103000f0360340b00318903038209800720341031004200b4140700700f000b05030b1148000c001103c040c85400302002841906024881082c0141d0815064040c01d2032450303034000c000820a1400108945084c3c82c040d40444003103540120008001d00260301005c0d01c1602c511643c03075003c6400803810380e00f441c82680d050249a480700c4a42c0000e000900c80c00303415130015004401d48224507030242030b0f8120014000c07040c1c000e401000040304c20260704200c40d02e044400702801101c81c04c0125000a281038030701185080e046c00040707894040003081070340e964070103103440c8400c580c001d00c180c0b0141b02807d020301410345440101c004595000b624241d03808801c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 191063444 1250 191062194 191062199
    0x51509030f0115060503130b04050a051b01020d0e040f050702061602010603080406031e05090114060906061b10090c1502010c091202040b0405090102070c0b0c120d090c090c09 77
    0x1010f00a42d03031010b4001c00c003e44803d14040044d00e99a00040010148180407070b2048002017886c2003060045c0c0c021001060003c2c01850b28615001c1400d0304241c0e40144154110421782e400618503514001c01c2c0780c09154030213a600444d01802005400003907460030f00b000c000742c250380002d241d80b050003140711001a05c015907906a00722080303404086e0420004200030b20090703009802a80d00040641d03030808802614800c1076046a4090300e1006090751100600d4801c0454606042e8200c84101d40703003c028100000010514801d075641a2007905080000900311202131014404900d00b19600703001c40340039032400d01a802654040c0c421220a00303803a00f0f04403441481603c181d0311143c1c5401e070181d810305200140680c19039100f20303889521009120015202c9014050003080180009a1a44440d14003004602520303085001c98040a204600b04a14005010107900f1000c81c41503a6a0000e200b49101038030344200090320161403600c00007086229644080c403444c1c003c2c2d650905058 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 191064694 1250 191063444 191063473
    0x307051c06090f0302070b1201060c022e1115010909020604080d080612160b0f0d0212010503240a0506120d09060e030a0818061606020c0705010809061f05150903 71
    0x80c2310300046005440340014400c540c0115081409140003c144004000c40c0c50707003d14400d00300b80d0341903025000344482c070340c0d00a4101d60402c0302004142c01820b01c00c4c01c0703002c0146c0003200520444001d5515044100c01359107036501160046c00b10107050b101808083d0001609140e010340700030380105802e210a541110010500b000341e02c601c0c1c080d1101452070324000003110342141380c01d51140c80c400c1100300800302c007a1006002801d110f5101e20070755031529040604102401105007040481c85410140b01d0034000d07611a0b005142540000f000e1f102c143c04103010b20092542c007030052003020b688208141d0080002c0c0110348195807501591480441816210030b1240e10040c6840070500c600499486d644014109001c0c01a10300c40c14004100c021031882c00080304140c41c000e600141540c034010050005d070002d00802c0c01c1400d401e00f0818031040d61064002c2c0000483e40c1400c80c1484808142900d500050000808140e40654004032700e5015502181d0798500c00d108101d807104515 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 191065944 1250 191064694 191064697
    0x11103120609150d0f0c0b0d060302120a1211010f061806051509091504020301030c06030b06030411060c0124080705030c010804030f0e040c0905031b0307051c06090f0302070b 77
    0x7090b0140503081c160006070345d03a44c0e418551142c01c94010803402400301e030328564840940240c203000000400d000b0301e180103101e0b140205010b42c1c403454201e104090041511000e801c4001942450410200c0c007020a04600501c02003e549103e0360800c1d50010309075583d44075102250154003010003c5c19542c42c208140e104a4070800280b0580c18130402d84146448900c0d150b00c0a55601d10200d41c481050001d4120381c0242c10480c0d440c2010b03001448402d030715106041c107031182035640324910b0038140c0381c0c00500000802181d00c5110005013500c2440710070f420400e820260201c840d200791340910005d40642c0c8141c0100c0300280705258000641303140c001020340001c0010386840c503450b211500d0884844441d410001e0910040c0403500c10780b511103201e02d910900c000e94a90586c2c9042104050a0081d140a1a06000700f100c003007110b103940106401080794400c480d0002c81c203036800042c500c0c00c1c1d130980028143c1454403440c80107101c00200c012503e140300350709494840e600c926403034909 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 191067194 1250 191065944 191065981
    0xa0606090504020901050403060903171605030415090210030e0f07030807060213240e0d0c150215190507050309030d090809062d040803090d02011103120609 69
    0x1818030000304078a04050f80180b00410041c9881460541c8a880c0e644c2074501c404400c400291501c0047c2c2040c80d86143e0710754100032500ca03070200e0515246401402808044c00143c00034a000300b044854608ac1c0d03111900166024001c800101c1600401034003e221100c6884658043d201b00c070f2060a0002c10900c5c00e81c0c0d8009400c904101190312098020342088440d19413400c69000c01141c84035640009404c6100310503a1300001a200c884010140c00b0400006400b40744170302c000000081c0000100381c15a03503a01301c040080c1003d641c0481c5800001114580f8805001042c86070084490001a909001c51042400a034540740000c0700d05200484084807147c0003031003892a508581d4009401c4c180c06150300f40c0c1000b940d100022000c0c0d1000940c105401120b0114114803044003030729408540d880c40d6114101468144925282d01c1861000d922400c9015901d004680c05103411005c1101141c0450782c440444040300c83d0f1140c402d0b1802441011864001421900d00754100100b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 191068444 1250 191067194 191067197
    0xb0702060301030b04080408100b1e030a0b0c041e0302040b150f03041109180106050616030e04020f0a080405010b0d150506040b030f0a02011404030c1511031206090a0606 75
    0x107503a280d40c664101c0c04402a20482c1d200b54100000214480c0c1000182603410382e100001461041000030000c1c80b0081621610b2010142d40d0a20320300c0d80c012400d4000280c11407840d00290342da020900d4003911940d003092240d5118141c45020500c54110318070242c0b072003901c0801041418034100f10b00c0213102224550185d504201c02d2503422000c1d0059900b0500c11112000c084024200081d28500c00b20b80c0d0408402000c545010380440900445006010640303c0a14000d180380700d42c00d0f1046901d01c054107010440c0031254031900c03968100c881d007003044000b5540f02c03618030400816001c01510161007940c24596441410314286243c3c41c0c08540c0180304000090000500d00082c0c40000e007104d502564681c0c4518176904c0034011000d050341000b014140c2034400d44005000e0844003001745080240912040c80003540c2c025461049d2048921501c10318400d00c0760449103030845101e0f12140740004104901119003413680d45004203000c07581112540d07a18000c4600700c036001e101d00d00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 191069694 1250 191068444 191068447
    0x10b120c03090303042a0e0f07080402030325080304030f1106010609050d05011404051606110d0e0a090207060b041a091f0314031e040324060e07020c0a0b070206 71
    0x2000079411b103109040034214808a0202e5602c2019a0307071505589620031072210501c4d10420aa80751004101d50b4000030501f000f00c203502b05074003c00d079240100d51800010109582c4d10b00300c2c40c0c04080300c14882d240c0c405607603580c81c50140780c001c00d03908046c01740c2c502081420176a10482c040100305a0b040e10415070726605454a000c041281c0f504454805139110755842d00089102401e5980d401d224501a00041505150f23046d038800143c220b81e8403003420414003010804a07108049003000c4158201c0c90f183c403060000c00d0010350011410b0380000100c3e880040d81c20101b00913030b0010719145e013003100e00700940ca02d00d54000c0240030005503110780c4420380720300140c0c51407815551001d101a0b14100c103000c403500e0755154140e0120384c048415007a8030100e05042c509036034800f003007024035041d5180c6080c94a103a481807a27102580c200c0c1002e140c0c0c40001c18008915941c45a8024519000d0444190608a03000fa45403490a607086000b4044018082403401c1c3c0700c0c0850f100f43d03a01a0003107 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 191070944 1250 191069694 191069701
    0x5010b0a1b150c0e06160203070602010c0e120c2106070e09071d10080a200a030e0319180501020610060305090106090203010815060a12110d0b010b120c03090303 71
    0x40101d0500030f028441d8011360b946081c2c607100d018000502131901d01e900d403148240105032038404554004002c41e0b044c4400c1d400c00a40c4218a0103100b281901e2004010300c031581c049060585c0303d820140c002c050705030010080c4040c09000346100340380c40103554650312419000c0b90445048403008d41c2180380d9102143c2c0c0184150780021041d070b800801e100d1b203241210300003218081e40c081802c0004001c0002d010b880701980c0300d00c030240000b424066412200304c00443c910386c01906100c10a15503140b1a042d101c20003070003191810700c0c2d214030855080c11032040c00b40402d1019404140316000385100400e4650001409a0103220350307514240c0b40f546054411000f404004000502d15502c0300c20010f108241070000d940a4620140a8012608108144017803608010200b511480b603030340e41000700b0103004400002c501e8105111911341c0d4801d00102c1c8540c181d222008004403020000040c808440304c2c05004110040842051365445601e0722103130360b000a484040c203980041011 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 191072194 1250 191070944 191070983
    0x9010e010c050a050d030e062a070503041a0418050f01090c140301330c1502070c090204090f060f14031e0307061b020606150d05010b0a1b 61
    0x3195400748900b0440b21041400d40e00c07281407042a0446a010948401036644400030030b010b400c1c1c0c000c01003501c1081822441c0f101c1400090224982c8014020015a88082c031005008480140451030010318040c1d540b030042301c03819489440783c1d420030511300d24044040903a50040c180201c104008929003070742071410140003080744041d107400780300c5000c50030000c0e41d484001450003000e4000c201e840d030a0018038003810a041c0142c03611003c582244802541c01d40094400d0312031904000741000b1103907040c0d294802031040c0360000e400030b100c51000086018441d002042500c412601c188504030000782d07464291801c5000d80c1c00c07200640901070180003d00061444208001400c40b011580c20050440b010400d2a00c0303600542c00000311b00040c0701d03003400340004035840314800721544440d10000944403440a0f01440c401d00025420710040f046840c25030700e00c2906984208060359589507210601c0e44120007960104000301c071020f80760883d100c00ca012454005a102e05440400140b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 191073444 1250 191072194 191072207
    0x100302040203100504140f0705030408190c060905100c050f0702090406090b151801080c01080912120a0b090601020d052a0a200f060c01020702060a1701050609010e01 73
    0x83c14a5042c00c1e9480040c40d6a105d001311002c0e140300000c0b071031250a040d5218130324410004c2ca0701d0248041001840002255181200c05290a25044951810001000703e44c40502d501c8040d1825003003411017400d000c4003150031014200000d10030890428050819a041d02a005512110003000e000800150818580d0664442e1140200107100d9440e65260004001d05076581008150940c5025000d0b00f0f2088000454225110040b0000c3d850320800d01c0d52103c2c15002e01c0d0400003104040703008410b0802100026401e0500b0361a05c0b07040040340f42d043c6000464540c00494204881610a41030691203c4d0090070181d02400a0b1480a103003514641d201805c1a5031011600b0f81c0040400000e80640c03241d0044080540280780740fa00f0103994000070304001403004c40c098015804213544400c80050400c81c1620301940b00c0904494040c028052684003a401c00000254034038a650b22003084801c171508040b0014007643c0301e100713000070780c040d254a86000c2440c1500c24003040d8002d91 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 191074694 1250 191073444 191073451
    0x303030f110705100e01021306030b0d080c0c01090f080a0f0812010e0403080f010f06230c072c04060e100906020318010905030318150103050a1208100302040203 71
    0x30300800c0403219001c000ca0390b507100950503100b5803c043c0e8080800c900a000da0381c1c010b84944025403d11021850141130174505114102c20b2550302c00d5090100e407103180c01504d020740c01981c010f440b03030501e008036034854078007000e060300040d00c00c400840e80d54071030401e500c2900d40143c0104900c1e40302c1d5444407a4070300d500d201501c03030ba2070a00000d09200441c0b0205406012030138000246402c0034600904000409001443c40000280062000620f09816802243c030946000b0740208040380c50603040c10000c11407e803c214001802040c990760018507407003120030082c0c401503d40c604010120a80b013000910003080c0e801e074008500030a80a8102c0001c400d221016591410000a1500c0459225910444240303401100b0821050703c2c0b4603083e00700170f014a00a011a94036a5221078483c4001042c28065001d0041501c25091041012282e01214800c404226586034202a6960700124070b003184e0765120320452080c0f003841030004078042d810075400c4064490556080101075040103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 191075944 1250 191074694 191074721
    0x1807050c030c01020d0213091802010e0f0303131401020a050304091109040c0207180b0108010e090703021206090106090b030c13020c1b091614030403170703020a27030303 75
    0x502c000011001c0a10061482c140070800c0140d03250300800c0d0000e40e0750013a07409851200e16005100d65042078490042c00403e0b82441d00940e082003040c0050b86004038010020f40620010818a5022a503111808180e0701ca186c101001041d81500490b9110900080103005400900c0200802d12403a0890010500100316003800e0080c2c84001c9012211180c2c0c0140041e0b000d01030801240c2c04000d21101e07001c4c100c4070144004c1000c2d10000c1c1c04040b0621490000c003030120006003c04d0030511000018580c0140b1045000d10a081c600799600750036074840185500e801e0000520710f9961140d6103080c90301401510490003d801085000385102d054544003e03000c005815211a00307005d078a0800016621401840d046070b414030181000c001c166224100c680107a2911464010701100980b041e038124103030742c81d5201e140c1102d0b030b00c168016201c91411900240044c0a8042c0c02400d101a62942c0300302c2e822010880b00c8540400060182805540914040c00440d2003900420000c0c1c180d03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 191077194 1250 191075944 191075947
    0x110a030c0909020708121f0e19020403030801240806060309010603081b070e01060801030215161112070509010909050102130b0a020706051e03040201020c130203060406051807050c03 80
    0xb590740b018282d038442c00040744d4042c03002a800101a40b078030440707604600300740c05129403001640300c6265141c019010f9080c80d80c0c400c1000030718401050841a0019080040540d00d640c3d076071401904041c402e003d441c604121191040000001d4404800140c40b01d907520320140f510b4090500c019644040d01403c007554803188040041803100000704400700c0080158165080c40c81c1903a0300341089500400544581c0340010000345500c07080d407a055a0b01190034140b802d4118a200800d44507a2406800d4000e5502c060018048201d2000c4040c400560340ea926680161107490346906450241c1580808290b00602007030030b2541c0450070091042c0d0006282041004e04079030004095400301e5039130040001c07030766000e5505000d807c0081c03041b414413604200442035940741402255071034011b445000709c001015a0720802400c0c03c00c081c00b80080c0314003200075400710041e501c121a030600450a2110002e800c0c2443d40351411420005501010355840703101044425601030804541540320 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 191078444 1250 191077194 191077199
    0x215090609150d05040b1b0301030b0106081e04030801060801080a120e0f040e03190207060c031d04050f0a05061005070f02030705151201090605030d08100b18030f01110a030c09 78
    0x7031388540d50040d4003940549029280030b0000c1801d4040d10ba86829000742e041c001040000d506400c0d050644d5210708050300140d844449003402561400403022040800720240414543c210f00104d042c3c80403aa100c4185a807522401c40c0c0c0c0e51001000208001854140940700300c2c80b8040c04034400e180200700300e20700e03880e007800142034802540c05015960000101c05510003456070211543c05014006448100d01d0510080d00030954004080c00340480f1200001940312003544010a0607001402000541800c89101401503000c80d80744c00b40604d0440400c840780b030080541d1942c2060b5940d0107245c02c08941d00d6403580e500141e012a0540700707041c00450207940b100f0072600021071900300a900d45482850709150a60182d110342c1c1000d152a006000580340030820f440f4000c150704000c06240c5410000864440c0180e204020a00e40454048584191030344c41b401d1b0f110f42242280c0d40b007041e00f24028200c0d800c13142104a02541004840c007924060303004000c00760841c0c01c081c0d41103076 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 191079694 1250 191078444 191078467
    0x6040f02120a15050a09020a12150507030507030e0303190e12070b07021b0a0b0703020c030601060210050a0c0c0b07020f06070e010807020c091f050303070f021509060915 75
    0x400440454040c01c01c4039000c080c3d11070900c1420760103402d09500380f2110340650007003584000c083c0107450119070580d03e40f03010f01007102071030400020307002020050b503d00201d004008280a40b503a6001a007010108200e01100200b40c0c0e005214541015a224400a03058001030161044c4200039004a54800311540b50000151140c107005034030b041868600003000074208030788604441c0c242c0362954920710b15603e078046204180d03006691450b64800ca1400c0580c5002c0000207641c2e414440c0400119040f580410344180d50005d25005000c1515846d05500c2034400124030200040d011038050000301c0e6101e60000d8100c4481d005503a01080051308103420540d0860fa20b0001c20700c610880c05440d42e10125503a8050340d58070241094010b40000a282c4403405052442400070307207036480c5483e21840302410001d00e8004d046075076031015440d0000c41c56000880a0f0700c180c2035607001c1440c0f614140300700d848188009007400d207000300801c104561580d0036140342100f00c100744014510704 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 191080944 1250 191079694 191079703
    0x1606020c03041e0b07030305090f0f0c03070b0301080d030b060f070b06090903031b0901090f0305161e0e0406060506030a091103010c050301150c0209070806010806040204060206040f0212 82
    0x203410600035650b90350512200c078105141000080120b103207a10340030400380c0d15620584403407a50500e0081059250030302d0341850b1076800b200c4840e2a00500d0310300055400d002601c00702031801a000c0d03510803030390381c50000304c85e0100b40b05040c89500102a0040c10911a0380104e6060740c004000500742107075800e03818103d40052804985150005091210918040000c83c0d480f8025000440c914034021821841d0550310504048001c24042a4100d05030b00911800c0040c000a55248007004c1e52810101c1da1071024070000d4110810781c0b0004101c01001344807100d2010003c598001a041c13900c01304520220004000340c070507a92310078001c126940c440000754080d0100034004910110305081c48210f4518000c4c1951023603140510880440750850290b0b411290130180c0441c44030a00d0000b40e40c40c48240000a612543c0d5001304100203420845450041c035081c4d95020301583c1d41c0342413100f24403440c05400b0150f48010000740004608001d903084036440545190365028a0194440c40d1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 191082194 1250 191080944 191080957
    0x20909010e1b010318150e2109101b03110102121302090609220204180c140102030f0712021f0c0206151804061509060806090703030212160602 63
    0x1c0003500b0444156560380360141c05070901c0058900840354584e55200740c003451030304860164150703c0300d42d90748900506010030b546000761002c0d2000d03400516015504241c0c1b041e446503202e1062120320034401d034403d06030401da08007507400005c1342000c20744090b9071501140722090603940d02000005c2c0d000c41140032850081288411001038229248100708a816000741410700410004041003101d00c62400364004848004c210b002b4a09170074000715004c1e00c03401c1c034290f0030301d40d4039038142041100170340c400800c844400d030740071034880301c0f090049071a44520486030b02c0d086800d210100100321221071003036044000380104d80804030072032090300501707084106000c40d86613101000000b29405001a03a03000b403401648420509180c000035480703641d6446c0340c2c098162502e0014042190b280d1144e004547c8001601000513564a80751000e80703805d009155280c01040f02007595907030000340c0c290980c1d6054001d00740c60401d0840180003600180681000741c2c403841111030204403d48001c214 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 191083444 1250 191082194 191082223
    0x7120f09030809010e0c0102060703020c030408070f0e10060f0f020c12010203070207050d020604030b04020604030609061506030b0904020405190501030606090e190f06020c19020f1903020909010e 86
    0x500f0314280d00081d08640401201803680d07002001383d45c00c039a82c04149258080c0321814016110001c00500070300e18042c80e00310340500d110b03422011803110381d00140c2074120394002d103151070150f6032021440400420340c030a500c003040c0c0482c4500c1078075000c0c540f459110000703441259961001100050701c0c40680612003e6583d50010601880c250305104040c0a03040955070fa440d043d5095020914174411480058140728090740414115500d17a03045800464001909201d58466400d240000f03140107a00c1034a200a00100002c080d8003e00450305600b00007003000c240c40ea40c54003400040c040040c01c1108909001007040009142032180074040c60285030f0004082e82070036042c00c11640f8640700220650300c2248000e00c0c90744c81c010744000e410f40c009912600c1081e1441d00c68068003c1012941a5004070300070a40400c40801000e58039900032515060b00401d0441800b9010300700c4600c892610114101c1400503050400c00c403500000110000618280040a018203000d00a544190b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 191084694 1250 191083444 191083457
    0xd1505040b01050d020303040b13080706020309090a050106050316110f0f06010e09070315090c140415080a0308060d120f02120f0d09031707030c090e060907120f0903 73
    0xc240058004440d024150644454031003000766000256203026034882c00808003030008282c80d20b01c114907142001001c00b0011280700ca611000080c0d1a0b40111868078020711010002500c03942e880e0286504035012516000d143da102e1070750706800011035a070800c00b4442c0c105048a440070003040744002c0654100082c2862007985040b1900f0310406a2013604c61050309000c1c0f0000c1480030400408690740b0a000c169560b0164071140080c00604401520f101c0c8040c4001421240e540c8404811103001ca504000070100f44403c2403c0c4403d40c060f680d40e0b64400c00120001034041e4010a40025005018103070445459640f8005940441d036440c000840d100300d80e0b03e5845d0100000000030440380d200300c0c1441d81466146455005189041c40300c036888d02400420b150141c00031900072a4078817540080361502d5030002d8082d00a030441d61000401e5014000743c0220b0103040c070380c051240188500c68076220080121100c414001c00031040c59501c0020b128010b00e684140e00700c05102c0e86030366 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 191085944 1250 191084694 191084701
    0x10e0a0915150e010c0303110304080304060b040603050d230412020a08030304030e1c06050109050601020f03040f1203090f0f170609072c090307060c110a02010302090d1505 76
    0xa09940031540e02c4005128280003071031038601c1d004050801151828601a603128809041c100c0207000700781c2c9580c48000d400024801840341900046100d540601024009516020300307020459080348006801604008404045540300b00c4110f1004106505c070700140c0c158181c07000c599584260f010f4484146225400011400c010781c03084010040c07070015500350301d016140540440240c0c49560300c503405040280701d2541c4a0340d120450550071160800032507840342126802000203072140760240c0310324aa580c00403600042120155542c1d01d039050150340c503240540303901001c0000b0032410b01034004000b042160340701140500410b0600840d408441c50004001a0115140c0d180e00b074036084141040f0340742c0c0700068500103c0329084022106c400c078484804403004481da040b641840f80541c10710501440000181c140c3c280502e50410404c8510241601c0003803820400440680061048501640c06a4050069413002a10405003002c9680d01c0c440500c50003aa80b8680039643c1003030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 191087194 1250 191085944 191085971
    0x22d0303090714030d12020a05121609080a150c110a060506010906090b0711040b060d06150f0207060e0103090206070302060f0c0f04030b1012080a02010c02120301090b010e0a09 78
    0x4001083c441903000e00050400c102008054420002005000540020b80b0080e500d10580403111601201000c0e0149410a4980f40404008402005001802103240800d2024000c910080b0fa42c0d4040a0400301070007480801002e460001150310610040e000361a510300740c01d203d100039003403203494001038514021001410035149034200c00d0812017421020700c1104500002c4900c119000f4003113243d044c031220000b07805004c03400d00254000c640400c80c86000e805a030405015928040c40301c510101c15081e0413641c520702a10304d08010b03030001a01300109805203c240b59107000c10b25010410044540100d45e0070f91144c8003c0700143d00c454204140412062001504409140815464040f1803d0084a00e000741d02010f808114208085092a8402a40ea000402030420440f0400c0032505001025030031210038280954205200c06044034404200c0700c81c10314521180f00d09590800341420010460460980d06000e059410100c40b980c603c29008001c22600f8408188050348410 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 191088444 1250 191087194 191087219
    0x5120705030112020607020a0f080312090309090f09070305010603030504170a150c110106080619020702030a1401020d0e01061503050618041505010b0d0c0c0201022d03030907 77
    0x805010040240014415004211601c198441c0c04840fa0b44c0c44a00c5400001c14240341984105107024541c00c1c0050601404405060f4041d52800700b80d02c25601c400d0f10580364441c041c0008c0e40100e06600250491712112180c54000381c4000c101c03801c03036881366900b03803c4510540042d0041000072801b000345401c1c9144908004a003040984007802ca90303540c06044d00134031080d40c109142c494103141c000500ca1010074403408a140300a03c1065071b5a0415501c40c20103550310001c0c103801c10035400140b00d4034002c890180398080c00405800040e500c441490102803c40401155020440280400e2040c00b8041250030703050000075003e490104800c2ea0300040c020814181402d103404c2000d03590b41d0b081e90804591449130300711030702d6403035140250448025410184440740b40800110300040818080c050020303140c10200701c19801b42d00700b661200c0d45040000d0040e88540c2d8403280d01d01d410030b4120601900e1109481c00c04000d00012070440d00112082e800c581d124a800b00409449400c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 191089694 1250 191088444 191088451
    0x30612380705120603030c0601170f0a060509010623131b030b031e100b030115030b0f1003020904030c05030904181515090b01091206020c100e0a1e0c060512 69
    0x1002980b80c012141c403000c1c3c423800b051290140d0b0907100065070007460b4046c050140300088001c1034400f8820b552074074000a1000f40c444040315881c00c030000c14800104200040354590441500c2040d180c102d04101031185028030440c0101c2d101d0318001d8041b00d0200661070f5194150710f01240150000090515101c5c402c0c0044150240360040b81100d403002280c0740c01e1110b290301c400708a00324080042805000788904e11155015220b07000030030301c0010038015004a01982e9003500c240c545c0c10720720f81d00c0012400040c0d40b18480d0000300e0000703400340a031304806c94801d4003928100212030000800701c1d180044c4140f5101840c0f80000704018550083d143c0721440c0000c10840d0285200205520140c2c500469103070556850b85030b00c80d41e0191440100030201041d85000314103041c0f400784080d420000042c138852150111400904c000c500030b07132a0b10b580740c0b001000b02c00740c0c40c0c0b5082e404c41210a002012074100c800c6040104801103040c40103000992100c60755180800c06003440003070001c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 191090944 1250 191089694 191089699
    0x906050903030f070305060a0509060a0f0303180b04050a050915030601060210180302150712180323090d0812090609060f0906040204050403020309030105160306123807051206 77
    0x10100400da544800d8000149d070010f4a80030129a100c6000c180c1401e8140c21056140000e44030000405074401c814400e030742c000380142ca05044e943c0049000c1030196009140d40044100300602190416180507603200349c50540c03001d942030014006ca03050440a030407801c0141c0241e071211408018078001d101004d103010030809a2b08000380ca00940303481c1d0103080c0e00c520744805004160960b02ca0b02a0449020104030100150022040200c050300094001240400d860030303403404085d4035005042c407100c0004081a890299a4002c010b540d25044104581281c0c0901a4046419104a41d284600500c000030581f6052844009107403500040420154010080030000041e50110740c3c1d54006034143d03808103103a102c40c5805d80c214011009010780540c0707083e00700144d40485450201d000c800d9503c0400c0900c3c0c82e149900100c00714900c014007071680e152080c1041102e48401c80e500790145040000e018402220015042c070016298140007500c0810300d0030308400403140c00c2d900660308 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 191092194 1250 191090944 191090951
    0x105030c120a0803041a07031b03021c0203060303070c0305010c110d1d0a0801092f0a1a070c0f09050f090a0b150a09020d0509030921010906050903030f0703 69
    0x2040355507441400c404010000c1001001045c00c0085800e18201c0140c40c2d030088071098500040000d0082c189a6650f032041200e000504070b140f03000e4400c803160108450030b80e02c80b0303948500c0054060341c4088c3c4240d030188420466207011901ca11155400741d4801e000200d40403c80b09402480c07142c0d45072098610ba08807001407a10107400c044070006200c030031102c241b0310300a501c0010b43c121405a00c4812a5401e2491590401164458090300e480d048002e80f0050282c0301c20b12101220890000d641240008030280310041800001840e8801200c1810345807507181d50310300d00c00340c020341e2200c0d00c0c00420031000d00c1002020700810b070740001940001d5070a403070034030800340c0e488245c40350280158000c0340125002c55030703810300d41007061000740421801a0303454203540b00030741c0b042c403064144501d40b41c0400c028030701c040211500b00b00f00502034800701801e01c03980c0b0160b0404e0022010030350340c2e51100000140d050300989106280ca01c024584a10b4800300b07401c83c0366401404242058507 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 191093444 1250 191092194 191092219
    0x10c020601080d050f0421060c030905010e010b0307171212010f050607020f04020304020a05030319020c0307050d0201120e010c0c0501050609062101020d24080604020d080d090f05060105030c 84
    0xc41c035046d6022120030071050240540031140b8201d5000d41410007410140c280460558416010b81016865070b1048000701302c14000c3c0d041440c02c031b0350000121507054010410030402c0d0f02011044050410800050b5030504401261107151980301c00454121984681b004003c03140b680690300c5c2c002e003015600f8600d405081d500081d17510a14960003031103543d000c00840d00355180c10807048041e0401500712076944607055010f0350411582c03c41340005200b070304006101030a0218090007207800250803221500f10135801580c200110700c0c400c2c070009a07201d0303404078000002d018a01c0d03200500e803106100c80d291420a5425110018881401740040c0024041c45072651020800c00400302c80c000d443c0607101030a000e01910800310346c120071030700303041c2d40e890314042c00c107010890400321051401d030a41c1e8030b841c03650712280201c6010b540102020480030100304108014a400702e03101800150058035580d8100506101c49020ba44907030150f0b00610060904128044e6150300c00c41d0000300e8940f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 191094694 1250 191093444 191093467
    0x5100306060503010e150a091d0a020a03061e060303050a031a0102060118060f031415090d03020307200709050109060b07120201020f1c0b011d09060f03010c020601080d05 75
    0x8010310446003240501c0001605401c469a8010300c4000003d07e1001510354428401d0040c10000500c1c401c001402c01d07048480e007000045442c4025405004c00c00c50b1881d544914008103142500c0b181d401c5202e54440c0c0020029100390f0001d503110381c580e103440300113032600102140c0420821900040c80440c034100c440e03800289403811240344410050820400c1d20140c009460303107501c920310f0150405004410442c0030450b032000d031100c1c0d508903441414040c02c8110310b03100a80300075595170071900101007003a21a400442d0711902a00b001c001c0c048806084a80441c144c1a5980054010072001e02ca10103460041900400d559103052060900304803030106180710300e000c014180020b071030050107050300030f40540c0c0b01e504401c280c01d502d41106004808841848413020050740e46010903942c010340c040d00090491101e8034030106100f5200038180700aa00c0d000d402c007507200c00e49071000300d01507030309000c2e07502e1040e044d030302511041d4940b20705940781054904600091090a001c401d4480 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 191095944 1250 191094694 191094697
    0x6080a1b080414030d0f020301080c0613090b03150405060702010b03011b03020d06050405040f1403040b0304141509420a02070c0306050402090a0b060a050717070507051003060605 79
    0x1030300103959400103c103404140345544a030100895000b07062902480380c15103940c0c055812a020750f002c0d078809440d240200080380c170070494801c0b030504604070217200800c20b0342c1c030034a071400c00a801c481201454450744510352604070f0b0202c98a0340700d141040482582806080c80103502a802441b105c02180d044002d0095519041e070b04065007c50350340100c13009500040010440948100094201410055149122814103030740900c4000840c01800c4000000c0305c00300d45c60012101e0035500c85035070f001d44880034106e07515168885c26442c200f01d10b0300004298000c00d044402018034064100c0c0050361100381c587c040a150708150700c21101d00c01c06180c0e940e4070a1a0080e103e06554500c1c030b41d40c0090050000c090080325019401000f00102c0e41e00413401070703000f160003a501e0341e03e414501c800c0d2107030131007601c0c0c11035030900c00c4401c664001d00161a10603c50240700d500b800c540394510348184c0006609850683c00302400700070a08140140560300c00082c0790070311800e8240100a45103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 191097194 1250 191095944 191095951
    0x90503031611040b010f11030d050c030907080c0306070507050a0c1e08010605090c0309120c0105071704050c01052125020604050a021e04090c06022808031f06080a1b08 74
    0xb071101c61207002001d56000d02c09c031841008100f4003008141002000c0c0000c030740041766509054403031b00e40c5c04200c0319000620b18038a0480200180010303501c1e18011511a041040c8c1111f052280c0a80301001410345060b107030144c020304001d1102e544c80d100c01d9104080042c0d1049102e80d16001d024040c6403503004100341d00241520306039589440d020704061030900e91052003014480c012850b018816810740000d40a1610359880140507038803480480c101c24001d88000b40168024030030800c4c55405040502000940303825580c004202c21504121446400c80d000c1d140302c01e1130320a80480c0e03500342141c10366801c5c03588000c2c400c0380391a82d00d103541c030090160044c2c8074880035080f900c42c408074801c0c3d003110f4500113403040c404960180340481340d2001c41d00900c00503000300d0079895907045208140c200301c070016031203c0100340d81c2c079128101594009064409410f0480e4030084d10107043d0108640241420b581d49500c03441c005e18804201c4500c0500620351650080500c603546038840b185981 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 191098444 1250 191097194 191097197
    0x10f060501050c191106040e190e1903030605030703050c190b0d0b06040b0c0307030f020609100e03070f08071703040b060f03101a09090d0f0f090503031611040b010f 73
    0x3e20030380d28241703800d5081e196103820b07a002c100000c01107100d900c600b03170b601e00034400305001000702c03420075a207441540e0402846440b60740c04030b01c0807001f100d540400da4807021700074200025626110380c082828103900d030300300f40d401d6444250900a241028100440307840383d421003580d40c260034184161103c2c41088409040a92160400c0049a66071411140240403205649940f0710114001070340380d812561003500403603440f620f1400030703074004602d80c0d1060020fa4068014041c2034070089004001c040004265031006120581c00100301540d88a541c81c01407041540f203064500e00b80040350b0041001044101040c000d210020322a01c0c002900800c040306c00c4070081d02c100011a15000e65410211640d40c20490030b0071201031072400f8400760f000180c400aa6542d14804440d58400001c0340c8180003500e01d8847c01c000c0c51186031461500304d40d5141c014030456513040060b10715081134071444002c0418402c41c001b000354440d000d0020038016201403004c4803020703001800c040c420800950 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 191099694 1250 191098444 191098483
    0x10b0432060703050d1a240f0d090503070f170c0304030b040f0611091c020a0e040f0b07020d0306060c12030c030905010509070510020a110105070f1202010f060501050c 74
    0xb4200750080003662061140040100000302595100720b1400e07500800c00390107004d002d2415056038507404190610f450340e0780c003030b28a030242840040c4110f602c00b242511000b1740e10316000001820a02c0140300d001e02409a42068800e42c4c102070000000103543e4100e908401c110046600801106680459070041c0402d480d42e543c030300700380030307940e0704500014801d80c07422104040d034100c40c1001c2c02d02800255070b41c0f1015042c010414414050150000c1e41c0710424400c02c0140704000c400c01a80540310f0b0f0ba280f030b180491942d5000241c042034901501681220340400e02c11581442403500504042c505400d10080544600840c4030003000084101512107140c0007031036000c0e4200d4071860341c0c0200204003502c0c0c40d65181d512b0f81020b0040301d2041e00000b941e41c00881c4000303001481d440e041460306c00c0c8255003100546050380f1601d0100c0d05824410300710030200d000d41c080070110201c00e400110710404040c00980071102e56400140c10702a080c000310004c0103001a06c07103180c450010f0440e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 191100944 1250 191099694 191099707
    0x609060703150b130609050103060e160212180f090103080d05070318050a06050601090f0e04050a0c080618011b0e0301090b130b09032817010b043206 66
    0x1000099550f0040715104600192110104d203210751090116040b55840d8042544c5582c0110207840e1070744070340406502c0c00400304404071070750050455004810b0046628503040c00e0414803260b08116510b0110780c0c0b1030500d010341801d214400c001e9016045403444503d42c1156a40c0b840e07401503851420405030b649000826250090307015a00105040317480311440070b181d24240ea5248440c0d43c00700e80b810b040c5404101135502404000040d00c44100e9a048120304010500f60002e4006200340e03010b114801c6240d0102d0b00f2900e140010342070702c00c00341c0030610f4500400d440c0600a140046110b0b8544100c050740800d0020441d620b000711480c100401032000d41c00207015000035070b000750409031207030f080c0b0040c1564050100304107881003100a04550b66914032079103d000302c444000c0030714100011030200b281f80601e5110704844a08050700c48080742255010306032400d0b049200c0e55840003034184400c8140c180034034421581503a643c2100c142d01e0071100e44d101401c050450241d44081002c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 191102194 1250 191100944 191100971
    0x50304031403090a06060e060f1003091a1611060601230301060201021c090f082a060a150f060f1103130311032e020904021c05090609060703 62
    0x2155401c4519048154403802c01540c0d90352280c41e01a8121441d519201e00050020764200356540300b0800140500c0c44400c0c07110500c103004610345884400c01d81e541104a000607001100e0000e0700544892011080c07415140c04030940407400b020034107012100704854401900006d8259002d102807818800070001c101d0b007004684da8491440c840ca420220000c1056a41580038100da0b03802080300c0c48220443c0d0b000314048400c0034201800b04514115101c0101c1c01d44002014800c079444800101c0c0340406091510481541d4900c03131654120700f062001258030741c0251600340301c2403250951b0461400075803403000301c0144217490900c1807490904002c1801781c2d04c21001204200183c0f0790712001c0311f424903410324003030004842201c650304828a081c01c0002c0c0c20b21503101c404c440d214210405400415024010001d5040c0b40c640800c2038000c1c907111400503000152441c070b000320814041e0618441652401811011540e0240c4204001401c2c000760172600304501c1d0400094422080e00c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 191103444 1250 191102194 191102207
    0x6081f1e0e030c0105071814061c0b0109270902010201091401050601090902190309020f0d030207031a0609070302030910050103080703030e0d0207031128170a030c0305030403 77
    0x80100d142032600320900400c4601000034032a1002d020001c0202d0342e65094140c400503201d0000800741000100305000400e6403082000c1c4c00711004042a00700003002c02a40c80b5000074241c0b410207070391240e40090103945c0100a580181064801041d00c0da906030101403400b000c1c02c022101c806845610000c10369000b035104803403294120302c96200c0c0410310130b51107010300410ba480ca400140c1c100c600040c2d01c10b192090f911910484241d95803821044401140500710006080c0d0740440c650414900940e540c91078800e07218400e0700a006050b02d1814130a05040c403641400920341c00300810003007950b8503d00150751012240c1001600c0b9107440d003003149401c1c01b183c10110060700d00130000c01448820000f0f4000ba9110790746c10f004010031141410303228074180511901581c011041400010409111164003050103040090780e80050300100d4603510503182100305031030806006001030045050100400502c1c02e0040070b500841307a50003040078410700009000c10801001050400d44161f4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 191104694 1250 191103444 191103491
    0x206131703030f010506090f190e01180501140a121718090601020f0c0d0204090c090e0d09050604060806030c0901090b03010b180105211b0406081f 65
    0x60344994900d038018041592580162a506082c2241000000d4603280a504403003044c20080d1002d00244038460500443c140c1144034040790007400b05002c0303070b41107910300b295009064100302400c1c01601042c0c0c5004440c2e041e00055401d40020110207400e03103840e00c8110454011420707c0480718030304d0610514850358a0b1a0030400040001d415010030400e00310018444402c480f002d5540d15520016640e81c0c1250800c00402e42007000004440e10b4880c1e483c03206d0074005000410312803555907a0034181011b68102c1480c86a4484199103584820032018a900d00705e4200382203d01d062400003006c40c0120311814041268400c001056030724280940842d80030050524880c55031a194580085c00f201804140250310308440589189440b444080218140382002403050f400d14050102e42c00c10028113507400c0b00d80b4401040050b40801c103070801e046000b07a18003140c007038002c20003094504075400f00045034041205845604000d81000b80d13030825040740010030362614285c450074044081c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 191105944 1250 191104694 191104709
    0x6030a060216020907030b0f1e0a030605040506070512060607020109050303030406050f0c0406090b0307020c0904111008061c11100c0501060e0702060c0d0603080307020a030905010e01020a020613 86
    0x2c5401e211a400020940030954422181d8014903500c0c1c220803800c84102a02e85580032042d214000e0706814101485484c180090303055207040c5025a0204001e044a6803040707c50940c1e402c00c0106021090165640000346450281d16201c0d061420141030b1a001e00394a00c10040007a42504580c041c00241c1c00a01c4084c05403916454035050080c01488211481a1651036200028024540f14003c450030780f039480c0c880c00d090608080b00549940c0006040301c044d881020318450381650340140303851040e881204411813101096044c088a5005085800d0500a03040c09200340d0341d654200a100c0700421f402c000c00e40b12103d003070100113070110000140d04041d00903e0702103d540d016161044180c0240000d20105a84d4030a20170080300031928200160800c6000c101605040300c0180386500075144045000ca860707840710340d5240e00c141c40c0c050140e448000880201500000d00200800003402d14801405403900043c0d1100742c00d48000384100c00c0000d06000b440c078099a50400f60248 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 191107194 1250 191105944 191105947
    0x3030c05040e0a020306150a050a03090c08060103080a0212070b01170a0c120512030106050a0c0609020a15230406030e03130906030b0f010605120c09130209041a0d0b06030a0602 78
    0x9440381c9002903109031181b40c0180b0b194208102130761120320485400354215035a10b8580280c405048004050f42c2c0707400c44802401e0240003810398400c00603c1c2c0a5030240308102e540d248092000391501c00d8410310340c0c03100d540a11030b010100f8140300550381115000011500c400800541c081d040186900c0d000f0031002d1035036004143c00c0740440781c62a440d88207500307c8a1a0483c04810143d07400b09215220004100b080b030745100e24407401d84d11444078880c40d00410415410350004589500c540c000944182030340c0074068100b07034000c582d5000d0740c3c0e60014100400d014a0b00b05000c42c45140103442c1490b4540310741c100c9200d410811a09113280c03207844516001e4842c0d01c61405882c0c1c61205654110f03035040440c01c0c024814210714101c41040e296103240c80b807612005051001c00800042500b1000d001040032a1648078010403042c001c60001660b41c120786080104032201c050b105050040400030b040c4e019142c1400c0c480c5181d0b0420fa00202a90f140e0001a01d010750580700102490300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 191108444 1250 191107194 191107201
    0x170601051005070501090b060a0f0e06190807030b071b03090306360512120411120a0303060f120b0414010b100207060825031104050a03110a060e01080403030c05040e 73
    0x920311f511400381c9412a04410000c2c5ea50003802c008500b103015944009034039a001c80d883c0d2801444020180300e00c02202088299103510542c10a040c561040e900d034000f09080087c020b82c09100b05113000c5040305509030504007030710300078007000d5180002131015643d40034415200c0000c003500703840401440c0d19208480c021004401d00d185a40e201110140320b45030034100e1801b1000709840c0c920200003420300007503840c3d031900c3d050300c60800461600252202d0b00110f014105000020031180a924086251464018001c0904a0b40d034003011402d4180001500041c03843c400045c1c00c42d82100d013040081e01c028110302e0040109443c1158000c046c04949240240c0220310203003210026110046580d84108011811180d6080c0d18081d815000d212250050302031b90004cc903902000b030042e41000d03180c00100d28080020f8005440c03220b4031403020205454101c00c001c0180c441850054518503180001924406010700010b0505440341381011000b0703c610140c0e03009050b2001801d65070309 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 191109694 1250 191108444 191108453
    0x922060b040315140408090d060501090b1f0f03020c1c0c1104050717040501060e190e03040605040b0d0f0203040f030e0a05010203041e05041d0717060105100507050109 74
    0x280a4441200d4401c501c19103014120060300c5408680130000080c01e40c00d031354581c0c03960119030240c02c0590340400301444503000f080c9180325070341c064180a2000200c02c11102d040002410040d0703c4546590750001940504640c00003884189459900380541c94032030100c400307802d01d0b0700c040030f070020002e1010881c080d40f42d00c420005241d50103100c645c2014070305c3c0428001a01d10855905010400300c4d12207440030f80004540755406401400000342058036003420721600d410981e11036289039506080d07110308030001c0c03107250b0070700c65072000542c603003440e044015149002c6c41c401c0c10220380f004544480f02241a4016288010100340110b5980c501403804c1d4800440f850000c0d030000300190507004507801c06807001c00655405070020360506140c501540390070104050f10580d610103082c0e00203480d4581d40108a107401e040d000c40401c05048608451a0440d1684105580d01040800040342c102c045103480c11f56400b501d154440104d19032080c4d54600c1460b44c020603a42ca011303103c50511 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 191110944 1250 191109694 191109697
    0x50d020912190b0a0203100b07020301090c060513080c0307092a030f23060913020607080d20040509040609080d060501020111070b0117250e0601030903050922060b 72
    0x6440383c0c21005940d244d6040d82002c1b400229452440e14046d054280700c40714028000d05041d83c8000e00106d00c00c2100e80d03410919240560040000c50008079480f0b21302c000382d00d194400740000d540180340814070000001e80d01d8506100300305070503541d0b40410101c240001884594241c501c55000c0388003025090080081807422050f99101e8074040d000d541250050700c50801c0d880a1040d50039407a1a85030802050070009001241c0241c1381889410040c1c0303903180540000c074021100c0341e48414020390b82d24140c400d0811030503800e0b049d004926840360a18410337203003554002d41c0c28001c035983c0d40c90710030014030b080301001c0c040d07503804690b0a483e0400f0340c03c414240c42003030f4000e0040e80c1c004c51030303d08a40250f0764001d10300c050050043c07082090b480d4400324024458000c56428030a80b80350342426640c0529603050341c001c452010f0000c01c0781442c180c0c0d00241c00b07103800c020140c20790300c0c010110f00503810f015110381c40c0c2c0c2d28038200000360f013000004000d0903280200030017956070641c440c99 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 191112194 1250 191110944 191110993
    0xb0c161a070e04020a0e012a140601080604050a14150103050c0f090c27091311030604020d03031d0f010c080a0908030103240f0614030d050d020912 65
    0x1e03142c0440e14100e030525000f07545420500780c44501d003014501005461801d045070860b0820704c81c1a450070b9221340c0400618031224001c0c01c40c042101c040040c800c0c00c150050700304522a07801403050100049000034800d50554000814000c100700051005052443c40002d84d003203485406c002000f0b00901080714080707090115000003a0003140d40c181b1040351030480f190146c00400340001e031000781c03070b10320000401d103c0000440360600000000440e260710581d44c45e14039040d6000200d081007141c40c0040c0c0341d040210000c0c10740e0701d001d0f80040c54202099100030101500c0e8a055050804034900501400c0e8040080c0d030714034481300d40c4480c02000c1c3c4100000000e04118040342c0307031000920880710340c02d07048840a480c5a0843d00c904180300030b85c020101019445600d000035100107441140c000b00c01c40b65010a80c1e9180044075a462186111402c0c0b0a0b0845000181090341200441c0c541c501d1501d0050780750300c000b100041000d03c5003042c03030041e4019000c03207502c81c16005c030751480d4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 191113444 1250 191112194 191112197
    0x161e020a14091f0603180c0e0402090705090d02040c170705180d020d08090109031403090414190c140d0b15040602030a050d0e01021602030105070302070b0c161a07 72
    0x740f5510804000c01c6074860b40781c0e44101c264404000e10069100350007402c01c100d43c1602007524258070342d9a40c920300340c0d103a00180414200205120031450044030417900a02c0c01e1618a00301210080080d03e1250030140081c4201d0713032241c1c010701183c002c2c2107030249039020f91412041450301100c007800541c0514540b907082ca8262000c08542d19200b6a02001d40d5005000c280d07107121aa03031050f00942c010f000507414000c0b50030b400030000d4440138020802c00b4920000e1902e90f4847d0041c401a030f505038081c4210300c401d4600700244c60360804541c480200c0045c901055600c8005130035a585400a41007081c801000642100041c1007034020001084042c0c0e042c00c0c15043c20440c3d006680038a0088800503002000a0301100348182c0140150408c0c0b20390000c1c540c008080c1e05822030b07001c1c400b00140c1e1604540c519003075150a1040c0c6920015038202540390807110707541e041800c48014685d015290010950941681c40035119080f0b6903403100310708440c1c442414601103001c0f01100c01d02c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 191114694 1250 191113444 191113459
    0x120a020310140a0905070e07030c02010b01050a08040213180309031b08150a02130303020109030306170a02060c250807150e090402011806030f05010803161e020a14 72
    0x808074038141c481c4024105031046480c00d81d4851007109009848228410f0300d03103121b48140821440540c44c401c42c0241f10507140041c0041030f0210190070345000708001418840e042c8483c1c81c2c4580c101ca0415485070381110b00504002007499180c00501191800302090054650204d0030035401590503c142c2e8010b400300314146c45440710151200900d070240c240b16411002460300620703139100369a81c214003c484058184815028480041f81c4241c3c13080c0c0040c0c2d1500e051109041d01032007547e01510241c0e00c0203040401c400c10b2039a440010101c028041c020001d400c5110580c10305c41040c0702e04407001800782c6940d40805903045410f4500076004c80b402543c400041c010205014001c840d9501d80b50b031a1a08002c0e400c002d203184009100b64180240782200c0081c84002e11241000b50041d9280060100c1d00c481c025000c9a4050f04010300b40e5204003d8080401824804500481e500c0003048141029104100740703542205600290000d0300e03124085200c18014500c05012403041e9030381e0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 191115944 1250 191114694 191114713
    0xa0302090f0d1a04030903080f031515160302010f1a031b010f030c1209060501061b0b0a021b03030c120601020a030e011b1e05010608060f010b03040c05120a0203 71
    0x6034a00c560400400303078003a5144003e942c80300b00402c503070720074040d0070549400c40d503a80311a0822341c4515401c9101080c00410803201d04001c20251643e414192242d018100045400000f107204009042c0744c010701d01010501014400d40081a07008502c46050128a51580d802d02c045040201014400c0c0191a24400c0e9265244e048141101d01603682c2c8002c400c2601e8268020040140000100319204803001481c078801d018442c2c40d20701c56000061250701d080001089980071100700b1002c400024101400304401300310141e04121039120050b507070110004080310700300c1000700c0000c0030f02000c810041212000c0d0081c2401c4082901e05140d5580c0743c1c401241c846d0b0088000801240c440e1820750140c1d40b080c401c42710111101e041c5503d50100c02c1c1c6500f0342910003004420f83c804465650700c410401e080c010340700100000e400030009030134021185545940140250041c00d48080001400e105114600c80001c020103454200b8841422011980b25110200140c1c0640310340080d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 191117194 1250 191115944 191115949
    0xd0e0d050304080409050402010e090702060103120e01050f030901180f11150a0f11010f09111801090903090e010b030a06050f0105070803040503040323010507030513020105090d080a0302090f 84
    0x200c92080382d2000e00c16244c907080880a0004120243c820780c104011403c6203034103510f44240c41801024140c008041a6240d49028411101c2085c8458200002000da820a59800c941903400c41c0c2082441d079910381d554040c4030384c01002c0803490803130814900142c2c0c4c41401078100b140385420b8005d00c031311000c0b10f006a0600c40110304018001510320b104015044426100d041c807240d00740e5075803400755a40840c0340c3e035003825140b540582c513040c41e9a8050391400c110b1203050b0050b082c0c00071303104003020a80d2042c041250150502c030b00d00750142c68000b020101445104002c010f40f4910580e4011541c42c0c0e0100a0581c00803030308903401c5868190042020f1801007041d1042e104160b41e0149404501d6844000e076400c0034200701c2d001c1c0f009100120014030340300c0d0a5034941e0140c551141d04280d20701007107404d490340076000c0001c4c54a42030178481c00e00c3d61302c4402d010440e020708103140e03030b4103140780031a4101e2100c540207400b0788404034030544a558160010404610211075100c20740c44003104 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 191118444 1250 191117194 191117197
    0x80105060a0f05100c1b0504050105090903070b070216140102010c020c0901091d1203220f080702131109030f07081e030f0301030302242a0f0d0e0d05 66
    0x148035090310041402c010038644030041544403515031601d40c1807a41c250380c40240703141b440c500202a00c0c1d6520001d11541c24688200c5005041c1100c10918a0803c8810a0f449104902e4060654110320b400031300c01c00e000304000490b00c454501c10380601a91a0040034000041840050042d4205080c1c0d81e180e91001800d0138502c0802403240c4816460444090002c1010400740c207030341c5545030340610340701c1014000050303c48000da51040d03403440c1c510170303d1040c5001c810801100501740000c01d00440d6001c0a150301442e8000005995465140001140400c00054802403e401c245402d10406032070170150518079010303030445003040503442601d512a90940100c0354598003c00c4405000303442c95810801814008083d40e00d0308000403503858031940240c00507800b5070f000c80a03410400e001c080c00c81860250b50740700240b60b030420036250b83d03440c991840b10480c9010b01140044400042d00700700c400180d0341d050580e90f2141210080006032440480070403c60003803200e505070b020300510 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 191119694 1250 191118444 191118449
    0x421020c0a1e060f030b0a0902030603240604020a030902130b01020f030406050d020a03060b0c03040501080606070503030f06040617060a060602010c0804080a02120d200a0e0d110603040804080105060a 88
    0x20200c240442c01d2940031515141c100b0f0303025040548400040301547c0351841402c02501c01083c2c0943e580ca40307c010315140840400c128000d2410418413080c0d07042503812165001701c1c08440169407800d9240341100034040244000e507101c008101001d0701040b541e0301400804200381c0035540c000d1001c442054490140b8842c80011030740c00c0014401d10706407540103020040d07003401c0002e84243c6076807403c807054200e201481450f03800014180034a680010040340d0086c0d04903805440d050b002e0391099102c0c040940a171002c615011b02094480e951600020084c02c1c4003280c10b40c1d41a4640342c0a551a8410b0b10009502d502e0010b0101c0d6580c410700a40540039101d446000c030580b03a03940c4008143c3e0100e15144c0860240c01c107032a405a481100820604950400c0402c15461041e141001c1c8105403407a2040c8010411000d2a015004010071039440360480e00d041100e40035042114030341c082501e00342e60141000081004100b8080c02500940c1c03205c10080020340d0b5001e05114500c140d90 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 191120944 1250 191119694 191119739
    0xe04050705091e0619080607030e0115050118030b1914040302190c03060507050301060f0c03022104080708061f0303080105060d020903060103241e050421020c0a 71
    0xf02c0100031401c6240700d8458100c04050001340d80706900c0c920055942100da0801e500c0d80e0050320610007a20303854050f1180315405040200711482d003200440d9004180c030700c20241400744488828a0546140d65200c0c010b41c0c21000d910024075149004000160700440e034510402d00c3c14003601c41215201e888140f180b58540c005200e1046003482e0002014915582251841c0e9441d00110004044d4003070300340038175160b80b2030316101c0d410b20001501340200ea044503010080c04414000219030300042140c0003032104801c5001e050100c1440100c540300da504244d64a01c01c040d000100f511000807964860819001a213904031042c01541040c0180c46c4005030014641c01c0044c400c5107089001071120000e10440140390540d000e0110381024001d90098030f0920191100301c0d4500306e50003403806560301095040211220440400d6121580300103410b04099854000a042000380561449002d61005000002c49020200203655642908103540038021036440010b10455141e4240c9041c10708 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 191122194 1250 191120944 191120971
    0xa060b03060f090c3604020309061501020115080a110a080a03082e0302030105181b0301021e040305070909020d1b0b0409050a05090304030c03110301090206040e0405070509 76
    0x1201000041c803400390011540403020800400c014402480382c013018000c017030110700404401800d40d00a5904a00094082d034010401c1102c91080419401e0348411800b880000c0074001c0e0004038010609a41400e2800e103400c0c0d400f0580c5031000602c0c10b080c510516490329003c500d00b091101202d243d00c5040002c0d8400d82e070290019016001441d03101d94200791000c2844000c21101c15461503000000402e4000e500061055050a0060360340c0030189408a40d002d2903e005502d54540b40000321480351000001c0d0600301d80d80a4049400318020190000c180b00700c0c5004c400a2a40544070844092054110000308614a4040d00c920320fa0020b0a000340100030b83c0395020310300d04440c0603000340070ba03283d008134146d0103440140c80500201a800a0140391030000a4100e6102030481801903005000820020382c58021038010b81340d00203d0780388003e0145011a0250070780010080d4416008200800ca22144000c0349102c1c0f80204121001c03165180184100b0031415600240e48101 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 191123444 1250 191122194 191122219
    0x3060a020c03160f0819020d0513060507050a05060f160903032c0a060309030216050a061805030106030f030e010309110d020a170a0c060504051e0d1205030a060b0306 73
    0xf007060040301c0c090f000d5608140090301ca990f81200320362003c0301e5420000c0780301d00d0960110f07904100d0a00c004110303003001403525010811411941010348616010484001040c0041000030701c842c40280780d02a04448070341c106881c00e4400842c0841344c4240645220701205601c3d480b45010108036a050348804007505804500900355070034940001d584814103021070801900c0d5208400010300c00c660b00055400c0c02c61030004e048c42c01c001c00d00004030b0a91b613818031082d038444404000f1903c8a0505014a044410010380c000702e503070b8003281c0d0552a040780003040c0940203141100741403290352880c20f0150b12400541c00c031444e124010300640d400f0009400305003803c010000c40c2600040a594045640e54502e420740900302c0e4000386241c000c8043d180070044c0741c04881c805042e541c141039051a04001c085602303001c028500d4076800300072514441480d2201c060105105400003075070000f5409441e0081c10300d52040c0c682411492401c200000c1001500059902810008010219682c0c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 191124694 1250 191123444 191123467
    0x60114010c050f060708060f0a030b0708100317030708010602030c0606040e0c0324060607050606010302091f08160207050303041e0e0112050705090603210903070902040503060a020c03 81
    0x740310042190684154080d80b500c0c0c010402c840d6100e00015910380200e40fa186041c1310180c42d003494998066145a00c040c00000d841007125503000b40e1310300c2c0c0300d04596a0f0f1001800c00207059880506074800350500d019450050740c0082d0701c540c2c401d841e203161a903a11030301281d50b4031603115030150719001300340030481520b85604010710340150030048622400100c00024141154000d14070745001c904280c188c00100714480d02680000304590080c1021350781c3c0c861a80742d44000b03248504040d800698034225030b8a5002406000441180b0802030080c0100042e00c2c1a1056030b403d40d41491300b450140480c1d10001c0c1c041c0c16034034043d014500f0310340341a48000b00c443c9a85000c020307920400001158409180d040d2078001c00c10001308003500342031818190f00f0240c2d507400c114010f080e80420098143c030700181c60280c020043c0c80c0c10780308030001e5081e81c1e42c0340507042d607440c1e042c001c03d0400101e41841341c01405c10b0f28400c07010b84205d81c41d41c01c2600200d128400d44c01c08107070002d1207810341c5030f03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 191125944 1250 191124694 191124707
    0x209060f10110f070f1805010602060a09080403080c01050708010f1208070503040905191505150c010b060a020a1403070b0403050309030705030d061401080613020705010e060114100206011401 84
    0x21070501e4201c98001030350f07090641c18821660410182c0d007402c41d6040100c14050845d0340321081000b003040205504000b0004e4940d00300429442d40c10ba200d4206d0000c0111030b804403030046400142e00313612104034071078143c0a45806d50368a80020310030800401d410f00d00341c5604040b602c80e04950400380146540e501c005800c00c6070f00341d64038002840700003240c15081c040c940c0303d500c880c40540c0d1106841040300c422a002c2d02040c0ca0f808800e0b10040c00b4603150000352a03074403d40c050000303481e4a4044400c03409071007003800054101e00082598569244c0000f0b40c800f005110305100c00300034003010b509a07500d0141a4000d0710040000e4003240119000d04001c2d500142c5000640e4039003215034948514607840580800210380d502c5001308100314040300340c90190b6109203048407081c02c100c0d000402044054241c84180e0381d0006001d41084025404070041206a13425141d031903070b444152054211032600c4d1580510403807484003200310300c089011070603610100001c0420f11003020044840 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 191127194 1250 191125944 191125967
    0x3020924220e030c0d140409020705031e0306150f0306060a090305071e080102131a160c060207060f020613080708070b0712060605070605070302120c0301030209060f10 74
    0x26116100d07840c0c0d962100d8024200c081d0342150040d95560810a0601e20780042101010100321b205804c003446201c114040300c0889004110150310b440281c00c08900b18429000c881a00010303401c0000c914000c0301000c0c5100b004101c81c280e0a14003942d03c4a074492045000201006404200151840c40d0980c0a000315560030703d02a4182510b96403810703d4000c080e0000f0007004803021034002014029400314001d0b107480030081d401c0018144500a03007484500450303421070b00d0185038441105161095441d9038078000d04210700c180303041c10f241c2002d41840c001c000040c0103922010401c140106e00b8625481a250b0007801280d840c641c020b00914040f800445004900300032441c04114034038040d203c10742c0100301c076903c0e906000002a021007803401c030144c03800f8113141c0d003041241e411106a414540e00850007140c0c0f5a00c048c02100244a41c0040340382120820041c805900940c60246040c2c86c800d03500c008540e11914100100d41c4007070807503194000302c000dd84e01c40c4c00e4851003140d07a2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 191128444 1250 191127194 191127229
    0x5040e100e03040b070302250e0f04030e0303070303060519210201020102210f01150c080315040e07030303050c07110609130501081518070e13080703080103020924 72
    0x81940b509103000d010f80c017001040e001603210002901001d142d85040d0107030040019814090035241514465281030010030006c41804402c0004060501603084001804c100900307aa69852082c81c01900a150b28000d450154041204240550710900700520954443c0c050b2111380c004522115686164102000c070304554083c0101c005004081c0c401e9045601c802581c034007545003001d81c0304d412000507841072100101d2007544461140d0060111800a42c0020409a0780e0f41c510066400d920390480b811a00146494102281c806000c190385e0141d034403c3d6014400d40e1104000704107035000b1410058911224090380c5d103401c3c60010020079180002170a044c840703034108622802207a400f68401e010582110151502d0303100a21003c561000825404014001c1e258078015980c9170746004074003000036110042101d190b010f41400c16026489000b10f9035541d078030319000341005800e22080f8060301d0804041003003540e00103c40c02c0800c01c1503019101d4089018100880758603241202c01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 191129694 1250 191128444 191128447
    0x5061e0403062903010603170703020a0b070c1e0317060d0f120e010201090c03140709020706060f051c0b10170607021510050105091302030a051005040e100e03 70
    0x40002e0490007600c41808030380a2164042c1c010510308185201c3c80086a480790349003c0083c000030f4045eaa880a04005c80280c603a01d82080c1e25040e07207880c074407a0014003540a00e1041009466000c0384907541c0034803807030608240784074a4441c0035a0174210a402000b29141c1c459180700072456007100340d44000001c01d202c580f00d4098840c0050301290100a4401c607907d08000c5000580003413061400050a01c02002411a95110107030008107030b0000411120954802c00001d03401040034401505081400b10764035501c034948040204a02e10076200031859440f00042e1902c0d240b0032144211454002440700d02004d40c0d540724000c0402031a1465101c0802004611514280d0010072000e041400600e07075070030007080107440c04a07240c2e1041c141c2c804020410240501000000c1c04454003801c00700c1e10313550103900044c42140c0d08003d00411600c080304000c1c803407440e900050b00403011030704032808880d00c4905101c00d641a15002041560041d00902c1114a081d400b03c1c01e0001c00400b681d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 191130944 1250 191129694 191129699
    0x515120d260a0903020c030706140307050903060f0609010501050309100e01060b0a11280b04050c10031a0303040b1c02040302030601270b09060103020d150803071a0105061e04 77
    0x1c065209a40041070740790380d9018081016010004150244c0f8110300400b034161402c0e000408450341a41e441c910040044013049020b0701403000e5414480c801416104180703440044080c45a604603011445045000000611540600212800780031700c88050481c00b0301c42c04444015000f0880c8120ba01c1d03607964000603103401c800f009000c00c05480e644d002c0c5501c070801482450060940c0c240300540400b030501c0820980d10341e920380540c40d4042d01f88a11542c1e60708201e400c01d10080312840d042807a10f40c42104159056201014501c8078800100c254002c0d00f090556900441c082c058a5003420010303150b860400700f00741002e0714040070b0054a8542c4075801710307081c0031003a8051641040d540201020300c0703c0c544044040c003800174008200800b20800014a201740c081d00307060600d41c0c00a0500505501d54010484000103002d0000e50780e599138642076582d41c017444003a20081d81000302c031000349404030b44440c12280001c241508160306400246030034215101d0542c2c4412040100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 191132194 1250 191130944 191131007
    0x27060c090b0409020a030501080601060e01080901060914040b09060403200c031b09130222021b030927040b070504080709061502010507020a11060403080705010515120d 74
    0x40003c1c00d05140c01586035800490054161071060b00030fa80e003500620018455258440c1219071b096509182c00d110544030f5406c054010400c81d00038600d85420300d000408025130003d5040d0080d0f02c1a41c400100740d69107003a041e120300c000c2d10014002102409101c10f48440c0c840105001800c035002d6803900c10701800000c0c94088008214054000ea404c1001200d01c0d008000642c4000d40002011146106600246c84a01c2e102120f61511908201c0c0340080c6105505440081c020340d480d0703001c46140e0796542641c980040c4105c034820008641e001a000c003800c28529242001100021125161551800c40300c0f0002010b031020824140301c00500244100311150042c01a42c40c001201400e1003527894090428082d442e00356030511041c800340640c00540058a150000d401901c04154240001d0f105d20981d40701924071135001c80c806007071100640c03069000380050140480c82c01003010a1004c00102058840700302d0b0407514040b41c149025184881c20122008104511001807211 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 191133444 1250 191132194 191132197
    0x171b0f03100314030a1403100305010e0a120e0306241807090608070815010210020c03030a1505100f0309060e0c090c04150509060c030307080a27060c090b 68
    0x2003840c1580030707040c001c00501c60f00e526072820242030000a13501e000c0d507101001c0c2188075040380403a481000000066601440c64071580c000d5035000d002441003c8145207440d076035a00801c01518041c01d5400154481ca01445424a80240c050090f00c8660b0b04c2c2d1200e0190741e060049449000c1c0d8904a84510580e40d220701d4200303511001c0400c1505090a4800600d8918150407940a000a50051002035500800c01941c045812103180014204000040b820700d00b0001b00d0400440c0045404040c008010001d540f05015800042000c4444901000c1c08101c031031181c2600315841c0071028150b58401c240500301d4200a00300801c2c414415912135084a041a65241c0c1c15005018a10380b14503220060a401110307606c015810030b03082401140c204000c42401c5414400b001814003281e403108000e603051841d00c0303420749440e490305490290280400320b510545491801e60004144464418401400111a102d600400566070b075098000e052103e4220b00707110500c2000074030702820710f0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 191134694 1250 191133444 191133451
    0x15080411040e0f0705040b010c110a091b0e0a05360f04111806120109050d0503061305010e0705090409020405272b051201030c0f0501171b0f03 63
    0xb00a00202d40494800350070400d04d83c20941c031031400e11801c0200760380d0000b07156401701e030020240c030004c50155002031002e20071a80010441c1d810b20544107001e600c0d86005c0395610980b0740390792103102c001d0b2040100b80c800f00d0103150f501504108445010022041841023020014505420f03841010303000c40310b0f0954111042040740c000c0000704800c00000b07184842000e10b0654200f24030003401041208a1032000304401d00a031002e001d41a401d0409400185210340c0101c1912031002007000c0050042e4000c8823028011040380c0d641c0310b591540c902c610350481c3d284002d0103000e0348611404030303042d0b4028203041d44e11a4640b444403000d650b071031244501405401000e500c0010f421840c209106442000c41403450b000380c006003520541d015071100382c1c200042e444c0380c00c0c0042c841d41a80c0b103004910b01031540e4a2544008001c00c10503442d10401e4075031050300a02c05c0f0b580c5100441c0c5086640424090318001000843d1811982010030510000703200110b600344846510100300540084 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 191135944 1250 191134694 191134721
    0x50312010302040b0d0f03030c050919080c0312040506070303020906030f1012020306040803130c0e07080c0301060507020f030709020d050615070803070f02070302090103080712091508041104 84
    0x10001042189040d01c1801203480c019640c180003540b06850381146501c106d1000307000c0c1500c0d21110b100880c420011203103904002405502d00b40c840721b41c0521103440c540a000400c0c030603850740e03d0481c075000400c1c01c0416280c01c0801e180a042406001541d000302a080b018180c00b0301c4555000e9031103070003840c03040c041510505100d01c0c1c404040e018480c0a9403003500e410044ca1a0f0700c002d82c6011884991094101803026540e0300d507404d2a400c2d90200c00c8002d0183c0307600520104d245e408032a010741c0620400d546040c090f0f1109410001c03548800c0c420503000c640c08224503001410200c01000030614010306943d1800da95542030410399000030418182d040d0384108200f103500c1d100354065942d40a440c02141030846541e80e0340e0035844083e101a00b40010041000c5080d40300f0800c0c1005180c2c041c090149a594030700c2c1c441344a411040044400310007031450301d140f6500c2039502c201283c403407041108200076100c000742c44100300034005070f440031061035407401541c541e8082d880445a00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 191137194 1250 191135944 191135977
    0x260408010c0f03060b0a0c210c030810051810030503130504150b1605010b040c0309060b0d050c10050c010e031e0708031501051902071a0306090a0203130503 69
    0x4070300c00a215444940d1001d0034189008410300140e10000142d80b140409820441000031403410902140391103101e41811500401444c4540c2c1a800b00304034210900c6600c428500b52100100511184080e02545d40c0000406000c2891038800c000c0707240c0c102d0f079001e949003841ca4481d1201ca0540d03000554070211a03414080070810350500703204880008035000024020f40342030000c0c40c9080c0c402c0300d1110403d00342c1000c012003844002c2d4010700075100010001c11a0204244000d0050241c100084d1000d03440d05100070b0b141d0420010880c46a503000001c0d04800e201d250070012880041485001007280510031180484000d115050010407240d000716103454114140319600b0b80d41d41041c0b00c9051040c0030200c001500f0740c0607650040710303400841d41829240c0380100c616008c2c00d0351b0030f110000c5041700c80181c1c0390041004800d980c443c2c80003961240800a26203a9403000f038a489411101200002e0400c0c50294080c503008104040b440382c0312000c0c0e0b290a85540c114024904e54041c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 191138444 1250 191137194 191137211
    0x140706021b03030304081b030f0409050109051302030607050a110a1110091202131e15060e0603060402090114030405070608131a060102120c010e190c0326040801 71
    0x10020340c1060102040b4015032552500e91307038402203800307080680100c201d000c143c3d42c6d16426090003669a0100545407050311a03076070342841d401a00e000e106d210491840d06e404104034845883c80d04504580160041510b9114a001254640e10a03501036041107a400340c2c1d0380103030070148410b4000602071140a0310600c3c40b03a041001300b0380e4440b014018441340a00030040d0f00d001c0c10140c15443d404503098490100542031400c02750240e09442080d07412134550399104110b15a010b00801c1c5402da111b2064a038031894161401d21100340d042354803100501c0015014070300b0390010520440d043c500020031a000140c1c0c45500d400035602194280c0108009210603580042c039164031001c0c2444c10a0b071001c041d00c901e071341c0c8000080c85101038101f101c00140e00c0d074002c00035081c0761180d400c40700c1e54500202031014002d05a1102c12407190040404030b510308ac02000703044440c0340c3c10240c03542c50685540e69100741005d16041010001d02031003201d0028564450180004018110022070401e2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 191139694 1250 191138444 191138473
    0x31e170a030e100b10050f0f030f040c06020d05040e0606070c27090201051218070b0c06010803092b05010f0b031504030923030703081201060306080a030c14070602 72
    0x183c1c0846a040040c54451803150564915040080f265590f05000ea510740662222000d648110030584055407000801d00c030b104080c1605441c40b45003e91204401d0315143d0008a8854000180b4a4000f0707a09000600c49501024803031030308080000d012500e0000c41d5640c00e201c0002c03a07070280b40f407100110806400000b9407503c00c025826004000c200780042d031b0740040c06134000c0351000d409489011000880315174002d05481c814a515000301d40c078030b07a80e600000600d980440a145000d0041400010301d03104000309607000710714000c0039201900f080d8211441c1c3c41c852120030340001c49405a2501c085203003842418180e011100020130403c04120905260078260384034050120702001c2040080b03940721102c50240e0b04a8035403410900d441c010554500d2440310b0030b0342e902d030003044d60001c01c0080c074070300502d4014419860804280c0e030b5a2401c4c0c04031102882801d00300d410016422000a00c54000e101005101d407540b8410000d107401c4861030005140c12400150740460070384000d80 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 191140944 1250 191139694 191139703
    0x40303050f09070b04090b010509090408030a0c0201110406051e0a0504030b0606031605031305030316030509030a1b0f140d0e03010b180402010c0206030a0222031e170a030e 76
    0x18401002003011600c1c1090113941c0f84100d00ca20500700c1d0f07441020000720f80c0f00760101c2c0c00d050002490b210842c2424188480140e00640b800100d4900d400fa60b441da4a0043c092868800c0d8190300d00c500307003803030079405860550008401d10f10000350001505001c16072407029100c144555603800303441d0350940c43c200c03200c1000a884030f4030806040c01081112501104c60031140102860165103075211310820515820400500510901000c410448480f800b060b00c07403540c8686980c1406152503e0407140c0c0c50b0310030100440300190080703040221805003002c7e21034000f231040c40310703401c4011140c48242004021403400c1c2403a4100310310780800164806116100020204c000b005500241d10015803c9869540d012000102c0301000400356802206260b07041030b0050002c950f03034a00403034101c0003584109031103408049241441a24034040e60404000c0d254003040c805000610914100d01c400c4c480d40040380da0b1524000445400d501240181000040b00d44000c101081450301c25420b1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 191142194 1250 191140944 191140951
    0x309050d050d1d10020a05100516111203090f01150b0702040e15040302031b0a030c080d090c0f080c04150b0d0f090c060f0309050601061d0405040303050f 68
    0x200c00a2103018046800819401c1c01c0c00c5250074540020400e04140c04650a504100a540680d000c00b40f11130b09600400c4094103144660b064a1040c0c54444004e011500c1c1610b03c4500311510151580381103000d02b82c1401c4001003e0220b4a4610440c0381007181607000701c840300702d42e810070f101c0313103201e65024001c81c50407c0040385403015150810200320100c3c01440c9029200d00c0d01c0d0098010a10420320040d460104010300c103c0f840d00d05428042d6a80d4001c1008480c801c0740d000301002451300104175180e24035130542c0c0f11801e81c241a156200260841341128040507502c3c1e2000000500c5007807000004d0000b461181001860301c40581d0400034800a06070089040070041c402c029180050b45059502180f0382a4403140d88544500c028285113000c066528582820b1100707000c40241a802190180d41c1c4050481c500c00e0400c40c1944d50180000740380340d02c02401448280d0081d02c00150000151502001c0c041001c0e0000d41a00c100f9101035000c45d5076141444000d100556243c0e51 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 191143444 1250 191142194 191142199
    0x5030123301507030f060302040f02070c1517070e0306090714030a02060a0503040c1d060a06050a0e100210050c0a0806010203070308010605090d0206071a06030a0b060d081312030905 80
    0x200110440c110142d49002040c182c105540c40048003400d0301d49034030030000755401030070403c000403094079114002e61000300300307540601402d10000384d8440d00004108420f046552602c0010500001c03850b0190005031200c1c00b48410761594580701e84040001d107210300490070007405203500e4980d059400c04c102c1c9031100d000350800c191550241e2a580d0442c0c01c484940c0c03808990341d40d40da00b40044140d20326086121882c181156601480c0780704002c0a001d0542103666046e1a50b5440d01500c1d00e1250701c0c484000309100780700307403d20792520b1300d0182c118000d02e005580e200160044c10204883c1e040b5100720703017280086140340101b58088aa0307584400280011864a900c1d40c6001d405102c05129640c02c00800048003411522502c526400090f0701610b0380ea25101c2d14504606d041c0607165105140380705100010300d2500c0d00280141e00160490800754040d2070ba1014010400003201e01500c015008000c960321101e4003140306402030500a00c198000340c1640340082c070405d2280d1140d803 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 191144694 1250 191143444 191143453
    0x21009020d02030102310e040f0c08061f051c150e0f0703050706090e1f050607030806040507030516121104030b180102040303090b1b03030c07210503012330 69
    0x100c0031607a50700448c0c009030081041007c0f809146000000701d085500600583d009100c2403110402640101640243c9520321046c9225200c07018040385404000350391200d130103446e0824000c0b40310558010340c5801d148001058501001c00384a00c1e03d21001c21010782c50780000000c1052103414003070240505070f60b145c00c1060516083c0a0002c5004c0680a65000d030403e15540c003401c0c0b8420512002803901810302c40c0c1340c4c40b050030090410882180c4c140c2c0120304020014031058424821035104480183d4068001603179a9400c031200c152500c24501010b6907202503c0b038585008001e440207510071560003455141000842d10900364200e4000142c5c1c1c010300090002070381082048055800040502d505c86c403a468469007400150700c85201c40d408004103000c280c3c03a40800400c443c40c0154a945071000008018614944c02038508900088050005100c050700300c40c000d0340c0100010003121400c0181000048000614410b4217031200c1117164040d200d1111060445021480080a030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 191145944 1250 191144694 191144699
    0x11030604081b0109020319110103060b0d0b011b080a0f020d09030308060616110a062c01050d02040f050f040c0801050613080f0f1606021009020d0203010231 69
    0x719864002e648000410082e40c0300d01203000e140c250301c4268031940080844036503d003500c1d03180784030400e058425964944124035021b260750107401020121400038100301d20f030807403c542c03050040c40c400a195041040d0002846081122101c21a5030030f409040110349d04d0b00b0f510005481484400c0c20ba8040d50001b080310144c403900f00407180226074260078003481175580d000000701544201c2500d4003000c40c503c0745010a208100c544c03400f01d410199021105c458540b4000e880b4001c5504185810b41107000010885580180030745a02103410b062150034404076035007139000d03600320750051030071103007104030400c400d01d0300b203d00302d10082c0191020410041c40403401068903805000c1c141c000e080c0001d1540b105040c15040c038000703080740c2040d0707262040e036144100d40b251500700c00c914041c4214461803001c410411480021125140c008041c191810341102015000d00305090740d202c82d080c852840503072000c3c0024158042c21a40350401c071800c4105910408011380d100c215450b1410303009 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 191147194 1250 191145944 191145953
    0xb0f0a1b1e0602040909060b0a0b040503250f0b1206010e100f051b0a23060f0603031c140a0519091b0e010e0114010906050a0309080f0711030604 64
    0x141c071012522a000305481c0c0a42408006445a98482e000c01860000b801060141e180d00202d0044000c5a10380080c90381c0c0d8100880c24002ca02070903906400141d200c98820902c074a41149480881d41c030304101c10740e20551028441c10b107501c0441c000b8000103c061075040c030640d09a50101c02400e0182e5805580c0c80030442c3e0514658940701407102e40d01c1412031281c09603058070b0554140c04402410b00354004802a201d010847c01102c4a00681c4001948005240020440409154000e041c942d960041c00150320002900017a05400100032044501c0d05521802841130307500500883c0142c076038280102154401004041440e00c0c040600058103401103506008440b60f00b00411003000034205034441311507194501c0c02c0c49034070b140000ba00f605000c180324122580c02d002107a2613030f6101d14000d5800743c019405400103142c000280045400341e00a05001c0c481403800107401640c598034440541d01c04440191251000320303450042040158940c00e9a18040e00541920b003003681e103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 191148444 1250 191147194 191147213
    0x80705070b04020310060803040602010609020f070b13020d062c1902060d060e160309030807050307230d110405033d05040c06030b0916090b0f0a1b 65
    0x410781d0003504041010366030100303c0e4200d800d2154104001850f900d500e80c6a40e9030281c4119000b5508040c000641c4c21031a2081e642d44440002e030b02c91070000300f682e6a511002c0001e102c0003081c1508403140015840d00680103180c60b1207210300091070081704003070040c0302240c0501c0a01140740a00c00c0c0c2e40a0001150551580c2000004083c1ca0b600601c0007a00500910f50302010040c5004000200c01c1c1000740c480d801a4402035040b45d00d808a085c0031801da5850741000380204100002084886108600450303001d0b9151421142c405009031003602844a02c0501c400c1181010455032840c2c80140301d00902c05d000c4d2400d16103414980408241c61fa444850030324401102401c04c42000000713030864240182c0b05c070281c40d490204103019500100703015107058502000c06540800c00c0b03406482042e0002800a00740d603180d40e101d14083d1403030703500c8058050801603403c4001403a490702c0006041182042480f107500c0d20100710b4010440c20f1002c01070390300800c440903010041f503403a20 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 191149694 1250 191148444 191148457
    0xd0506090f061509061c020304110a030804050105070305161b06050a0e040c09030209090a112d0402090a17120a050a11070f090905070e0105010e0f040e0f071401080705 74
    0x400e0303101c1309101c0018078103008045852201e50503941d40002080050390040d40b089208050700059443d00f0401e00104004500004080329000c20042c04503602070f1004c0c00c03581d4841e00e0f107141307015850301501c004404007050495580309541300302004080c80003d0f540c0940030380d2411a0810005001c000d00c15a2950502d500403075440c409414894400c2c1e607142d0165401500c00c024074144410159902c800f001c0c1309036001071039069100c8003480e0088603004c268408480505006030340034040c41d9041c0e907010b0041d81c066030030072400110780c582000e020020205544040718484c0e01d41e4860342001c0348c1c821092800001081542002a08101541d40d00c42c19407500c0303a150384928403402d00d041607076000a11a541c2030034000402c0300703041c0c11440d4040d20079815690740c15903c283c6114555020301483c0c2c04203c40d2070640305581003c110545452070010800700d00d1081c0b11088034100351155020742d01c10741010b04240071001e14129034100a420a1910403d10301c0c0c00c0300c00500500554 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 191150944 1250 191149694 191149729
    0x306170c041806140a0f0605221407020a0b0a0203011203080c0f041710111605031309092f101106160207060e06040e06060f0d0506090f06 61
    0x1007031034010003a415502d02200c1540150308001003190b140140005084c00c6581c111030311b007000c2c1420f000350100e00031203042342c10241440c0024881c2030309070f821183c5960410300101340c0d0342042030b000038240c6e005280920a02c0e005001150a642050107000c1002045054041d004000401c4080e088075420020035070180b07400910f548800030508098803403100c03d11a035040114002c81c0030364500308901504003944044070407021800d035244e019107600031103004503014207006100b000c1c40c6c8821070481d03503440303401601d10b021120003500b00d49c9030640d0445040196180070102c1002441c850591500f920307140c10f60390144150759144451422055054001d0203105040d0300210300454400c805c40c3d00c40700c181c0c2d0061a040c2d104c03034010940d03c2c440100510612a00081b014060700b007156010601900092506040069582c2c2008016000b150406c8007084a03d035400c207940094415079402550100da82d0034802c0c00c0007000c00c03024048121249200d003d0068658940d80402c10782c9a41 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 191152194 1250 191150944 191150951
    0x30c09100e04020d080705010506092404020315030105011e0e01081b010903050609161508010504020f04050d030c060b0618040c03152402010209012304090e010b010306170c04 77
    0x11840420003201d071130700f40246030030070101d2000108041074000e94403c1c4002c0c0c1c3c100384150780344200355a402c2030180d00070314803d074128034000560500e9001590320842c8600207108001070a0302083c01c40e44241d112081c0c0b1101c0840001402c400700c1c01d20002441d87d24041c0c0d00c0395050903802516020038207241419034442249442059008119070002075400c80e05030381c11803802c2600f560310381c4011030140c00302076000803011803605058400a903180361941d841c0c01c080d070300704000c1c070000350b200341101001c0c8002440009080c0e034a850800040c14440e542e0803d01340c0b404e01d0000141c80f0b6043c2c4561090300144040c082100f03a43e90610321100302100c001c6060740c52018150010080c400704441c0d14008500041069150302c04641d0b80e5543c0000020544040084124200d02660740014001044186204412803d403686040c0b400450010f803490182d941c49540c007243d0002202011a94617242000c0456815120740b900900003007a1062a025442a24644402074503852074441e65a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 191153444 1250 191152194 191152201
    0x105040f0e060a05040203040f11030613080f0c2a03060f0601050d0603140114100303050906070302160f0315060b040902160204090b0103170403030c06270809030c09100e 75
    0x80f0051804002c140140c400c40d52428141401581d80001c0c01007500e54602c699a460014140003802622551040c000080002c0c0710340c1d21040264400c4040b01130851041c06220355510090240c01a50403a066000700d100c1c1079030b400c001c98080d403180c060748260030042c200300d541c0100c41016075001c402482d09540d203004004140c0024003941e000546640803e08c42e5034605c2c81c05500a852429070b20041010036544c00d1502c14801d842800020001401404000e2403820010f028145040c42401516003480c2010184191340a8035484040e500103140b5080050050f0b41d0542461071382e51b440280400750401c200c1c0462481103201d520401c6e54005000003020f21004900d00865600a0051000d41d4107801c0640c0845000c2c041520b5482006005c0c002050454046408076503160f21120103580180d211311000f0502031080c074405581402c5030b8070302400a401c86040c02449454082e0711165241d00f814903102c201140310b401071f20030b0000d0100809203d1105811255030501200b07840e034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 191154694 1250 191153444 191153449
    0xf0709180e010f062304020304050304060c1a070507030801090203060102280f15060b0c06070521070908010509030f0d0c21060302011209110d170406030f06050105040f0e06 76
    0x2030080c850501c403501e4020f0200f00240111940060f41780f8800519031032a40c07400c2004220310051710000d10aa00c2088100101409000041e141d1350103440300c10300c980060030b808081c040d022148007000030400240b203070170103802c40001405003501e20000c50442c80c1c8080003030354071042e03544100d001c201d6000b502c040740c2030b000801120145d030103220701050380304138606501000d00818603082100d0900002080c03580320007040d15220b40300e0b88020889a15081400c6d2342c070768408040300b460440340036940301582d03903101d01d132a01551040e941c40014500d0b1000c15400c4800181400d090b40d0010000c00c0c0745083c080050700d2641c3e040d4000040c6c46075001006882102d0194041c0303c4c15001c42e10503801c088031503880030702100d000307807101e084880194440c50700f1034011f94002000e06800805443c268104070240a0285219072040031403044d440c90410056001940000c0009454660041444045004100003402d086c203056080c9401d00030718101c052200d000e07024500240100149055 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 191155944 1250 191154694 191154701
    0xd020a0f061209110f040f0617100e07030303201b060109050912180d030504090c08040201051213020405270d090b0a0909090b010302040c0c08030601120b0301060602060f0709180e01 80
    0x4203040d19040000b00d40d1405d1248143d03d2803180d19600cad01490501003940d03819402411500304010001e4160942140e40a500800d008155000b4040c074034896404141d00741c40050850010708001003105020011060b032501078143c001c1c6141c5c9042c0024400e0007440010300343d100010a0054540f83e40703140340986081124020b440760b1291111840009140c1c001e0010320689003004c40900004600c1c1c2001d444002c1c0c252802070016008104110300e40e586070300c0c025004401c141201c20700d515140c0014080e100141d403660301d4081d0203401c0b10084042e82d0351310030b5102d00c0c0700b002e05013003055140b024201e00510300c9100540710340010380c42103480c420820800603018880e400c00c000022404c10342c105e0348003400224001d910b04881110b61728020810b4820703265000b1300041c550f40d13840b401191800c0c480c801d42511140c6401180d41c86550030301440c4051b003442c0c2e004003494942070040d02c07540c500140c9048240720906c04140081c491180010f80d114202c410042131b01c1d21b0914209005 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 191157194 1250 191155944 191155961
    0xb09030a0209040c0509071b060b03030903070605030916080c09071e0801090e06061011010605150309010605150306011b0b0403080a05150307090b0d020a0f061209110f04 75
    0x40b409a008010401c1100d0f4000380c140c0e070080c0e0f21048241d5640c042600c59443e6074411041d5180c501803100c1c0024234035002550340b020082c040c1ca003800101d5002c0b0340343c40c40756009000858004030030443e0241d810000b0025000016042e194401d2511401c65210000d0308401390280c0080c500164641d40211205404400140c0301c608900c800e4040080c803400c0207000380b200142c148403010740c264100040703050007044000c10310b00d060325080000f552020300110b0440500d54031a04001443d50300c0d282100c3c0c1c005601000749940c0d29051001c00c2c00c488082d08803910440304151148044e10003602035992101c0b0a003852000c4940d031440681ea10410344a00505d40501d42003048101036114a00d01d0140c0441c4906001c15107072000309000b1951250f00e0700b5050782c0b007100c0400110b203094000c00080103015114a0407d00c0c0360700480d940c030185400845084880c00e00400c5001d62000f00c903500d000d17480d03004015402c000c2d547d90b290551340410a521814103030207909115991503110014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 191158444 1250 191157194 191157199
    0x1204051306031e0515150409050c0a0306021801050301300212010905011401080a03080c1905030115031406010c021306080705010e0303040b12090c061303060e010e070b09030a02 78
    0x5103c043c8200701001040483c8220703a00d0007000079410301c881209050b04d00903410350051011800c090000d000041042c50001e803402d01c0744c40340c01401038481c03088880203140110701c09030b81c07030000012101c6288140050705041080c10001082100680c05044080000341c2440715014100064541a18404400041e611032080d03200d40d000341c0415404852041d105200038040b000d05508445800340091058640b0f41c3c010040120019106500e15940103003a600d085080081403000002c1c0c400c0d541040001140000005006012100040e001c0f0340d0b80600d0140700e006d443c400c0c680d111540107003070141482003219102086613181c0c2482031070b040d200034040100940d1244103507980e540c03521542c0d010440064608085003004800c13a0161501d42403007518080ca041c0080d84507150090004d40940240312400c05c141d512800180281080154142842410b50424030204e41c010044090142e1609149145000c00032640100301d40c108100c403030715086580c001c0707403d20303411070b00095 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 191159694 1250 191158444 191158463
    0x1e150e0c130509070c15330f0914091207120512090c100809030403110a08010603080a0923130e0105041a07022a010c061401051002120405130603 64
    0x2c5616804000b50341003074001c900d5440041642070300c140482e50700c0c045030740347d400039442040700000041d100c1b0120720300b00c1404000255a18800415000c41d190400728038036449820789181c01c81401c0510707401001d42400340800c580b41241000c1c291182523130080200c410708690340c03500c900030410f449500842903000d40640c41d101c505181c860940302111441000004400e1074402c1c030403c01c042c0b01c0c03004200118642829170f112818090120404684e002c0202c0001007a52182806510015441644110703101c000200c8081c00010312a00201002640a20f01010202c6091241c1c880b205c000c0d00d25900400300d00d60020060048103d15144640c00c1500b444100a000d075000e56060101420800d07807920340744000c0761160002059040303004410a2010500111036180c04030030203050401c81081441692103400381d42ca80185060600c1201004200c2c1c5c0c1801102078078001d080e8406042c0f03120360b03504408194065030299601525814030b00c1d12844043e644008007541d003150105 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 191160944 1250 191159694 191159701
    0x1a060a0c050706020c0a0506160213060501031d1c09080a0c0305070501080108103603120204210c0b0c03030a0b06070b040308040f061e150e0c130509 66
    0x20304050000c003401c8609120320040096014808104082200e0b00248a03098003481c2004014003504601c5032002000041c61000300166204151100a24120140868224034044c00542110703280d500e200800070066030401d1021001207030005104100c1d13180c40007a8032040104803102480d50b0407018992240404140500402d05d01440c200c030710800890710403540701c9004490305402031044004950281e0700315200d28034160403180c00010809201c40c1035509032005c80000e540c15002c400d40240303407411200c00f41075011068200c13040064000f0346c500381c5015140415001b03000c520081c070f00204000001005089150023000380750700c4608648030142000c2c010303105d41c8162500000030b440c2016807261070400009032486240c004003c44800c0c1c1c3c8944054500300380081040b1074002ca50450500004c08502c04e42c50b000c0b5005c003000000170780d1340201d40110340b01c5441011425588050401100c001115000e5200d011844025243e11650407a0801c0e8074842e0030040d8081500b1003003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 191162194 1250 191160944 191160947
    0x504060e0f01200901140a021501030c08061b09040902010512010f0501230a030c0309060c030507030c0c0b04030c0201020a140c04111608090a0305033c0301091a060a 73
    0x3041c0402c0000e10601c1003405682d4801183d20859882901080f10300010241c050f440c01b000d03100741d80c06401582e06145403107403030030341c40a001d0b0022a00305507048814409441c040003215401448803100c0b00002e5601c01c24201c0038000d45840c103100395112840d800459208509880f801b100032400d000065031a100313044503c02d614061355001400b20706064824004250340c0c038585031502c1c035406140440c0c01d44114007034461002c107031080c50f844170f42180c0000e82a2040140250b1a40c0c1d002543d1b0501380c0c0014241c0f500d007000c0c02d041000a909910206010f240c0c0c80f500190b00d42003042d001da00034401070f424500a0400a00250350f0110b40010030f4802003122041c1c4a41220f007045105061310041243d8011840c41426008034050302031300044c0b4520041c01502d80083c1840880c565035591103165500c03d84140b07281c11014184090b060310301030742030000c6480b1840c03ca101040c15405103801f0340814420300c2c001c181c4a000c881111941507951221090026080c00c2c0e42c3c1d1141c3c0c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 191163444 1250 191162194 191162201
    0x18050432010e0601051c2d0f050a0b0c21060111070f030507091b03050402030708071d06060906030f060d0b0c03100e011401110c040203041b0501030b01080a0504060e0f01 75
    0x90301d01030490400e142d00114142041c6951b001d80c4000903515200c0030301244a06010b40040c40341114200740700304404a00140801003100d4031640c0101000d41c12460004100840a4100140d0030400d1080381ca0b4120309480c03400005821001d580030b50365410b401242c0440c06100f0050850280f004081aa080c1100a40c01924007a80c1111506591480100d0840d1079a03075910407240d0030b90540001192194100341d030040d000600311200307a5100c0042c00d0030142264403905150861041c55200d0500c0c80d83e800350301510480d01141825264000b00d00303103200090074440c1e00f001c0074001820640e41c8421803101140c0098500c0001d143c11090380d1015403040e14011008220900c0010300250b8041c5400d05980b18100b0019030000d0240c010345000c499822000040c3c06203a40c418040d440d42c1c030155200d9805a04e000f501c10543c0d4038601c03c805034942025040600345604a4200d98002000d00d070043e0700c0701c0740000c2558881c20a403005083d5880014214081c014182008600540 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 191164694 1250 191163444 191163449
    0x405010b0403060b101b030207030b07020c01021b090103080a1412011409010302011d01050c030a020607110c01020c1203161b09061206050405120a050418050432010e0601 75
    0xf002004112441010007051214224102e00001c943e03c400c01c2e80443c0a4040c052181d10900440f4021900c99480e0340b12141c00700c072640016403007061000c496603810084046204c41050500800c020440d0104003e2081400041c105400004601e04e0031840303009a4141c210600b00c80d1a00c0342d100074451100002c00b841000d04040b980c00b00000e079858205690383c101d950585030440c101c81904c0403080c4c2c48100713240c1c0c00c0c103020080c0074000006d80d06000500080b2902d501038007243ca45442d0107010715900b4080c00f0f045900030007440c90140d0700010300d450221001c4900e0315a05103040c419524510504a80174418041c090001041003420324080c0c2c0803000b00034540e0311072511925420102e400a11890000020142e841e0f40130411913400700e03821900032415641241c0c071901c40b0038026440a50b22500103400040c2c03c000b540f041c10306643c400302d41e1480c144070382e082c80c0d2180880158034400312604c10b0031b02c1143c0031400c4120312502c804408488000d02c21440003240d80d507202c00091 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 191165944 1250 191164694 191164703
    0x15020711012613140601050307080706051c0b1807030b1203031803070203060f04060f05070c120216120b0705090303030a0b010c0819090608011206050c04050405010b0403 75
    0x44560380c820750b000e9038090107101c0c0c0049a00407204164000c0320340059001d0105034101003401c2030740000c00c100c810704640040307140c0000c115a514060625203800c0143c1d00c011102c1d00500700610220364408120341410b88a40c2d458400e501e0350084242c01480e0162256a002101c100c02200720a001c0b01c842e0301c42c1001c0d45013084103501c590180006181181004c0c2e500b6007040001500701030700500320007040c1c0000e104982c2000c400c3c1d0b02007885c010f001d55500d5103039203509007000100803080c01030740881c28140c4000d0107541407142c805008800552002009003115440840f040b5100300006181900340508580314140e8407007045041003554442030b80c00d418141c0c006016640035208603070603054094011032650351246035010041c03182a440504103c5406500d4011407030b0340020704101c2e4419090040401600c11019001070401d51114062005da64010051b01007440c401d50047c1c3c2c0c005c000411790b0360b070304903403c0a50700c00c607005550301078036007400462200502c102800c141ca226 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 191167194 1250 191165944 191165963
    0xd0c1b0b10080106061b080d29011713062009040b0402120402060c0a0b0c0a02100501080304120c050a0b09031203061e010309020409030203091804050a1e150207 71
    0x50b2041c00f400c4c0c1e501400380300e020650502c1c0150041c03548002401201e40207012582c10180c00307540c00d0069595800c0281c41c00c1d19401140568003030f070b80d44659000c0b038090a06c100400d81e454110400c00d02d0050085e014180c1140302c000a04c22a50000c0c61200c040700030380e07055000c2246034600d080e00114500c0740140e20307101d0603400d2410588202d42c40c00c4d10000990165603196401c00c6456802049a101c032401030181d204005141c2d6281c80e40542d00403a543c50310303500d0000d4000e140966085a43e0032040c1801c00401055201108540a039049215071480d00d449604009510410340d03803000d900b042c8030540004802d03070741c480035002442089080e00c541d104403841c50400c80c003007034421300e6001403900d500200140084402800c034140606011036003084640014003100c1c85a201940940c0001688201c60b1802e000a0100c181d41e002c01032145062a03142c0707075642c103d00440141000c200d141020300b900341d1444d482d48401c0c0d021140d20b0305031200007050070280d089000b00300da00c8081c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 191168444 1250 191167194 191167199
    0xc090f0106090f1d060d2001080f070c06050c0c070f090606021b0d060b031504050609010c02030d0207030e030d020a0506060a080a11010e0a090e070e0c0d0c1b0b10 72
    0x14014440d011251803c909407001c10305407401c40340c1c4010103045d07994406070321803c1c5c400040f291883c0043c0304c83c1c41503a000c244a100310004d81f0040004200d540c82681040c01c200c00190044010452180c0203900010703580d940200e000303860700c0350300c81c1500240303d01c090004500303920250000036100401402e00005a9402d403c0c1d0340c60050700c0c40c041c1d404182840382012070514620102c01b0728020080401e42046410119062030a58a0708a0000c50140100418454200641368018030510020080d0160658009440c1e010350016034014030340010f100014180f144502c00d000e00b50081c1656599000f501020303654021620045406003d40000903409141001d10442280c00c1c0350003502100849a0b5a1241c40102c400140e05120070540a10510707107034941818064181207000082c02241460b10318a400c0303090f4080c10702c1540700d070100003105170080207650411881031004503010b0740440083e105466a4443c1e01201204440da94040c042940b0030725000c0c01d240392521138401d8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 191169694 1250 191168444 191168459
    0xc16060b21010e1902091315020a0f14030c09060d020c010203010e09010b030c0a06030507030f06060e010e0f150309010b03010f0203041a04050607050901030b120607020d08060907030e0c090f010609 87
    0x13800c0c0070b0043e40c04a1784600056008030003904981b6250f124400000385140d800542c0d1040f60441c40c02100056990784080b02c071980c0210b01921000c00c04141d40c0c2c114030b8100b8042c503a034841c440c01d80380102d001003070785607200b401901a540381c840400d00039926580c5401c2e2601c8414400c943c03145842d803c2c4001c1001e035080100e900d0560203406803d14019604100054015040140c243e030101990f60b411010861150301c80c0030041c0113180d80d100c5441804000040c44480c0c28620280709403181c403101810b5070790b035200e451424040300c0c480702d07101c2e990510444d004000050600381c0550030001e10a0440d0440e078000c1d4821846402d0288909200c0300303641c40c91a030100ca00800300e0307110002240c5a1402080549450a0140b401084001142c00490040f110381c0000300c0c640d074000f03011302651030740510510800a805250079009480c0680005403441c9019000e64240b40c0d540b030042c2c0d02440c0c14400400540c402400802150800074051415003109100d0740c00042d00701440401e900 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 191170944 1250 191169694 191169733
    0x901140108130804090902011e050c16140d0c031b1703030601020606280902250c0905070c0f1a011d0a0e030412050c04050c16060b21010e 61
    0x4a8002c0f0000d810b15040031502c00042c60811826414040c20800e401403004400700e401303080c2c480c01c2ea40c0d503840d04543d5580c1894109103018401046140c50404d1140c84200184400b2120003101c7c520044071701c41c03d091805440301c2c2c0010700310950074a1860000d55154904030700f100c01e544d11074201e07040e4440003186c5a010540c0d556005801c040040389140c500b0b4049483e6601e000652464120003e01e03201142104640c00184015000b0801100905800100c0110001c1c0040703942110085540e400e90400c910b4007032052055681c074003260f5214071541640c1e0701164042440c542d0030343c1c9818081803c003200c0054501214440001103502019405951000300b002d0b10034030903548581101c00003804c41b10300c0b040c880788003c1c070002912180900e00c640b1014000e07001780081e04036880c107120980d0001002a200c40d5001c00c100e64506c0c00c40c409000e800d80d000000080c00341c00030300006105041140040480d45201208140352610660040343e00d58000303421a007908801e2078029111 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 191172194 1250 191170944 191170981
    0x30605010203070204050402060d14060316030f0b07031404060b0a0503071a030429010f05180103080d0f0606030c03270807031b030c0209090a050601060509010e0901140108 76
    0x50b0400e000220060920b90000c0d600644002c060506004041c0c140604446c104400d0388401001d000c14440c1d241400d02c0210010400e030b0200c2c2100b130717040d604c89412248404400a1203910758100050a880c425400740c0080c682e48000b400309030600e81001d0b0040d1120360035161140c440c0c0080011b00745000545541100c90ba181c0b9054406100715840076a030300020801d461504941c030303181101c041e01003111421043c1c08103040d01e442d4102031204030001296040117024903010800d400b60007010581c03240c11640c0c00303400141c3d00d032800c0c8240400b6190580420104a04210f00400c0240d0181c22042800307105503820000e001045601c040884084170304501c0e03050001d800100410b4960000b0130707490740241440d0141009407940d89000400c5144150000303030350455024214a450340c03041d508400014010240d07415151600c686511041c4140c40034004c1c0028030480590141d00c003010b0012005140c90300e590307519502d007059102d015801500060010340010308255501441554 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 191173444 1250 191172194 191172197
    0x15171006020c130e010207030809070b04080a021e122413120c0b01080706031107030207051002151005240d020702010e0303030406060504180b19140708011503060501 73
    0x2c200c0c0b00c4007031142c103000010a408440303441d201032a1950030240010840181304e9541d60310b0914081006900f05003154003c465050b10401c4100107004d0006003403801ea42d011603a80c0d400c20020848201d140c03001072000c03500001d00603490001c4400100c1c4500300c9910003414140c0300c02190040300e20034101114a41c828112440b22240824400701300c15540c41503d00301400301220785d48805140d483c090307000c051190b010090038880745905014440d0070b4031500e9442c600700042c076034020391500c07800e0241c203000e03c2880112030203a620800c40441c4698a400c01030070705007000c0700642458412402502d020f000f49264005406603c2c915a81035582a81c0e206800c1c0024003405401a50142c5404d0b030401c5010314604405603000d2000b540038510642000034428a440d080c031042d500d4810300c100070010b80400c8400401d40b0110030b950305c850310340301407510500c5586418008090b018001e441d00c202309002c010132650407a031558184c840800c9142c03401075100c241100ad40d040d03809000d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 191174694 1250 191173444 191173453
    0x36020910062c0901090209130204051809071206060806090303010f0e1504060b0a081f0501080c1b150903040f0504020c0109080a0e0f09060d020d03091517100602 71
    0x1a480c0500c00b0b0500300c0c403040240318204141d500400200c11210030303040500301543c0002c040610f40f600003050344d05410315000c02d40c00d1500c0d1600041d803c200c04149040411110000640c410000780300c1a0090072000f041c4400f80c1909003480130040201c0c2c0181e25851090602280c04444d00000b620304030387c2e08810701100c0c1400c2c40503100b0035003009041502d4402e03070110f00301000d981d1030144030083c00341d1040c0140c8610014800921100d405441c44d0140b072480d0000c0c5020b410001840025100d007800c005566440381006034001d84903026a184904480042d01c000c2403c0224080c4411030b0801c858814917215808080d84a118500c2403440c02e4040540410240c241b5401a0001e080c1c10f0000003060022030321207108550100c0e4140e4000b646402d202082803500c040d0040c2e0f24034003904c5110481ca0b114000c22021800d800d0003034401e50030769040300100b511030b04072100030b03280d4000200e05e00c0a071040d01a000d401c0080301c01c0390a000200025140504000108080303d07603e60081 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 191175944 1250 191174694 191174717
    0x204140d12110c1512060109080706030b030703060f0504020102060901021606090813030302010c0917064003030c03020a170705040e010b040807050a14043602091006 73
    0x940b641c2000c241e061589016a0902c188555502c10f2608003422444100503902c03042050300d2540e40c070004080906000301c080060205003030001707a00b800c0e0794050070009100d1500000203464111207500c01400d41e0301300b2700b140d4028a41c5421150040c0e100780c003292000d17200d9901c11070a0f40540703400128500f40760f482c52000701c0d1076a00403500a41c000c03500c242c54585030a9001e800c0c1b418613002500583c1d100da0440f44060f50004e0540010403400a143c011458401629030710b420002c0d0290180540780c3c0001454071200c4000204440040000380b14074683c4400000400304c0201c40c00c0d804a4074100d60b0381402030290003252602c107915a1a206142c0c10907503100f0f0003001c00740075841002000e0102050780c40b000140f05010300200400c054131545810141480c24000d904107078016142c4001c2000500079141c1d0080511030101c8010a2400d00310a80b50284074420b00c000d510800c1100315584200141c00201a4942c002d85045900d0ba40324440502c4c030910a1007001c1c001840480d80 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 191177194 1250 191175944 191175947
    0x190905032203111905041401051e0d0b070207120c081902180a0e07030501090c0b0a1e12020703051c0c0e01051312140706030506060316030603150204140d12 69
    0x400134641109614600c8007a1a8004142180c550360041e01c1030380300980050100346090800c030500400300c6c1e020b41032980c0340f100100e0303060113100c10003c00d0215140302144695000b8024800030b0041245100c0c807400d0380e41000c0443d54107903c900e00203801141e00e402d00c49018044030514a0b074001d8035004201039807011040d01501c00504004110340c1c2c408561010a00500c414802540100008240c0300c2003410401c83c21840380c1e014512618081020840803604203005500522644100500004460380240c60a403451200340d03200c148001100c03810150094007518a03211604c403040c1c035803102c0c00340b58000c44030080e94860205000d10780500306907200f50000c2110000800805440f242d41c0d84440301301008070070081302c06600030620240110800c024110082c20325203000c0c0311a08049011075510320001c1e000140c03500c444180800171501030b4000070300030340d03024922036800e41405a0540c001c0d0058082c0e0061503140c1444030381c2521f0181ca01c1c14045400c07000048031140500780 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 191178444 1250 191177194 191177209
    0x203011d04020310060807061d0d0b04030e13051504060e0a020a0e03070e011e030b01050f06070b091b0102061b03040f0614040b0105031506060319090503220311 71
    0x8126030503c80c070082c084084004d0300079007000304106002040502e00700301c400781c002443c00056021041c038003221210a5502d082207010140d4019100e40281e45582c00c04075248243c8000d001d03002100c0c075000c4620f000c1564842807160110003450002c00184104120694440f072040140b0035446038042107017190180e00a02001d1482c0c1030090250004002290802d0441e0384060045071740500104000304200f08030420844407070086400721401c550710781042c1c0c0c40c180a51405403000802d02c110b2030300c68400301d440d12500a140303140c16140580c50b0301d603501281d04440d0310104d100c103003510b240c0d400010218012131b080c03030b111100c501500c40081280c1c2c1005000703840f1403080b5464070010500e01d00c203090280c00c1d00e4141514501d8141881031008006038461b41c000d5028018010700c0980b40950550007602c101d90155498503a22403c0516840f83e91820301800e2a080800f0204200080205240160758803030010500207455041e01e014203030711000c1c08080c001c00d04456149009031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 191179694 1250 191178444 191178451
    0xa2705060f03070801060303030617030a0c02121e0705030a0809090a0209060a03060f2c07030b150d1b0203030705070606210c0503061303080411060307050318010203011d 75
    0x620510900c400d241c0003e241541c658001c001c944d41d68a8103106055041c050305c00500034446011050080d09104d265483c8a4070f0310b1401004070070880b640465450310110004004a04304589420002c0529400391070303016a100c101500c00d103034000600c0d00340426000c6440d034000001d582821503007418000f03003a00042c103464001d076080200101c0e42e5526070140010b0303440d82d9030010f1105c0c03d0046c00016084240c2291181c0c0616900d20380d13101d484045850040c1003403090307140840c3c9615900354050203421800c1d80d817002007a12400441000800682413000c601c07502803010b000054144600e81d8038900d4003400581040000540c0c280c0500300400030b851003024000350007540c405141c82c4152107180301c4280001900d8030750301071140c4a10200c0c040c1c41c1c1200589103e040c90403801e042000b0f103140040034803444000150500441c0c000c24500844041d00155480c50f001c17900410340c0d8021541820070843e40100b00810f440c052090324143c1e4036040c207865801d22100e5403d415202c0c0107 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 191180944 1250 191179694 191179699
    0x6021c0b0f030a030e131b02060921070606030b07050c0c0f010c020108041a0a060618050108130c0308030906040507060305010605090d061b051c050f06240708090a270506 75
    0x5203400c1c1300d0b006c0751180e10390590000c00744031042c145404d0000d04054000e040401c0c554403401c01c802003032100b96654510130002103041942ea080c1450018040c000507800603184404400400c602c0300d412000400401c0c400000303940104031018200710800e08128004c0340081c03507a0100c4070055002d0502250850302800442500a1900081502903030741215100040741d1502820443d05820440120f90303d0301251140500c0d41c14000000e00004004104450008404518009020300509044043e54100b48042e90324541041500d0799058148e400b00d80c64400c81c00c001603014402d1058034140c0760181e803402d1510041c1c0041040c0403414500c140d591664400080d80848512141c211b003003055500d03401d40b92070702d000c09085c1034041404202626400c14080015280750f280580354004030465902c0c8031031003052180e85041105c00010034140c0e10006c1e41b4818070603140050101c1b40b42c1150310070742c4e26459000d00310b5880c10080e2403507080e185080e003190b8042c8c0b05802486d4840d030301 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 191182194 1250 191180944 191180959
    0x12301050d1e061d0d12020d060503060408090108010b03101a0c1902010207081f09050102070c0303080a0506011d010807020c0a03030809060f01230303040306021c0b0f030a030e 78
    0xc0508100c40e2080e00315045440da56030345074846440910300191000f0702c0d00714000d410001c490400103840d042d503200d20b06c606580d0001d8144098811070344a0005050302a00301c039180d01d07051600f44060791041da10306021550b11070000550340003580480f4402c40c650003055014610340300e2522018446c0942e054082e20041c4000d5242040c1044080340c90ba0080244140710070542c00061b040130450340002109401c400d040c6401e036200340c41821011040108000751011040c00e002e0700a005807100149442ca040c0710000c245a40111000e00403400c940082000f9198031005407a850500c26205107101c1d24884010744942c068941c0c5c6a00110303500507030701c90381a0b41c0002200e189aa400032000b1402c03c40c18081c5582c07040000584c0907500d0554251302e541000644083d810400c008030304801c00c003070f4a01d81a600d082c4183d80003154402c1d410b40d10740360050414082071241407147c0032114a41110400036181100446d5000030b0058044c02c1400314030f84085402c40302040031340340c01c03060 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 191183444 1250 191182194 191182223
    0x7060f0e030304150c0e0112060807150306060e0a0605090a09050a021803010b03031207050c060c0903060a060e0a020a090512030c1204050a06030f150314012301050d 73
    0x16025510320328a8403405556070380b41500d403c22008001240d402c0c00760303151110843d845134002c0c000002d0880b090030b080718103480701d5040344042c000315002041d490241c0b4000085d04121a2030f84181a10b43d03407410f110040d1984001c491810024880503400418540304008541c000c06c0284800e08002d000700700b980c0e846e003000c00140c03001038030910049030b0b0001c0c440c041c403040d560300721818103404c400a02000c0300c0e8a001940c1d80c02140c2d9101d080d1103ca40c00b140f1034a01a004803008802e032282666068604035840c0d00ea55085140024040e0049000080320400749200301c0081c0c0c1c05404034103507036881c4d0214640c002c2d003101c0071a03014407a007068085610b90311900c1c1d030070558404070002c55868034222616814001c42d0031000405500c180820710050380e80d6207219007510030502d070005050354138403001d20150080b0039103490100d240c54404014080c0ca00d07100c1c070703540e55941c00030711400035640518460450100350804159400100500c0300c2c4c9841c40e090040c6500540350325800c8103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 191184694 1250 191183444 191183471
    0x7020a05100902180c04060e18040809010207090e0d08011413020a02030708070c03020a050a0305032203020d030314011502120702030a0213141b12040c080f0709061203050f0706 78
    0x70117843c1c0565200010a04100d40c0380d201d1140da8007560140c6403400c44000742c025003880510003510013003003458046440c0c0c100343d10070000c1000901162805004d000001070409407515030301140b03280000c4030070001041c5482c0c0d0010719031b5030701d030060050752103400d0010300c100013034000d001c1c4a000c50004100300408140c44001402d0410301070390b1401c1c0018a54410001501d00321340c0102e014500010b001c01c080b81c1d0220580e00140c0245d0340315007542d15040400c01c0740d6041a0002580451044051b000b415070580c00b1000181d040c814000190741c80312145581c406030300524400681c043d01002e55004070701405000d034607201808a90100c1c5081e400070700c0c2e8444000420780c007507546601000d400444180e041d5000030300e004034003610500c40701c40710506103d461045055135048501150802043c81d00210040145406642c450124000220307120700d4548120301c04507061280218950826642c414416680758950310315000800d42000c0c2070b90088102556500d03034810303c001110 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 191185944 1250 191184694 191184739
    0x50a1710080714030d030b060d0216060c0c02040c020f100e01110304030203190c0c0506030403200705030c090601051e0702060a0e041d030409091407060309030807020a05100902 78
    0x1000c60401d51601c0f956000149031a2518901c0c5ca4400c0505100c07542c8100d440303040440d410301503491405640d41718030300081110051340340001000300745001d1910400b160710002c5910000d00c03c071014407404541c184126601d03483c0109107030030f41c3c00c82804011182030b9544154211868040085030304c018181021510340c00440341640960400a40a00718100c1216500f100a02c5400c20851040c000d80b11541181c00078080d8034062032002002c6014140500c69803000d03941e4240b0b8160a03c02200c6481d07407100307014800d56010b407194284440451900c6180e0301c1c80756906948103410a032030304111644501c40c000c0034080d0504c040024201607100c85d0011300752604c0d10703105c40929103011020303c01115410501c181d20403172400000000e56402100b00c85c1140da02c01800301d4500c4e03190030400181007111521802c1c912401c1c2c03000031040d401da045281418000d8484801c03540d111001641c036650b900342d0040c10758218040111159420358401100e85002410b1080c03016400c07940010300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 191187050 1106 191185944 191185949
    0xc09020414060a0e04150512010204140d0c080a120f0203033c1e1303080403620129030103030e010e01050a17100807 52
    0x10f80c1d202d48141840a000100104910700c46034508080510b9035125980c0a0402030354840c0807a001842582d00b1111402c4114130039003840001c100309069890340c04c407042a14903801013412941080602d00c540e10900079046801e61a40c0058045402d02c0b88030b200310b520070410007880080018031201c1140040c2521585410440752251811324150440300e141900320b420828040d040c0f03c05810410f03c056200300042e1929412460f045000d142c010300070030000c2020400080c402c840244044160054045807540301c81c0d00001203011034000040081010412250503402e00380c8801e40304402218644115003082c80b40c0b070003241c014031410300703409a2110150b000c01c1c00c90340f224400b0501094110f03542d68413807501904001c504010b02c3d00090059048544550249048500c02131aa0f00c40044800b4244015080740c8402841802000b805440c0058034210400002c0c01 = true := by decide +kernel

theorem cover : BRFrame.Cov 191007194 191187050 := by
  have h0 := BRFrame.cov_init 191007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 191007194 ≤ n) (h2 : n < 191187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
