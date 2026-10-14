-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1403
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:48:38.404373+00:00
-- url     : https://prove2.me/submissions/8471d717-c7b2-4551-b445-0ab6efeffd17

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 252158273 ≤ n < 252338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 252159523 1250 252158273 252158281
    0xf010b0324010216150f050f0313150c03050709050906090115030204081903030c05160f020f03010f09060513080712020705060c0a05060105010c08090910090e010e07120803 76
    0x148202081c005040c01070720b068a042c40f0303010001038000c3e8445040ca4101805c3d40d0156580091805a01c0c1e2660070424140060407800700c28a0200070001c0e018090385454507014004404408080c0301d140b004d05100b4004d008c1c01c0140941010303a042c00108000718404507031440d2010f206032162502401d400e519a107402e00f24400b056140f8218014164204804202c0c40d0084c0121401c1c0303520480800080c401c0c82c91700070129140ea8694204000041c00002a03000450401c42082e58004542c10504902e41c000140f0860f5840c82030f40d070541c602a00460940b605801c800d901d18042d1000b04811360340c003000c1c1d00888518860081c520081003120b0f2000615002100860781114030484071400e13140c40110700c407584075058442c00b40c0d0011890000b00041009102c0c00361500786801d01e801507180d9209a42400380360607036032140324001c0014000c0003281104d80000e0245102c18005520f039010300701d00030b10f890240c80c52980214040400c0c030103c103a0310003d40a9020b1409865591 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 252160773 1250 252159523 252159571
    0x140901050d0807030f090b0d0603020306070503040c0b07330c030605100534060b0d030c0b18010501060f09050306070509060f0f0d0f140105030601060e0d0206120f010b03 75
    0x1864003017424070003505004214800b000c4090100100c0000c0300140c0e0600314010186002c00c01800700003001000c2007000009582c0350b84a0007118101100c240d100c0c0d0040c40c00064050b020340c2c41e440e400c1602100c0e1400b065105141542151443c40204070380c5001e000110195000d034000c50b5081042150038140092141c03004111400c0b400701c0300c0e00c070305034991400e0940103114684122500410305401c8280400c620840ca0b19407021154510701c50010340e00581965581d050207070107001190009012426219210380c4580000304c000c0000b507071500e07001781c000f458031144500090050352020440c0d04001034198080d182980710513007030006d29410016035a0040590118400c818024401c004c3c0040300079042c010401d07407010078940d070700c10001c100700e03a4600c1045008007044401000280c402044040c19135429103044101d0901c0c0078007007032a010b102c0d04002c1d0004030005a507a03e941040c10058040d1400e09104c1c4100d90f03803108880d0315800183d80c480075020408030040c5200c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 252162023 1250 252160773 252160787
    0xe0a150513020d0906051801050609060108071b050706021015090e0715120e0a0209150301140a02070b09070602070b030a14041101090605070b01170c0a140901050d080703 75
    0xc900740c00c015240081c2503103400281c4800e200129000390702d40f4288440c2c00d80000501d4003145c4094020403291610400080401b14041c181030705200783d20700030642c0603108200c80242c8074204104035a96012610b4015030700c19103889140018000d00240000d402d05a01441002d99011441061180e02b8011200f0003803690700002e440a20501000080030420303d40c1032068201962a2844260208882e10301030b1159080d11300159040701650070016950110050380004440c9141c03442c520309070307003c640100482c3c4119008402c0c05410050741032a50340080050304e108001e0390b01d030381d2070b02e25906541d400c10303014040150f00008410300905602c2c4000c0d551003907184c01c000c14980b1102d0700010b11070906507020750314040740e04040740807075030041e85100c020085880c00c0c0c2d103001ca258860b942c0717071013040c010442540c600b0140d558020004111941401a0084c00e2006e416641d400b03444102520340800c2d0300900b6090000641e5240614801c1d01c0300d41c101054a01e44642a64121504 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 252163273 1250 252162023 252162049
    0x91b020a0803090a1a06100302030f1503100207060f0b01080105030604080703090e010303050a0207140a0b072607030e0102030f0f0904060810060e0a0219110f160e0a1505 75
    0x113200d908004004a5075858a6680300c1c3c494540c01c0fa01e41c00d2820600810340b000034084414580100f05014407403012464540e4000b501c01d0101100095040002c0d09048038555500e2609001046280c00d000040d0b121086c00e000b1901c0400041400304010741d03130980e09204a50745a084000020085a0050f00900d03420b0703c40e20304825004e889802c445001442a08180c1c00114085640045d040e010802d40c80502580000d2140c1d0728141c00014070182c803140030b4450814004503121040105654640d0203040d150b14038031010200042c614a41500b02c10b90030780010390007140c0f51401f54008022a401016a2842540f40400c04104c92181d0342c0520610743d04217541e1100000d90010500040780ca144c40c282c07010400c1481d0012004a07000041c0121a0440c41040310701c035a1038842c0c1d0f000000c1b866605051324810000000d50382824002100000c441c007030103080b0391003140030048030801e0700d01044500381140c880b6001601100c400b1040c8080b0031039201800c0c86146800d83d030440032 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 252164523 1250 252163273 252163291
    0x50a02150a23090c151909030b10240c0c03141504120305040f1a090f19020d02060d090606090f1404140f031801230702040504150510091b020a0803 65
    0x2d012070012501c2906809106d0800000700c401c10103000304541f0094143c0c12031501c25880101a003032031800f05e803a404100c0c2c45080800044001c4180c5800360440099050b0040039074020a903580c24a0076206010852006950040d414450350024010002a000e960171182009640f1031404003680240310140c02030b140c030442c0c500300000048101401c0c08501145004600d4141801e000042c1741420f0304010840365004003210f10300791614400d0b0160200c0e012100701080312418004601d0034425800945056420300728032070148080c1c2d8000404032071035440200700081c41d85807604125042da18505036885042804640401c6844105140080100e4141e52101018595451441c0d01c4414001c0c01d840039000d03c845a5a04207110203802c0162000d1015104241d400150046c861400c0007440346a490002ca020300c0380751414141c41840c10001003029007800380003410a181c0901c00c01c0b00380c504208540d05500350498000149101a800400003c80d42da6205461760300001e190080c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 252165773 1250 252164523 252164527
    0x120d0b0a05060d1e0903120906020f070f0507090603260c030a0207090b011b0b07030b06040305100506120c01030b130c110f06041101050a02150a23090c15 68
    0x2001d503281002050039040c8000002001e9404d91a150140c441d40480080a1890072400e1000b090704800082903980c041900080d61030b003d440c03c24028020041d912900001c045000010000c002040c100b41c0d038022070131500d00300e81d14008082a00c41c0d80c000205040d0540003690010480904c1d1000401508d03405030342050080d001140c915081042440c0040c1d00c60142080035521034820b012005200303180036600c0b59a011110b89220b1860b58004040a40320030028040c40c4c031036400031504401c006e110655981c0d4030704001c4d40e100904803282c1c402d1841c0c8404030303101d8544640002162000381d4082c14003007141d44010b43c018195000481d0300100000c2c40c20179420011b100e10082050b080e00c0303901400000c00c050f940350604000c1220340315030101c003e02020940407500026411403d2034030b0366403280d03d82d1080703007046203101306120400e00c0e11050103061021608210700c0121506641181800704030314041550030152031070542c40e0883c03504420581402900312100d203104480080c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 252167023 1250 252165773 252165779
    0x705120a0315050d020303160f02060d02030a29010e1801030503030702071401020303010918020d0c0602010e030702090f07090e010e04020f010c020f0111010906060e0612120d0b0a 79
    0x181940200203100c0000e9407a0100b0348441240e6190201410301900c4840e0783c0c0b4250350109a07284541125010302000c01503080041228002d10270040680c081c12554036180709811520103500213442e510110390a1240200100d00c94014040071845059100c1c511500c0c90801915030061080c0e420380c000c2070b20803846145400402e2518007c41c4200011540d81c038200200030708125a1750000003400c4600680403009a034000305a9042d50f40d449000211988130300f8640c00b00c180200c1000b504a080c4000320360600c044845110102d800540003440140707d050459900e1f4452604025030000074000401d0504454201056005201c1d09281d6540e64407003503000080c45090b4841182013801d03400300300c114204a666416008800c0c00d0118800c40c15500203505002003a00c00c60400039175507140845100d003500200b4480d50060343c200043e90704e0342e5124010507411908540500482d84401404540c0003883c0640c0171510706095090021a540840240c4105010190b100340488408 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 252168273 1250 252167023 252167053
    0x20304051c03030c170105040209060d09121404052407020a03080307020c0901080c0f0f1003050f070f080a020706090c060e0108010803040b040e0c0c0703030206100906050f01050705 80
    0x90034900c000c07107800d0100d0511480c2c020b080d40c1c0e44006204c100011618111581c8405a90082c10b4803421900940c54000e4403010481d640038503104403110318200102d09041c020a24222501001c0382d80e41d82071040782000307204413107100c1c6100d0315030003a0034075007004101c10a500155440e462080e1049141041030740002e600706603541c105603507810380041400b0000b85c0401100c13040c900241e13900c0400350f2502c000146c985101c41d110a0090714100c0454000755586202e00603030700802407071903100940400b401402000200c80302900302a80c4004560182d00541e82c850300040265103050042d40c0d000105c002a401c402c000b10ba2442d11b8600500014982e0340800003d0310040d035a40d03000e035000710001005540184e01a082580003000103010080f420012641580c28004070010151a088480038552042a041d400342d0b01410341d001c8101a40840c01a015261800100003510780b503000c0300d812600c8030702c40e0a510100d4185446259406200509a118001e10559044091040300c03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 252169523 1250 252168273 252168289
    0x80d0509030703051c0e030712020d170d0c0314040b01121a0406050a05070c08040b0a0903140102120f090607112a1c0f0206090a0807060302030402120f10020a02030405 74
    0x52081605e0103001d15201079000c20840d5401d80e0450080c4503007171400c030b01207582004030302019004001d5081603200f0b101d124103d141c0207180e40071449030f40c0c101c0c00341040001e02c0a18030290019007800804240e00b007010344110300807501f21281d4983c81c3d00e000000c20039900b003404215441c01d01200010081c04001c000d0f244618004c030001f2546103061a400c20403035000404910910615040c2c41c004030384084185d6082e030705e558080e25604c81107d0400e0344d010a650380010000c41c0014452074901c0703010740160a08002060f8a07100c03a8440a032207048031803007215005440d0b48040000759241d0300c20103004000500c464184c030b209850230504030710b001281140036005040000300440c01824a6010741c0ca441561a002e07058226440d0394403d000b55008201074401c41c000701e0200701c10f50340c1030080030023000d0040c1190801d564418000d0044e400449080c1d205642150314850643c402140003100d551164000d851400103000804000350445101c031801c503c0188008034171070b00d038016 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 252170773 1250 252169523 252169543
    0x702060d2a0801050f09040b0115030b0303040f0e07050304051b040b03010504050705010f020a0309050f040e10140109061d1005030a050309040e01061a070618030e031006080d050903070305 83
    0x1036414060344c104010300000b55800901d150042401c40b003048082850072456030306503513821107480d96556803031508802600c2801d1000d03903d030000282c0066401440d80102c0211005098030040f250745120054030580812500649a90410ba00100c40e00d00000d11510f50144028000500c085050000c2404c4a2040742e08a074280d03c200014400c44da0030814594001c05284001d00105100713a50003000910144034a501903260034540b50000d540c0d503040260744120600444094542006d0f40c172000d00040200c20017035203540000442d140e84107001c1c0c2825680111000d40601d401041404100600100188841503100754040755030358003884103000180c0100001c545940102042200701d61240d01c42c80300c145c0c54600e0401c100780c4461101c42d01240340201041e214103080c10458080c040304038188c6c50288220344000100b41e04011400c113605015003c585405038641e4800c0c003161082d000e0f0351b80719030081d100028030504c60301c0240040d90024090f225110390301d9840340d1030808000c0e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 252172023 1250 252170773 252170777
    0x3030f0a05040e0a0906060512030a0305060307050d0b150105091c061e0b0108130b1b0408031303051e120f070507080f16060f03022203080910050702060d2a 69
    0x1c0d905c3e1052010341c0c0136200207000201c0e61035003d000284021a42c2e1b1042400e440305040c0c58500040541e0b0702402000000c21001c0e2044845810f2441c0101480100701e449101c41c481542800065510807000d4590034200501a41c65000d0a0608050258403604080310f1044e240c14003506034002a141ca40c3c0c90340342c111b4010600c81d190308005409400c0007000819403000840c1c1d1440440e06031610300380c0188508100407400b65030a01e42d402103100380e400c003c1207844001184104018000038840480b40540140c4107070400c1c4650554801e0420003140c43c4580c8407902203649005024020000f100c42d4030541490107200d659043d003020269440900c080c1c02240e5400405001400010746010400100403025810700801400302c052451020040580c0412100400e00c04054000544030362581c003005055903c0c82c010f20140d100110141c02000f6442e0351040c1c0500600c1a2070031150b0040040d030030316003600003440080c0140041e80030802400e1007610143e00c0ca040203103030703a402c2d20703 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 252173273 1250 252172023 252172031
    0xb03010501090b0c150408071a0f010e0f01050f031510030c0e040506040b07050403060e0a0c0f0f0b0c0c060d06030507050108010503250b0c010603110d0203030f0a05040e0a 76
    0x68005803000c01d09034000b2880c90400c1050031904d40c004510380018414a030b90035011a15903050004c240d016641c0c000f0000125540241e45040180d40d010b0303c0f51040c1100000369a0302c402950203000c10a0714440340c0c803550a0014070041c54000e981540d2100301800303d0364501c113840310f564224442552a9141e4447c2c01409106001e001100540648880c41f406800c9040550310380d82d507410010000740c400041500483c1c031240c45803080310011500400240a41103998203c980c131403000c0c5100b11203440600304001450780c070281900c401c85205505041000f0320702003103041e45900030005801c0502a541812036550748000180c880884100b40004080c0c0c01e5251440c40c091481d08214140922000104000d5a00080d80ca200c205904a540348021481085012040c110307080b10410010114050310386840541c041c808172030083d03000b00c0310011807a00344504c03841384000103900341d0401c0180d0000711407010300610040000f49080c41c45e10383d550301c4010131410280e6075904400c0c0c407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 252174523 1250 252173273 252173279
    0x2070602040e090a03051909030b010306022a070e270f0705040b130b030f010f0227060403030f0e09070509030f01060605180a05030a05010605010908060103021012090c0b0301 77
    0x442407282c1d50118692005040b07806035514080c103940542a041d5819400091030f01208900c6030117102e00440d80700c8000c00703007541c492070301c903000e500005010701c14000038103201681c040000403070b00c40d82a8a100507101550a00c0120303154118001c00481859018150722582554035600c03251600d0300001c050b003807107500303d19410708040b555400544034500b408410341030b9030790396401880700b0381250f1000a00e40240a0200341003415414088580354607041c3c03040c0c00c2072803d400030700e081c910314492820b510100f05102d0300502c0758520040c0c0c1110043c0020310000c0d0242e14501880b61250a100c80c8483c0c441001800c10841242e04c10b00184020403407003041d041c10027415034618800b20084c4a803506100b070003406070040000daa00c082d408032109e50030a4582100a0000d8103001e010f80d000b01c0704d02c1c10001d010b0030180c82a6030004130281c400045000c0042507842c180ca90007808400030b00115003080b12540380c45041d40c0d549640c0c0d15402000245441c220400038948102c84a44940c5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 252175773 1250 252174523 252174539
    0xc110a060e0f12030a0203151509010306050405041707080408071202120607080613181406060a030f0602071110030501061404031a0709050909010218041811130207060204 75
    0x912019140e69480003440d03c54618605042c0ca500443da0900107882e56105d460205250500e050015000000031082a0100101e40001c00c003020003031724184140c83c2d40c0e00900044820032500940540040583c01c0c4142c20100000e162182c01100740c00e0616494413256400c0200e5503010908481940c000700c004c605082c000421440d401d04064001403504d40310190914000900092182003080d1050040401a42c00403e20f45480c602203103015071745180042c0e6803884142201c945206601c00142545860203042041d244d01081d403031102001592004069005148121410740304044450780075119442c00d0400030382182d8012400f0b500d44900901400c050181e01c46400104200500200c2ca134100c0c0002e4010f2085403442c103554030503408a420090640105500441c004184500703a101500a485190300c0d20800c251841020010803044a0000d0003030720082403005480c8012640d04811680b4948002c1c184482d0315512829403000c90b031244c0c008980d005e9020500f813000d10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 252177023 1250 252175773 252175783
    0x140a0203040201030c0815010c05030c01020c070302030f0105070c0303111e07031806200f060106180501050301050a03060c0c0203010509010603051e070b030a0f020a0c05061015030c110a060e 84
    0x5060910400901f01022954503640300e0300d42850500c00782140d00400c0000c04c004441c04070507407030021500c60b4240341050391500070511080c0c1c824030907001107410040c0107104050155001ea19500301246143e941a0040d2425110041c1201d030305001c1401c030042c03000007141e0700124601445690302868500038003120461038100c080845070220070702c140303a00701142c0303841c140b0164004042c04199222203440d14000c141040c00d1400b414000054a94000d000700c0400f900f81d01421501c01d0300c500044a0501003440390540c403207210701040002c01d19540c40b5896207021450240c0030440207030082425500d007515802110303991071000f002400024042100c01003a9040558181180407250565844003030240480070880040072845505540d40507a0503250101400e41d2105400300014000c1995401d050710140030b0f100000c1c0768901004041401c0c2e40d002c01c0084042c25401e80304030014010002081c0602182544d1851040010000450818843e01c008100c0d5103c1d0750a130b03401c00c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 252178273 1250 252177023 252177041
    0x30f03050913090b0601120213080307031101020f040501030f18032613020907180e01030c0603050601021519020403080915030c12221b0503070602031606140a020304020103 76
    0x22920301040fa100062940c03050740d404c03130400d103030a0201440301c05290000703114801001c810700c9281c04002401c10b00110151854500907100c3c015805101280c446c2030384141d940010071407030104003d00566001c3d9000300328030340200c9000103082072034031040030044103c0e440c164003103200074100e04403550b281c0303401e00b40320440c98200c6180c0382004503000c030002d401c01c98000d03ca01228400034414070b01c5681c42d0086080c01b604e246080b03d82e603a640441c004c1c070070702003619404401c40c008a03e6078080e0050324020507042e401065862010200c0c840500c41c007070318410881c00a400425a05003490028002942c0141000342d9200c05c91810059180c00c070080e2100704117000e10130002075101074800d40b0b40700301c1000601403050b031b5108044001502c1c0c81700143c124030b841001c030109121044801400200f4940182c10035071f42c544007016907542d11132145a006038020032012a22111030450005085e102c1c8001050010051504068404003211081811540441000155a4035014407034007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 252179523 1250 252178273 252178309
    0xc020a050114040b03090102070503160204050f0903090405040305130306020c070602280302071a0c0d020303191d120a12050c041716080f060a0c05090910030f030509 73
    0x310b0700030200400a07a002e14494490341d1500480007821402080d01210b1400b507011003507030380e1208508455400c03110a00703401e034002c0e4501800246020b07000030791907001da02d090b0010741c02c2c030b1080e23420040a018000d000f1800c100c13080c00503029000a02c1c41c0d000103544151030160300e0341100700d800d40c680b00c000c2c0c2c4038000715408480b040c800d40709080d20081c001d00d101042905181c169007426880e00740f40d84d0280740e9006082d801d054140f1071210252402161800a0b28082d846100d02240d4900050343e171604491518180308809100c0380d4082c0d00303a054030312001140301c0c0c920342002e4100022100121101d00c00000c01c20450ba50042c1c012030700f80c401060802090a00f41000b800300e0050740201c404003508403910107c820000c0110044c0d18144403204a040f61b203030700c61507440d40700100d07110104e40b08160100c1c07000c0106020f02e0803112400d0f40d849041007014010020030840180c803180c1076007800800800401e0803011040c4e81c9a0007525491f90351038480d800d01801e1039940c2e090303200c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 252180773 1250 252179523 252179537
    0x60f12020123030c130b03040809120d020606103608030304030c0b06040216151a06030403200102040902180d03020c040b06040915051206090d0c210c020a0501 70
    0x28000b5400162a04518000c0c29103841d80290303a40d1000000a540144c0407000011041008010158004242c10301c4160341c070f280405440c0700600e6844103070510040142c1c000c500000c5682c00c01c982645103880703462510055007010306c100d1090741c41050400e400b10016082078003540c170b80c0d0a4a00c400a101200065142d880c01c1c0d100103280100309000184031244a8020032540d0b41c454050310744010210014000d2a1298a4400780e04491a46102d51050422a80d881800c0704149103403400b6402030181882d66469580407100b4410903441803c0229003001c42c410844001d00c00b5002503d260a00142d80d201036400a907056564980760030b2090481ca44280002607011075000d00d007500c10740e80850381c03460120001d10280100c0d000b000c00d240c40c1c4080d008042e15181e07210b00c11510195000c442105c4000011512008100c403020a0340e4082c8200500c4d5901c1001c8800c1454010b04000e104400c40b6041c03452038100f0000c440c0d000134240e00f403100035443c014090340001c0a090a00c02 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 252182023 1250 252180773 252180827
    0x60405010f080d081e0a0b1e0d020603060d08070602040519051008060310180c0f080304140310020409090b010603150b07050109080f12010803040b090904020301060f120201 76
    0x40c3d8908001c403504082003140390110f02804440c10785103100d0640380700c1c0407220b485d040342d80324001d1440b040c086200c1e044d040204121195111802404142d0182c858000d4018035024803135194400303803070359800070110140d60004c10a03010290038521300c0b502e0b01503a210301d0101005070034034000d0009511800d04040c204038039910f540c004a486603c03420154229922500064100b03a512440c10310501d00b4000714a41046910882d010340c00c2c413a10303c0c0c0807125110350358180302510341d006800f0581d00400051002c1c0b0041c0034507000b80b0078001e04036281280b108091030143d070050b50142c00040d807904c400c2810020081c8c0018050001442d08100030764074800401500042e5100e008001000065500c0500c4070039007003e80301941110170725555030248135489280d64014000300c811340d40c03a00e00100700f80c0c40200484003140e00361602d01b42051419020004c1040000d0800c0340d00d5981c41800040001c01c00c01130100821844011038000c6006000142142c1c400191001c0e40010240081c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 252183273 1250 252182023 252182039
    0x303060d0b060307030c06090e010806060d1b030c090605040e06070504120f0602030f0609101203030209040e070609150c0c0308070f1403030714070201083705060405010f 75
    0x2040300070381069080100d5128900868141610b680010304110040000410f40e190005030400c2142d00c076512000040c1e9a070684181c81d80c0d42610075030f900402a038500008241c01104044c0040b03126401c00c0c0417107550780e4812141d0310482c3c0c060400540c6800d020001454a4409c0720404030098001e4446803405103401000d51081d805402c074a2014418004144134400300c010f0700721030f0b200d0011036881c101100707041281d540031500248079000010004a0090036140c43d002251285001019403100d00d50301603002c0c0d04490902c607003055850303101455405040120400500c030645aa03044a070601c1e0074881800300c020015000d02c42003c5001c000600e01d0036030032044a0704580c0c01502c4810510b000c68480111400107007955004440c0001074480210046000e10207030b071641d442000c0c01444003a101d010307038540603020030703000400102e180305078002c800010314460b040300b11b0424030780140b0b54940b060f40b4120301600d0303079903000c000c00d40c10b00d03100d070034090b1034400c0d02c06c0b00c502c1c540025 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 252184523 1250 252183273 252183289
    0xf080102160209070c02040207050f060603030a05070b060111010f0e0c04021201050409140a1b0f0e0601030f150305100e070f060309030905040e0d120216390f0503030306 75
    0x402402128000f00059240b48a112001a20343d40104295518442c9042a41c0d940ba1140c114010501440e40810603603e0000100c039440c2d10591100d9041a0f2640c8500c201c03440010500c40c14044400445858a00280700e824160704140c81300158440350b035007069142c900040c00c12805180704001c0b0903840140042d0041c112030080f6404910344082d40350420064218107600d505500c100b440b0318040146111100041604443c00e03030b60495a10b07400c0303510030861441980c0c2d0f40b030340940110345254880d40200e200081d100c000132521030903100c1240e0340501d8a500c207a1f07803900a4111a241d8088501404403500003810050441c14180b0589200800f02440750f0014035030790782c14440030140a000c80307a00400004100700512110302002940720003e902940c3c000580003080d440f210340f25882556208041d58090b050000303c1a594415240109250920b001403031880b0003116a01400700c0401105c0d502903a4503034070b460451000390003120340e0040f6100fa003050003040140d07122111 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 252185773 1250 252184523 252184567
    0x8010b060d02130b040b070b0a1b0c0c15030b0108061806130b100306060e1f1202040806010b09120f0a0303180611090307170a021012060801060f080102 67
    0x10740143e5600c54082e082001c140d90f50302c4043d5120000c540084c101e2440300190a403d400f4142c08400e80d910140000102e400b507001c12043c80e0082c014213000310740f260303004500807441030841c05602911122101c14458000c3c103c8000262200d100404a5074002989070300b10b14281c0d901d01c02c07420014060000c0b1704004040b607003d1405c003001410584100d4025500040c405009143d01c4080311000501500e218001e00000c90b1054540c0b18642c04d1141200c1c0c00d401500304c490600c14180c040460307000c1450205080c0141c2c003404041a40034041c490700303008005000d4104e5660900c3d0092001041c000c0d0640005908812103c0d0669800403480300c242076454038001601411034061b840c1c40b0081800c01926441c9405040c440d560250002000c0180b8220b084600903a41e80b50002c5140d980e010a084517a04045036140c01800e240b0303030320321201c2c1640c1000a40c1401d01c0c040c0b48203d034006c4e407014009a4641804200000c41d200c5400041d006010080d460b03d40210b124a403c8a87c0d00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 252187023 1250 252185773 252185797
    0xf081006110a06020a0c020405010b071a0925030c0e0c1801050408030a03091104110d0b0a1d0103150204150c150f0e060709150c060b0a030308070908010b06 69
    0x5900e520300206002c0c03568010b0b4030800441d2124000d03240107041b0070392103904038040ca19180010580710b0340c01d0107640ca520343c44156442409010201c800030741002800242c002c4c8943c0055000000c040410080341300c42280102900303d1a40c20404141c428661200714281000300a0098824072041112282c401c40140880e502000e040103c40e41e20560340310740320901020480800c22030381504880b4030301d80241000d0404511902c2000115041044441003c040400004d29088881e0b00300511a20004100100040d0703030b003014003038a00312216481c0410016030b0061041152291101e036100b52000011401d19080c0540703001220114088403003841062440d02e020061644001000c8014514062149100458401004d015034900303030b024500070100080c80c40c40c80f4881c0d4800301e6005298805c946045002c041c1d40b20401000c0c26182c0c16210300b034408064540340322401c011403103542c43c0001403034503a2004150000d207401000c0583d042c0100c1541640d145001ea40e0120300328 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 252188273 1250 252187023 252187037
    0x9060305060f0a06080f0916140a03050304031401050c120606090d1211010f02091507050c1e040b0d050d050d14010b07020a0605030c04030609050102280f081006 71
    0x2210001d180110b0303005840703a01076400c90000c59402c0d4048000f0b401941c0751551200740b40c4a0580d4641c540800c0713180c20b10b034034814034400c01c103020b00345400010201d809842c1c450456100d440e0f89055611940003950900003110701c0a41410092180c142e125811a68136401c102d601101c03d8026240680403a01c070b9440030a9422603a40d41ca0b0707810502d258007007140044080e80741c1000c0c000d46450600c00798954a0321f81e15048004242c000c4035448040140084402c2c0e0b098112700c40140c02c8881c1c15103151007064860000343c2c483e041e0403001d04803080d031820b07100c000b100d0401041e078988141050240f820010150300050001602120740036050070002d840e07800c41d1144400400100b144080f031103510400000d04000d10800034032045000303581d80409940c84a8050341d00344410760b516004103a0411003000800e174154807803551144580005403401e0906a01c0d110030000c50341c51070202c1c0c1c00182202055903001500300e08620010308081002d03142904907900c9005084c8a104184440 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 252189523 1250 252188273 252188281
    0x906070c0f0609080903100605011710120f08040e0a1b0207031403090a0b090315090d0c02040605100e03010506040902010206040210180828111003060f030506060301060501050a09060305 82
    0x200b5017036403034911024044580000186081d05d001d0f1480c0d1003038501041c91074501c01d06c08807528803400c0c840c00d0320040c0180001c0c07034151080d0102c40004c0d82501c1404800451344000b407045002000100f0308c985060100d42001c032a1071084401484541c01480c0c241c9019030503c0d40c01040c61801c6a4000030400404403401034040c1c214030518200503400f6107504000b01e560a0380c5d801800031039805030211078a05000c41d030384400d44003042c0e40f60750b0381e40e001540b10280a441030641548842c40540007042441d41c07540840c1000488e040f80801183c0a241301c82a5130409129803640000c2c111001d0019146a4001039100c84002d0401381c081e10720042d4070071703109002c1d807030713641074038000e0919410602d0b9180c0030203484820307145083d60848a94800028a010041d240c50551500300c00100002981c0c1001c1180e00f001900702001899180da10000e0b81d0000f6440917001540203130f01030701d1140380441c03c00d421145990022414868180f08003617030070b07038405942401d4480310300b400690b98803 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 252190773 1250 252189523 252189533
    0x60c0d031e0c0503010806090109050618120a1e03180f0f0209070c0309090606080a0c0e090a0c0908030f04051c0209130201022118060904020c060906070c0f0609 71
    0xe040844500c807904140ca12081c0d29031241c0118125a10002500d14588030000740c1426141e041c0c5000e0025404080841c05c0380e045002820146a1108111200c448554890750a1600312200a9010440840400ea03100141c4210350021120610301000581a5825154406844001c1c042c0c000c000031044a0708200d80c0600d00e03240c0c00e4008210301c9052800d00c0d402401074000d0a801c40002d07441c0c8400003111603444c02a0b40c04d0b80d0541d1111803890782d500c03440c171004215040044042044001c8160310545640c00154041c5d110102c0c04210b1804051000d80650345c035520a039240e6000b044514018420a01510240c0c1d904854402c032012200841500300b035003000300a903100074100d040c410500400501168514400e80907604862400c2a03801c1c8076540071140225203000400000b6007040d0710050100004600401d8241000c21340008201282c00800954007a5482130051058041040010551000d03803413400c3c038071075030142d51140711990714200000c05858070380c500101002 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 252192023 1250 252190773 252190811
    0x10150b0c010e06040501051e07020c10050702090702030a170c0301053c040506040c020c0f04061703041d0c04120f0204020712030b030a0519020f0901031b05060c0d03 73
    0x1440d00b0881d0842d08181c1051802020140c1d20104088201102031003948211510030388210000e402030141080c010303060200e02c0c040c1d4140c9500304001041403800598441d0036041c02402c10347d00444d1940008030000c0c00c10501c1040e6141146559410801d4a04a01c001c41341900e205480c01d20b2000c0184007800403807102ca1001c84d00442030112001c4800031002204030a180c000c9030b0a000c25108c201c00d0104442d000d004110050708420280380c0f50b0301b80342d041c03500505400742000821556802e10b10908220b25103a0b0001500300007800c0040c40b00d0306003000c40e410021115485c05003008041c05209120b01e124500d00d00c1092070b4140300380199964455007098002e00290764075000361808210b11030a04080d28003107450f00103400d00e2400c6c001203e1000a46c444010301000f40044803115100341807423030803a4050700d4400c5454440d00c0c1e624009009520404603080345003802d85600c8066160380d00024001c20741805400d0300c81d0b40005d81002d07405120309002495540d2010741100705 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 252193273 1250 252192023 252192041
    0x90102072312030f060f010c030e0114090a0602010f050114091602030f040b0a020106151202031504110304050d051204110a090218040b19030215130e04030210150b0c01 74
    0x80b0044100700310401811004c61107100c003124604990300028005441008070b0081c040c000414444c1c40c40c0342540112440c0c9040c0000f007140c107080c0b2748000005600ea8000750068030050f5101c20b50000034801c18013070a80941442c4690003510301c00d600115807400390007808040701c1015103002604d524000c0c01100c80c0c620b03070003a003580d513903450340d42804e05948403141340c41c01980f070b14cc000254505020700945000500c1d640e425100640d150020010350805055140929280c6030f440d004e6a88030322461540342d101f01d48240e01d03031419003462410719819034014428440c080105120b103001c19240d056100360310181c501510203087c000b00d400d03001c03030f50880e215603840020706044601444200260b0a6021102405030010840502000516110055100c0d6000071030074070051500210f1007000e06041010f05040c1031503444010100600c03a844420100c0704481030006255051204884c80c0034407c1c0240103181c4031203440c3c0c07080340d101e1080e43c2c280380c00030400c8001c2180a401c00100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 252194523 1250 252193273 252193303
    0xf03090906040b0f01390b07020c03030306040228090806010e0103080a0c0f240c0c021e01050d0504080913140a0e07050d0605060906150906030a0204090c0c0b0901020723 75
    0x150300d80780001c410300300340e035286c0c15661100601c0000343c0aa10026424814400c0603000d18195140c1c501030002a4100d80c0303452980012030086800c3c203648405002c001078803a9078038001c50f141b40c03107140c078101401a04108541c221403001440403902903030071241d080c1c10601d041d0011171000d09001d02100b10606004001072007000074109103a41a94030390f012a00d071610208441c600240c02134420016481d0025005400781140c000f0884003c501e40d0320b6200c06040107454035443e0f00d018012113900320750031103012001013010076050414040c000160341005000704460610045201d851410050100c0405078031014880f11190081c01684001c6c500600740540c1d1a445261120140808071080b5006801c00710004807a498150050860703201a101140d1500d10a01d00380406684000c0845020603020480043d0204c098810b08020041c0341e59412074003d11440c10490350100600a02d009a00500400d804510702d4880d565440201c41440b07905c102244e8011404c00388c2c102d1b01440 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 252195773 1250 252194523 252194597
    0x1106010308031b1204020f010207050306010905270708010c0516020f1f090504110406170702120408010b0f09150f0d02091810140c030411030f03090906040b0f01 71
    0x201d50100d011813540120720072101300600061080049070317204014414554554070030001040007200507030010340c210401c080f40050035901c2402900014544140c10f0850368880103042040c1c0c04288102000c0c000303245840b9203041100351300041703417000910b0040c3c41144000003110495840c215030326000121601c0000f480a036912002d00038034464402c42e4012420070015642021a540454003921480d0f207900d86000b030022900950001c00800c1d000551041d44600469405480090001803e0b03200022602006107002d01c80700107500342007203000d011010b040c409802005034519003260300c203691244003688058001038028082c0b20380650000000420700a82856000d40200f086181c0400c85445103c800401c804a0f540c03503a140c00b03912001f902003003038100744070006c40d0814080d484c0010404190000241018a06505004030313620000390f0b0f200358189085001d17840201140c0420070100003802040c414007140f011700e0b0410080c1c0380384a10b00044602100c00a03240c982400c5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 252197023 1250 252195773 252195787
    0x120c06170a0c0c0c0b0706060902031326040b0a17091e12070501021209030f09091504060f050a0501050c030a031509060311090a0b0a05060f0403080d02070c061106010308031b 77
    0xc03e680d40046c4058801c1401d01c100032806180d14000c07240981c0301240665807104a980301e1007503241d00345200004404d64000e9501644c0000805000035010244e101655601c1c102c4002d042c45809600d00c401c0e900d15201000111740002c6404820200062071226081c098400594200351480b01c0b401104103011600e501444015070161418110360140d80c01541c80c1c41660750743d6400f0310800000e042c403080207070f081e0714140a01c0160700044200e1095030314600a03000981607902e00e03004034007a202c01040402c514640400d4850007040203082c40342c41c201e400304205440340708491109003455180c1103e28414514040b030340008100c015410010342d03031a0328180c0844002c42400301c0c40740c00c5400c04550b40c20224865004604401048265101d15260900c0394907002a10041b0381301300180000000300e65510020301044440340c4005a0710701d06440c194010b03800701d03080081000703001c842e642e40010340062558150b03034000c2101605d07507985102103060044108411552203501080c84 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 252198273 1250 252197023 252197039
    0x512040804030b0708150411090402030412030606090308030a02180a1d1012110f190e07020703230a0c080c011d0307060e1207120c06170a0c0c0c 64
    0x40e105580c070551420300b0316250f45804031a40745c0252595440e0104400d01d40c1030914142e0711101e030340c6103205070807428840014001412604100c2c0c00380c034007910b5104001c40e00d981c036100d80d401500c42d0b4107200081608646400c0d0071800b0081030403000035400202c0d103801246c0060340e102c070418000c20211525480300f0f1030502002c82c1c1500d98070900300c0c000100d020001440220000c0e42e11421844108001540743c0d03441c0c00c211702681070b8020b109401c00060648501c500c44100d9800301200d10001c510b00043c0d6404c050000f0003010445d0003c8205000141e00b0200300e20910000e11344d4405020315089041c1c5c1003290240c4000c2c03100320150000226003138003088101400b54242c0380d040364402e007a03203690019660b0f10b0340c50783e040d0400e400c00d001c16800360829400e421405011459000440005503203806c0090b04420612451701c0c0c1c112040060300351061015281c40d00d0151084901e0030070500d00d8403c003902c4c2e842c0182c1c9075111288007a00c20b0440b90f01d030a4010851800e903507952010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 252199523 1250 252198273 252198277
    0x3040c030f0503070b0604110d020d090615060e0405060102150702070801060e09061006080604020a0c06050426090d0308040f1208180303010b07230d020d0f030b010906030c05120408 80
    0x421180c21168000298187c6014411400c100c488524110b28180340b240c42c1400a41c4400164040c082da11030f50400072070800c0c40b55a28620358100268941c608090307001d00064900401c55110324244801c10100d030361701141041c509040020046629107036850103a0900b25190000011503280100020300700180762011801a036001040d280c4540340c02c5240d034a0214680982d06c0440c5d5000003040341d60500f98000c2481c1c4281c0d107415110280e040e540c2030b09451081d1426550642c0385015151202d0481144507000503814801d2482e1002c100c01107404103003044006400d000c04e5000040a20a01034188514a40e004010012080c20301d0405000080700b950f118204500602c141c0c2d100c000000101c906940d5801001814008039556a0360881c0707618190512501c0c20034410000b21904000242a150a40d0042d00f010007045000411091095940608160900d0501c030380d9a40c00c01510020340342d00386000b2408042c0504107480300d1107135160031b00188086104000c20b0000d0500 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 252200773 1250 252199523 252199537
    0xa17030c0f0a03030b181902041a0702010801230d08090904030201150807030314090d080705010f0f0207110405040804051c060c080702030315010210050a0506040e011b0503040c030f0503 82
    0x5081050120031006d002c4c1240100d4039401001890b8004a04401c941e0b4001c56403405a244002d807400344c171000c880c1c01c002a8421a02000800412803000f10340c0c0008265000d030540040c0729222030415252480d58140d6010042d008003200c520901c180201e10049035030402024260540905092500034008c101c00402c07036644003500a80031070200d0300403500b8800c5a406030742d86075103051159800281a030103000c0b102d074425011800000080c411101424595010380b00010f41c0d000ca04030b042040d12000798802e12018410845140011501884132640c80003c0d240000c4607550362902904138450b81e0005507100001040c040000e070600c1e03001000007403181e0000d114403001c3c0d180a842c040c0007542c074180075030410b00009580e1a10320101380d1800c001481250010059070380718408030303401603ca9900d181d44032010085c1c103043c41e010305013042001c0c800801220888203d4000d041003030305100d400700500080454184014640710002a41d000b0700304c03450310115898100d55907071100d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 252202023 1250 252200773 252200777
    0xf0a090b0c100c03020903032215080a050703060312180305030f071104150303050d110307030603050c0a030c05010309020d0501050a02130909051c031401170106080303060a17030c0f0a03 82
    0x40c03c114140c1d10074004d0b901c90042c0500210304001d00782104040c1c801e00c49412425245254074000b503420305407881d20306010100c4d11105d58a003022404a0103a650040449040c1824000208001031004091018098040c40d181420f0304c012103c520300c1540c41d9101501d030f80b001007200c0c416000c1050082c001948622010102e02c40541c05100580d4410400ca1181c0c20b80b01b481040800d01940040c401707000c000d2000240a18210141c007110b4105441c16800a85d5030343c0c0601c208070f02001075404880044454204d0315185540e40400c404250007824100358907a2100421925806020f191244d408002442549007800c2c9030130094100380f0a80451240301400095141c1c0c140c4101d880890308070024005d10306c48041d00e0080140340c181c0d01000c0682c0c69000410452100201d18060605c4000800c0101510000b19095500035004012150410014460903590b007410800c215245903c002c4842c40c8205c00081c1140140120b0700d94038056015100030303441011401c050264440e07 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 252203273 1250 252202023 252202031
    0x8030702010c030501030218040807140c090601030e071404020c03030a24060c0813031b051311030a0c02070b0304060605090a05060306040201080406060b04030506190507050f0a090b0c10 82
    0x260b04030140d42d002e21020703400c14034000500d00a40e00700c118050340140101318152602800d585c0301148503018404020303850f0030010000095140103400d0796008802442d0502500070010030594580340184035502c402440203006511640351601a640001c81250a41c0e807a4980052942c018111200c1c19002c9411401d021146510100210006540d240d80c0c440c0380c41c900703540e500050360740200e89003401008664000000281080440100a183d0284c00c48503240750009011000b600c140c11542001c1c14032803901150540c40c81901d0703105102c0e4001096850a1a800342d05144a54000c013402075000810441884125080303042280c1080c1c0e041c007001d0365141280000c46100b60342103a40354222001180c00f5600c600c1219410502075000058140e640d52401c1500398056401107600ea0011401c010303100e101000e4840713003400880b40038801c5192401000702039110b00040900001000308072420814030540c151400340140c01e64440d516000d03034640761350780c0700d080343c6002c42c690130 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 252204523 1250 252203273 252203291
    0x10090207050f0f0706020601060c060213030f150b011d04020c07060903031803030504030b0a0b1002150610210e0a030e031b060301090b03100f150e04051b19030803070201 75
    0x3c009940000c42c0c05960241000d40d082100c11541d003c401d0005032004d45c1c0901c91030401c001610610402580305842c5034181000c280381001881d0051b011000c090303450858011406d0340c0042c15039408044a2624440003540000014000d00480306041414490b6106c04100d80350080580c0094038000d4072030300349101c3d209c40800c070000b50500000740001d4084c8010400652400340f1150051800340000c507a540c00786001c2402e5140320703441c900060380031905002c01c403002e80035203d8005030159105408040b2040010b0211054917810f0300c07002a02040102100b1090340c080e459103503960381613442d0300c00b41c4e00340103140c4040f6130b0300d89211f0b000f6603800c5c030b44a419400c9141180e10001e003805045a1800c001d0900400ea240c2c84550903001d2079244030b103c0e048034841c0741000403203407400046064050100c51703210310382034110010801d0800240404600d000420303140c895090510114440c140c4e8020440085411900a4907980c0300745010040050b144040c601c1181c00b030f4003c2120f103007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 252205773 1250 252204523 252204553
    0x706080702070806012306090909030a1107140d0c03140703030815030607110c041103040c06020307050a0609030c080d0504060e07031e0f02090f070e151210090207050f 74
    0x4001c1c810540411400032100010030782207101c4100c034460040640e2304000e079a901084941d00100c511340c07000e40000406810554000d84891140c000d01d10017810224100b08225003da81e0410388a88207100c01c2c001801003050305200440a540e009440c41001c100d85080e559480c840c90000303c000c5411b6000081c020f20701a0186000c011009005021989600c00309031212924507283e040c00d40500038510f481610b50b4010002444488244999240b425003001c1e8140501500800119041001180042078000a900001da50408000a00220f45240035181c80d00850f80c0100142c0c400724404903003075050361159200318042e030014050340d0b524070903094880c0c189000c0101641801e537044520415040c9102d07014911031000c6100d8007049400148042d01c086440400d9020103408102c0e906520034284903002209490303401c41104020103d00f01402011310b03606600c001f4800141541d882c80b1000320081c0104801195217500600702a03441c0c1081c4200c0520b203200d42a40c40030400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 252207023 1250 252205773 252205783
    0x6021309020a0305070c0f0b061201061202030115050922060e0303040c0f0803041e080102160c1401050d02030a0b0603070302130b130e07020327010f0c0b0c0a1107060807020708 78
    0x1071f444410301000140640d0384502d21003014103070680042118408007540d80d000d101d041d019001d201c000416001c0305104160940301040c0c443c00a0300f40ba080100b19648541e5031442c1c2040081c44441940c0e0801241c07641d400301e4005025041c542480c508042c409800300c000d5000d54021004031010317940741e003c4080f20708a075202e054104c7c5c3c01080304214201200391080d203400100301d83c0d0942142d860600f0b5003660490a25005114030140a40c0100006c01c11304030300500d444048007030303010b01a00010f81395004144c00e00b001e1350b80001c00030f002404a035000a10301200100100d4980c03c1802c0024002d41003103000040c1503000c0d00c1e001c200682d600b82076481e02400d025210f0700c3c00782001c5c542020803801038208000e61000388514003480145403240c0c1154440001c2034229803642c6400188102c444502001c14001c0905d0000007058400c107402d40e128100385c040e1542c0c0c0480c1082160218101d00180006000e464004152076910500582c09540a68222068691220051500c403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 252208273 1250 252207023 252207047
    0x907030b1e060d0c050702031c12050c07060e01021303060509240601050705070810470a0509040803010807060503070e210604050609060901090b010504020706021309020a030507 78
    0xc1a400c3c8a100807001c040d4004255001c601d2420f941407903000d5011a10302000c0b4054540c0001100c40589200c0c0c0d072100b81f42124100d1001c0c00d0000307081c64103010000e0300c1980005040e594442c0542c41c00315000350101e90441114460040c041076890418a00825040d928900d883c081c5031705500003400851940d845907500d581c000c0042e6111440191825404000d00b203403d4042d01e00001071ba02c5081c050b141c3d000c40c00744404244e5088100d464040384801d4616000c400d602c840d19032a000303400d11180180254400884008607240c80c00241101d010f0781d01555000e50a44100410401d88401a5048070301c0282142c140740d0f1601c1c0260f42c1400100c88240c00607103614000d41240ca0030010080700392031541000b59031005407120346400e007902240c06035016481203050007401001041307115480b034003d0008000141d900da4621007501d1041c1b060358480d5401141d02d00034889660f0403201d01c010320100e0000e42075a1140b098010750880b14a2a012901d00300004e164180544402540 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 252209523 1250 252208273 252208279
    0x605011409030705060d0b0303030106020a0501050f0f04020907050d02372321040c061407030806040617060709050906130c1413031b030b070f020c0907030b1e 70
    0x440341c2003001740005900f01c1e0080c00030301c50325000d400040751000d10066018080c150b010301101303012414010300303444020704090071210565041000c0604802215074009504550f80f81068980160072034450254540f54100c0a01c00141221403086400007040180065500004806007540f490b0004803003814140010911080f481d808200d55040d00071009041d040016090003000e503114150014101d03079007800c419040c42030200780656000004001c0841e4a0800719142c45100d0b410030710f00036402c00030140841c2c840410841e1f90307540c008501074203524588280100390090055a80e190680300356011031501c00b00032505007020550f0510500b809080983c1002604000d10003c1035294000802c1000d51501c40c115000c84000030410300d04500c0ea11031815041d4102aa0201c1a200d07045501d82c09440e410000155070101d00d075407041e8076060501c2441c518102c20b904149450f61190b134041440401c02c00c1c0290154014580b018040e541c00e00748911040c80c99400c12102e04071564 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 252210773 1250 252209523 252209533
    0x510030203011406010c0f0507090906020429160212240f0705040b0f090a03050f010c020c0d031b0b01030b0f0115081b04051c02030c2e110d0201060501140903 70
    0x101040e4441881c47d0514490011568919070b107801070000c80c0c0604c031003220100c2c4c001808029441c2d554040450500c4d941010703428500d02080382c018103218010120001707001d0391035044195580c00c9038100720441098140c82403400309041d90017440c1e002c50560120050204045150401055940c0c0d10a91864603124606824005441e0b180e8000d4100c1144c840420405400c094841440799001944030384000c2c000520f12074240c0d800c0d84c88800800d4115840004111543d64603ca045c02500f42c15040554002407824510708120400c140007400e40d007543e9000108204104c030700e40c0e00c59078485031103442c10b90721210f0b460042190200d18030009270104010801e68124040b1b13800100065650716442c140e81e410208100503a044805003003420602c2e462004e600303040c00b40c06201001101c40c01c00301c01801b20071202c42c009001070110109480c1c08450081405024a049101c4100007203403140307041c5500080c00f0301024043c190020f508442220100d014030b40a441c1400e00003800f0702 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 252212023 1250 252210773 252210797
    0x30201150609180209030d020f01060503031e030a02040e10050a0f0506030a050a06180e0d0c020d03030e010908070b04050f0d0905040506060409021c0e07030c03140c04051003020301140601 83
    0x9150010422140f10a0075420803864403195000c00840c0b40b90344042c1c02618051490188050850b5010303844180603800401038400001000700c88010415000b0041e2a200d848035000750300280a190012488070b11044240600c96500342815021250112078101e0069102c01c4c0841c0751084e035209091f0004824000305100d250369411065020383e004900061072984c03060882500140e05515450352030750789500d600714034824003040f58504003504000000815580c080f495614100c04040d0030159030b02e106441400742904240300711500002c5040d181c101c5414012000141136400711040e200324440d6201c0010007080210107068903803200420301d8070308000d0101a040040115074010410000886d9402c260700c068074149140c0304480c4e240700300f401902c1046078008495054035a2180c0c00800c0050320b80c05401d01030781e0784520190428948141003600c0c200c59888140d5100307041904206144058905100482c4d000300c00a000e007903085850070001e403e05954240c00100130340030305 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 252213273 1250 252212023 252212039
    0x170d03060b0703080a11030a0213150f1d0901140112050c0301150c020909031c060312030903180605090f0a23011205090105011a030601020d120609020c010504030201150609 76
    0x4513501217641440070501c21480c0018000680c0103c40300c4007060f13804980c0b46080c0c558400c0b8000605014005840890902c0c02d001c0e007a01007584460307080084220300c4698a0400300304800e000407024100380300a507141c0d4061000d50f10100c21550016002343c4d100100d030002801214020300080084500d1039003403007980300c2000968800c070001d110042690b14016200c4910662181e40158083c544500000c0b00b91644c160007044003902107410a0024008102149410381421040707090001e030605052806031042d111455845550f10041500018a541c20000610f04410221081881503c50104002d8100c1e400d009002c501c620955014000b001d0303820140e44030020505160180c0c16180314810151031040300c0041e401d944a07001000411081444204581400003046055240210000b0341d500200541130042061424480204642c07607403004010381042d003070940d510b03400c0c080501c2c0a004180c600700c005600c1d000c00b00c00521401c2483c0b1040e110709503140c0403c14500030003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 252214523 1250 252213273 252213287
    0x2011220030c070302150f0c130302181b1312051e0109030206160813110a08030310120f0b061f1e0801120807080c0106170d03060b0703 60
    0x20055044896096900301810000007840c419000c16030b04642d80c1c129480c00a051020a90b41540e94181500c184034031001d20b069050351242c500b180860f29414540d1444955018960001c1c0d0046900191005044080c010311481958203400d01506401c850b00c5686051051030190641b600e42040140031804c000c10b003110a650041d01110348240010032100800828003c1051550799640d8a11003010f405010660340040d0741c4181e042d0650040c400a003280300010b0020380502024410802086801d245081000d00c028101c0240395446e4a900d568a5000365440022100d5003400000e481da0040350031030080f5400406c42030104d2056a030b02800c10000762605500044a402d6103c440c0100c8001120311549940c40c4011549191440c0b9140c00c1424081003c014150340140209141005d0845a580d88440300c940d88080c241010f0681c1d005402c600416035007005400518070f500c1c1600b40a407001d1101c240d502515a51400b03604a42542c414880c250b0814041e24000c43d000d040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 252215773 1250 252214523 252214541
    0x501050406120209030c1504180209091303020f0105070518040e0c131103041203050601081018060b12010617040201080a0203060d0b04140f070b190203040f090c11030304020112 78
    0x100f06c3d04400080f0f80002d00120002400000082c40031030300f002007840010b102c2440c04940c0c0300851070008200081847c070403000781403201e0101c0b00c20606082500c2004520f03141c81150000300441c1c10078890090050303011b4580941c80d028a5001205c0501c2e20b4070542c07040d410781800414040b800300c0d06011040854028440345181d44806481702c0100c958002c510591181c140100c03c0500180e01808862000d00716904010410041040c2003400b040d080303003920840c030301005c5200c1c450000b88019103125000711040e0080401d1070441205180640b40c181c03111500c4030450600400d010508070807003103c0280c0050310203008500c030701c0101e42c01941c1045001d03003400d0055003540c8032444000c41c2503904581c40e075544881101150020f1124000503e1a06c0150000901d00202c80c3e085004801005012201020703011f554503008004450082c0030450041d0300c2140e9a07500c05000b0041800e2440c0030804548414206402c0030084a2203698161282d41c01502210200d100601410b4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 252217023 1250 252215773 252215779
    0xf01090e070f0605040e0a1a04020903120c0f061602030315040609020307120f020a091503021201080609010c08190c05040f0f090c030501062a0f06050a05010501050406120209 77
    0x380c002c2440200b04641d000905400d03100c2c1070380c40e880d080d54030313595500050040c45160b2812005207140e0410b00a11848014120f43c0542c0722500000080e00b0600c1000182c1914240004c6030003200c60b001c0f854802e4441c160041d0b42d4265a06030401045065038492040142c00c03c00004214903030318080b05000ca40003038000200c25488200d10812a8016654103000c0b800050170301d00240e503035020380360350b0118075801907003400315101000d0414000e81c00ba007410100d0040da410384041c880d9059030b02a0044002003800d550b514000580c0f60780041c1e40040442d406d200741c080c0c0c65409050303468000c1440072104803035882880c440a00405c0400b0505c02086000c101c0001c820341c903c054203015284a064018002d481c0c030031032000301e6540712414814182484010041d4540002e84900e003214080c1d03540305407660100805220b141240300003042e11410200260038009198046803080d54074010070400c1d42d0301c900c019036050081e48180700005c0d1140c0082c21050f06142c0243c00501e40103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 252218273 1250 252217023 252217033
    0xf0309080405150c071712090f060301030c1802071e020d060c110c090c04050613051f0e090103230c040c05130906050a26010504051605090f01090e 65
    0xd44009400403480300d0150f0756110703000c07030b0002d1090014018071008181540410000c1030400110584038288003069444003840411003020544502c101c00c80c03048801021580d5035a12841c0c52080c00d0902e000b1503102014003540b2042444091003201d140e150486014014945e0404080485030100e0744100e030003200d04003840000800500400d502c40c401d60f01c5901e4040e20300c201aa03d0003a01b1460744e4800d4001d50305100c4018800f8045906546003640c0e42982c41000d51820310f003800245c0d000d560086104171180c0d804034a00310060a130400700360794000c940154101005a104000c0c00098032012480646002200c00c0305070140d404030202d130a88808a0b0134000050072680d05402d01e20129200103902c03017600100341088400303072000207000c014450400c0040741c0f051180c0d00480003400004600c2c0d4201612143c2594000b036580070081c0301c2e51419142c065103c1d49098941e0160203245240400c00b880c0500c00300d0b00c54401102d0000080c1c0c60901da201c058054081c80b03950600603 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 252219523 1250 252218273 252218279
    0x504060902040e06150a0b0d0b18010810050105040203040209010509061c0c080607020f0604020f120d110c01020d1706010e09010e0403230703030e0106121a01050607030f03090804 79
    0x140b4024290a4003c4102800c0d0501d0551054440014040749451160703a0044042c4071080c078810a072244100700f030800040c04ea0545001c41c005460310f01c41000310076428000050a20000902e04200750641071003400243da036401448186d00054800035881402040103002c0d604105481544c00440207044a004040c00400c403040c036074108005941700c11340c103c3e0a110000080000c41d070010084e100038210380c00120542501c40101400084c40340b40340b0002100950341d20341e8140d41003110313130041c0e881c00c01d60000090403641c05251044d0190092002c407000541c000f03e4031a640340050348a80c40040802882c1880f4000000c0485040c84003a00b100c8000d41c84150300c05001c0c004c0740c03517600780f03500b0300c2d0038080d000700c0e9407402d032a030100710a411141503409403809841c2c03016810f09000c11015079454145015020305d8011400c0c0280455aa006000c400000080c0010b018518603804d0390b215001e00c856071092407405000310b0721502511185c01c2c8a0fa1120303103c0b0b40500800790505803 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 252220773 1250 252219523 252219529
    0x91e050601210b100c020306161e050315060f0f0d090503120a0f060510050315060a1205130b04080a0c02031e010e070302100f0c05010e0d021204080309040504060902 73
    0x250082c03615403e541e407850400ca8203010240005200c142e051032850000d003540000e590369401005082400e900e4400c101215005881600210741005103d40c90140d4942c0d0003002c54008440d12003c0c0c100300d02400085007041c0c0221046d08154201325032034404014000c80e455804070420030130702540c4400b01d00104600b4800343c81300c41030391101040b582c01c14440380000e89003c2495215000d00e0010304101039034800e002d4141c541e686082a540b80d83e02c9400c8803c9c09070812801c035030401c0c4c0006240040d6035011541a0300001015010046515a8664100b403c2c0b02c00c0c20040842d6100808500402d1400000c0c1071103602c140b4001c241d000690340440d00706041c40590074440a00f46003105640002800b900201c080d5100041800a107150002140d074800000845c0c1441410804050510f00c12800c03408107a8129001380900494001080d5858601610719401801200040c030801138044e011141150903c80041d0308024030b420401008044c00741c02200c201d82d44040000040e1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 252222023 1250 252220773 252220817
    0x8240a03050a060623010504050f01020c030601060e010306060513170a0501060e060906060a1409030a020303040305030406090f0305101a090405060a05090d1205090c12010e0106091e050601 83
    0x68440c44020841ca0700e03000f030040d2081002d0140d40245c0032540b40000e10383c1d030702000b41c50880304111800c6541c0310788000141d0414820b140740f140c050140200201b81680c000f660140201ca003a41e080080030b95404003202c16000c2d648039001c114203c0c9800308082c4282c640d1401c1869180e030b003a200380c135150350f80b99821070350310758800c40021481c1000c00040b03203011100c0d594410300540b1800c0c0340445203000100640f4881007007400017880490522440d407002c0103c1e607003290340581207030307595a141c0c204655250001d100384000500c0b414000300389401250031a02c2201d6000d0004c0c1125900105d030303c8080d0440f400902e6400c4207a10003002980d0398411000d00440c0100094201d504010980c0b40a0b100c00030808481c5501003090814495400041c1e80120f160160001600351030b08203256044c21118280554001205040c1d01d44172031040d403154503483d4140c802000740581d0b40b03050368203030f0300b1140710303c030414911400058180c8026000180d00110514210210003081117005c0005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 252223273 1250 252222023 252222043
    0x906060c240103030e01080402010c062007060506040e0c0d0f15020301170c03010c12050402030a02040e0618120a03331409100320180f0708240a0305 66
    0x2029101d8010014190048405038500c00b0038a040503941c60250006070141906040003450241d03107401c10b10340b0402e0a045590701d103001b00b00d003540d101c1050803d14050700d0191101803159241c80340e0b4203051500016081e40e4803038007034014080940039032900001d04102d940e0175100312440407445040d15081d0300c015406010104d038100000203464007914035081c40c42c3d4506020ba0300d41064000b2442d0428940003807520202004501b41c2e945101003824005100e200942250500d0b03441a10800007052881c40343c81c3d107481d6482456941d02007541d41d41000c020b4018908410018625800c2c481d4000500c0c51421442c81c81501280d89002200075595015401300808060f0044c401c42070710414120160f1411640700c82c0c28181907070b032011200b00621004045175462050417440c2800f13440b503040581c0c0024030780c40004889000022201c00d045440c82364034001500061042c2d805420301600031058201146aa0514203e81d04c90f40c2651410b0a07a2110800400000092080012001c0c0d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 252224523 1250 252223273 252223333
    0x9011209031719140108061b03150d15090203190f03030b01030e070303110c01090b04050d05160306060603050106111c02070302040e010b0a0b120402060a0c060218010f030b0906060c 80
    0x4e90304d400c01d150304042018106910440f854100c203095000004140c03a007080d01e4066211462800c1070010319005501000204030018400000410080c0365000d607070910300070f90549840352411440b40700001c0120030010710303000303c1d0707400c2c00c0c04280309a0241146000604001901070064920580740040ca544200e0010b002201146030300766003440384500d0031801307080030294241090513146035800741d401158060320106142c0c40a0002c1000b82c00700c000085800d26192640b68202030010700018002c030404641442c0001510b07900c01c40d0808203d41460019091110400070903400440d1202c0ca00011849141404000743e903451140620740101300303000041150012050282c0241c080e8003229414200707000403e04003112200c0560301960464225039212503100b000c0d40c1008007040301034044da00c00b1404480780100c00560207110f1009881d4845000d142c8082103042d0343d810b10050f908154050045500c506140e4054200c3c44801c2d402d4480150b041d0342103a816454074060340c40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 252225773 1250 252224523 252224561
    0xe0a06090203010b0d0213051b040b2203030e13020408100902030708030a02060711010f020c010b090a020f1227071406030c09011805040507030209011209031719 71
    0x11440c091144c4540c3e0700c0c00381d951003411921500011a0b541c402e407000341565480d03078000780c0310300c50415403541d64100d154991038490340c542c41441d186401401c5900b201070507420014840c25401a51141269070665038101c1074200c0d4011700000058810707103458007540a20005c940c403031051180c041c405818000010f00c0c407071180109483c0000c582d010184680041040c0c0d42d5980d070104c0c110381e01c1480c5003864903d003041d83c0610741c0140980342d02c02c0103891001c114000d004034103401140d01c00b80102d80340e0340551520820002203116040d001c200b88070003040741110a120406030680c0c84202640070304c50908410301c8d0803101013a12212040103030003070700d0240f10202c02b00201ca132400c079003a29014154603210b56800254482d001c80e40c1d0600c954102c641100c6d4044402040c09000301400a02082c244000080c01130340007640c156001c18000600048074682074840c84800c15090740c0c0d4038140349814001c0901002c4080c04031a401c0a100c1c1c1180c0004400d800307513204c8500e00340500c4d4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 252227023 1250 252225773 252225791
    0x203030f0c010f09020315090c030a0f05010b010305191e060902090915100309080d14010f0603180308180607050307030e06160807020709110a0e01170f04060e0a06 72
    0x81d0846a6100c4a90300040c640700000001d1b032030000e50700140580320707003610b11140c0b81c511032039182811010066905100c0c0b07040d0703e020071591001070648603229030000d01c0a80c10301070041d4252a01168000441000c0308444030031908e40c0c0e040300b0700e41c00500c03000748480e141001210007900c2d62a006154500e4002501001500300404010707030007402040442c44404503140040c0e60217100821040425886254140c1440400d02c100c8402c4803604108100b003403c4003560001098007480360881465040d9030000d00540a03000328440345114004c02c1d2824420b035542511801b03005043d5032256040e25034400e0309400708102107030041840307888941e140e103064800102900c541540180c41500403805100d40d200301802110350784211818200c42da55600b000c120b02c3c0c5080e503880b0340310b0942055001d40c0030054000c01007100c449195200404202480c0041d5020b000440740403c01000540008101070112117146030410301c1408082100364940c105d8601d0025030354025152155661703006 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 252228273 1250 252227023 252227047
    0x1e060307210911031902040b040f0e0706180515030c040b04080313060c0b0a1a0414011a040f2c090d03050a150302060d0603120c0302070b040509061003090203030f 72
    0x43c444030304400402010800401d54071280000e078000034041ca441e0406444c26580d079400000559070407080410150302c40c2c11110355600101d2103000701040c1504c1e2010825002450800e00383c2d007014102c00c803000c200e40c900320b00d590700052443d1002d00082c800031a092400c68000c0004103030080c002d507101c004d00d204451081c4125030104041c041024103c0c4006400403001a078000300400c000604041840081c0759038810fa5020645d00030314284000b1400c1c1e42c0008424180e4482c0841140541c100c3c540c02030380c42c816400703046458024590200109888108030f07840301e204c04465501c0c04c8100e81032440c5051810340c0d0701d422940081003000d80c2141c0c54454a54014983e80702030014a46c42581c800c2603180170302003c0e0051034001007110380c100f4240c0019004641c0007107008020010b95000030001c00c4203000c2203006010340c81e400181c0e600710209540c00d0318001001c60f0500d80b00e1004006901011202c44028507031115000c101580d800d0019181910b0018051a41c42d03004000f0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 252229523 1250 252228273 252228293
    0x306031513110105090a03030804020f120706030f0504030203090907050c03070b06040c0201110405060d270311071a09240903010e1902150d0603050102090406051e0603072109 77
    0x40903040104c14015030020761788034210369044981504141443d0b80781d500116000808170f158880e0000010580c80108800000301c3c03a04130303469940d0421a49e1800900102a940252000381c0168030034401d441a9180c16404150400c1c0e06080592a01c01a0b00c3c3d014119000094261082800c0300c08000090500e4081d0342c406244610003000705480345a0412618040e0b4000c850003090040b03451285401207920849079030441d56108211f00d49207421030071101c1030510049000811a81c06003608040c001102d605903103440030701e042b1401101003003c441c0e800c000c10140d408003001c0082d0402c4251802108880240c0c040500d5a030044142407500399000e800d0421110352201040414403000100d4038a0070550486140340c900030b01c8124031318180104c9116000c0140340c118000b040200540c010001c10009075000d00805503107004011070301c8002140040c1521140f50459003500d81a00215400300c00e50500b0f8000c0d40c1c51562648140e070b904068918900d42d500045001e011240071 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 252230773 1250 252229523 252229553
    0x2162301110a090e1e0c211005060f030a270c0303140f0909150a0e06010801090b0603060d03200709050901020c1c03020d05040605150619050306031513 67
    0x4c4c440740c00d0401200000000e0360210035200c0041d041408920f02454820803120600d00e0b41c01c182d8620400002148140101a00c41080110301c5210014441c20b05c8401e498842e01079403038944c10b5669078121780d00900303020001c804000c0f281d412201c454510711004201605e0080640504160071860050002c0b050300307040c03100e611030a011141788008984111180703240e050391060881e4550b100700710031828007030250a5014030310b01801300e01000303010300b81071184100341c2e60070b03200d070340d95a01000c21582100092134000c41d0400010301141020440d4040d030303d11038a050045500000011703854103992090313843e09501302d04004c0100b5545809110303004407100c0300840c5840302d41480c0740d0780d0342c0c080310b9a41c01150400d40011134150107070b03040e01c1c501d0401010510040c81c03d03207003150081034112400a5104004a403243c01820a4820b84040006261101611000d00c0c2c006480d503030030081083e40c2c1489580d5822030001c000300f0f441406000d07042c50154200c4070a2030800c5105c100c2103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 252232023 1250 252230773 252230789
    0x130504030f1d0409020f1f021605010c0f110603090c040e0f07061b1b031b05060f0d02131202090a090b0a020c10090311010e0102162301110a09 63
    0x298907a02c01d1a040d600392603501204541c001008881440410309400101015650211403000ca0320640258107051504080c0f00364262184420780007101e02009801d4004c01e4001407208110000203410348035660790b036a0241d0f05000e61034200302d00068484e401228040403540141c0545145030901380268464801d003038020349604040400340c1641e52074944503400030002c84405651410780129000300110740c01031464101180c00c514203101c01c4103148011a01e22034000080c5050b44286500101035400003010685131006842c004150b5410000ba05080107608002815412042d50903210007404064220444e0148500400c5040034000f0210448581030122082c0081e0084843c1039102d640300b0700040e25030340304c443c0305894201c002000362030b61454138018070145038020084481c1e8103226402401066000c00e401030a07070040d02c000c0b002003606850204001a640a20640201c807102554084000182c1c05c071400c1d00c20f06214800481000107a540b103040c1d0250510307003e0030b051 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 252233273 1250 252232023 252232037
    0xb06040311010f050705031917090d030f1e0504060e0f060106080a0f23013302030909010905060306010f060c0f1103030f040f12120503070509130504030f 68
    0x907450758580039486612190401030340c0c0c0c5028450b107002d0810303914020341140889868094008440c2050503c940c00303840800d43e1000c41003140901011007a10415150000c0d2441601d008420750203403589400c010b00c0e09440d14030150401c032594009881c03d107543e20300820a41802c0c1802401c0301c03446920130303a05811604031070b05550000078810741115440e00e006407596540e109004014000c3d40220540300b420224140006900a504241100d15100e05075100b0390f40c4580b000070241e681210081d1009454001130b01510301d85c00412500d80890041c1c915080300b001c0024101142600420382c299600c600303110b420308081141e07030f01402440b040f04140d141000c5c400f501c400c0f04d8113070003400480111415020001a51700c14112030001404803034403a01005c002d01e049802c140501c2c05140d844100000b0408060f00b02d64548640111868020001c0c441088132594002007241003800700400481e0305d5034480214840d0b2654102400091504091a0007094002c250340c000d4100150 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 252234523 1250 252233273 252233279
    0x60903011a041503050d0e041803020606010806041815091a0a0606020303010303050904050a09020307080c09090c0108060607050c0a0306020703120903080a0b030709020310030512040312030b0609100f030b0604 92
    0x42d0101ca10966051a03d00243c10b400022301a14108071984510150311000404041d0001030181c050402601c4210b004d585140510044506141d14003184030340e0a8800340104a244002881c080d1b07c080c00807130a082c06485418086200b0306540007221941d004000017a042845581c025001c144040c40ca103504d0f45d103009145001d40110148aa5921070105100c90442e50102540341e50203001c1e10740783e50340d0781103050720342d201c8940c0c040c06a4015800682c1d40d40c000b00f06c640c10000161610074203a2207103014080d42d40c0148004540600c00c0119021041c0d40d13a106541c01148143c401580c0c801003494020848250840c03440269810300d510003001a420200081e40100104400500044200300292030b102040e44010345c02031000092100b20300302c64140c4819280035004651000a6072842d803242071180384000b5064001104207001d44601c0703a01700c01524a0004c00b69800e10f415440061034401c0a01612400300329036104c1c2e48807003a018002d08901e000c00b1981a41080e00d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 252235773 1250 252234523 252234533
    0x608010e010b09042a051305030102130605032a030627220602041e0b070f060216210e0109081207030327050606040203190902060903011a041503 64
    0x80c0c40d201038841e0b525260203408048501c0b9905178100d83c00ca142c20603481c4107400c064003c1d40684c0000b00706824054011840c1d0505000311560210b542c146e600f01585002c00869180d0800707815180d4494100c02c40c24048030410300b19000700501208659540d0030f001f000c1046ca4003105900031403034241460504003015a108a2580c0705594592550b0005190141039201020079039008000e6031022078040b401a40c1c000810034444c0035500c407021050b44030a0710050318002c214000301401941c1c08031100040407900075140c0003403070031141ea041e40d031180d4500c4612147c0c004140f401c10200c0d41c4c00b0161075802000d40b07482d8002801c1c032484280c201441c1c00d88800405600c19007a072000035031041054801c1c0e220356200700705030007812000004004002118100090155041d1103a0004500c05280c98804c1f00d01070f4021000c48003211503c40c0715140505130040c01039a00c8a82071007240c00c0740d01c080c000c030705003c5561841c030554124a81c0820084540060b200302042020072001e02c0050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 252237023 1250 252235773 252235777
    0x40501030317040c15020703020f090108070311150315010f08060607140c0d0f060b0114071407030204052d040302030708031902070b0109050708190f0b0909070608010e010b 76
    0x2650072440c10b800381d8841c2000c1140a44550060000e0b40000400003a46540810700800340c80c4212441341d2007080720343c100a4650710038007640b035441c0c110110420000d010040c07110410103020f04205000302c290042001240c00c21110500340c00300b0220b80941569124881c000c25140034100f05013141000c101040142c0501c210050030090010754814015808101c20207650800030014081c070301c410b03c0c0c0108281d80521040717400604091320340d081980100c000701000b200f03580b200e50030b10080d910750041c40361138110325a01c3c40c085d140010015840f180030b59071044484065602110000442c200f545a0784905089080d02496041c4000030b0740c080102d90201c2d4000e80700d00c4d00da803280020501c0755029408907124061002036100100610002c85034100c0e040c0100c1081540d030385480c166030032070707080711141d5030222588241c000600caa507000c202441c8008c0f10020390303118140046048844207131440344640d4070410003046007030b520104450140010b06085140c0e0b501d031a00300740040c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 252238273 1250 252237023 252237047
    0x1c03080601050703120c090510022b1101090813050f030c0f21061501030515061608040816150503040611120a06091109060304060c030e070605180405010303 69
    0x2c001500c2400c1c10b11880c0002180c0d05052020400c041c07403994050304101c014890035018464404030b0f0740b1801e0000c0750144030640440510001c0c000e000d40b90440124001c2a04014864140c900345003a250900c80c14440a2107018190758850b800c0340008016049a2311652081c020250340d2074554401090780741c4024001d035030341440810004000740412a10000507440b42060302468075504100040c2d2601805c44071b2080303100d41d5400f000440980b14200d9100c440c030b0351600200c030759900740b090040481341c0710141c001a00c2009540c0d0000310340d1150340442640d03402440c800c0000c0e4185206a0020410180d8949841c05281006002404001c001a02c0070713a840403404c0e00051000200d034000300c110300b600240e61403d04c0c80000141524050f01d0561454184c4000760781f00c400044404040c0000c1500f400c3d0390301e40e910b01c40030344008011501050b40743d02448011601c20080702c80901103036224181c80b0204500c4041c243c00040350101d10031400c2900403c04641c119140343e0f48 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 252239523 1250 252238273 252238277
    0x51816080c0d140d02010915050609061306171e0a0f081606230601020f1e03040b070c031101090e01210c0f1d01060e0d0c05040f09021c03080601 64
    0x140f410552144003188a0314000380c041c242644002c0b030780c1944125a501c4c4520001000b030200c425070102194422509150040e07615030210703555141c04184840481d0f00c100d40071a07003548804580d44034003011048550a9401b003c6880f1004c00b4200b4803e00f40f4288000400c10140c05455071440c082c0100005001c41031f000441c0d142c00d90718021384810458000e1030a120092030207042884d100103c0c074044080821040200d211988042410282030803e8001016807110b403d02040107040007030001003c51000b0400041d1003203113903026205080c095400d0a0803140b640c1003010001c1d41c1c000045041040e010001d2000e80c11040d186419500b0758a500300511940c2e84804240b510420006031071288810800614085c40c0480e03030059a404102550700c0d4000d5420494601c2000e00403180400c802c12807981080c1000010791505070b01500d051f50805907034201080440c0c0080b0403000e100b82d12000e1200541c1400040181d0760b09a00c01d580031100626140205440c45c00303000941 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 252240773 1250 252239523 252239539
    0x306030c060a02030d1401030b060f0618010905130603031205160509030c0409050304090e0319110a080c0c01030b03030a0e04020f040b0d05090d02070f1401090801051816080c 77
    0x65075882013055545450041804018000403590110b0f00920309120403a03905032000d0000c1c0c1700703080ca22420201514060400742c02c1201c0340c00e28007003a02804002d40e041000e42240000c080e0380719040b80c04c002c3c16035500010514214200184451490005201c2e080e00b454148400070008041c8419641c0c03151810688402141001038104188009619401410503412105218020000b082110350301c4000708042d606c54070156403079006000a08000c0848040055441ea000c1c0d4280c0d040c0000072000d41c1d016400039a0f60284903004000d203e50154402800c07074150396010722841c0c01d800c1e0200d008506207155840010000302040400724005c580101d107164070044d1010565000c0c20004a08276100d00b0200c0351580144803c64400b1a54403c41c11008604c13400070449c4030540e0b280d1000b00030018180104041c0102200004904002c219080041c42c10428810305004418801c203500009040c140034514003910844401c400b60b4030503030100700105001440560b141800e03201c0c41 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 252242023 1250 252240773 252240787
    0x2070b0f031e0a15091103010905251101050c3109060605091302120a09080f160c0801060803040e0405010e0a0308040615060509091302121e01020306030c06 69
    0x40c0c2a6101c02c075140098492031418811904040d81000003001e015040a01506a4940c0b00000b81ca5030740350001c1041c0d00400c0103012490b4260030050b44124941c0d41d0718113920140d442d2aa024000d01c40d0580000c5401741100011350702802041c1e0032001c4088031508000481000980703400c17048120003001030800caa084005102d00100c0300c0200b40c0a0710030840a607458401a01ca54031600d0654821520320f94441e0480c038140c0b0030b40c1d543c0103400078080c03003540d01e14001000030305a80c41c054030038150901100030a136004c03c0042130805100f14404010104c0f500d06009600700320780003c1c0c6141d04104060281d56000410358041356851580031010351640d00b0424014480400300c101c141c0108583c003000d143c0c001c0b04080c0103520811081000c4001119158400107143c050070001075020440340426103064001c291308003444401d10060060320340d002600c0d0408400c0300c2d00e8035410020301440886408100e942661508400035841e41c9004c000094407900280f403481c0c419038011800d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 252243273 1250 252242023 252242041
    0xc010609020307050f030405011506050a0908060915341d01081f0b04060503010509090304062312090105090c03010605090103170d0c02060a0f0903020c01120f0908071202070b0f03 79
    0x44480d05038105d42520035550bc4080c014583d034004007081012503030b40c1d080000c00c0e2000050351846150100e0190660050380654210010303005030038440120000142103400d045480302103114600c10700008224180003c0c00940f00d842250301036032030701c44642e82124159070012007190340007030f00c841c10820040744c54a41118280030b680000c0d842210100303000c03c402d5003000056060b0b070b20885407040d05668100c0ca040d41ca00c25400768000040c2040d0340407840e1030b0101c507031850038560900102c1c02c0c0407156603641c00080d130803107481000340e44510a218041600384100110f1590540082c0070f5542000041003c03690103100041c517140c0100041103c0301003d034203031611404210414031203008240002903680e07200b078900c50b032260302e84101215180254404d489940b5495006850003401e0a4015118401408030341d200d020f85031500308201c840c2d1071140402d0a0b1041c030800d03840f016141080490308692200950543d03208241c280003094045060b80d0480007409400d6517a13a460300c0034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 252244523 1250 252243273 252243281
    0xd0e0703030f2c01140c03070c0b070f1b05101701060c022209020306040c050907110d0c030207090c020123011211180108060405010e061005060702030111030403050c010609020307050f03040501 85
    0x550f05c04680040b81c2d001d40101e000c0000c2140d94010240704480c15165280c042c407512607950f008003564600310109001461482c0a28920564213038460314003a1b541012400000301400b100d00090f00d07400260010454505009024205600c1c01c0408454541d001c03803004c554850414114418294041c02d244409030869003a4941c09801d075020382c01e107403a0550002c10380c1d014091003007070481c0008081c24440d070b00c51220307a000a002842035041c04e903420344a6610700b0400794118060b40401003141620340c024020034540e9a030000803132441e0044101507813070302c2c03c12030102001c0e014010002e400b00300343c0d08008039070004681c000488500d00000d0314140a00d8607003038000c005000004600001164091160380602e000788800a03901e0021511550210307200200918021814009030600d43e0250262500c007400000d122210b0310020f45854104a400f01c00103003002440c000960b000f800351900500301340303105500398140620050103038010001103800c2d260020002030240442500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 252245773 1250 252244523 252244547
    0xc0c0111010f140f060916030b0d0503131a0703020304062a030f03050f0610110a0506090a021c020310051f091505011403060d03050d0e0703030f2c01 66
    0x1084000c0b03640f407082142c070078100d50034141c0d11440400120542040000c2c98400d030281e451841100a4142c400d5000b0302481080681010b00403680000080302000205020150b40080c41a40c5d40382400f40300d50145103001d21740d2164410f110181c0002c1e00042500c06417901800d1540200444110801e00f401d8804000ca03500c910402501050503002059504420030f1f1359414021966034003001c038a4500c0c296001504812440c9002c0c22091041003081210200001911543e03500d83d1109460164240c500902c01e401003001c0c402145050591800502010007408001100a4002035116510031a10700e001c1500c940009041e011b07011401220000354000d992040c0b40caa00b035100061440903c5010040040710001c9034940c0620220b401105c050340085145036101018082c009501c40411404d000c001d02a03034450302540e015003e0204003040003050032a242d0708000340840591109a000d00201c45042a2191000003070042211000352204044c0070075180101d59521442c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 252247023 1250 252245773 252245801
    0x40e07051e03071403100603110d0203040c0f05030f07091a0303070303050414011509090203010e0d080901050c0f1806090a09050402091506160501090231020c0c011101 74
    0x75810a2070030000303140038074a150355143c41202c1443c500348240c40155a52950b4100c508802c03c451071294110706a0f92040c3d41105080000046411090360420381c1e0803103481c00c00010078000d224101070024010034089005105241d40003001980b81c20803130041c058465220b41c101da04010310104660752121029007225600c880c2da0500400401c02601d0840d60110351488090030b501d0305000302c012088680d544502541e20b000f00e45002007031540c40c12038155407030b0041030428141c10300450301c1c9190b20b901c0b6018589130241034542150b03170040160040d204140302240103021480d05807000c45034603a141056814031a03000403260f00800e1745803907010042c0840800e60340c0441d0041c0d4000c80c42603070f4507107080d185c00036007081c4150300700121a000030091256070308804002c003540001c64002c000004e01d0b1580c81c3c01003441541916484040300300520b41072801a800e151614110b45601c2800710309080351809220b49a0840e24410fa0420207601800101c0040030750028803010385130 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 252248273 1250 252247023 252247057
    0x30304030f2303010305061b0c030d18020402270105070f030c0606030b0108010c030e070e06011b020607140c09060a0501050c07080607031b1407082a1e0f03040e0705 73
    0x192424035a1200125200100c61001041c558602c500c9001a101091004405582401400c0c0c090bd4000c2c080345542507030b20b242d01300754500961603510081486c0440a01d040c25015001800c00f058442600e0030783c0c0c108402040b01001048594600008540c0d01d403400e89540dc00c81c5c10300801510158102402e0800020700004042105601681001e0115107040c80b407210b10400c100c0e2640c3e824460011803071440000540c00358030420404008004083e0080103200d02c540100d10141c00119003210103580128061500701c808008150902c0e904423000718132442d044002c81d440d14041d1140c581400781c0071881d24002c01007030013140040c0028108581d0700d4074150400402034802d040003188076910303440c80806120700c154000c610859102d9040703440c11003240e40340410317584040e10a0180d10300c044510913058240c00d1500b0001100d10004280c8203503c03002d42c4182001c040001c007629072281c0c800d0012200080250f07021552142500441c0342e40e02842614284a171420140c94070080d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 252249523 1250 252248273 252248279
    0x70209040f0b070e01091a030619032901081903081e100905100b030403050d060509071101060b0903150601020f06090a20030c282402030304030f230301 67
    0x11001121200c050b01b44e0751400459940c0c010400404041000074820150410005030982410b2101c04a00703a9081081a88581d0300d480c1d009180078490380c2420244039000211680942040459001d001520080c00d9100e2810208010522000300d0040601450100041a150b109202300800382c0440b80b00d0f82540c5080e00c50f9641400250141c207582501c0c02020070b901300280c0340d02009417803185614a1550711703981c905540325002141440062070701c07a4004121901d902441d01c1c0680c14549940b6210105010182e003560010780003890924003c2c01224929130700000c1c00d41158a0094183d0115210680101d007405200044040071340328100c2408904040001c2c0a0807080c040c004030b0382c1c0024044a000d202040d8021099410361244640f01550f2a0500da8110312030060281a612440448070000d02e04440c0d602c44040f00110035088588a034420b40d80c403040004500c040c1d49140b4160b0b8000d0445010b070b4080000b0002050b0b010900d261480c40e041040b80071041a480d101c4d07075 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 252250773 1250 252249523 252249527
    0x1c03030225050607020a0f081c060b030402030c06090d02041e0c0503070905030c102607090302031204030c210611030603210a0f0e12010209090705030c070209040f0b07 74
    0x1844901c00c45442c481c100000b44158030108450b1052988056a50102515074540c10b40c0303030308a03182200c100320540c094883c0302c4c03400344901801070034010002c684900c0c0c9401014201741c005c0013654081c2c0310400401c01c1035542c40700d40c129240d074110b078005130720441c1d4204071030341404941c803c0c08071a2801c640883c1c80c03500729001d98481d22240d40ea00346129210800d0641b2095507450640c1c000c401c3c0c00c001c1e801d850042028011040311640600c070084049490101d040205403011030202e02823560620070360805008a0155904e05150340307190a103103540b0400418154131031104107040d6145606600a0201105241d868021400380a510071105000c00b440c1e100340d401702e00c02c0c480d401c05905e0740c02c401e0500c0402002c040558500b0002c00702819905088103c2d0883c2c10001c25141100041c3e89150312501e40d007003030500060f2034421503030611860401c007401d0b400074040244100301d00f030140102251070641e8150307514045038407103280406039540e440d0401000000c81508010280e9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 252252023 1250 252250773 252250837
    0x411060d0e07091d0d020d11010213060f0f080112140718230f04080a031d101107150908040b0c0d0206060411030103060504020307080a1208010906051c030302 70
    0x1050032641e569100301007038100c84d83d82c66140c45c0180984c003e98031004180c1d01481c0b06420716004000058075000400d45000c03000e1000e42c0008012404201c880c00d00190b100003010340d4a94207091600f0554100344c5031010a20a403400104078150703000620201c0d400601120b002400e85048c2050f00286480010002d029800020296800c00d11441d00002c1ea0181e4418007418400c041140c0c6078030742d0f850340402c41e4064418030081c0f6460741740c0c01403083c0350780031a4054885810040d1888480300da4090080e02d4490765840300042041c44010042120f09040d0781800c1c0301e40300b0018a4013a00e02e0007128034055036002c241112800b0400d0b1085080100340594114040ea095488940d01c0d181044100c82c0030400507140010240014000180140c0c02180c1060000b402c03176007500d558036038003032414511702803c4498100203454610700301c3d00020180d0141400b54818080740c4c2c109000704001456602804001c000201107840606002e64121a100a580c890f02d2a0442284011482c01 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 252253273 1250 252252023 252252041
    0x40f0b0903041a1809060402161a07210507021905010212100f030f02030102040803160b0f0402090a0b0a030c08010c090e01080601170c060307110609060411060d0e0709 74
    0x14418280d48111007450004943d10000c1305404848100c01001c103001c8003c0c0000c0c40d03190025801c10181c401c032064000090700b800c3c40398510300c0c039410107401ea031202c100c07018091078140010900c00d4079650341d4042103150519500200042d4a94407a0003c03403400162284900744d9202071100d44040c032406400610800c0032411210f0300d01c7e2250740340c007401c4000c548100c148024440c2014000600c0440526402c940000c0015040545805049003944e012807110b440f41c00034000c07801c3c104040d21050b2a4849001c00c0c0e40240b40c500758000c124a0721008040b194055501c0c8a22a6150395101811000d150800d4a8800c41c9440310341c894000c11030300503840003040f07009000158111074001e01c0c5050340d402c1006440d041e480d0802d000c14260044510381554040c40411410301d403506409948107004070394800340b130540316402d0f490078403c02510100076074010300100720108020848412046406031410741c1d41da4840540c5000903c5032292012071401070440004038610103400180c01 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 252254523 1250 252253273 252253289
    0x7020d1211070806130501020f040603060f08120f0a0c0c170111030c07290a05070e10020607080c09090903030708060a0303080109020304080c100606120c1403040f0b090304 76
    0x140c50540010582e5458188035005044d40300e080041c41c101240040c070002c0c0c81c4100005400d10709061204c0e200341c7c100350010f100080d034900c400c000c059a10910704008002c5503010b001e1103106001c60a0103071107805d10700c084000000800c5040f461033489940c07002c0d40c010484040e01074a5440d100507202254607218150340c00c22807414000009001101e00980303a01c0f1584e45403140f141d039000c00f84200604040303100c44003d0500101031a140e00d034148604446100080d0038030300060050308030700301602283d01030000c094189940a40004050340c019503a400c010011f40d0340c1c01c44041e240c0c854140803640000c146001d01c918500004042d60103480162079000c01d690b144800e2004440c024030014001a02900040102146c0c45d03000f51b8004c1e0041c0c01c03062610480c580003030b16002c030124840c41c5142c0d440c00b0820082e0341c0604650100c410005c0e0038028441c12810003420001c908260782504200000841c2c108004071403c9001c20b64000304034440d51070705c24100383c4c80c0e070064850310301c0c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 252255773 1250 252254523 252254537
    0x101d04060c09080c04230108030408120307410705010605010804021008071202040e04020f0906061b1e06070f0203040f06030e011103130615051c050307020d12 70
    0x2507140e000b46500426609400014141e21811034104005004071001a2024001d40c01113454511554040725001e0100e58000b03550307507481e20314940d240c4048480302413070700c5100b442030013400760340814801840a03038007080d0001c00045003010000342e14030300d075869100c05001d03980710600d208880c007604406008000800c5180c2c0d90340015035421408450096001403459242c0070703000d000f400c1040c0c0042c200c1c034110721004801a104022684030b80c000c4c684040c0e00320100011807030722510700d908000c400c0e0741401c0282056408161103004072224034001d0030340d6082500e141042040081800b8891a40240349528501c045903110341040e500c0000281204040c404040e0002080741c2c00c850a191007105214070300502100148059440c1070559525010320a10780c10200000e14000c001a0208943c1101c441c6009170441c2d00c0c001c40161430112942040020740d5401445011486008002d20b601200c01d1070004e045100e141e90080d4441901c2c085541808100090b10030380002c0d6807101c0d6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 252257023 1250 252255773 252255791
    0xf12030e040606090512120a0f0c02031603050105091b0f040b0a0f0e130302060609130c060806010905120d050313080412021e0d020120010204082b020d08101d0406 72
    0x1a2a8060100d0099189004200c0701c003223180b04070000c0500855a29041c10303904050f60000341040d94400c2101c0390f1039482c55080c81032280038840c45030480ca4480007000401c0c030100d103861025503180f207035620945100c000c5d0b800c1d0780c0b11078111140c821001410301003065101e8660b0680782e0b0440c002e030b04c203650303008001510034803009400301c0c04190150014001c036070340c16081040c60800203020200c0e1540c0759841b80c1c0003403c0341c5000f20140520780c55110003454141c00061004105500070b62103084034000c1e02c0d00c0c500c1c01041d012188082071a20690ba5074412001c900f80c2e202145000b8001803001400141001c0142c50402c40b2605c22980d121412444d244001c89070240d103c030603036020404006040056024412022200c1001e22003446c01c00d6087c450203003260490341c4901d12a42050710380c0741e40c1046c88180d036090140c4080d41c0c00c00210603268000c1d602c81d041146030043c4906180826840c0c0c00c00598600100000c605060300300c15205030f54030561106440840e041402e212401d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 252258273 1250 252257023 252257059
    0xd03112208070e1003060c0504050301020a02010b270a020c070b041e0504020708090d1e031701080718020f0d0e0a0c080c0f09040213050903040e09070f12030e0406060905 75
    0xa400356030350190b000321329410b68844000074040e044001c030601004020008054400703002600c101261a0000100b00b420b480501c82c2c452800800c0c00c681c03620349101001490701c481502e641000740c4000045c1c076022503a100c035140c1185600040040600403500040780c8281304c94000410b10b005040f00100e0b5501c2041c0016402100c030000d065280c140004115802c02c080c804140c40d0003100c020a10505a01c0c0d000134113031200c0700550004a803c01a40c01e400000e8003880c0c0100281801041c00c0d80c0f41461050404005800100d0001e4001401d290b10380503010a0311030320329410100f00320030303030403451119910080d1902c111002540214000ba000d2004180c081101d00041c1146054580640800592440040049a2001e00c0004104003400355105244c413a44140740115a84c504244a142080c0320040201f15150b0141105101003070441e42c240040312140c5190961175011032805660714004050744d1900503150820000380e15901001c40b4084610541d010008484507501c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 252259523 1250 252258273 252258299
    0xe01090f0c09140a0306020c0d0206010e0f160c12050405030d0e010e040c0c120f1209030c081617190e0307030f0f080a051b060403020d0311220807 65
    0x40c00380442c0c0d03641420000391244001c2ea0f203600c84000d006078105600d9660b0f2008a07040081d80e511140d02002d10032846036010071801d40034051500b42d0030306c289001301405050a4000306040d00904000391021149030003840d1206203035070300050304080240c1007000100289c100703104440c405e01c108007034041024002d01c180c440c0c60206039110841a0600300501028207451562401003004005030030002c1214a00300d080d01d5016660750a8000640040040c000e881c80300200103002d1030035403a440040d400c40a21903100d540503280c551038289541041c180d103501c840c1c8c0a0300c20030820320410215584a40140711803103405280801041d04510201d902c1b1001d000d01c160103074480c030010320204010000d1800f030144101d00c01e02807286943d03a01d234143d4100816031004142d01241801401240d55551000c0d80060380c010f000030314143d1402540d500c0081501001e06655007441015140024203e07550100e0080004403c2220709210540714003c610940d00079004041d0701003124001c00305c0c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 252260773 1250 252259523 252259541
    0x4050607030b1914010203070203030c060103030f1103160f0605250908192a05040605150d051f060e030d1110020d06030c06031415030307081e040e01090f 68
    0xd0060f502c0b80c24400f062035520391030781c0030ba070540c4802c3c0042001a07400301300074000048081c000d000e082d4910b140c085d00d01d181000d120070030300001044100300310000000b500c5201c840402d50084000440c14034051240030508064101c0b41003d017040400c0140307120098841100420b5810a24000b81040358180310600071207070540c00c60303181c2c0c06001a10021003483c1c1d600540e2000000200d41c140c040030b084880c20201c100844440c0d08004500d000d12500008000960b00c10f0180a0842c0858441e4813428074030a00d521b5076040407901554400703009071841d1030f003440107100e92900d91901500135036908030118440e100303014403000541e00c00e090b00c800148032540203110040c0d803400210080c2d0045141c2d001e00c3c0d541c3e65000000310703403590600401880c140d200050541500c041c3e481040c40010810201d00700706400d8080c8544000084601c0315401420298440e050100501350b44000d074240c40341d044001213004a940f10310440b04034100d502c9001c0402240404030380764010350b24821 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 252262023 1250 252260773 252260809
    0x702011a010e0f19090c0c02100815030106060201020903060c040f060c320c010305060f040f090807080a090e04020105190e03010608010f1401030b010504020a020f030304050607030b 80
    0x10809200c1940108024000c01d00000e103c0c880c641c6040c00407801c688440c009195141160450030010f403030191190407010041803078610543c101a4010680c0c401e0a101503504200210001070703292080c0c0d003090790710710f20014001d0040542d9004024044d40005202e9803003409441c0c0404d28180c035030001c5404031089400c8030845940362403001c3e620801c42500a0365180b0700d40d400031010500e903200c070016801c8002d00880d28092056100d501e00061140b200d41490b02c0c0905014141d5681113412462090441d0049603050142c020400680b61b9150004c00c64080810300400304036820000d1304ea001c809a4035490302542c0d0300d030316002040c4c094401034040395003003046000c5032111000c45250760106041c0054800100008a821200b0b658010b0340f1507552100f4000d458221405072040038401382e00c0800181d415600ca101540741c040c400d1912540e40020002c6902d8002c0c00784501143c40c0c1c2003a82d44074a400d0611540750b60382220300100013850108568514644070541e218820880f03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 252263273 1250 252262023 252262061
    0x70b010608060612041a0a3b0111220311061b1501080f120301120309080d050405150f0702040b0102010605060c0304031e2103110f12070201 62
    0x440030a840d5510003910880e0055404c0080c801e48004030b94019014520a04128500c44102c080301d11100d180030700980401c90078a004103941c422407201d5500c03141240441c0d01c0e2071210017940b0801203282c6507001200c65080404071510085c050b009070003510b0a04030b13600c2d0480384040c1c014042125500005006401001c0721400b141448800740a01079400c1e407110342d81c80c0215011920f40b400ca00203040000039141d0050010300404d01c5519a000442d00040820072803c0300301c10384a0205016501d0740610310140321003810b105110501c0241481016920692000c29009103541d0050085034000c0d2084210f081581d1a01070494441c551903107440740c21300342194208000340510306007040c1199211540441c1c150742c1c000007048004c0c45500110303034a078510f180000240211008944007801051301d0070020031030000e20383c50f455040c00304043c1c940c1034400c0300340c0082c602501c0007121918042112010007031410001c003140400e203600f11321195140c4d90103d00341c0c0c00b1410000503007110 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 252264523 1250 252263273 252263279
    0x2150306010509040501080307050c040c0c021201090c0807140603100501081305060106020d0318030c03181203050c0c0d08041401031803030203010501110f1b0f0d050115050402070b01 81
    0x54040a103030804014544186410503400c006015580281c020392929007001513000308114081105960050b803c2d030782072204a0664030b015010000b4118040d0080d1600031100440320401c0d030005960560000ea84080b81c6d8035869056916102030240054521400c005c0c02a10f10b00141075030310407040401440c013a1400c00300110b45000e03000d0000c0740c0c8130800002c60000103c044c0040c5010345000e074028035401040c5540102034a000003480303913810401100490200ea031002459041d00c4d00340c10040210184010511040f0005502041189184241d54420164840d00400004501d8021526005605420004505540d01005100c041c042100f0011a0060729052881120504002410642c000b204144c0030345103000441c002039002006101c3c035a007011503843d0b0890080d000300306001481c0207143c2c2d0b41940b61031148072140354980d411101c1d62090702e50150b020005e020015003001c103242c0300e030180c04000040c42101c0b2094002041c50f0809200703807840190000e8010900742d11f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 252265773 1250 252264523 252264559
    0x705190201021c05031e04021c150c080f090102030603070302131806020c1204060c1e0515010303030c02191502040b04030f030801090203450106170a02 67
    0x152450101d05500481c0d201000000020490410000b001d455069480c6400000d2400782c01001c070070340c9100d8181c90140800358940061800e03604c02e000b40545101c280f10300b4114000c5002e40044003103103082c011410000da90010010f4010303c64000004440c0c5c0390003848a0a03800201c40c3c251b05503005200c100050b20f42071415180d02d40c506540002c0d40e40c20401921118079601500b40c642c01d40002d4801c444040800ca420005607071041c1c05810a03080400080000c407850a0141c49081980040d08400340410000e030074150b804801c0314101c9040f1200d00700d00200900c000e9022920b4102e401085074001b05154460196450514180300100e58031444071004042c00070194513420b100210f056100b0070000c0c03020358040c491b07a544450307252500410600d0144c1021304554014800d20041e9044200540081c8442140504d2404001c240300d002c80b40b640300194a840300703481500f101c0c80d1b0066011000b42c481928000d8866405c9501c100d68030502c5040094125000c51800c0b50070f80c0c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 252267023 1250 252265773 252265813
    0xc01080721020d020a0201050615030402030a03182d170d0c1b0803120907030b2d0a060f080307020105042303010204181a0603150f03072403020705 65
    0x141c4800006081c24580d01581040740c0080c050040136039922001e1040a25008c40b840c2c8410f02e42076440c81c074518160b40441d444090000004042c0300b804001150b540c072040303040c0c1000e011045400c0070314100002141d50815404031401d210141d0300c1c500440c0c2e02d901520080090780c03240b8000e00e641c0b80c84100440d402e86003020180d881072058400c0403c958034840c82c180051480034011500c850b0580010580664040d02d400c00c10380c040d079410070008400d110610b03404a404c014510348101117075288242141d5002000b804188113074100950071000361702010607a00740c09840d0080f1034882c550701d030391707841840c0010780400c4080c0010000d4080002d0301200828032072078400c00b008026400303e800d98006400450b00e560f04802500100c02d4107200c0d086208200c40c4001034181c001d9800b140d80343c0302c040c151500101000c2c04004158443d0390400500200141c12540c030a0340c0c0b00c0d14010329120014016064030030134003011003014030a00a4494541d0040007038040c44505506450b614 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 252268273 1250 252267023 252267077
    0x4050f04080901180509090a0209070504061d01030e060709080c0315180a08040b0706050f070c1205070b09010b040e160608100302130b03190b04061d0706050c0c010807 74
    0xa10040e213000c90a501c4205a072030003860b1000080403100c826104001503010028041410888184410010640e2000021100caa031400101514030a041c0048002c4c004607001142e49205038010310409a074041080030440741002c01340c2e48101000c40405485000c0846100d40103196403001c40c58003692030700d40c441402c000c1d20403112442119550301c0c05580141e8026038419102140d040c0c00d210041c061541d00900007403c1400910303000c240030300f607200500b401500540301e2241c0741010324041c0c81215041d54205411004034030300340e4016400381080103040e40c05182410240c103d07042d000100c42c111039902107144c0380d011742089000c5842c0e0740010500c841c02d400c075450000168a811440c109882d440303203800303d9000401c8052610f030038145140c0d00e1900c48450f0159010070039182c10b00303810a07071286001c80d18410203220211300700c86202125145000d01c001c00140300d900800180300c3c1c60748034002d980300142403800548241d1030807102440420003590780720003000070b0990340101d1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 252269523 1250 252268273 252268307
    0x50402122707030813120201300e07031103010902060706050a0216060212090c0d03080c0405030d1107091401263f0a120f091104050f04080901 63
    0x4124902200340d864044160f00540343c090b8001041d500486030f005d00c00c0094181d48400050903404d5500080050780d800409541c0200a1b0716260003000c0480004034170203e0358a02406420180c030406611441035100407200344a5048208581d801c3c18000c8c4080303150005c02c0d149c10701009840d41e802400f401082e040c40070350300304003410113009600680590307240a61710040c2c4a01d4803043c10000080d015025441d03a41c0100c05104250344c910101d910900d034189490060782d190030100c546c03507016503040a41d02d405005000076806a200c650341c44d24000c3c100c22155100c0d951650001141c15880c100e0400008460040c40840690f19001040a0103c00c0c129403001d504041d03542480d40110240b410001e1f0250117504040c002c41e04030006440200d00100000010400e0003000d00c42d207006501400001c00c0708020221860703000540d0303550015028020b03001a4038040c00880c0030f00015602c00e40c648004103140c482004d003101e1180383d111180030300d00b10040b00155486140d0b0719000d85 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 252270773 1250 252269523 252269581
    0xa15110f121b07030305040806060301050609130c0b04030303050f0a090c05040218040504110112020306030a020d020109031a371505060c0616170105060a031d0d0905040212 76
    0x1000c41c0c02000b4010040d4001d070b403690341f00d504015545080c81c0d00603203914400e07030412083c041695161112290442c207400f5600c143c00071540b40441c4d104101707038444011108040303400004e060f05504900c0c0708642e801a25130903503071800001011104190780141180f0244c0304244820b05280e4014403d10300070000600c188002e00000505483c1c0458003101c00044842c00000696001241c05100e0000e24005508502d0184080b0b41e850615581c0640b04e07808025404c010343e4040c100324000b850b0005016150030f20100c05c40204010705641182c041404015210643c00d00d40d903141c1440422800c4070210303845d181d0480009409001404045440c42501c0080c445e6600c00003420b805601070041d00070303841e1112001c90301d00451218001800032001c101482c3c9250106c400d4151502100d4283e203070742401004800400340150711410401030400c0090403842c3c0061941c1d0840502e03650300f6002a01c54041c0070680c001c41ca181811202804007240500c00950300310588040c0c0c01c0d00c100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 252272023 1250 252270773 252270817
    0x3020d0f21020c220513020310110d0504020f060d0e06010b0325030e0106090501080c09010e01090e010b1c05160b0406110a0507030309060305090115050f03010603020a15110f12 78
    0x11302100e030107036611210342e4026034020046040500c403074180400400d80400c034554015440300c409108400d140400265654001411580c1e0181080c580c8100075003000d4458000e042c440000b800040481e04580c0b20b000e0002400c52201401c4030300c40c1c1d1540c1c20b03101442e5041120300b01d0b42e444600c41c1d142450780f11000041d110381c0910814005140802001c5095450200d00c1810000c80e03800d000d01403540900140400e4a001400e00d0450300c00c1d07080081c45011070801039004001800505070702126540c00d6680032480c810107080d030203000750140c4140307078941041000d12101500c00c40b034004106000400c100750142e05941803040801c41542c200116075a1080c3c00d00320a81c104502103400c06405016a03649445440c1c1e202003201d000708103642d804103541c50999541d01c14107210700901c004202c01501e0a41004004690140141d026a45ca40d00c03c54400ba002c00b980d00002031158020a200020000350303006603001080140c6400d558034074105110307a022902d040c1c0407a420343c00d08 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 252273273 1250 252272023 252272089
    0x203090f0313090506040603030e0907020a021914100e040e030c1c08010b07020a05100302070614090d020c1c05120d0f14100b09030703020d0f21020c 66
    0x10300c903602c500709218100e242001c040c80c00310748020740124080d519100c0c1c2400040e07000308810001240850701d4a0b1240d4603131008a18016000b400250400c220fa100d109078907000c1c029520680d40601d403d9590002c140c018000240c11129410300082c00100c402c1c3c20703604003076000034040c0355190300360303480c0802c1617a0041c54a400c02e8205103400312199035140d01c00394050281380c0580080c0070103070b00e40140f07a000102600d48601032030303208803a00700c40c42c00c01a000741d0407510140e81c032000901c00394a071003240c0039200c20200c410b130710140030b1100420302c042c1c40400d6102c400303e00104105d03240d010100c42488281d0030381c41e0894036071152415050a400c000c00c0503145d80349401d1000729452010042d1401610140c0c0c5e0220422803d0341c082c8240b0f003c218130035400340c1c5d00e0044102d8482624a002a20309503285c1d0010b5048182d0220700001e111590700480f109502407122502e1203030001120070540e1495840d241c0058122401c14005850590100c0c6a030388251152409070031540a00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 252274523 1250 252273273 252273277
    0xd0209090708070f0f090c1e020604050607140304110103090516030c12051c0e2808070308122d0613020906180406030c1e09020702130203090f03 64
    0x10916500c400c0082095400811080001d13191140c1c442500615004222040300018058500c00c103890b00c1301d02e40c0303640c401e141215010000001e20304400900074406510391400355000c0c0c0d810f005801c009035078940911918a0000c2274920518a15904e0342c0740c0450404101741d4043c10151103100c6603002ca0f200300f0a508403da202c1610520103403075072401546002e0154402c1d50000c41e02242800400c8011510b01d44a1440d401181000d80d5120000c071a5a1080081d0b07941c00226a50780444481103002e10400b8056242e031401c014070340795240782d07980c3c1c41184001015800100111381c60103503c422015009046100326150391040940805800e01c0e000c51240d500500c208104201850400a07440440420700d07000c40c503100006c0040340651207072460035090481d000264401c0d545682d07110304011038128a2400c141c60f2a8950310000c5c1d01c039480303100c9440c603000c480403030204003034401c480042d0b40c01015101625403054001c002794200038811345003400b48031420541e03550300b400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 252275773 1250 252274523 252274531
    0x3142203121404150c020c1305070e040f0c020f0309030712030306080d080603060709060f050f0d110c0f0d05031311030114101d060111100903050a1d01120b0d0209 72
    0x3c02c00700000c904000c103004640c45211043c04543c04807e01d01d00c2c5031100f0300c500712055180000420703103030b56148058416084062500303030801d01d0000034203004242c40c4d22520b1410400e81c01e868044600e27001d920750700c0c0101103c15905030003e00c010000c042c0305603100045035200307041c041041c40ea1a0aa1b6040079843c00d1640c0c08203a40104002d824613040c23021550000503410038202807810070a0042454800e00801c2c02407160000e0241d520301038800550329009607a040c2030150703000100e407140d2160003000518069108215290390010004103c1700700541103665001c0c00c0d070b52002036803600d14038004410351b18180041000c07045900c01303010b1481104901d02601d03c0710304044205520000c0c00e544100861004003400c40b043d400300180b1150000004d181818000e909800c89a08000d1103400c0e20402c0c030303d07240d030360420540c00030003400040c0080c0e00c554250f500d00d2150001c660030500062800500c400c0086a076400381c950084e0b1b103440d00541021001900365011a240b84c200b81c2d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 252277023 1250 252275773 252275783
    0x1020301030201121407030e0c06070516050a080606011b140d0e03010b010c11060910080403030c030212040212120a080405121c05060409020a0603142203121404 71
    0x200501c00d550308886180c2c040c0c801e040381002141025110b502c0890405802081015100c40c500e069441c020422101860300c01001c00717035100d100740352617552107501c0c0180203d1906982e800144070b00d80341640004a8400070081c00d059039610004451400c44510f42640642c3c1e5881088046007100710990032311200000106124110086c010f07114141c4050070a00c00d07810400e804082e66800008440c415500058a800c410802d8000400c0c40c0140035000c0d410002450341c00039040da00444040c0658000d03101000103042940045050344a051052007090301d00d1004580107080c816140791084010205889101d03240324242c3c10242c1c07102d921a40041d42210130710090050510041240030110100180b4240c1c5115604400311041c900904010340c2c2c660020381d05484540080900542c01025422041c5e2a10005401404036090b00340d0000c05490026001c030131503650040c502d01c0c6008107588102e0041e90101c8034540e0305014581c9450f103800c10000c0c55101295214000d0b0b01c94 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 252278273 1250 252277023 252277027
    0x601090e16030320010e0c090c0f0a09030311011503033209030c0a050f0603090a0b010e0a0f060f09020d0b030105040c050112060303050f0304050a0b0a1d06010b0433020102 76
    0x80c448044040d00f18007110044e645441e15440c1d500d20300051000408105a4110781140e49485814410303004800b16041d00704030014900009a0b0701ca0700c804150780c801e489401d5241000b41509080b0b450b080761268446501400c2440441c0c081c0d0141d15001c3d040300c0c02c20040027907080e0103815808058006624020000c40e2200591034184521180400180e40078070b089071410000400c9240050130080c01144000b000c62400d000074811702000b0387d04542040503950755880180d4400300d0840c0c03008451460701508903038050050203000111803485400c41015400e01106000a510110034040740035526607801c003003a1070038001c0a101e0341c0212681054071345404000340100b8009051452103610341803040c00000c0d0040c1c00c0c1c03140500342c1c20907140c40365210320b8841e00d012842240585a00030341001c101e20600150440b445004510380c0c0000d1000d8100d1000c0e81d105820300401e041400180000e10040345400d408030f10074000096200c0c0380d901c2c1c10f41421440280155084010707500 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 252279523 1250 252278273 252278297
    0x8040f0f060605010909020c070b030907081b0109170d1107091b03060f0605181309150b06070b0c070501090b04060203040302010605090103020d0609080904060803030a0608010e0601090e160303 85
    0x310f071740c0d0000d19a41c00c3c194649000869410785440341405080c4841c00080301159120350700300444005003400380300312101c0325050003103042d0156540f07100b107000410180001c10251240010400500b021900408107000000c4003070b10100d010b43d100e03c1c030074461000300040ba1005800ba0b200c0b6030034401140e00341d030800200001c0689076030b50002021104880410040164044100c40c4901040b6807050020004803002a035180e07150450700012a0030b0201c0c000a2001109462281e5000c0110070485a4030f0f41d82400200c5c02546800385c100c03100c440001e40c680006000820050b84520b00028200800e0741d6544d1810b0380940b81542c101d6804000c00c001c250b0240f0440c4040c1c2400c8444200661550740010841140000000c2205445000c1c1c02c040100c0c003015205841c070014000d020172034480f040d0558035001194690b640310304000303002608400600c1703800352411268000e066540c0c20f00b600f140142014040d10412482030b2540b01c215150201c1c80d200140d0700c250348102c54408 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 252280773 1250 252279523 252279527
    0x605012c0d080c060a020c060c090a030b010801020306011106150d1a0711010e0105040b060121021606050a020702060f0a0e060a030f0c020601050604170102070212011418070608040f0f06060501 85
    0x3c13000b0030b103440441c07040100b040c180d000003038282d5000203c10015507580030603c003c140c8010150703000038500940035002095201064001c0d510404007170362140c4050074500c251980d140700c00c0c2e03414240500c1c1c035401801d240c10014440fc40003070003014140c01030114a24a0044054100c42c1c500014500c099400103c41b000c0c05400018201c1d60000d00c454101600e03446000200031b007486050000031000411800b0448040c0c030102e000ca1303241151070360290501840b6138480c244040300d6083c54900001e40c01da0540c820f0b100314940160109050550044aa1b2010380c400344202040c80b4803504d402c0540c1d0789000043c21030160301d580c0172800540c002c0141d001c1d14088101201036401c88001403240e92500e0003550101d4205c0c00040803100351070014640207100c1d00300041c0d04000052913406006005400980351000c0c0341c80414181e0b640c1c00203403540045071404618031a001100e0030801c1901c501d00e0550000d0141d51180700703102860340c41c454080f4409408850f06525800104804e613 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 252282023 1250 252280773 252280783
    0xa090612020705030405120c0306090601091d0303181606050706050108150f060411040b0705060f01031101031e09060e060a0b06091011060f06130605012c0d080c 71
    0x261680c0c009500345011940d03070799200d001c1d40c0142030107480080ca0310700c3c10300c6c0d0401000303d8100001d02035502500300b00c203895482d00024058040590708000e03120400c60119800c003e1191021400346046444108002c2c1025040f1030070419584500411080c040504a9501d8000c10301611081d5407681c6a00c0c05209580c2c05030700010307446d0006c034a81d00201e913841c14800d9122903242c45c403c0190b0384003000640102803480c82280780d018040b1b00804e1940504000300360071070090003190000c2e038a490038050120790901000b0b01c0118200103002e180d5001e0b03040703a66002900038802140702146130808080b2450460f094920a40721180c200390082e052000c541c1041026a040c41040c0c107000c080f450030b00c1782c0d000c2c1341e019060358219901c03600d205031080c0c600a4144820780302241000e18001c0046a401d031840c522400c0c0010103545c03002d000d441440211001a100c01c90300c0c0083c161420700c1c0c010a0000301c9801294031a8048447c2e84411070018030a2180b0f42e4151614441152a4900303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 252283273 1250 252282023 252282047
    0x20a0906032c011503051e06060105041701021b01150e0732070b01031109070f0509130606020f1b150a02010f090b0601021005040c0b0a030e030a0906 66
    0x45803034641410074020401c0071440000b00145500981201c200c000c1da0b006104141d002c0f0900180390310040f0401102140062a2440d100b80101e40310900944468560000792405808164200010450015295006180507201400040c20507107030440040c01c180c0d20228812240c2d644031300041d0600c25a207a07107070144c003540013801c07101e1510000c05494803e440300c0416951300c0c03260041e2000c100940400d500190f08450043e00e03140c0764944412400700a0004031070381e036610303c501100f42c145840303098800c9413903030351b40c2c03008410416007580c2c075600800d401c5800401440340c01013020094040c070801010386500909a03070030f200d03031141c2c1084070020006c0160035680307154540564415046591200d6050403031a541d0706502c03010f03401000c034803940748003a500700b0409030240b0075445002481804280c0a84125044600c580e10884070111401049401a80310500c00305d110500030b081008000d00340010015001c1503003030f02e1500152108800540d040d50240455940540c1005e54 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 252284523 1250 252283273 252283277
    0x80d05030906310203100c0c05070603020708030c03040218010e10080606060f0f042111030109210203040b1c1506021009060605040510080c06160f061e020a0906 71
    0x184003440c0c2144104108440101c60308070f000d02081905564090003500703440c1503400c000300040e868281c4050013450540506407501c0c0108400002d20714080c0c02140c14043d8401503d80c91075445c4e00f00207006810240041e40c024000c00803034070900c0000312659000c0e201c203529541003490301605040380b100c190380180145070440814070115865500650f903070030f6020a50b2648131076007041640924002d40c0d026031036410031841d1001050b11035581200d9954080c1d9002d4500302112030505007038901c542801400f20309007091514680d042d8001d49104030620b841a24070f002ea4410b5401e040b41c008201d043e0940c0c0040020005a001910451846116840600e5011031800344042d4039202c0c1c000b00400d1081d121600c00c0c0800142c0c1c1e1100019240040041140d81824004121082c11a018900c4e091040e0080c401591510b002507441d09201c002e034100600c04541d07612082000c41c440f007202c019454007040582ca41c03003d8083d0001e403614078401078494000d020700a001400917804402 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 252285773 1250 252284523 252284551
    0x60e010501080c012c0d1217190c050c010c03020c0c09010b0403060b1309120306050a0b0702040b030a060c08070f0c12050304030e0a081b09061c030207080d05030906 73
    0x483c698001010015009080401801009210445401c200c105c1807019038003907100044a030410013002040c07400240650740392030303500e1000c021030940b0741c2056411145c8110544014900141c2c00d030080c0c2c1511200d40f408505003100c3e00d0304d960a445510002e240420b4000c100d407210381b0010400010b140c0422541c400d0b95501d041044040e40c46140800341a49440708000011a107403000c8807440180c2012003000b00c12814140035a18150070809200000d051020004491415900c1a815211040400b91604210307900704401440091605905070043c0303842040031624038426031542e5282c07522042068a4641c1c001088908110201401e000c1114680008125800b004001680490800780d95079161f605041d101d0180c028849a8095040c041c0407030302c2000030924a524000c07602d075070504581f00208003c2075980485007690008048045034440083d4000328169290083c0140e0b000079403102443d501740b9207030344c014102254000050142113001040140d610104035007681e1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 252287023 1250 252285773 252285793
    0x606040501210b030a030306090e01270c0504060b04081c0801030b090a0c060908070b120c1e030c031803210601030e030c07030507061b0816020904060e01050108 71
    0x60840c849041502058182c0d04628609030b8000d03603c5450035072030040888031020418903006025244a0085080f0141441d04c00488000305002c1c070509001075080b40c90322072640c5091070b002070350140419078044440030300c0090309031214499000a005149603031950b0f9810192011700c0d00c119aa605894000d1050407030040b07940c0256000e041d07035400140c40410b6210320448a00c4c001c03a407600035044084080d0005109600159014100c64042c07060b0f0f401265100803041e414048d00349500c0e80303d01103000003841c1c0e4000100403d01034010b08210003009403120000c0803190411665180640c40c0001030201c407081d09000303202d00401c100d004600c3c1100c1002c42849451518280031100c2c4001e401045031680650072000568042034101d9464001d491441a0340700c100d444260b403d80140c880220310984070310030000c0f814446510407001400c1c2a907842100307a1088810b1641c18a01000b0480181e9901c1c01050240e80109800720304c2000c0d4415460031910180e01030040c0da4840440303a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 252288273 1250 252287023 252287027
    0x9090708060f0c09090709080123130305040b09040e1b240d0c11010e0105011409010303090e041502030403021f1b030e0c0909160b03010609030f05071a040e0606040501 74
    0xa0392580d5050300e003022152684a800c1d18002c83d01d402400392035090588070301445801d08541d400310184040190140cbc0c032a22003044c482036082d08090001001000140b000d03c1c404002407400740409800042c411406900207403c112410890246807074001c0303c0281c0500e0030085089030000c80c050030076070402c0d1004028880d4410000821944da80320810340f54683d003d164103003090014500240110307a840200d0303e001301407d00801000703020054042410f4104040e80c18142c903410745a1400fa58100034081001490080007100c45e5502e41151130071802c490300140d40210b100b50010001501c81e82029048058401400c208840c86c0050701001003071810f00d00d03680d03030ba03107820300041c40c19000480034200808600c5403a00500c07244140083c041d0b0000d40300b5001c0c803a100b03849840f00d03100e04088075944820710070800000c044c2031090000c40d641038851000b07144920308030780e0099512039008007203c8a03800d804289500208040200303800d5950035640c004011101149454102000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 252289523 1250 252288273 252288277
    0x150907020318031c0c0f1e0519021008040c150e0405091c0c11030d08040210080601090611030712120b0402070f0303110715091e020d0201080a0b09090708060f0c 71
    0x90541005030a50541e01070100054400351103a401801f0080ca064620602080041c40c2d4107084030740384a11513800c1000c18903440001c00d840d0b4000c25151107070100345021170386081c001e007060b00c003240403010010310041020164008110b554442c110200d0a40f0200021103000500034030047d0000c000000390414450348803ca402062304120070b2800e42800d00305040560007c40d66014410ba41c12080303919041100c95101c3d5108840c07030301c0c011840307180446920b4000d40c2d090340460305408050041501406955110b4240740d811a4180704230b41e12840ca0260300c20100c113010500301c14014040c030619016291040500380d40039440c0a00c595118000c2e0502c041019042540d42c411503c0c8a100810449e80c1140e00b10307013004482c440c1c0b85074610003010701d01d20498606002c02514161411004206010070341c0041001880001540054929050081c03180c42c0341e07030391000010b1540d030320b269245002e1300880000f00642c0b07091522462038080040c0000441055590800c0f8602a030802 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 252290773 1250 252289523 252289573
    0x6050a140907030213030512121e01030f0f02060d05101215090203010213030804090b0907020a0b060a12140f0c0d0f050a08041d07030209031515090702031803 70
    0x10f00180d8a803030f80f000091211031507810041840c0244c0d104541c005100e08090065042e070909800100d45030045800c85001c8201c3d04058088c0c0142c004202207945000d1420100d80179514041c0c2d18480795000035020381c04500d152510a903140300380403800c1070502800010b04050003c11495080c25141c0e100010b4035160070040050b224803d00f070441d00c003034040d951001e10319036541c00b032a52030b490000d40c80d42040c041d40c1c07029803030070b0110011441c00107849030040b046c84d005004620f40c151190390429070000c1c07065801008100c400241ca00d1407240c5580840d00078081c16584120090320203050003400d10b003080b45035010810401455541c13001049085600214003140c04140c0d103050381c01c145141002070030030440441c000540780040c00d11442100b080d0352801025a590150070b0b8120300880d1851034142d03004d0141d00703500408040c0b120b41c01045118001c2d11921604000803d02c00d0f0480c0c4200060708081540c840301c1e81940d4048144050403030107000811203480d14842404000a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 252292023 1250 252290773 252290777
    0xb07020606180c090910151b020409020a0305072606040308071808010c0305160f14070c030b0a0c1d1c140f1e1515030304090f06050a140907 62
    0x40103e444440e8030000c07a514035030301411701403061912544c01045038100c2c0c8620500140c5120780b050300c980c421410b0742404260301c4c08500d100b4000da020702c401400313410f1080b0780200c1d0810021001c81d00820129005020542065450340340ca012052221445a07100d21403a90040c001c0c000000c0c1c000000c2680101c1c00e290680a2a100072540780320308000c0d038080e1842c0d501c0c0610810072140c1c1a00083d10442c820311181e03104c910111401c451746584030810390b0029480d1007981420074420b00042072030a002ea5200401107482e611000c0c200e00054515031030803541d1b001000ca44940080007000303040120030b140c103118080710300460208000146c005040b919060703482030401c14400460b941800d42c0808849100d0b146000321540c4200c4640c1003400d40740102c411010400c0001650341a104029101c00d500b51641901805044030351451903900d40018000070402c00401c2c81001940b40301c196000c03841510300001c0c03000c0088130780c010030303e1000884040311545d02c1d003a520039001003e0b8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 252293273 1250 252292023 252292069
    0x14010503120c15041b081b030d0e1e190906050307030807060c2006090f1b060703050702090a06150c1101230f0c0105090304080703080f1201120b07020606 68
    0x20b454017401642504a113481800c1e51144082030892000500301d0744010f081001d1420b20300c08400305030340c846480340c80c44001801c04c800107585082801e1050001200c03400005100f84148002172004511510300c11071403c0104010428424503000d01401400e0550107041143d0075a207660b98148100300024041580740c00d407000e4040c0c460503040f503142414403564141c00403000551034841009503954111441217103000c0000d0b40300410011041111596a03032503c42d420343c20b00055401604040e400d122040c456500075031240d207807683c4030701810301000610a0a10051209840c00e142000b070030000280502d40010f000302e400201070300000d080411143c00b00300000900c1fa0344002d603080410b0408515078102c44140c03c06001c1d41d200d40c9000b880310381c1c2c44c9400e8560f603001e00d228141c181c1d402060b0070000b00f001c00c0000e1600c441c03030f1400d151510300c020038615420442070b400a0403650035880300d41c082c45503100e1059041742040c40600f106051100010f0801035140351421120401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 252294523 1250 252293273 252293281
    0x7050310091109090c13060c080d1401030302101802012d030209010207090e030f0d0608071203030c02151902070f1a09030f0a050a0203090414010503120c15 69
    0xa50000010003144109126400d03100d01e07101141d400c20583d403406074402101044400101206680317066040c0300401185034a00001120300014034071341500c00140c104074882e500c1066000f921401214005000c001d545145002850000b40084918145282500380301140c0780d05400c002d0143e8091034100101d200750389000e14542c010011400c01e480d45c0e20030910555805401a100e50341c026000d0b82c000715a6446004280c600c00c98020741c2ca5002000401610081c1d2006002008c445550001e03205848454040c60103196401486041e22110b0014042582c0350240d004110014809401c500c0310001c0720008180d0040c244819840d03c1e281c4c41480c01480d581581d0145070007900c0c3c0c042408007401c10714241983c28501100e1070040b107000407681c01001040b221081000a000e134600101d5030811519038214960640c1180410480e00c603c075610350064280300510300405003985e514000070149081100d40c0c0d801328020b81484100b00c1c800300800d195030741c0d503880b0340304450781d0f0b1b1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 252295773 1250 252294523 252294541
    0x402070f1113021815190f1803080d021b01050709030c0618051014070c0e0106050a0f0503100b07030f080114150f040b0d05070f0e0319080c0a110406090e06070503 72
    0x70b0320086108030941ca101c01c81820747d1060350100320f2030b0750f612411010218002c401020440d01d00016181d00300400950a10301c5480d40180036a02d60031101c03180c5818068401c5080d100252508000074261000a1091000f0401e64100610681c01c06110707260010260f11000d41300341c800e1902ca8440d00c10500c0103140209400c5c4a00441814081d0781e8003c1da24280004c0d0b07469008421148141000101d11b15000702c0440704030f01129118000c0711521044125820fa0000303111b40f0200c0c518000006882a01034090007210b0311940380c2c007042102030b110003440342c1030590202c2ea01000380b1225002a8807003192810000100e01483c44e650414000c588000380f1455001f20421000020700c4440c2e4450307640414064400e42d03840d0188450402c0c02200c46042030605250300d070b0810000c4100e08e102c00303c45803900d5441200f1107030400640c0007146040036004c00c03003910320000140c01c5a03818502403081030081c1c14400c204101c260740e800400d07903440c038005080f1820b000c8008045544a0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 252297023 1250 252295773 252295777
    0x904050a03081f090504060b03120d051b030109050f0718050402030901020f04081006050a05090f07230703080f0417130909080702030c0a03150b0402070f1113021815 73
    0x14202c0707103610f1649070f44510510042c0400c490548495160000784611854082100c614808407041c41c6400e003140045d48000602c00507000c040f4018a03094104030315080798006c0c40c001c00500703000003494608040c05441d00c91004000c0303410003038010a4610800403544940060768000e550050300c981d43c41c280180207100f01121035032103020100d00084d10100001c3d03403941000c60f219090061070f664005114403164140070303c41d40040150005624840c1104540e540440c3c24138154140500010351044501c3c040d90284203000400a01074092580107010075821550703581c0d0f40a248d01d01a150391800c021106d51440b02c144002506c81c081d001c1d1404808003400618074100700c00d07085480c003a85d1a610101c0304030300a005842240c14036103402c500c1e21040320782200c102c0c1c0400c6620311401000f0110604196481582840610003099526410820007446001e03640d03541010403080100c280600d040032070a8030300400034000952032003031202d510441c2c15134003600c4055191205010074 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 252298273 1250 252297023 252297061
    0x306091009260a1409090c0702040b0d061b090302030a110a0308030f2212140403170309070e101e08030a03150506040f3003020705030c0904050a0308 66
    0x5050750045100c20010b414004040101d01e07520340d03440859099004816034003400112070352066940e000106c490b158400106003240c80104005400140c444c00a0b490103800a0103981c09565040c2c0b44140100c0d51241d090100100d09190303181c28610b80c000313603641c800038900030302a50000202c200c190302d51400700d9015681c00284261a490040180030f108041144c3c02450303001c00c607501c49041e1040000500704260401039603010ae03500100c00f5100c1c811306140c100c0d4061810400080032841c40e04110001e010154007460740e0341424445030703142070350580094140101c90405d100310324502d1706001d0200c07240c1140a050503026510020492501c6602030007103400002901c84516a040e40804107000001000140b2181c4503814445540a240164075140300958403d10903150203814101c0d0100e1841c03148030106158500e14118601c142400310f000da0300912041c84146024031541e0403c0c0c40a0704d0306a014a800e440740b41d0751703011550000c0d0030b010020010810100343c0301e1600b462 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 252299523 1250 252298273 252298313
    0x4060302090103060203060a15020604060e19050109021f050304060509120703020609011401050307300c06030c1803080309010e031b060f010605190504030209070305070e0306091009 80
    0x2d603581e04202002e1743c01210f0307041c801c0c001904d0100e09030780212a100c0c4000300c0356000b00469541c42d07a41e40018803852441c05d82c1071003195140d2000344204003650300540d10400c004a81c2c5416841440745505d000501c1128000906903a03501e500c0c0c1c0a01a0ba90040d0042004210703030f12501e04090600d401160f040c8010400002d249041c183c0000701d160168103004000c20044490682260035010203004442d4141c0041c217003000541d50b07000d03000e640c60094030000600070003502070310300341040c1043d01221300c8100350004011040d05031003544041041810410401d10b401940c0c4060345101e800010b28071480840441c00041d001d41c440c8002d851000112a03640c001d11100303e0020004180146542c452030002903450807252203514101c900030384944d0300303206102141158403a0903c0d20401044014000040580c0e10000303454000e02d001e860000d018281104002c110000b03642d00d1a0083d4441024851a6030000480103c408000f0b030000460032581d141c0b1840c021440403242c58 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 252300773 1250 252299523 252299539
    0x1080c03161206152a050c010c021206010e070207090c020c01080c1c0f0c021911130603060605130c0c030807090b0c060108010506010216050f130f06170309061804060302 75
    0x903a05400c643c905c202403035404880007007501c141d10000711402c4429070003001a0001002d01d0860b50081402d40305651004065a1401e80302440700c52810100f41c1c040b45a0740802c0f8248082d4a0b0184400f501400c0603107014001c40c03a4200d0007a54038226405418100160000018a80c204007000c0d40d000400700344600055280c1000c0070005005c50307040710f00c04d2600e41000503404600005482400b101580c05040b90340e101922544540d5451494a41d04441450a08010301c40da0b486101c02861281c17600040e282e00b4102800b03d0300140c0c07809150154584644c91101580160100c10056070600e4041410b9a45410840749482d0a03400103094550208040c2c08100000c81c0307460680d035910000b0081d6542d4480120f07038507540540d40c4120029098002d016504194904040d02d0f030014180790340722081c0491040460780e640740c0d1400c000d5900c01061008041b105c1d0f00c841d00d65998002513083c2030041001602500c00c10031605841c86c0c0310b040c880c41a40303483d00414011500241284 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 252302023 1250 252300773 252300809
    0x6040f060e011e0f0212010506030a020408060c030103030f0e03100c090f09090210170a0f09080a020616051911010f1112010b030c1c0f060b0901080c03161206 70
    0x1030f40140040c41c02440042c10200c40f91010751031442515014034140e070020382641d285c013042c02080e078805810750349540c0e002c10000c1746a59040110300e000c0d403654282c3d1070b034a61560400910311004040da1104002d9105d00303142c542d603030000d4403d19140002e00001002124800d0954062001c1d600a888000788000700150210055104028031802683d5031800419546006c4500351000e052044001c40c281b0b0119010244130f50204021400c81070700002c0307684140d140c21805400001103070005030320400401c600c1800012010001e0516070802c0c9003020704d034250012081c00645200010400030aa4400300c204094100840101c0d402c2003c2020325071010344501d2650140084248114420000003800999101101e1062519420309030034840310101542900c5e584c0100300501c02d8482c1e44400000c0010f2060074001c0c02c0c8200f400e03a0f1401c44d20b0015049000082000c2d039440c506000300f105601044501d2080c0704414a040107850015034070001c0144016000040c240a03460484 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 252303273 1250 252302023 252302051
    0xc0a0506091b0907020d05070816080901110f100e1009050309030f070501080103020f27090c060705060112020111060702030a03110a14090a090908071e0506040f060e01 74
    0xa0854000c1d000b5480000412814400051400c4d64a180107034845400d03041a584035070f02403c1c030248108003803803030121b01c1c8000c51000258004143c804050008201d00a5130304880545403030305442002d45403104d6400111a206c0541c103c100c20401d0b00d664044060380414003516200c8902c091040040100900b00075a40340c0104482601a10500850314041c000008540003210416580c00105a080d82c0c24040c504500c40c2415800000c141d42c0c400307080104c08806c00c0c0f04440b6054020842c80c00300c100f18640b030115a0994050720f010030010012460101383c50b030540c0d1441034552000011480126a0300900c401c0f8000e2a01810302801a0140e0110040c54420340903030b030900c80b44a540300d061b20a407040c1c284002c0814103007807860450850000291200c40001046c0e91074456599008600355010001b04840441000541000300090600c0c43d2800c1d904101c00300c035081000c0c2d0386031955030714080e2028061841d01d8400104200458010f000c000941e03100a000e085040841 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 252304523 1250 252303273 252303283
    0x100504110717120106020f0607050a030216060b010305010915120218180705010801082a0d05010920010903110f22061a07030302090d050d1809060e07050c0a050609 72
    0x802022814800f000050482c400210303034640d00000c0c3c0c040c021ba80c03030307940e001e69095200f80300303507401c1c10740a000b98605039400301c04042c031045c010360011036280e55a5000404849050f00034210003440c14583c021241000d8030038400307403044120315071140156400003078031051b9502500c040e414400800c00490100b40740740010102c00300d804031980303542c5840040d070b408030090055040076031002003100e546900c0da45039184034038030041c412130000103058040303440f070030b080c41c0c060301d050f0f4681d2038070000c1114803598008001c148a15484600c024000003d01c086807920015040180e03080c00c01c20741e581c800c070301c1940204004002c1000400d89030301e6214009840180f4a011600d040c100290020300c0441508442c3c1010740300b0f503d4403400d0b0b68198002c3d0010100990480d26081c5000e000600401413200180610780760409210b032190080a0400b2641e00502000d900340300342005502c1b440289035800c88694101903442c0d4665001a51500040180c00f41480c4181c8050151888020071 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 252305773 1250 252304523 252304537
    0x405010b1c2618012c01021b01210608030711010806013f2408010908090f0d0204060b180a0806042d1104050609100504110717 56
    0xe00203441c1031200101a0b0b0114140403140100d101c100694034000e03200c1203907108041c00504141040240c3c066a107104002c2441c1c0e160384005030b030b0300514019a010032101c45000c000c901d41c002e0400c6680002071425900303d083c001c1550f281c00da0780c0920689030704070b140503005820490307480700c603d0f041400c0c2c000141d50581340410b1401000ca41c25504c10341c00700e40303601044400d01e545850703502100303007011081d030714042d550002d00280d076100796a00d8058840d10501c84070341130040c0c1940f1060100c18481c2d551110121f6854803c1010000310814150340892600321580e03000c50741c403e408544e0051148030002d40c0300d0315200e40850200e4082016001c070748841c01d0b038a18800c40c1c40040c00004803040c012642151f0100c00000d0021f074a000c000c583c41c0740c039141610000101e0305881e03d09203441c5002103401c1444001e0000f000d080a1044683c410303000c54809000342420b00c07180a181035140189130265072a01c8081220008100031a492643c2c072075240d62107040855558400d0303401c059 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 252307023 1250 252305773 252305783
    0x24061513060807050c1b091305120c0a020406090b011707080f04080415080a0f020f030f090a0b090f160509070e030c031603060c030504030215040c0308040e0f0a05010f0e0405010b1c 80
    0x401080300c0300c00c01e460042045500800401d0032048468191005130064020b03400c0610cc1c10b0025801a2201d0151200501c000400451050090381c009040d4100d100300104a40b6010020070168981c8040d4441d089020300303107c100c03282c5032070901203424030681c3c01c048040200103e480202540c03050b07120340301d074200c40402c211a00007100c0c9001644110084180101814408107503507152900010b031f00080e2010441d21040d40310340d00e60005040171220b00c000303504120501d44020f1403c2c800441c10b900389600c60004207040800003083c0c0140540060104802c1c1000501c0310f031410030000030309090003009c880004800c002647c0182900b40422207119003130940341005071b4020302440340034135855005088052041c1400b40f0814800410a0303e2945c004100000414001801000500030512003680d103458050140c3d1948507001c2c14404001e458880100550b6034400701c694140c0d030081010b03240940700d41c2041409000c8607400756500000c2c50201c4034440c4949084402401c4c428 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 252308273 1250 252307023 252307039
    0x70204021206030723090a09140f01050906060a0b0c160906030311010903020312040804030b01060c05160b0a0522060c0c0e070806040b0324061513060807050c1b 71
    0x3510418801070b681c03240c5101006a14100000c0d46d1920b412265031110f07070500d00142600d0142c9031005200040b00c20402c07140c02c40755403002c980702c003800340c04c0d400112000100100d05040c0080340c149049031141d40d403800400708001c11000c00034031a002ca031265002031420840c1e15100410300902942c8401c401180c6620f210352000074060160903410b6070150084d60070407401c40301e4000c2c00e0f00d004104803400502080007000044c2c02d8019507020703000d10b54604100028600e007481c5010300500f030079642c03601c416404018076500003003251b4130155585010f5864050072110216600000324010281c4100002c0c0415041d61001d43d0040e46802541000741003540c61036000b0a00c0b90907107040c40080d0300750000a146060030b82010a41e08005030440728207140110240198903055860401c2084140040c081c40e0b160150480803000f141542c0b0b90318001226034100c2c0c1030f144912a039414401d100000801c428003d6017071760381c407804000940701090890400341125a4000840d40d1007241c2c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 252309523 1250 252308273 252308279
    0x3030c02070e150d05120a180b0c0a020f0f09090a0302010606110303010909080f03040b0612070806040f051501030f17161104060915090b041107030c03050702040212060307 76
    0x140480040c041c1448415000c0e0300f5a002c02800001000d102c0160350300e1244800040c16040b42000810000140383c1d100041c2e807200c078a8499516003e03034405c0f240c0e0b04050100d40d9000c60041520584150704541844600141002240c00d40300c0003402aa440f0100c4c204122010401041e0b01046034403e80c000c110790341c0c80701010b442d14501c4000b20b1840ba84180018044600280d1103289044e0040e400681442510100e0088560088a00312003040c100018090907051200ea150b6294004001805e107150920b01402c0c1c0d82c5c2030041c00600280d15030000202400360a01002040800d06035802e5913560712820040c0d810001c01008032540408500d207085540307101c40584e001d013000b812030780c00c526403a034840c45144a0f10929059205664020000e4905a18450011000031459031030b510540b070062a6812102000500d5011314105545950000790100071601c101354141480119480d43e0b0078101c420307014944000b508244001145441e5412194203d40301e41c000700d0455054a403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 252310773 1250 252309523 252309539
    0x150b120f101503111b07060203041505070807020918061509010603150e071713080403080f0705010f02091c050d050a1b080306032401270903030c0207 66
    0x1000321824030201e00441d0003401004418000c00c2d2141810349804940440e4444040c130300c81c1d100044000e2103244881c4240900139051003510018a01070001e10b003807030b1405034000d04081920301418108500061144200003101054450365600603103045840c0c60041c15944500a00d00c03460b014500c20400040d6100750403500091121101502c003c0182e407810074140c01609240b640c04c0c59070a44d2001c04140907a030500750034800d403203540e02c03c600900592000c1c01040000741c80e83d03e02c0d40f00e40d001400424441800c480480307904c40c0c1c50566884200c010740d00d5600070148018115401c00060100d80364881c0c001c2e2100a808542103118012014100ca041003080400148250060348256a0080c001c030081c051011103401e2010700c00190f504001038100c440f042c04c13a24070801205001040c20100032442c0301038100096810b40320f40715810111075a00c14840c2d841600094840e035003103070140c1b441207030346400d0107100be000321050340c900600030300441c000040051242820000700381c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 252312023 1250 252310773 252310801
    0x3070c09151503020c0a03091e140d08131e080606030d0305100f0e070311160209040230190804030b070221030f01060905010e09060103150b12 63
    0x1600c00c6416141d25498280c030241001d1080c0804802d1603400d005400c01e00400340300821109100b0b5a6241e01581840000d05020941c480740004070b0701911310a014100f944070502c40014002c507014400040c80740b8000215104031030b5840c00d40004110000744a4903c1002c042c04481441240a8600d480d1a6001d0b83c5040455000703070315500401c2c054407002d000e0b52282d6040b40b104c0c0c21745102c46880317242c074100d000d1035544151900c213507480400c81c10a41c03510444911181c3ea007210761601d140f10060520540b01444043d21640010307001c5800c40d9108060fa41d40c00c1801c040842c490454408038042010f20070701000707654010b2645441402c62000800411180c2c4104201e040c80e0964844400700503000700a001136102c1c0c070503c0b40240401c2e503540007940c2040d586442d924603000c01d803400115010b902c0700b02401a64403061007d82c0c2c1254242c1c000e000c0940c4d50410651b40c0c44012005854400c1101c0c6400d1040e0902088110301f0701d0080c611081044e00100b0a42c42d00c4100c0c83c102 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 252313273 1250 252312023 252312041
    0xc0f07090b03060a0b120a0318120f120e040501090902011101020a0c1e02061603020c01050f0f0a090302060c251a0a02030904050a0b0f03010c080c07020a150203070c09 74
    0x41d0490f00000d00401c03119440380b518250040c1c500c8030f4840d10315a04900d000ea0000056000c9180060301c4252615040005005420b80f021652400c0086136100c5910101030140180115014032008601d00c0c814a4071704c0d034004000300148581d595461100c0000c100200b0142c0c00079030f0015400c54031003414001c84240c40000c0e580c00c0000c0306580c80b2142c40300c403206840046d00789103100c1e103405a070b01c1c000900b194003180c41200302c02800750b02e0013900d41031080b4070789814400c0c10710061026040c0368041c1c0d8204c098690500d562408900b00c21120406290402075000b40007103100c944001001900f0304680900010603d10b500c03140c0c0004801041902c64041007540c48200030415000500c0644080c40703407030040300d091600c0c0100140a4540840d03841005650b01d07240125189802540000302035003c0d00200082c44401ea0b005090341001001d0715a1084001140011034403040d001c1002005011300104c600b0152585c0203403258050350041d20b07035030200640031400c22102c0c4034540013 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 252314523 1250 252313273 252313279
    0xc1419120e0901090e030c01020a0e13050705030402120f10150e13060213030f080a080705031302040b0a030b01030b1f060f081e04030f18050a05060f0403080c0f07090b 74
    0x100e42c3c40c112883e0083e1a034000d0700080ea0000784a07c0461132401d002801da032028a44a5030043c0150304180605098946161a501c80c285000e0201490b00102180d0308079070180c40d204800c40d185084107140040c0ba0041d4021481003086844010a1540c0891010345645040c040320540d11340e0360f110143c40541e0ad0f0400c3e00c000d4106540044e07040d50043c15143c003d03011050040382e03a41c54500000d075051105541c07a0f0000902c02c880c09034082040c1d584403205080407070640c2016a03081402003030501009006039510240410281c0e104403460700299407003190b6450540e128030300094046c4056902c540c020800804003141c074409032650b88155201540c440c1024141103e0894104001808601800901400c08120500401c05030361081e03009459042000c000150010103170340140f15849008248031030107000c559220020750f421108100c44641c0c580c059903040c80410b00c200d034401040881c0004400e80c1294010500450721701e0164217455075695104654802d8580c50380c52158 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 252315773 1250 252314523 252314539
    0x90b0906061f1b05010b1009081c050904090c05060c0c04060803030105030d0e040612030201150608010b07060504080c030a0c031e690f0c1419120e 65
    0x1500f5070704008075016260140b0000324030404080d0118040384500703007c171800640e0001c000e1005100401041308045c1d40c0224132812041480801031403801b80200a503c20340e1030b82c81103070a00c56400800c50187c1002070225030b40c0c4001d191240d03034800c0e00c5d41c5a640183e05141d0b0003d507030000802542e040701c0c0040c0c080c09885283d4001100d1041407d81505d60140c0d4408002c10a140340ca019244010b1094000241d80150b0345940c280c1c4a80c154000010010014014009450481e040c0ea8105900540100700750301c55191900240c05210003010039448082018000c9950026911000c60700a0316014801c20400d98030307900c0d00d0111032103200462004500811a90f010310065032075043e10b00e82200c1100070540c8110150700d0080c0300d100c4a2100000d821821080c1c8142082960f80d050303d180841980c4410082c4c00b1001440c4c8910500241c90320b078000303100c0280517451b00c0141d4981a5014220100d40032400c2241c0c2c06011b450031f4250b049502a13040c003030004410002d400400c00c2c6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 252317023 1250 252315773 252315797
    0x20108040f0f05030d0f051b0a03111c050105120c0d02010815090a020a09080a020d08031312030c030c0234030503030f150307060f030b04090b0906061f 67
    0x44a402506900b250750244102412000ca0018805004c2082c1d00b940007007002841d80900b003058440140164103176030f110580c4981c245030200b088540f52205404d01007229003080e444600240500308211204c40c036000440700030034665910103410b03a030044485d807806240200c1005c0c2c2d0385400c245029006040c0040c140e02541c004d20055501030310310740c580c44080d05200302184504209803417001e246600401e5190001f9000750740040980a400300504174a4481d8000034000300c00365101034103520000011131180c010310440110302d25085000007c107114030a600400508503031503064000f030703e0f1011103007500d032010503610104180401e21070085a4010b841401d210341286c140c0001c142603403000800240240051407082005107604242480c200e019600c030340c000c05007081d2007034109003402d02615030003042d09500500c481c03400007842800d40c0f001c50014182c43c040038102100003400c1200404000881d284621402e407010b070030810019106121aa95804a10300410700f019005 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 252318273 1250 252317023 252317033
    0x6080115140f06090618090c130911090a0303180f030f11060c0a060b1207060503130305041a03180102030118050c0d09050303040506010605040501050307050904090b010f1d0402010804 81
    0x40c2d211000050201c4d10340b0f002c0c00001082903101241b00e52040c100260403024a1400714a250380c040c0ea00c90786140781850303000341d00c1c8140605000351b1003040e645400e5a403c0c1d00c030303100c161780c403000000c0d203036100e000c1c0c884c2005800c1c9240321201d1016a41d20004c085604080b40c45039108407907005000311601a65a81d40800c843d005060311500701200380846c0440080401446040714010640050044020303421b00c001c56918400d0500264008002040034a91140440c0e03480f99184104103140d09aa01e000c440301d1181c0d601c2808000c202008007001081c01c040118017810241020311014050b4030951407d0740804d102d035202c151b0490421040c80c0c592508900e610407034000f4404d1901c07908254a8046448101d41518a030b8000700400081040400c00c1d503000d040541041c5080a16201c0028024800140b00008006d0f010980000c00d40b510740112446c241d004017510802d40e115500f0342140034170380c401c00d6109859509104c00c82070075840305034000d940696400020b07076142d03122 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 252319523 1250 252318273 252318289
    0xc08031606020702040f05100302041406060301061d04020a0906030f0e1b040603050f21040e060d0f0c080f070b040e010b090307080a03120c0e030d0f050f0304060608011514 76
    0x5980046d01c84042484901c1d4a108562142c941c41803151b0b0814118010722040703460b0b17213075804001500007040c0030940c2d440c00c0560b811143c1a146c204a401240c1c0c0142034071040100c040d503001400810080100c0c0e401c0341100098400350f40c2c0802032000d0040380002911441d560034600d90304900303803015100b1101d10b940c1170001c2010303102251440d5603686040c0380509000c041409a0002c10440e40405007440e1500303940c00195040034101410044a032031401d1001d05918400c000c01e1100c2c108121100c6484c2018540201c000084140d0318005140c8500e8030041c042098017403040c0118400e00c10038184c80980f0702c14003600040760308145040c0003d500840444ee414400d06d074000648075010002040300c41d101c0e43d24882c2d845180c0c0744840541d500a8941e5081c8040290300140945000030001c903100e07442d00d02904071402401c81a103161040b03904000313540100004010621626420040844031000020000c6610303204ca44020300409000e4903045201140380000c81d4036206170 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 252320773 1250 252319523 252319537
    0x10f0c03111609050f010e040c0501030207110301020a080402031009030203030a0507050f030108010b0117010803090f010320030402030f0c03030d0b011b0326070212031305060709030c0803160602 86
    0x10031542d5400040d4072055904030107600406095071038800700483c11610302107003401403001002e03a21440c02c290307841784080b4180740a1641019400f040700c0d024000b000400c42030300d94001d4000c42d5109001c400040441034105d8090703010380310341581910701c0b9409120703d000c01b9400d64003071801c54691001d00000361001428010800805022500c1c01008000c000c500030071419000081459002c07001400400510307910301280340e0b01600402030312030080115034007020210788407116440e200740168010446c04003041607003c0710307040b0010381610001c01075020724001c078100c980c400341307040d0120390342c102c035000050f0143c00902041a070071890b81c000034114807050401c00701005000720800300540700e0071b03001e40004050440110208003c2c0c400d40019a81612410100b840e00d500c001e50348503d02c01d42c03001c016a000000030b441d071f4034100349069600ea000301640c1c45420000c1000f045260180402e84403011480c000150580b0004221080302c000611480540281503c0d010000d4000707403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 252322023 1250 252320773 252320807
    0x31911040305030a0906030c09050604061809050a0e0f07030c0501051c050a0b13050709050f03160306020c07080601080a030818010e030a020d0206371b0e010f0c03 72
    0x40300100000e10180b0240085000c0e43d541d1030001860106c1c000d06407a80104a182413000c07061040c41503032510303012203059500300e0402c0f070340d1540740311031000444030f00754400d0900524060a000d11840c041e00081e000c03025404c00c4903181200313114900e48a60480c400144101c501c04c9040149500500103008003110400b00b1906103c42c01350190155841103c43d070302103607503c4251b9101ea03d0300004580e6212640e001c20085890440d4000d8050000c2c3d000c1c480c0702e0824040c0d00a2282d400f040b510456842a00c10240d1269983c83c020300603420804003d4683d0003036141c003044004000807024121802c2d0f0b00180001581500c007640c4882c80500a0f88080016041c02040c8072003d01594001c004000300542d55201c501d40b0080c100750110f1010411504030b003081c84644003040c240a078044541d04180340f07007888000c8510681610101095069604060340c40001190000c8484030691300d540702d000c40034051000441da00da01c010301e043c010509041440c03001c6441004034041a410302 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 252323273 1250 252322023 252322027
    0x5090403020f01050f0609011d0a05100305011503060b060c03180609040e0f010c030b01020c210d030207060f14150a051c050c040203010501090308071e0b09060c031911 74
    0xc49543d083d600200e0304241c0c6102c150f0140420b50138410031841c0100f81c00d4940710030b1003080e64270f55072035540080c1600315244d444e94003141c1c540035000c110000443c0e01030001c100003018007803040e000710181e21058030540d240950b0303814503081802c11503000510100107185408cc40e103009080814074141401e8200d00d05002d200d0040c0c4851280c0c0c0c1c00d21170041c0040206401005107079003914400c852090402d42084c88000042c2d03000100301030301c01800c0310004d056114480c1552100400e40950418511414a084c0c1100b42c0503402040b002d4000d0340e0034482460480b00c04000d8505c0300c402c40202c40d48010001e0340252059074618800900240310742c42c031644e02d030001102d42149030b20000c01036517481080c108000e020822023044403820b4a0075130a41d890030001034198030301444042d08076100081c2001c03c100040c510703a10020020680b1880604a42c28844080b05c401c44014105128190100703d07039001d0301056920030115901c1c425208030716801313400701a00707119107071a1000d80c2c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 252324523 1250 252323273 252323293
    0xf06030f060902040806090c040615110a06060609030519080306190302090a0b0901051005040510020304050607140f0106050a0506090310050903030708100308040905130c03030908071e0509040302 86
    0x30b030000348011716204009043d54180036451600b06010107041034031507440c043c82084940006560f542180015080c01e8103850300d600841c0d418079116180060440b440c3c500701040c0643c0188030542a03a0155086910b85221000b400100075503c92000c0e04100c41880000c6040c504400e141143c5d121000c40092801c4c5c0e00d60118001560a86d01c40700400d8a1b001d030204542000c041c014018001203462071030a0b01480c001810303610890090b40d00a52000300398641c401e008004803401404040c10441e500c642038140220310610000b07440c00d15000b180b1035004108014041d205c00d4840040c014000c3c82c2c42c0408008944e440204044d4040c002d12140c0e0220064603c5a1072242c0d4a40000c3d642e285004c4200034101c280c02000110310602d0501d00388046005003007901e0650f920f03c0b5000800b600c660381c0c182d4040c500103100a2041d9641c0101100f05a405a10507044915800841e1007490712620008070036921240119001d5800042c02c120524200c0e8105820600074015210943d81d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 252325773 1250 252324523 252324539
    0x912080906011203020f0f0c15090a05040203040f0c031a07020d0e120f010524090f040809040b060a1206091802100c020a0b18040207050c040c02190302060a050a060f06030f06 77
    0x1003000d140c7d40c141d41050030502e9141c14240516041041116070303440c0391642042c00229014040d00855004130b5021001804000801c240505041d4000305500000b40c1d4030300c0c01c003000d81c84298602d11226007034000b2600031340c0001009003108a050325413500385c00051052243c1111004140c1c03c2c244105d1102401300c1c0c1003072040314000e042503143d001d0030340742d10500340714020684800d079806030301010304104030081e44105403600142d01105803651080c000c000a005441c0e01d85c841540100c0010f1030b00310650b0020840c20408203500c600340700703c0d607aa43d0441e080710f0411140080c44000300c0241e034010307d82400c4c0310703039089e01500300303a0062220740e00801c40c01c030060707003119075400800114503021748034510100000a000312020340c50002c643c1d45041d00c0e88140500c00f4000c54039030141e1100b103170090100500414801c00a800350bc445414000d5030b030002640c894921501d01404100380305624001d02c01521040c8440c101001c3c0382010071002024450159102999500b40c0400d5000c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 252327023 1250 252325773 252325783
    0x60206060d0c15050702040c0e031f020d02040815060102010501080c04090816240603020d081c0c090303090806010503030318070911070303050a05091c0e0301050403030912080906011203020f 84
    0x542584c2d680c5880d0b55941c418001224140e4600209002c40c086411000f45c2d07000a42281c0c60082d850b100210044c1008210064081e0343c00024443d8008540030503031550001d03030003420303003c0c1200b4041541ca81d100168200d4100b809440ca841e0031005951800d801c0a8026507400d03446001e0040ca0418400160036000240e407008541f0780028074020601e107050b00c10705600089a100c010880d85241d40e0005030000c03200c41c0300800030400425152503000f00d11404012000107007805101d04941d950700100405c0003800200c000c40c02e0028007182c1c1800008030035050b02d00c064001c5155444541c12030031514100c071110345040c0b0a02c034011907664100e004004c820155200030b6a21801280740140590b08010f200899080c5400d0412882d403400040321515900e44c03091100105265120032560001c00300d840c1074143d070a00303007403004040d17156001d940f80c1809020051843c41244030100c071040c0d0240c4484080c0e80c0004010f1003070003442d40d04824030314400d0044480c105030060b6050b00341 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 252328273 1250 252327023 252327059
    0x4090c0207030302150921071211011d1b1c0b0114010e100e0d060213030c210b07050702040c0201060504060f0b07080313200f0901060206060d0c 64
    0x58000c000c0400030181c042210680d4442d4a61070000c00b850030482c0103a40d01700c0c05052611003844044001f1460580f030007110002034009500100300d000c00752025100d125161a990029860074008090364030000d280c0c61140b60b006401740054002d4107104080c04803003540507642c85002800d1024602c0070707200b041c05080b4440c0b1080003440d0724200240740103c2a80040d50b050007100c09076a2a203540b000c25200c02d0394010700b0b001e105018030700c0c04030351801e26110008140900c001010005080c13121861021079116940a009454a8416150403010921221404d0718428010301001034454409280c2c804001c1c607005041c40d0342500002c0c20b9a901d000d850300503075552a406e00560905018050140c01810032102059140540200d030f6442501b0015088000203c08503400400080040c0b501c0c1d07030042028540e40402c0d05030141800120070600d8400d10000344820110309050400504840458000c0c25032a0b4a800034006100d031151811603032191813030f0340030a000c000c2034242898 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 252329523 1250 252328273 252328277
    0x10e01052706150616060b040f14041202070b0a030b0a06050f030a050603010207060f09020910060f0311090402130608070e0a0308030a090b0108010c1701030809100519080403120903050a0302090604090c 89
    0x1f10101c10051200b01c59041550003416400c001000b14490481208282c12650004640b6441800741d28103e08180480c1c00c144040030b000201600c0c0a90f060b04165019503007140e1039070809684071010750700c0e4818500354422000d005d200045400384541c1c4056030204010300054909a855650b050440e4134007000700074516902c00c4610250b04006e55010307072107010001088201401d0039000382001981c003c5503030030140c075007540358088000d110681e40250300142041d5141c1030318040701c1c0d850420328021140054250f60000d240240301e98004031403200041c10b00b071a4141140c940102507403008090035407654131031601c2c0f0006009050054000c004042c00080e40000c500f00040c51906802a0020482c2d088401840804c4e030800840708c140700b0845480d103030b40d0f1035404192000d000f286e188010400d20040d25600c49030300010300d9031085209070340d110952080b500342030084507031703095028001600074400a0406030196005181c1c080c001851103040c1561159401d09403000c40e088100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 252330773 1250 252329523 252329531
    0xc1e030703210914040209040b090a05241014090a080c0f04020c0c010c0201110601080303071b0b2205070f0603050906011508060a08010e0105270615061606 69
    0x400042e80301d201d59061525241c4000700e240b82c686488010346120384114465640002c001e41140c0e00d0f40d0107258942e00160458055260150004c0003c100c01c4400c400c184c210b080100e04d406c4158181100310341e9000300501c000750211705046800090360406401511070400c100344543d03895100c100020034000006151180c02c03041803110301086040000d004a005010385032200c0804151008988070a280900078a141ca0004031002d240015610b545400f510002065541000c8000c601c10f100503140c0b0041c038215194080c12690410001809440d9610003085403140c1007408100e0401400300185103404464607140e003003036020f52010031003113508101000510341500403240d00c04404009842c41d50715024603240307804114003610003005072000002d4000c2d41c0d0352300319a0240c07044000030403108980b03070509030080909075003200980000031a011024000c1804044000c5601c0740a0b01c4152590740c5031800401c0740420955001c04203010700440f011003002c0d24600140100c0001c9 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 252332023 1250 252330773 252330803
    0x3080a0b060c071503150b0a020a0f0b07030b1c11030102042616030203060106030507020316060c1e02030913090212070e010f0317090409050f100609020405030c1e030703 75
    0x30a51380c0c490415801890b081178a4055020060507204080714680340500b90f42d2415640200e0400800c0070340100b1b410117000102040c002c100049c140720351020b0314108008a44c0341c1c1007000810201800c181c0c0030807804c103c0302c0000d500300150000044090005810f0640752a45010b517980c68017201c440c45501125542500041009600884008195004400790840c4c0101f5242c09050050005058840001c15a91407003003003151003450100310b40c0c4060901b40c3c900301c03018000c0700c100b0b0350008900040380c1100d1a002c604160310301c02d09030001e41c9440400070502c2298885800c10b10f0100c0d58655031000540c4685081c01c41c10b42c840c1c00a05000c1d414080805017448060b00890203c582e1848284001049815010081c00292680503110000f0400080c064204510f0041c554025101c555210003400102000c0100101d101801081e89840021040380a50b103c0e081d4151300001d51a8035a0070907a04008a811040c5824102c140403007003c280380a81d19802110403414403400a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 252333273 1250 252332023 252332039
    0x703080a050c070906140d1704140f030d0207090c020f0a050106050907030207020f09041e030306061715091b16030e09060f0f0d060608030c01151203080a0b060c07 72
    0x10f200034118003031081001c40d0401074002e00c0c4900501b266401602c40d00c9021040c4100d03252a8030b4080d9009299a54554685140030601c00e01201294002c0800340a11240d070b1801007030030348040b071103030b07006101052400b01204064644048040b0541c01501400c40401100348484503802e4001c40010801074600814000540402001001010b01c14450300c00140d441240182c2d0f07610741103c806600380c860303042000f100b45c000003918040162881c0720f14101901078100b01d00702c3c1c0c070503200e000f202e103d54035000b1041c0702c0844041d16442c0c0e0101d0f103242c86282803007000303411051009001c0610758410000c3c0c00740340e0000c40c0da8001c020450240c0c2c0c00301544070762174800e00e15080d83d83c01550b0a107a0046400d8641e1040007900c200d0500030503078041d07100d9050202c9010f800003014403c2a5583e20215144d51106000904550a00e0302c119001002c0c04010700071600e560070340081040e0b079520119201d03e4054000031100780c4030090140aa500c07800a000b0680401e409013005600c1c21a0b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 252334523 1250 252333273 252333283
    0x3011505011404150e1c0b0708010f080a170f13080723010c060f110904060806070212090315090c040f151a0904052809230703080a050c 60
    0x8941c071a42c0040000b032200d00c404184a00119003a800d0100c0c1414250000803000904a040010b40c00c46030309102050160b07404116010384000c2d00e40070150b0b600e407440805c0c4201a8054411641d005480c0f040c00202c08020980d102100e40c00c0442c1040c14250206007a94401d1800707000c0d100c0b6a4034140a4100140f0686008003842210810031700445500d0034041700c00d00314454148110440018240103142e0820045489844401c00c2005031501010020741c0224900ca80241d180c603a0104500c980000d6640c0600c082c0c2d00100010443d6068840c4a81d010780d1a00d50140180803440f04c154030080380280c090b164200c041d044030800c00d000e00045856080300d8094060178500800b0300101d016888806454410030002800c0e1070210034081103210f000580c13508286044204100c504140348202440880b244420120780405071010043d031f50384100113040b11200c5900007100c4507424070400c40c00395411040c0c41d5450780e01d8035280c3d081d42040700008045580080c62610080e400d002d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 252335773 1250 252334523 252334547
    0x1401030f0308090607090e040f060e070f0506042d0f030804031118060105212e08070b09031005160f090308040308030c0c011109040b010309151104050301150501 71
    0x1000b01344600e8004401807844803244a0494107440041c0802d040c0640d0b600e518403013030b800200c00d008884282c1541650381200d803003000c07500c0300ba031030380803d0f1403500004450031181007a40da16a186201002c24111a1103e0700e58840d0010003080014412901c0004000a40c0500e0040c1d0b1900d18604001203e80e811064840c80f41c4109000c040f0100d8100864940000c1c080c81c2085c0c941c0b50550080c03010a014071804511203524004121041407050155850a49050404061805c060990005034496030058498540000e18144040c1120710007624031080c0c001d08071482100d800494000322a800d56881040d101c4c1c1982d20101d842d0080300c06244420035242c8640c0c954a90b458000560107507020040544034000301246520884009035801e600d1900001c00481513120881030103640141400c6000d07908000100040358000e200b1505d020ba0040c0420a101c16080d881c500104500c1c500b8003402403040c000480d05841c24442c54031000c0c20b6680304207400d400d00d0009800010451 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 252337023 1250 252335773 252335791
    0xe010503101511030c0604110105190f0519030b010305092404030309050f1606080c0a0c030203220503064b090616050c0d121401030f0308 61
    0x20500248422422041c42101c54607000d16080805000046550312110951918075201c04105440c00c038402040d168001d51003458140600ca405200564150155044d281d021200d06c882d42085940599440c0e92401c4070303484d265180405101c1d50000340d59042400000080c0d841250b82c0640d6054400c00d07412044000c000d140b48060801c840a8040160112074803d1101501044c1058000c0d00070340c054640c8041612120a4100c1c03d49a880230f817a100c0c40310001d003a250000d07040f03024114140c029600810124a80511342c18252240c2d103200d0400c90451104001f801000c0c0c1844680200c0602e2250207594100e16000406141a20180c00341110340a001c2d00045402024040fa4003000607402d42c0c051402002c4880180c0c515020b01d44058480c1c242042041c0c6600210b9242d106115040380c0c08640440c0310001c6505024a50340e03442d80703602210290110341c0c00b481c3e01400d504140a00854803c0c03010b48802d0301d018003030388102c030700c55200407129041542000029511103004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 252338129 1106 252337023 252337027
    0x1109060708091807260c0a090b0a020a02041d06010e04060f0f0f0c0306061209300206070201050402150a03022712031e16051603030e0105 61
    0x813110030780064400d0100c0c9a07090038512444020800c103031009039903941c8030304000d00d6a1b400100f0400034000560380c0084d50718806002404040308030340c060300040b9242d105010035200501011031821141d00c82041e00d4500008100c0d0465141a4807038a1980352030134841e00402544480094450510313142051302d440c00d401892040351403050420504415041c01c070211401401004001509840901c0e0402c24130340144205030300510030101701c11615001a011164900d0502c0c1c04001041061a2105e4060001560014041c002070246e4602540040c40941a0124240c0b442d040801c07500c500c1c07840303a070550b5586e030320b5044030a010920342003030a4102c48644440034403d0b04621080d00360000040140c940002c0c6000210010204030504011035802c0b040302c90580c180d4520014000c2402001207910091f14a423408541e5411810018285180c0c01d20b000d0602200b = true := by decide +kernel

theorem cover : BRFrame.Cov 252158273 252338129 := by
  have h0 := BRFrame.cov_init 252158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 252158273 ≤ n) (h2 : n < 252338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
